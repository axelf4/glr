/*!
LALR(1) parser generator.

See: DEREMER, Frank; PENNELLO, Thomas. Efficient computation of
     LALR (1) look-ahead sets. ACM Transactions on Programming
     Languages and Systems (TOPLAS), 1982, 4.4: 615-649.
*/
use hashbrown::{HashMap, HashSet};
use petgraph::visit::{EdgeRef as _, IntoNodeReferences as _};
use petgraph::{graph::NodeIndex, Graph};
use std::cmp::min;
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::iter::FusedIterator;

use crate::bit_set::BitSet;
use crate::{Grammar, Production, Symbol};

const S_PRIME: Symbol = u16::MAX;

impl Grammar<'_> {
    /// Computes the nullable nonterminals and first sets.
    fn nullable_and_first_sets(&self) -> (impl Fn(Symbol) -> bool, Vec<BitSet>) {
        let mut first_sets = vec![BitSet::new(); self.nonterminals.len()];
        let mut nullables = BitSet::new();
        let mut changed = true;
        while changed {
            changed = false;
            let mut result = BitSet::new();
            for production in self.productions() {
                let mut is_nullable = true;
                for &symbol in production.rhs {
                    if self.is_nonterminal(symbol) {
                        is_nullable &= nullables.contains(symbol.into());
                        result |= &first_sets[symbol as usize];
                    } else {
                        is_nullable = false;
                        result.insert(symbol.into());
                    }
                    if !is_nullable {
                        break;
                    }
                }

                if is_nullable && !nullables.contains(production.lhs.into()) {
                    changed = true;
                    nullables.insert(production.lhs.into());
                } else {
                    changed |= !result.is_subset(&first_sets[production.lhs as usize]);
                }
                first_sets[production.lhs as usize] |= &result;
                result.clear();
            }
        }
        (move |x: Symbol| nullables.contains(x.into()), first_sets)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Item<'grammar> {
    production: Production<'grammar>,
    cursor: usize,
}

impl<'grammar> Item<'grammar> {
    /// Returns the symbol to the right of the dot.
    fn next_symbol(&self) -> Option<Symbol> {
        self.production.rhs.get(self.cursor).copied()
    }

    fn shift_symbol(&self) -> Option<(Symbol, Item<'grammar>)> {
        self.next_symbol().map(|s| {
            (
                s,
                Item {
                    cursor: self.cursor + 1,
                    ..*self
                },
            )
        })
    }

    fn is_start(&self) -> bool {
        self.cursor == 0
    }
}

impl fmt::Display for Item<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{} →", self.production.lhs)?;
        let (before, after) = self.production.rhs.split_at(self.cursor);
        before.iter().try_for_each(|t| write!(fmt, " {t}"))?;
        write!(fmt, " •")?;
        after.iter().try_for_each(|t| write!(fmt, " {t}"))
    }
}

#[derive(Debug)]
struct ItemSet<'grammar>(Vec<Item<'grammar>>);

impl<'grammar> ItemSet<'grammar> {
    /// Returns the transitive closure of the specified item set.
    fn closure(mut self, g: &'grammar Grammar<'grammar>) -> Self {
        let mut set: HashSet<_> = self.0.iter().copied().collect();
        let mut i = 0;
        while let Some(&item) = self.0.get(i) {
            // If the cursor is just left of some nonterminal N
            for production in item
                .next_symbol()
                .and_then(|n| g.productions_for(n))
                .into_iter()
                .flatten()
            {
                // Add initial items for all N-productions
                let new_item = Item {
                    production,
                    cursor: 0,
                };
                if set.insert(new_item) {
                    self.0.push(new_item);
                }
            }
            i += 1;
        }
        self
    }

    fn iter(&self) -> impl Iterator<Item = &Item<'grammar>> {
        self.0.iter()
    }
}

/// A state is uniquely identified by its "seed" items, i.e. the kernel.
///
/// This is because the transitive closure only adds start items,
/// while the item dots of all kernels other than the first are
/// advanced.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Kernel<'grammar>(Vec<Item<'grammar>>);

impl<'grammar> Kernel<'grammar> {
    fn start(items: Vec<Item<'grammar>>) -> Self {
        debug_assert!(items.iter().all(Item::is_start));
        Self(items)
    }

    fn shifted(items: Vec<Item<'grammar>>) -> Self {
        debug_assert!(items.iter().all(|i| i.cursor > 0));
        Self(items)
    }
}

impl<'grammar> From<Kernel<'grammar>> for ItemSet<'grammar> {
    fn from(x: Kernel<'grammar>) -> Self {
        Self(x.0)
    }
}

#[derive(Debug)]
struct State<'grammar> {
    item_set: ItemSet<'grammar>,
}

struct Lr0Dfa<'grammar> {
    states: Graph<State<'grammar>, Symbol>,
}

impl<'grammar> Lr0Dfa<'grammar> {
    /// Constructs the LR(0) DFA.
    fn new(g: &'grammar Grammar) -> Self {
        let mut states = Graph::new();
        // Augment the grammar with a production `S' → S`, where `S` is the start symbol.
        // To generate the initial item set, take the closure of the item `S' → •S`.
        let kernel0 = Kernel::start(vec![Item {
            production: Production {
                lhs: S_PRIME,
                rhs: &[0],
            },
            cursor: 0,
        }]);
        let state0 = states.add_node(State {
            item_set: ItemSet::from(kernel0.clone()).closure(g),
        });
        let mut kernel_set: HashMap<Kernel, NodeIndex> = HashMap::new();
        kernel_set.insert(kernel0, state0);
        let mut stack = vec![state0];
        while let Some(n) = stack.pop() {
            // All transitions on shifted symbols from this state
            let mut goto_sets: HashMap<_, Vec<_>> = HashMap::new();
            for (symbol, item) in states[n].item_set.iter().filter_map(Item::shift_symbol) {
                goto_sets.entry(symbol).or_default().push(item);
            }

            for (x, goto_set) in goto_sets {
                // The goto_set:s remain sorted here, because
                // transitive closure and shifting preserve order.
                // Therefore kernels may be compared as lists instead
                // of as sets.
                let m = *kernel_set
                    .entry(Kernel::shifted(goto_set))
                    .or_insert_with_key(|kernel| {
                        let new_state = states.add_node(State {
                            item_set: ItemSet::from(kernel.clone()).closure(g),
                        });
                        stack.push(new_state);
                        new_state
                    });

                // Add an edge X from current state to Goto(I, X) state
                states.add_edge(n, m, x);
            }
        }

        Self { states }
    }
}

/// The Digraph algorithm.
///
/// Takes `R`, a relation on `X`, and `F'`, a function from `X` to
/// sets, and outputs `F`, a function from `X` to sets, such that `F
/// x` satisfies
///
/// ```text
/// F x =s F' x ∪ ⋃{F y | xRy}
/// ```
fn digraph<R, I, F>(xs_len: usize, r: R, fp: F) -> F
where
    R: Fn(usize) -> I,
    I: IntoIterator<Item = usize>,
    F: AsMut<[BitSet]>,
{
    // Let G = (X, R) be the digraph induced by R, for example
    //
    //         (a)
    //        /  ^                               {a,b,c}  {e}
    //       v    \                               |   \   /
    //     (b)--->(c)   (e)  reduces to the DAG   v    v v
    //            / \   /                        {f}   {d}
    //           v   v v
    //         (f)   (d)
    //
    // For the graph G' on the right where all strongly connected
    // components have been collapsed, each leaf x has no y such that
    // xRy; F x is simply F' x, and for a nonleaf x, F x is F' x
    // unioned with the F-values of its children. Thus standard
    // tree-traversal would work.
    //
    // The following is therefore an adapted algorithm for finding
    // SCC:s that computes F without explicitly constructing G'.

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum Mark {
        Unmarked,
        Active(usize),
        FoundScc,
    }

    fn traverse<R, I>(r: &R, stack: &mut Vec<usize>, f: &mut [BitSet], n: &mut [Mark], x: usize)
    where
        R: Fn(usize) -> I,
        I: IntoIterator<Item = usize>,
    {
        if n[x] != Mark::Unmarked {
            return;
        }
        stack.push(x);
        let depth = stack.len();
        n[x] = Mark::Active(depth);

        for y in r(x) {
            if y == x {
                continue;
            }

            traverse(r, stack, f, n, y);
            n[x] = min(n[x], n[y]);

            if let (a, [fy, b @ ..]) = f.split_at_mut(y) {
                let fx = if x < y { &mut a[x] } else { &mut b[x - y - 1] };
                *fx |= &*fy;
            } else {
                unreachable!()
            }
        }

        if n[x] == Mark::Active(depth) {
            loop {
                let z = stack.pop().unwrap();
                if z == x {
                    break;
                }
                n[z] = Mark::FoundScc;
                f[z] = f[x].clone();
            }
        }
    }

    let mut f = fp; // Initialize F x to F' x
    let mut stack = Vec::new();
    let mut n = vec![Mark::Unmarked; xs_len];
    for x in 0..xs_len {
        traverse(&r, &mut stack, f.as_mut(), &mut n, x);
    }
    f
}

/// LR state index.
pub type StateIdx = usize;
/// The index of the LR parser start state.
pub const START_STATE: StateIdx = 0;

/// LR parse action.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Action<'grammar> {
    Shift {
        goto: StateIdx,
    },
    Reduce {
        production: Production<'grammar>,
        count: usize,
    },
    Accept,
}

union TableEntry<'grammar> {
    count: usize,
    action: Action<'grammar>,
}

/// LALR(1) parse table.
pub struct Table<'grammar> {
    grammar: &'grammar Grammar<'grammar>,
    entries: Vec<TableEntry<'grammar>>,
    table: Vec<u16>,
}

impl<'grammar> Table<'grammar> {
    /// Builds a new parse table from the given grammar.
    pub fn new(g: &'grammar Grammar) -> Self {
        let Lr0Dfa { states } = Lr0Dfa::new(g);
        let eof: Symbol = g.num_symbols.try_into().expect("Too many symbols");
        // Build the LALR(1) lookahead sets from the LR(0) automata
        let (nullable, first_sets) = g.nullable_and_first_sets();

        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        struct Transition {
            state: NodeIndex,
            symbol: Symbol,
        }

        // The set of nonterminal transitions of the LR(0) parser
        let xs: HashMap<_, _> = states
            .edge_references()
            .filter_map(|e| {
                let state = e.source();
                let symbol = *e.weight();
                if g.is_nonterminal(symbol) {
                    Some(Transition { state, symbol })
                } else {
                    None
                }
            })
            .enumerate()
            .map(|(i, transition)| (transition, i))
            .collect();

        // Read(p, A) are the terminals that can be read before any
        // phrase including A is reduced. Compute using first sets.
        //
        // See: IVES, Fred. Unifying view of recent LALR (1) lookahead
        //      set algorithms. ACM SIGPLAN Notices, 1986, 21.7: 131-135.
        let mut read = vec![BitSet::new(); xs.len()];
        read[xs[&Transition {
            state: NodeIndex::new(START_STATE),
            symbol: 0,
        }]]
            .insert(eof.into());
        // (p, A) INCLUDES (p', B) iff B -> L A T,  T =>* eps, and p' --L-> p
        let mut includes = vec![BitSet::new(); xs.len()];
        // (q, A -> w) LOOKBACK (p, A) iff p --w-> q
        let mut lookback: HashMap<(NodeIndex, Production), BitSet> = HashMap::new();
        for (&Transition { state, symbol: b }, &x) in &xs {
            // Consider start B-items
            for item in states[state]
                .item_set
                .iter()
                .filter(|&item| item.production.lhs == b && item.is_start())
            {
                // Run the state machine forward
                let mut p = state;
                for (cursor, &a) in item.production.rhs.iter().enumerate().skip(item.cursor) {
                    // If (p, A) is a nonterminal transition
                    if let Some(&y) = xs.get(&Transition {
                        state: p,
                        symbol: a,
                    }) {
                        for &symbol in &item.production.rhs[cursor + 1..] {
                            if g.is_nonterminal(symbol) {
                                read[y] |= &first_sets[symbol as usize];
                                if !nullable(symbol) {
                                    break;
                                }
                            } else {
                                read[y].insert(symbol.into());
                                break;
                            }
                        }

                        if item.production.rhs[cursor + 1..]
                            .iter()
                            .copied()
                            .all(&nullable)
                        {
                            includes[y].insert(x as u32);
                        }
                    }

                    // Include right nulled (RN) rules
                    if item.production.rhs[cursor..].iter().copied().all(&nullable) {
                        lookback
                            .entry((p, item.production))
                            .or_default()
                            .insert(x as u32);
                    }

                    p = states.edges(p).find(|e| *e.weight() == a).unwrap().target();
                }
                // At this point p is the final state
                lookback
                    .entry((p, item.production))
                    .or_default()
                    .insert(x as u32);
            }
        }

        let follow = digraph(xs.len(), |x| includes[x].iter().map(|x| x as usize), read);
        // LA(q, A -> w) = U{Follow(p, A) | (q, A -> w) lookback (p, A)}
        let lookahead = |q, production| {
            lookback
                .get(&(q, production))
                .into_iter()
                .flat_map(|transitions| {
                    transitions
                        .iter()
                        .flat_map(|transition| &follow[transition as usize])
                        .map(|x| x as Symbol)
                })
        };

        // Build the parse table
        let num_symbols = g.num_symbols + /* eof */ 1;
        let mut entries: Vec<TableEntry<'grammar>> = Vec::new();
        let mut entry_indices = HashMap::new();
        let mut table = vec![0; num_symbols * states.node_count()];
        let mut row = vec![Vec::new(); num_symbols - g.nonterminals.len()];
        for (i, state) in states.node_references() {
            // Given a final A-item for production P (A != S'), fill
            // corresponding row with reduce action for P.
            for item in state
                .item_set
                .iter()
                .filter(|item| item.production.lhs != S_PRIME)
            {
                for s in lookahead(i, item.production) {
                    let actions = &mut row[s as usize - g.nonterminals.len()];
                    let action = Action::Reduce {
                        production: item.production,
                        count: item.cursor,
                    };
                    if !actions.contains(&action) {
                        actions.push(action);
                    }
                }
            }

            for e in states.edges(i) {
                let symbol = *e.weight();
                if g.is_nonterminal(symbol) {
                    table[num_symbols * i.index() + symbol as usize] = e.target().index() as u16;
                } else {
                    let actions = &mut row[symbol as usize - g.nonterminals.len()];
                    actions.push(Action::Shift {
                        goto: e.target().index(),
                    });
                }
            }

            // For every state containing S' → w•eof, set accept in eof column
            if state
                .item_set
                .iter()
                .any(|item| item.production.lhs == S_PRIME && item.cursor > 0)
                // If S ⇒* ε, set accept in eof column in the start state
                || i.index() == START_STATE && nullable(0)
            {
                row[eof as usize - g.nonterminals.len()].push(Action::Accept);
            }

            struct FixedHash<T>(u64, T);

            impl<T> Hash for FixedHash<T> {
                fn hash<H: Hasher>(&self, state: &mut H) {
                    state.write_u64(self.0);
                }
            }

            for (t, actions) in row.iter_mut().enumerate() {
                let hash = {
                    let mut s = entry_indices.hasher().build_hasher();
                    actions.hash(&mut s);
                    s.finish()
                };
                let hash2 = {
                    let mut s = entry_indices.hasher().build_hasher();
                    s.write_u64(hash);
                    s.finish()
                };
                let (&mut FixedHash(_, idx), _) = entry_indices
                    .raw_entry_mut()
                    .from_hash(hash2, |&FixedHash(_, k): &FixedHash<usize>| {
                        entries[k + 1..][..unsafe { entries[k].count }]
                            .iter()
                            .map(|x| unsafe { &x.action })
                            .eq(actions.iter())
                    })
                    .or_insert_with(|| {
                        let idx = entries.len();
                        entries.reserve(1 + actions.len());
                        entries.push(TableEntry {
                            count: actions.len(),
                        });
                        entries.extend(actions.iter().map(|&action| TableEntry { action }));
                        (FixedHash(hash, idx), ())
                    });
                table[num_symbols * i.index() + g.nonterminals.len() + t] = idx as u16;
                actions.clear();
            }
        }

        Self {
            grammar: g,
            entries,
            table,
        }
    }

    pub fn get(&self, state: StateIdx, symbol: Symbol) -> Actions<'grammar, '_> {
        let i = self.table[(self.grammar.num_symbols + 1) * state + symbol as usize] as usize;
        Actions(if self.grammar.is_nonterminal(symbol) {
            ActionsInner::Shift(Some(i))
        } else {
            // Safety: Table is constructed such that each cell index
            // points at entry with count followed by that many
            // actions.
            let count = unsafe { self.entries[i].count };
            let actions = &self.entries[i + 1..][..count];
            ActionsInner::Entries(actions)
        })
    }
}

impl<'grammar> fmt::Debug for Table<'grammar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let num_symbols = self.grammar.num_symbols + 1;
        let num_states = self.table.len() / num_symbols;
        f.debug_list()
            .entries((0..num_states).flat_map(|state| {
                (0..num_symbols as Symbol).map(move |symbol| self.get(state, symbol))
            }))
            .finish()
    }
}

#[derive(Clone, Copy)]
enum ActionsInner<'grammar, 'a> {
    Shift(Option<StateIdx>),
    /// Slice of parse actions for a table cell.
    ///
    /// All entries have to be the [TableEntry::Action] variant.
    Entries(&'a [TableEntry<'grammar>]),
}

#[derive(Clone)]
pub struct Actions<'grammar, 'a>(ActionsInner<'grammar, 'a>);

impl<'grammar, 'a> Iterator for Actions<'grammar, 'a> {
    type Item = Action<'grammar>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            ActionsInner::Shift(x) => x.take().map(|goto| Action::Shift { goto }),
            ActionsInner::Entries(xs) => {
                let (entry, rest) = xs.split_first()?;
                *xs = rest;
                // Safety: The slice is always constructed above to only contain actions.
                Some(unsafe { entry.action })
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.0 {
            ActionsInner::Shift(x) => x.into_iter().size_hint(),
            ActionsInner::Entries(x) => x.iter().size_hint(),
        }
    }
}

impl ExactSizeIterator for Actions<'_, '_> {}

impl FusedIterator for Actions<'_, '_> {}

impl fmt::Debug for Actions<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_item() {
        assert_eq!(
            format!(
                "{}",
                Item {
                    production: Production {
                        lhs: 1,
                        rhs: &[1, 2]
                    },
                    cursor: 1
                }
            ),
            "1 → 1 • 2"
        );
    }

    #[test]
    fn test_build_lr0_automata() {
        let nonterminals = &[vec![vec![0, 1], Vec::new()]];
        let grammar = Grammar {
            num_symbols: 2,
            nonterminals,
        };
        let table = Table::new(&grammar);
        assert_eq!(
            table.get(START_STATE, 1).collect::<Vec<_>>(),
            [Action::Reduce {
                production: Production { lhs: 0, rhs: &[] },
                count: 0
            }]
        );
    }
}
