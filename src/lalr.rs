/*!
LALR(1) parser generator.

See: DEREMER, Frank; PENNELLO, Thomas. Efficient computation of
     LALR (1) look-ahead sets. ACM Transactions on Programming
     Languages and Systems (TOPLAS), 1982, 4.4: 615-649.
*/
use petgraph::{graph::NodeIndex, visit::EdgeRef as _, Graph};
use roaring::RoaringBitmap as BitSet;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::ops;

use crate::{Grammar, Production, Symbol};

const S_PRIME: Symbol = u16::MAX - 1;
const EOF: Symbol = u16::MAX;

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
                    production: self.production,
                    cursor: self.cursor + 1,
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
        self.production.lhs.fmt(fmt)?;
        write!(fmt, " →")?;
        let (before, after) = self.production.rhs.split_at(self.cursor);
        before.iter().try_for_each(|t| write!(fmt, " {}", t))?;
        write!(fmt, " •")?;
        after.iter().try_for_each(|t| write!(fmt, " {}", t))
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
            match item.next_symbol() {
                Some(n) if g.is_nonterminal(n) => {
                    // Add initial items for all N-productions
                    for production in g.productions_for(n).unwrap() {
                        let new_item = Item {
                            production,
                            cursor: 0,
                        };
                        if set.insert(new_item) {
                            self.0.push(new_item)
                        }
                    }
                }
                _ => {}
            }
            i += 1;
        }
        self
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
        let production0 = Production {
            lhs: S_PRIME,
            rhs: &[0, EOF],
        };
        let kernel0 = Kernel::start(vec![Item {
            production: production0,
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
            for (symbol, item) in states[n].item_set.0.iter().filter_map(Item::shift_symbol) {
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
fn digraph<T, R, I, F>(xs: &[T], r: R, fp: F) -> F
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
    use Mark::*;

    let mut f = fp; // Initialize F x to F' x
    let mut stack = Vec::new();
    let mut n = vec![Unmarked; xs.len()];

    for (x, _) in xs.iter().enumerate() {
        traverse(&r, &mut stack, f.as_mut(), &mut n, x);
    }

    fn traverse<R, I>(r: &R, stack: &mut Vec<usize>, f: &mut [BitSet], n: &mut [Mark], x: usize)
    where
        R: Fn(usize) -> I,
        I: IntoIterator<Item = usize>,
    {
        if n[x] != Unmarked {
            return;
        }
        stack.push(x);
        let depth = stack.len();
        n[x] = Active(depth);

        for y in r(x).into_iter() {
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

        if n[x] == Active(depth) {
            loop {
                let z = stack.pop().unwrap();
                if z == x {
                    break;
                } else {
                    n[z] = FoundScc;
                    f[z] = f[x].clone();
                }
            }
        }
    }

    f
}

/// LR state index.
pub type StateId = usize;
/// The index of the LR parser start state.
pub const START_STATE: StateId = 0;

/// LR parse action.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Action<'grammar> {
    Shift {
        goto: StateId,
    },
    Reduce {
        production: Production<'grammar>,
        count: usize,
    },
    Accept,
}

/// LALR(1) parse table.
#[derive(Debug)]
pub struct Table<'grammar> {
    num_symbols: usize,
    table: Vec<Vec<Action<'grammar>>>,
}

impl<'grammar> ops::Index<(StateId, Symbol)> for Table<'grammar> {
    type Output = Vec<Action<'grammar>>;
    fn index(&self, (i, symbol): (StateId, Symbol)) -> &Self::Output {
        debug_assert!((symbol as usize) < self.num_symbols);
        &self.table[self.num_symbols * i + symbol as usize]
    }
}

impl<'grammar> ops::IndexMut<(StateId, Symbol)> for Table<'grammar> {
    fn index_mut(&mut self, (i, symbol): (StateId, Symbol)) -> &mut Self::Output {
        debug_assert!((symbol as usize) < self.num_symbols);
        &mut self.table[self.num_symbols * i + symbol as usize]
    }
}

impl<'grammar> Table<'grammar> {
    /// Builds a new parse table from the given grammar.
    pub fn new(g: &'grammar Grammar) -> Self {
        debug_assert!(
            g.num_symbols < u16::MAX.into(),
            "Symbol indices are too large."
        );
        let Lr0Dfa { states, .. } = Lr0Dfa::new(g);

        // Build the LALR(1) lookahead sets from the LR(0) automata
        let nullable = {
            let mut set = HashSet::new();
            // Simple O(n^2) fixpoint algorithm
            loop {
                let mut finished = true;
                for production in g.productions() {
                    if !set.contains(&production.lhs)
                        && production.rhs.iter().all(|x| set.contains(x))
                    {
                        set.insert(production.lhs);
                        finished = false;
                    }
                }
                if finished {
                    break;
                }
            }

            move |x: &Symbol| set.contains(x)
        };

        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        struct Transition {
            state: NodeIndex,
            symbol: Symbol,
        }

        // The set of nonterminal transitions of the LR(0) parser
        let xs: Vec<Transition> = states
            .node_indices()
            .flat_map(|state| {
                states
                    .edges(state)
                    .map(|e| *e.weight())
                    .filter(|&s| g.is_nonterminal(s))
                    .map(move |symbol| Transition { state, symbol })
            })
            .collect();
        let xs_index: HashMap<Transition, usize> = xs
            .iter()
            .copied()
            .enumerate()
            .map(|(i, trans)| (trans, i))
            .collect();

        // Returns direct read symbols
        let dr = |Transition {
                      state: p,
                      symbol: a,
                  }| {
            states
                .edges(states.edges(p).find(|e| *e.weight() == a).unwrap().target())
                .map(|e| *e.weight())
                .filter(|&x| !g.is_nonterminal(x))
        };

        // (p, A) READS (r, C) iff p --A-> r --C-> and C =>* eps
        let reads = |Transition {
                         state: p,
                         symbol: a,
                     }| {
            let r = states.edges(p).find(|e| *e.weight() == a).unwrap().target();
            states
                .edges(r)
                .map(|e| *e.weight())
                .filter(&nullable)
                .map(move |c| Transition {
                    state: r,
                    symbol: c,
                })
        };

        // (p, A) INCLUDES (p', B) iff B -> L A T,  T =>* eps, and p' --L-> p
        let mut includes: Vec<_> = xs.iter().map(|_| BitSet::new()).collect();
        // (q, A -> w) LOOKBACK (p, A) iff p --w-> q
        let mut lookback: HashMap<(NodeIndex, Production), HashSet<usize>> = HashMap::new();
        for (x, &Transition { state, symbol: b }) in xs.iter().enumerate() {
            // Consider start B-items
            for item in states[state]
                .item_set
                .0
                .iter()
                .filter(|item| item.production.lhs == b && item.is_start())
            {
                // Run the state machine forward
                let mut i = state;
                for (cursor, &t) in item.production.rhs.iter().enumerate().skip(item.cursor) {
                    // If this (symbol, state) is a nonterminal transition
                    if let Some(&trans) = xs_index.get(&Transition {
                        state: i,
                        symbol: t,
                    }) {
                        if item.production.rhs[cursor + 1..].iter().all(&nullable) {
                            includes[trans].insert(x as u32);
                        }
                    }

                    // Deviate from algorithm to include right nulled (RN) rules
                    if item.production.rhs[cursor..].iter().all(&nullable) {
                        lookback.entry((i, item.production)).or_default().insert(x);
                    }

                    i = states.edges(i).find(|e| *e.weight() == t).unwrap().target();
                }
                // At this point i is the final state
                lookback.entry((i, item.production)).or_default().insert(x);
            }
        }

        let read: Vec<_> = digraph(
            &xs,
            |x| reads(xs[x]).map(|x| xs_index[&x]),
            xs.iter()
                .map(|&x| dr(x).map(|x| x as u32).collect())
                .collect(),
        );
        let follow = digraph(&xs, |x| includes[x].iter().map(|x| x as usize), read);

        // LA(q, A -> w) = U{Follow(p, A) | (q, A -> w) lookback (p, A)}
        let la = |q, production| {
            lookback
                .get(&(q, production))
                .into_iter()
                .flat_map(|transitions| {
                    transitions
                        .iter()
                        .flat_map(|&transition| &follow[transition])
                        .map(|x| x as Symbol)
                })
        };

        // Build the parse table
        let eof = g.num_symbols as Symbol;
        let mut table = Table {
            num_symbols: g.num_symbols + 1,
            table: (0..states.node_count() * (g.num_symbols + 1))
                .into_iter()
                .map(|_| Vec::new())
                .collect(),
        };
        for i in states.node_indices() {
            let state = &states[i];

            for e in states.edges(i) {
                let symbol = *e.weight();
                if symbol == EOF {
                    continue;
                }
                let actions = &mut table[(e.source().index(), symbol)];
                actions.push(Action::Shift {
                    goto: e.target().index(),
                });
            }

            // Given a final A-item for production P (A != S'), fill
            // corresponding row with reduce action for P.
            for item in state
                .item_set
                .0
                .iter()
                .filter(|item| item.production.lhs != S_PRIME)
            {
                for s in la(i, item.production) {
                    let s = if s == EOF { eof } else { s };

                    let actions = &mut table[(i.index(), s)];
                    let new_action = Action::Reduce {
                        production: item.production,
                        count: item.cursor,
                    };
                    if !actions.contains(&new_action) {
                        actions.push(new_action);
                    }
                }
            }

            // For every state containing S' → w•eof, set accept in eof column
            if state
                .item_set
                .0
                .iter()
                .any(|item| item.production.lhs == S_PRIME && item.next_symbol() == Some(EOF))
            {
                table[(i.index(), eof)].push(Action::Accept);
            }
        }

        // If S ⇒* ε, set accept in eof column in the start state.
        if nullable(&0) {
            table[(START_STATE, eof)].push(Action::Accept);
        }

        table
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
            table[(START_STATE, 1)],
            &[Action::Reduce {
                production: Production { lhs: 0, rhs: &[] },
                count: 0
            }]
        );
    }
}
