/*!
Right nulled GLR (RNGLR) parser.

# Example

This example shows building a parser for the grammar

```text
S → S S
S → a
S → ε
```

and using it to parse the input string `a`:

```rust
use glr::{lalr, Grammar, Parser};
let grammar = Grammar {
    num_symbols: 2,
    nonterminals: &[vec![vec![0, 0], vec![1], Vec::new()]],
};
let table = lalr::Table::new(&grammar);
let (sppf, root) = Parser::new(&grammar, &table)
    .parse([1])
    .ok_or("Failed to parse")?;

// The family of the root node is three alternative lists of children
let family: Vec<_> = root.family(&sppf).collect();
// Either a single `a`;
assert_eq!(family[0][0].symbol(&sppf), Ok(1));
// left-recursion; or
assert_eq!(family[1][0], root);
assert_eq!(family[1][1].symbol(&sppf), Err(&[0][..]));
// right recursion.
assert_eq!(family[2][0].symbol(&sppf), Ok(0));
assert_eq!(family[2][1], root);
# Ok::<(), &'static str>(())
```

Any one of the infinitely many derivation trees can be recovered by
unwinding the cycles the right number of times.

See: SCOTT, Elizabeth; JOHNSTONE, Adrian. Right nulled GLR
     parsers. ACM Transactions on Programming Languages and
     Systems (TOPLAS), 2006, 28.4: 577-618.
*/

#![deny(missing_debug_implementations)]

use petgraph::{
    graph::{self, EdgeIndex, NodeIndex},
    Graph,
};
use std::collections::{hash_map, HashMap};
use std::{iter, rc::Rc};

mod bit_set;
pub mod lalr;

use lalr::START_STATE;

/// Index of a language symbol.
pub type Symbol = u16;

/// Context-free grammar.
#[derive(Debug)]
pub struct Grammar<'a> {
    /// The total number of symbols.
    pub num_symbols: usize,
    /// Lists of productions for each nonterminal symbol of the grammar.
    ///
    /// The first nonterminal is the start symbol.
    pub nonterminals: &'a [Vec<Vec<Symbol>>],
}

impl<'a> Grammar<'a> {
    fn is_nonterminal(&self, symbol: Symbol) -> bool {
        (symbol as usize) < self.nonterminals.len()
    }

    fn productions_for(&self, nonterminal: Symbol) -> Option<impl Iterator<Item = Production<'a>>> {
        self.nonterminals.get(nonterminal as usize).map(|alts| {
            alts.iter().map(move |rhs| Production {
                lhs: nonterminal,
                rhs,
            })
        })
    }

    fn productions(&'a self) -> impl Iterator<Item = Production<'a>> {
        (0..self.nonterminals.len() as Symbol).flat_map(|x| self.productions_for(x).unwrap())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Production<'grammar> {
    pub lhs: Symbol,
    pub rhs: &'grammar [Symbol],
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct SppfLabel {
    symbol: Symbol,
    generation: usize,
}

#[derive(Debug)]
struct GssNode {
    state: lalr::StateIdx,
}

/// Graph structured stack.
#[derive(Debug)]
struct Gss<SemanticValue> {
    g: Graph<GssNode, SemanticValue>,
    /// The nodes of the current generation.
    head: HashMap<lalr::StateIdx, NodeIndex>,
    /// The number of nodes in each completed generation.
    generation_counts: Vec<usize>,
}

struct Path<'a, Ix>(&'a WalkPaths<Ix>);

impl<'a, Ix> Path<'a, Ix> {
    fn last_node(&self) -> NodeIndex<Ix>
    where
        NodeIndex<Ix>: Copy,
    {
        self.0.stack.last().map_or(self.0.from.0, |(_e, n, _)| *n)
    }

    fn edges(&self) -> impl Iterator<Item = EdgeIndex<Ix>> + DoubleEndedIterator + 'a
    where
        EdgeIndex<Ix>: Copy,
    {
        self.0.stack.iter().map(|(e, _n, _)| *e)
    }
}

struct WalkPaths<Ix = graph::DefaultIx> {
    from: (NodeIndex<Ix>, graph::WalkNeighbors<Ix>),
    length: usize,
    stack: Vec<(EdgeIndex<Ix>, NodeIndex<Ix>, graph::WalkNeighbors<Ix>)>,
    has_yielded: bool,
}

impl<Ix> WalkPaths<Ix> {
    fn next<'a, N, E, Ty>(&'a mut self, g: &Graph<N, E, Ty, Ix>) -> Option<Path<'a, Ix>>
    where
        Ty: petgraph::EdgeType,
        Ix: graph::IndexType,
    {
        loop {
            if self.stack.len() < self.length {
                if let Some((edge, next)) = self
                    .stack
                    .last_mut()
                    .map_or(&mut self.from.1, |(_, _, iter)| iter)
                    .next(g)
                {
                    self.stack.push((edge, next, g.neighbors(next).detach()));
                    continue;
                }
            } else if self.has_yielded {
                self.has_yielded = false;
            } else {
                self.has_yielded = true;
                return Some(Path(self));
            }
            self.stack.pop()?; // Exhausted iterator
        }
    }
}

impl<SemanticValue> Gss<SemanticValue> {
    fn new() -> Self {
        Self {
            g: Graph::new(),
            head: HashMap::new(),
            generation_counts: Vec::new(),
        }
    }

    fn paths(&self, from: NodeIndex, length: usize) -> WalkPaths {
        WalkPaths {
            from: (from, self.g.neighbors(from).detach()),
            length,
            stack: Vec::new(),
            has_yielded: false,
        }
    }

    /// Returns the generation of the GSS node.
    fn generation_of(&self, x: NodeIndex) -> usize {
        // This requires that GSS node indices are strictly increasing
        // starting from zero.
        match self.generation_counts.binary_search(&x.index()) {
            Ok(i) => 1 + i,
            Err(i) => i,
        }
    }

    fn add_node(&mut self, state: lalr::StateIdx) -> NodeIndex {
        let v = self.g.add_node(GssNode { state });
        self.head.insert(state, v);
        v
    }
}

/// Pending reduction.
#[derive(Debug)]
struct Reduction<'grammar, SemanticValue> {
    /// The GSS node from which the reduction is to be applied.
    node: NodeIndex,
    production: Production<'grammar>,
    /// The number of items to pop off the stack.
    count: usize,
    /// The SPPF node which labels the first edge of the path down
    /// which the reduction is applied.
    sppf_node: SemanticValue,
}

/// Pending shift.
#[derive(Debug)]
struct Shift {
    /// GSS node to which the shift is to be applied.
    node: NodeIndex,
    /// Label of the GSS node which must be created as the parent of `node`.
    goto: lalr::StateIdx,
}

pub trait SemanticAction<'grammar> {
    type Value: Clone;

    fn value(&mut self, symbol: Symbol) -> Self::Value;

    fn reduce<'a>(
        &mut self,
        production: Production<'grammar>,
        children: impl Iterator<Item = &'a Self::Value>,
    ) -> Self::Value
    where
        'grammar: 'a,
        Self::Value: 'a;

    fn eps_value(&mut self, symbols: &'grammar [Symbol]) -> Self::Value;

    fn merge(&mut self, a: &mut Self::Value, b: Self::Value);
}

/// GLR parser.
#[derive(Debug)]
pub struct Parser<'grammar, SA: SemanticAction<'grammar>> {
    grammar: &'grammar Grammar<'grammar>,
    table: &'grammar lalr::Table<'grammar>,
    gss: Gss<SA::Value>,
    /// The queue of reduction operations.
    reductions: Vec<Reduction<'grammar, SA::Value>>,
    /// The queue of shift operations.
    shifts: Vec<Shift>,
    recent_sppf_nodes: HashMap<SppfLabel, SA::Value>,
    action: SA,
}

impl<'grammar, SA: SemanticAction<'grammar>> Parser<'grammar, SA> {
    pub fn new(
        grammar: &'grammar Grammar<'grammar>,
        table: &'grammar lalr::Table<'grammar>,
        action: SA,
    ) -> Self {
        Self {
            grammar,
            table,
            gss: Gss::new(),
            reductions: Vec::new(),
            shifts: Vec::new(),
            recent_sppf_nodes: HashMap::new(),
            action,
        }
    }

    pub fn parse(mut self, input: impl IntoIterator<Item = Symbol>) -> Option<SA::Value> {
        let eof = self.grammar.num_symbols as Symbol;
        let mut input = input.into_iter().chain(iter::once(eof));

        let mut a = input.next().unwrap();

        let mut generation = 0;
        let v0 = self.gss.add_node(START_STATE);

        for action in self.table.get(START_STATE, a) {
            match action {
                lalr::Action::Shift { goto } => self.shifts.push(Shift { node: v0, goto }),
                lalr::Action::Reduce {
                    production,
                    count: 0,
                } => self.reductions.push(Reduction {
                    node: v0,
                    production,
                    count: 0,
                    sppf_node: self.action.eps_value(&[]),
                }),
                lalr::Action::Reduce { .. } => {}
                lalr::Action::Accept => return Some(self.action.eps_value(&[0])),
            }
        }

        while !self.gss.head.is_empty() {
            self.recent_sppf_nodes.clear();

            while let Some(reduction) = self.reductions.pop() {
                self.reduce(a, reduction);
            }

            let prev = a;
            a = if let Some(x) = input.next() {
                x
            } else {
                break;
            };
            self.gss.generation_counts.push(self.gss.g.node_count());
            self.gss.head.clear();
            generation += 1;

            self.shift(generation, prev, a);
        }

        let acc_node = self.gss.head.iter().find_map(|(&state, &t)| {
            if self
                .table
                .get(state, eof)
                .any(|action| matches!(action, lalr::Action::Accept))
            {
                let sppf_node = self.gss.g[self.gss.g.find_edge(t, v0).unwrap()].clone(); // TODO
                Some(sppf_node)
            } else {
                None
            }
        });
        acc_node.map(|node| node)
    }

    fn reduce(
        &mut self,
        a: Symbol,
        Reduction {
            node: v,
            production,
            count: m,
            sppf_node,
        }: Reduction<'grammar, SA::Value>,
    ) {
        let mut paths = self.gss.paths(v, m.saturating_sub(1));
        while let Some(path) = paths.next(&self.gss.g) {
            let u = path.last_node();
            let k = self.gss.g[u].state;
            let l = self
                .table
                .get(k, production.lhs)
                .find_map(|action| {
                    if let lalr::Action::Shift { goto } = action {
                        Some(goto)
                    } else {
                        None
                    }
                })
                .unwrap();

            let z = {
                // Add children to the result of the reduction
                let rn_part = if m < production.rhs.len() {
                    Some(self.action.eps_value(&production.rhs[m..]))
                } else {
                    None
                };
                let children = path
                    .edges()
                    .map(|e| &self.gss.g[e])
                    .rev()
                    .chain(if m > 0 { Some(&sppf_node) } else { None })
                    .chain(rn_part.as_ref());
                let sppf_node = self.action.reduce(production, children);
                // TODO Merge z and z2

                // let z_data = z.data_mut(&mut self.sppf).unwrap();
                // // Check if Λ already belongs to the family of z
                // if !z_data.family.contains(&children) {
                //     z_data.family.push(children);
                // }

                match self.recent_sppf_nodes.entry(SppfLabel {
                    symbol: production.lhs,
                    generation: self.gss.generation_of(u),
                }) {
                    hash_map::Entry::Occupied(x) => {
                        let sppf_node2 = x.into_mut();
                        self.action.merge(sppf_node2, sppf_node);
                        sppf_node2
                    }
                    hash_map::Entry::Vacant(x) => x.insert(sppf_node),
                }
                .clone()
            };

            // Push a new node w
            if let Some(&w) = self.gss.head.get(&l) {
                if self.gss.g.find_edge(w, u).is_none() {
                    let z_edge = self.gss.g.add_edge(w, u, z);
                    if m != 0 {
                        for action in self.table.get(l, a) {
                            match action {
                                lalr::Action::Reduce {
                                    production,
                                    count: t,
                                } if t != 0 => self.reductions.push(Reduction {
                                    node: u,
                                    production,
                                    count: t,
                                    sppf_node: z_edge,
                                }),
                                _ => {}
                            }
                        }
                    }
                }
            } else {
                let w = self.gss.add_node(l);
                for action in self.table.get(l, a) {
                    match action {
                        lalr::Action::Shift { goto: h } => {
                            self.shifts.push(Shift { node: w, goto: h });
                        }
                        lalr::Action::Reduce {
                            production,
                            count: 0,
                        } => self.reductions.push(Reduction {
                            node: w,
                            production,
                            count: 0,
                            sppf_node: self.action.eps_value(&[]),
                        }),
                        lalr::Action::Reduce {
                            production,
                            count: t,
                        } if m != 0 && t != 0 => self.reductions.push(Reduction {
                            node: u,
                            production,
                            count: t,
                            sppf_node: z.clone(),
                        }),
                        _ => {}
                    }
                }
                self.gss.g.add_edge(w, u, z);
            }
        }
    }

    /// * a: The current lookahead symbol.
    fn shift(&mut self, gen: usize, b: Symbol, a: Symbol) {
        let z = self.action.value(b);
        self.recent_sppf_nodes.insert(
            SppfLabel {
                symbol: b,
                generation: gen - 1,
            },
            z.clone(),
        );

        for Shift { node: v, goto: k } in self.shifts.drain(..).collect::<Vec<_>>() {
            if let Some(&w) = self.gss.head.get(&k) {
                self.gss.g.add_edge(w, v, z.clone());
            } else {
                let w = self.gss.add_node(k);
                self.gss.g.add_edge(w, v, z.clone());

                for action in self.table.get(k, a) {
                    match action {
                        lalr::Action::Shift { goto: h } => {
                            self.shifts.push(Shift { node: w, goto: h });
                        }
                        lalr::Action::Reduce {
                            production,
                            count: 0,
                        } => {
                            self.reductions.push(Reduction {
                                node: w,
                                production,
                                count: 0,
                                sppf_node: self.action.eps_value(&[]),
                            });
                        }
                        _ => {}
                    }
                }
            }

            for action in self.table.get(k, a) {
                match action {
                    lalr::Action::Reduce {
                        production,
                        count: t,
                    } if t != 0 => self.reductions.push(Reduction {
                        node: v,
                        production,
                        count: t,
                        sppf_node: z.clone(),
                    }),
                    _ => {}
                }
            }
        }
    }
}

/// A sub-tree in the SPPF.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SppfNode<'grammar> {
    Node {
        symbol: Symbol,
        /// The set of alternative children lists.
        family: Vec<Vec<Rc<SppfNode<'grammar>>>>,
    },
    /// ε-SPPF for the given required nullable part.
    Null(&'grammar [Symbol]),
}

impl<'grammar> SppfNode<'grammar> {
    pub fn symbol(&self) -> Result<Symbol, &'grammar [Symbol]> {
        match self {
            SppfNode::Node { symbol, .. } => Ok(*symbol),
            SppfNode::Null(xs) => Err(*xs),
        }
    }

    pub fn family(&self) -> impl Iterator<Item = &'_ [Rc<SppfNode<'grammar>>]> {
        match self {
            SppfNode::Node { family, .. } => family.iter(),
            SppfNode::Null(_) => [].iter(),
        }
        .map(AsRef::as_ref)
    }
}

/// Shared packed parse forest.
#[derive(Debug)]
pub struct Sppf;

impl<'grammar> SemanticAction<'grammar> for Sppf {
    type Value = Rc<SppfNode<'grammar>>;

    fn value<'a>(&mut self, symbol: Symbol) -> Self::Value {
        Rc::new(SppfNode::Node {
            symbol,
            family: Vec::new(),
        })
    }

    fn reduce<'a>(
        &mut self,
        production: Production<'grammar>,
        children: impl Iterator<Item = &'a Self::Value>,
    ) -> Self::Value
    where
        'grammar: 'a,
        Self::Value: 'a,
    {
        Rc::new(SppfNode::Node {
            symbol: production.lhs,
            family: vec![children.cloned().collect()],
        })
    }

    fn eps_value(&mut self, symbols: &'grammar [Symbol]) -> Self::Value {
        Rc::new(SppfNode::Null(symbols))
    }

    fn merge(&mut self, a: &mut Self::Value, b: Self::Value) {
        match ((**a).clone(), (*b).clone()) {
            (
                SppfNode::Node { symbol, mut family },
                SppfNode::Node {
                    symbol: _,
                    family: family2,
                },
            ) => {
                for children in family2 {
                    if !family.contains(&children) {
                        family.push(children);
                    }
                }
                *a = Rc::new(SppfNode::Node { symbol, family });
            }
            (SppfNode::Null(_), SppfNode::Null(_)) => {}
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error;

    // Will not work for infinite derivation trees.
    fn node_to_str<'grammar>(node: &SppfNode<'grammar>) -> String {
        let symbol_str = match node.symbol() {
            Ok(s) => s.to_string(),
            Err(ss) => format!(
                "<{}>",
                ss.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        };
        let family: Vec<_> = node.family().collect();
        match family.as_slice() {
            [] => symbol_str,
            alternatives => format!(
                "{}({})",
                symbol_str,
                alternatives
                    .iter()
                    .map(|children| children
                        .iter()
                        .map(|x| node_to_str(x.as_ref()))
                        .collect::<Vec<_>>()
                        .join(", "))
                    .collect::<Vec<_>>()
                    .join(" | ")
            ),
        }
    }

    /// The example Γ₂ from Scott et al.
    #[test]
    fn test_gamma2() -> Result<(), Box<dyn error::Error>> {
        let grammar = Grammar {
            num_symbols: 3,
            nonterminals: &[vec![vec![2, 0, 1], Vec::new()], vec![Vec::new()]],
        };
        let parse_table = lalr::Table::new(&grammar);
        let parser = Parser::new(&grammar, &parse_table, Sppf);
        let root = parser.parse([2, 2]).ok_or("Failed to parse")?;
        assert_eq!(node_to_str(root.as_ref()), "0(2, 0(2, <0,1>), <1>)");
        Ok(())
    }

    #[test]
    fn test_dangling_else() -> Result<(), Box<dyn error::Error>> {
        let grammar = Grammar {
            num_symbols: 3,
            nonterminals: &[vec![vec![1, 0], vec![1, 0, 2], Vec::new()]],
        };
        let parse_table = lalr::Table::new(&grammar);
        let parser = Parser::new(&grammar, &parse_table, Sppf);
        let root = parser.parse([1, 1, 2]).ok_or("Failed to parse")?;
        assert_eq!(
            node_to_str(root.as_ref()),
            "0(1, 0(1, <0>), 2 | 1, 0(1, 0, 2))"
        );
        Ok(())
    }

    #[test]
    fn test_simple_includes() -> Result<(), Box<dyn error::Error>> {
        let grammar = Grammar {
            num_symbols: 3,
            nonterminals: &[vec![vec![1]], vec![vec![2]]],
        };
        let parse_table = lalr::Table::new(&grammar);
        let parser = Parser::new(&grammar, &parse_table, Sppf);
        let root = parser.parse([2]).ok_or("Failed to parse")?;
        assert_eq!(node_to_str(root.as_ref()), "0(1(2))");
        Ok(())
    }
}
