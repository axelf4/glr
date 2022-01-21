/// Right nulled GLR parser (RNGLR).
use petgraph::{
    graph::{self, EdgeIndex, NodeIndex},
    Graph,
};
use std::collections::HashMap;
use std::iter;

pub mod lalr;

use lalr::Symbol;

#[derive(Clone, Debug)]
struct SppfNodeData<'grammar> {
    symbol: Symbol,
    /// The set of alternative children lists.
    family: Vec<Vec<SppfNode<'grammar>>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SppfNode<'grammar> {
    Idx(usize),
    Leaf { symbol: Symbol },
    Null(&'grammar [Symbol]),
}

impl<'grammar> SppfNode<'grammar> {
    fn data_mut<'a>(&self, sppf: &'a mut Sppf<'grammar>) -> Option<&'a mut SppfNodeData<'grammar>> {
        match *self {
            SppfNode::Idx(i) => Some(&mut sppf.nodes[i]),
            SppfNode::Leaf { .. } | SppfNode::Null(_) => None,
        }
    }
}

/// Shared packed parse forest.
#[derive(Debug)]
pub struct Sppf<'grammar> {
    nodes: Vec<SppfNodeData<'grammar>>,
}

impl<'grammar> Sppf<'grammar> {
    fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    fn add_node(&mut self, symbol: Symbol) -> SppfNode<'grammar> {
        self.nodes.push(SppfNodeData {
            symbol,
            family: Vec::new(),
        });
        SppfNode::Idx(self.nodes.len() - 1)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct SppfLabel {
    symbol: Symbol,
    generation: usize,
}

struct GssNode {
    state: lalr::StateId,
}

/// Graph structured stack.
struct Gss<'grammar> {
    g: Graph<GssNode, SppfNode<'grammar>>,
    /// The nodes of the current generation.
    head: HashMap<lalr::StateId, NodeIndex>,
    /// The number of nodes in each completed generation.
    generation_counts: Vec<usize>,
}

struct Path<'a, Ix> {
    ctx: &'a WalkPaths<Ix>,
    last_edge: Option<EdgeIndex<Ix>>,
    last_node: NodeIndex<Ix>,
}

impl<'a, Ix> Path<'a, Ix> {
    fn last_node(&self) -> NodeIndex<Ix>
    where
        NodeIndex<Ix>: Copy,
    {
        self.last_node
    }

    fn edges(&self) -> impl Iterator<Item = EdgeIndex<Ix>> + DoubleEndedIterator + 'a
    where
        EdgeIndex<Ix>: Copy,
    {
        self.ctx
            .stack
            .iter()
            .skip(1)
            .map(|(e, _n, _i)| e.unwrap())
            .chain(self.last_edge)
    }
}

struct WalkPaths<Ix = graph::DefaultIx> {
    length: usize,
    stack: Vec<(
        Option<EdgeIndex<Ix>>,
        NodeIndex<Ix>,
        graph::WalkNeighbors<Ix>,
    )>,
}

impl<Ix> WalkPaths<Ix> {
    fn next<'a, N, E, Ty>(&'a mut self, g: &Graph<N, E, Ty, Ix>) -> Option<Path<'a, Ix>>
    where
        Ty: petgraph::EdgeType,
        Ix: graph::IndexType,
    {
        let stack = &mut self.stack;
        while let (l, Some(&mut (edge, node, ref mut iter))) = (stack.len(), stack.last_mut()) {
            if l > self.length {
                stack.pop();
                return Some(Path {
                    ctx: self,
                    last_edge: edge,
                    last_node: node,
                });
            } else {
                if let Some((edge, next)) = iter.next(&g) {
                    stack.push((Some(edge), next, g.neighbors(next).detach()));
                } else {
                    stack.pop(); // Exhausted iterator
                }
            }
        }
        None
    }
}

impl<'grammar> Gss<'grammar> {
    fn new() -> Self {
        Self {
            g: Graph::new(),
            head: HashMap::new(),
            generation_counts: Vec::new(),
        }
    }

    fn paths(&self, from: NodeIndex, length: usize) -> WalkPaths {
        WalkPaths {
            length,
            stack: vec![(None, from, self.g.neighbors(from).detach())],
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
}

/// Pending reduction.
#[derive(Debug)]
struct Reduction<'grammar> {
    node: NodeIndex,
    production: lalr::Production<'grammar>,
    /// The number of items to pop off the stack.
    count: usize,
    /// The SPPF node which labels the first edge of the path down
    /// which the reduction is applied.
    sppf_node: SppfNode<'grammar>,
}

/// Pending shift.
#[derive(Debug)]
struct Shift {
    /// GSS node to which the shift is to be applied.
    node: NodeIndex,
    /// Label of the GSS node which must be created as the parent of `node`.
    goto: lalr::StateId,
}

pub struct Parser<'grammar> {
    grammar: &'grammar lalr::Grammar<'grammar>,
    table: lalr::Table<'grammar>,
    gss: Gss<'grammar>,
    /// The queue of reduction operations.
    reductions: Vec<Reduction<'grammar>>,
    /// The queue of shift operations.
    shifts: Vec<Shift>,
    sppf: Sppf<'grammar>,
    recent_sppf_nodes: HashMap<SppfLabel, SppfNode<'grammar>>,
}

impl<'grammar> Parser<'grammar> {
    pub fn new(grammar: &'grammar lalr::Grammar<'grammar>) -> Self {
        let table = lalr::Table::new(grammar);
        let gss = Gss::new();
        let reductions = Vec::new();
        let shifts = Vec::new();
        let sppf = Sppf::new();

        Self {
            grammar,
            table,
            gss,
            reductions,
            shifts,
            sppf,
            recent_sppf_nodes: HashMap::new(),
        }
    }

    pub fn parse(
        mut self,
        input: impl IntoIterator<Item = Symbol>,
    ) -> Option<(Sppf<'grammar>, SppfNode<'grammar>)> {
        const START_STATE: lalr::StateId = 0;
        let eof = self.grammar.num_symbols as Symbol;
        let mut input = input.into_iter().chain(iter::once(eof));

        let mut a = input.next().unwrap();

        let mut generation = 0;
        let v0 = self.gss.g.add_node(GssNode { state: START_STATE });
        self.gss.head.insert(START_STATE, v0);

        for &action in &self.table[(START_STATE, a)] {
            match action {
                lalr::Action::Shift { goto } => self.shifts.push(Shift { node: v0, goto }),
                lalr::Action::Reduce {
                    production,
                    count: 0,
                } => self.reductions.push(Reduction {
                    node: v0,
                    production,
                    count: 0,
                    sppf_node: SppfNode::Null(production.rhs),
                }),
                lalr::Action::Accept => return Some((self.sppf, SppfNode::Null(&[0]))),
                _ => {}
            }
        }

        while !self.gss.head.is_empty() {
            self.recent_sppf_nodes.clear();

            self.reduce_all(a);

            let prev = a;
            a = if let Some(x) = input.next() {
                x
            } else {
                break;
            };
            self.gss.generation_counts.push(self.gss.g.node_count());
            self.gss.head.clear();
            generation += 1;

            self.shifter(generation, prev, a);
        }

        let acc_node = self.gss.head.iter().find_map(|(&state, &t)| {
            if self.table[(state, eof)]
                .iter()
                .any(|action| matches!(action, lalr::Action::Accept))
            {
                let sppf_node = self.gss.g[self.gss.g.find_edge(t, v0).unwrap()];
                Some(sppf_node)
            } else {
                None
            }
        });
        acc_node.map(|node| (self.sppf, node))
    }

    fn reduce_all(&mut self, a: Symbol) {
        while let Some(reduction) = self.reductions.pop() {
            self.reduce(a, reduction);
        }
    }

    fn reduce(
        &mut self,
        a: Symbol,
        Reduction {
            node: v,
            production,
            count: m,
            sppf_node,
        }: Reduction<'grammar>,
    ) {
        let mut paths = self.gss.paths(v, m.saturating_sub(1));
        while let Some(path) = paths.next(&self.gss.g) {
            let u = path.last_node();
            let k = self.gss.g[u].state;
            let l = *self.table[(k, production.lhs)]
                .iter()
                .find_map(|action| {
                    if let lalr::Action::Shift { goto } = action {
                        Some(goto)
                    } else {
                        None
                    }
                })
                .unwrap();

            let z = if m == 0 {
                SppfNode::Null(production.rhs)
            } else {
                *self
                    .recent_sppf_nodes
                    .entry(SppfLabel {
                        symbol: production.lhs,
                        generation: self.gss.generation_of(u),
                    })
                    .or_insert_with(|| self.sppf.add_node(production.lhs))
            };

            // Push a new node w
            if let Some(&w) = self.gss.head.get(&l) {
                if self.gss.g.find_edge(w, u).is_some() {
                    return;
                }

                self.gss.g.add_edge(w, u, z);
            } else {
                let w = self.gss.g.add_node(GssNode { state: l });
                self.gss.head.insert(l, w);
                self.gss.g.add_edge(w, u, z);

                for &action in &self.table[(l, a)] {
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
                            sppf_node: SppfNode::Null(production.rhs),
                        }),
                        _ => {}
                    }
                }
            }

            if m != 0 {
                for &action in &self.table[(l, a)] {
                    match action {
                        lalr::Action::Reduce {
                            production,
                            count: t,
                        } if t != 0 => self.reductions.push(Reduction {
                            node: u,
                            production,
                            count: t,
                            sppf_node: z,
                        }),
                        _ => {}
                    }
                }

                // Add children to the result of the reduction
                let children = path
                    .edges()
                    .map(|e| self.gss.g[e])
                    .rev()
                    .chain(if m > 0 { Some(sppf_node) } else { None })
                    .chain(if m == production.rhs.len() {
                        None
                    } else {
                        Some(SppfNode::Null(&production.rhs[m..]))
                    })
                    .collect();
                let z_data = z.data_mut(&mut self.sppf).unwrap();
                // Check if Λ already belongs to the family of z
                if !z_data.family.contains(&children) {
                    z_data.family.push(children);
                }
            }
        }
    }

    /// * a: The current lookahead symbol.
    fn shifter(&mut self, gen: usize, b: Symbol, a: Symbol) {
        let z = SppfNode::Leaf { symbol: b };
        self.recent_sppf_nodes.insert(
            SppfLabel {
                symbol: b,
                generation: gen - 1,
            },
            z,
        );

        for Shift { node: v, goto: k } in self.shifts.drain(..).collect::<Vec<_>>() {
            if let Some(&w) = self.gss.head.get(&k) {
                self.gss.g.add_edge(w, v, z);

                for &action in &self.table[(k, a)] {
                    match action {
                        lalr::Action::Reduce {
                            production,
                            count: t,
                        } if t != 0 => self.reductions.push(Reduction {
                            node: v,
                            production,
                            count: t,
                            sppf_node: z,
                        }),
                        _ => {}
                    }
                }
            } else {
                let w = self.gss.g.add_node(GssNode { state: k });
                self.gss.head.insert(k, w);
                self.gss.g.add_edge(w, v, z);

                for &action in &self.table[(k, a)] {
                    match action {
                        lalr::Action::Shift { goto: h } => {
                            self.shifts.push(Shift { node: w, goto: h });
                        }
                        lalr::Action::Reduce {
                            production,
                            count: t,
                        } if t != 0 => self.reductions.push(Reduction {
                            node: v,
                            production,
                            count: t,
                            sppf_node: z,
                        }),
                        _ => {}
                    }
                }

                for &action in &self.table[(k, a)] {
                    match action {
                        lalr::Action::Reduce {
                            production,
                            count: 0,
                        } => self.reductions.push(Reduction {
                            node: w,
                            production,
                            count: 0,
                            sppf_node: SppfNode::Null(production.rhs),
                        }),
                        _ => {}
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gamma2() {
        let grammar = lalr::Grammar {
            num_symbols: 3,
            nonterminals: &[vec![vec![2, 0, 1], Vec::new()], vec![Vec::new()]],
        };

        let parser = Parser::new(&grammar);
        dbg!(&parser.table);

        dbg!(parser.parse([2, 2]));

        /*
        println!(
            "{:?}",
            petgraph::dot::Dot::with_config(&sppf.g, &[petgraph::dot::Config::EdgeNoLabel])
        );
        */

        assert!(false);
    }
}
