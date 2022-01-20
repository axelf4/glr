/// Right nulled GLR parser (RNGLR).
use petgraph::{
    graph::{self, EdgeIndex, NodeIndex},
    Graph,
};
use std::collections::HashMap;
use std::iter;

pub mod lalr;

use lalr::Symbol;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SppfNode {
    symbol: Symbol,
    generation: usize,
}

/// Shared packed parse forest.
#[derive(Debug)]
pub struct Sppf {
    g: Graph<SppfNode, ()>,
}

impl Sppf {
    fn new() -> Self {
        Self { g: Graph::new() }
    }
}

struct GssNode {
    state: lalr::StateId,
}

struct GssEdge {
    sppf_node: NodeIndex,
}

/// Graph structured stack.
struct Gss {
    g: Graph<GssNode, GssEdge>,
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

    fn edges(&self) -> impl Iterator<Item = EdgeIndex<Ix>> + 'a
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

impl Gss {
    fn new() -> Self {
        Self { g: Graph::new() }
    }

    fn paths(&self, from: NodeIndex, length: usize) -> WalkPaths {
        WalkPaths {
            length,
            stack: vec![(None, from, self.g.neighbors(from).detach())],
        }
    }
}

/// Pending reduction.
#[derive(Debug)]
struct Reduction<'grammar> {
    node: NodeIndex,
    production: lalr::Production<'grammar>,
    count: usize,

    /// The SPPF node which labels the first edge of the path down
    /// which the reduction is applied.
    sppf_node: NodeIndex,
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
    gss: Gss,
    /// The queue of reduction operations.
    reductions: Vec<Reduction<'grammar>>,
    /// The queue of shift operations.
    shifts: Vec<Shift>,

    /// The nodes of the current generation.
    current_nodes: HashMap<lalr::StateId, NodeIndex>,
    /// The number of nodes in each completed generation.
    generation_counts: Vec<usize>,

    sppf: Sppf,
    sppf_eps: NodeIndex,
    current_sppf_nodes: HashMap<SppfNode, NodeIndex>,
}

impl<'grammar> Parser<'grammar> {
    pub fn new(grammar: &'grammar lalr::Grammar<'grammar>) -> Self {
        let table = lalr::Table::new(grammar);
        let gss = Gss::new();
        let reductions = Vec::new();
        let shifts = Vec::new();
        let mut sppf = Sppf::new();

        let sppf_eps = sppf.g.add_node(SppfNode {
            symbol: 42,
            generation: 0,
        });

        Self {
            grammar,
            table,
            gss,
            reductions,
            shifts,
            current_nodes: HashMap::new(),
            generation_counts: Vec::new(),
            sppf,
            sppf_eps,
            current_sppf_nodes: HashMap::new(),
        }
    }

    pub fn parse(mut self, input: impl IntoIterator<Item = Symbol>) -> Option<(Sppf, NodeIndex)> {
        const START_STATE: lalr::StateId = 0;
        let eof = self.grammar.num_symbols;
        let mut input = input.into_iter().chain(iter::once(eof));

        let mut a = if let Some(x) = input.next() {
            x
        } else {
            return if self.table[(START_STATE, eof)]
                .iter()
                .any(|action| matches!(action, lalr::Action::Accept))
            {
                Some((self.sppf, self.sppf_eps))
            } else {
                None
            };
        };

        let mut generation = 0;
        let v0 = self.gss.g.add_node(GssNode { state: START_STATE });
        self.current_nodes.insert(START_STATE, v0);

        for action in &self.table[(START_STATE, a)] {
            match *action {
                lalr::Action::Shift { goto } => self.shifts.push(Shift { node: v0, goto }),
                lalr::Action::Reduce {
                    production,
                    count: 0,
                } => self.reductions.push(Reduction {
                    node: v0,
                    production,
                    count: 0,
                    sppf_node: self.sppf_eps,
                }),
                _ => {}
            }
        }

        while !self.current_nodes.is_empty() {
            self.current_sppf_nodes.clear();

            self.reduce_all(a);

            self.generation_counts.push(self.gss.g.node_count());
            generation += 1;
            let prev = a;
            a = if let Some(x) = input.next() {
                x
            } else {
                break;
            };
            self.current_nodes.clear();

            self.shifter(generation, prev, a);
        }

        let acc_node = self.current_nodes.iter().find_map(|(&state, &t)| {
            if self.table[(state, eof)]
                .iter()
                .any(|action| matches!(action, lalr::Action::Accept))
            {
                let sppf_node = self.gss.g[self.gss.g.find_edge(t, v0).unwrap()].sppf_node;
                Some(sppf_node)
            } else {
                None
            }
        });
        acc_node.map(|node| (self.sppf, node))
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
        }: Reduction,
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

            // The new nonterminal SPPF node
            let z = if m == 0 {
                // TODO x_f
                self.sppf_eps
            } else {
                let c = self.generation_of(u);
                *self
                    .current_sppf_nodes
                    .entry(SppfNode {
                        symbol: production.lhs,
                        generation: c,
                    })
                    .or_insert_with(|| {
                        let z = self.sppf.g.add_node(SppfNode {
                            symbol: production.lhs,
                            generation: c,
                        });
                        z
                    })
            };

            // Push a new node w
            if let Some(&w) = self.current_nodes.get(&l) {
                if self.gss.g.find_edge(w, u).is_some() {
                    return;
                }

                self.gss.g.add_edge(w, u, GssEdge { sppf_node: z });
            } else {
                let w = self.gss.g.add_node(GssNode { state: l });
                self.current_nodes.insert(l, w);
                self.gss.g.add_edge(w, u, GssEdge { sppf_node: z });

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
                            sppf_node: self.sppf_eps,
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

                // self.add_children()
                let lambda = path
                    .edges()
                    .map(|e| self.gss.g[e].sppf_node) // TODO Reverse
                    .chain(if m > 0 { Some(sppf_node) } else { None })
                    .chain(if m == production.rhs.len() {
                        None // f = 0
                    } else {
                        // TODO x_f
                        Some(self.sppf_eps)
                    });
                // TODO Check if Λ already belongs to the family of y
                if self.sppf.g.neighbors(z).next().is_some() {
                    // Has children
                    todo!()
                } else {
                    // Does not have children
                    lambda.for_each(|l| {
                        self.sppf.g.add_edge(z, l, ());
                    });
                }
            }
        }
    }

    /// * a: The current lookahead symbol.
    fn shifter(&mut self, gen: usize, b: Symbol, a: Symbol) {
        let z = self.sppf.g.add_node(SppfNode {
            symbol: b,
            generation: gen - 1,
        });
        self.current_sppf_nodes.insert(self.sppf.g[z], z);

        for Shift { node: v, goto: k } in self.shifts.drain(..).collect::<Vec<_>>() {
            if let Some(&w) = self.current_nodes.get(&k) {
                self.gss.g.add_edge(w, v, GssEdge { sppf_node: z });

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
                self.current_nodes.insert(k, w);
                self.gss.g.add_edge(w, v, GssEdge { sppf_node: z });

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
                            sppf_node: self.sppf_eps,
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
