use std::unreachable;

use crate::{Production, SemanticAction, Symbol};

#[derive(Clone, Debug)]
struct SppfNodeData<'grammar> {
    /// The set of alternative children lists.
    family: Vec<Vec<SppfNode<'grammar>>>,
}

/// A sub-tree in the SPPF.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SppfNode<'grammar> {
    Node {
        symbol: Symbol,
        data_idx: Option<usize>,
    },
    /// ε-SPPF for the given nullable part.
    Null(&'grammar [Symbol]),
}

impl<'grammar> SppfNode<'grammar> {
    pub fn family<'a>(
        &self,
        sppf: &'a Sppf<'grammar>,
    ) -> impl Iterator<Item = &'a [SppfNode<'grammar>]> {
        match self {
            SppfNode::Node {
                data_idx: Some(i), ..
            } => sppf.data[*i].family.iter(),
            _ => [].iter(),
        }
        .map(AsRef::as_ref)
    }
}

/// Shared packed parse forest.
#[derive(Debug)]
pub struct Sppf<'grammar> {
    data: Vec<SppfNodeData<'grammar>>,
}

impl<'grammar> Sppf<'grammar> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }
}

impl<'grammar> SemanticAction<'grammar> for Sppf<'grammar> {
    type Value = SppfNode<'grammar>;

    fn value<'a>(&mut self, symbol: Symbol) -> Self::Value {
        SppfNode::Node {
            symbol,
            data_idx: None,
        }
    }

    fn reduce<'a>(
        &mut self,
        prev: Option<&mut Self::Value>,
        production: Production<'grammar>,
        children: impl Iterator<Item = &'a Self::Value>,
    ) -> Self::Value
    where
        'grammar: 'a,
        Self::Value: 'a,
    {
        let children = children.cloned().collect();
        match prev {
            Some(SppfNode::Node {
                symbol,
                data_idx: Some(data_idx),
                ..
            }) => {
                let family = &mut self.data[*data_idx].family;
                if !family.contains(&children) {
                    family.push(children);
                }
                SppfNode::Node {
                    symbol: *symbol,
                    data_idx: Some(*data_idx),
                }
            }
            Some(_) => unreachable!(),
            None => {
                let data_idx = self.data.len();
                self.data.push(SppfNodeData {
                    family: vec![children],
                });
                SppfNode::Node {
                    symbol: production.lhs,
                    data_idx: Some(data_idx),
                }
            }
        }
    }

    fn eps_value(&mut self, symbols: &'grammar [Symbol]) -> Self::Value {
        SppfNode::Null(symbols)
    }
    fn eps_nonterminal_value(&mut self, symbol: Symbol) -> Self::Value {
        SppfNode::Node {
            symbol,
            data_idx: None,
        }
    }
}
