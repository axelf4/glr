# glr

GLR parser in Rust.

[![crates.io](https://img.shields.io/crates/v/glr.svg)](https://crates.io/crates/glr)
[![docs.rs](https://img.shields.io/docsrs/glr)](https://docs.rs/glr)

This crate is most useful when parsers need to be generated at runtime
from context-free grammars that depend on user input. In other cases,
the [LALRPOP] crate is likely to be more suitable.

## Example

This example shows building a parser for the grammar

```text
S → S S
S → a
S → ε
```

and using it to parse the input string `a`:

```rust
use glr::{lalr, Grammar, Parser, sppf::{Sppf, SppfNode}};
let grammar = Grammar {
    num_symbols: 2,
    nonterminals: &[vec![vec![0, 0], vec![1], Vec::new()]],
};
let table = lalr::Table::new(&grammar);
let mut sppf = Sppf::new();
let root = Parser::new(&grammar, &table, &mut sppf).parse([1]).ok_or("Failed to parse")?;

// The family of the root node is three alternative lists of children
let family: Vec<_> = root.family(&sppf).collect();
// Either a single `a`;
assert!(matches!(family[0][0], SppfNode::Node { symbol: 1, .. }));
// left-recursion; or
assert_eq!(family[1][0], root);
assert!(matches!(family[1][1], SppfNode::Null(&[0])));
// right recursion.
assert!(matches!(family[2][0], SppfNode::Node { symbol: 0, .. }));
assert_eq!(family[2][1], root);
```

Any one of the infinitely many derivation trees can be recovered by
unwinding the cycles the right number of times.

[LALRPOP]: https://github.com/lalrpop/lalrpop
