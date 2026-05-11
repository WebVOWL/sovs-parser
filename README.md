# SOVS
SOVS is the Simple Ontology Visualization Specification language.

This crate consists of three components: The SOVS language itself, the verifier, and a test suite.

## Getting started
Using SOVS to verify a visualization requires the following steps:
- Define a conversion from your visualization format to a SOVS graph (i.e. implementing `From/TryFrom<T> for Specification`).
- For each test case in the suite:
    - Turn the ontology into your visualization format.
    - Turn that into a SOVS graph using the previously defined conversion.
    - Compare the two using `Specification::is_isomorphic_to`.

In Rust, this would be something like:
```rust
#[test]
fn sovs_suite() {
    for test_case in sovs_parser::test_cases() {
        let visualization = Visualization::new(test_case.text);
        let sovs = Specification::from(visualization);
        assert!(sovs.is_isomorphic_to(test_case.specification));
    }
}
```

## Syntax
The syntax of SOVS is as follows:
```math
\begin{align}
\mathbf{Spec} &::= (\mathbf{NodeDef} \mid \mathbf{EdgeDef})^* \\
\mathbf{NodeDef} &::= \texttt{node} \  \mathbf{Id} \ \texttt{\{} \ \mathbf{Props} \ \texttt{\}} \\
\mathbf{EdgeDef} &::= \texttt{edge} \ \mathbf{Id} \ \texttt{from} \ \mathbf{Id} \ \texttt{to} \ \mathbf{Id} \ \texttt{\{} \ \mathbf{Props} \ \texttt{\}} \\
\mathbf{Props} &::= (\mathbf{PropertyName} \texttt{:} \mathbf{Value} \texttt{;})^* \\
\mathbf{Id} &::= [\texttt{a-zA-Z\_}][\texttt{a-zA-Z0-9\_}]^* \\
\mathbf{PropertyName} &::= [\texttt{a-zA-Z\_}][\texttt{a-zA-Z0-9\_:}]^* \\
\mathbf{Value} &::= \texttt{"} \mathbf{String} \texttt{"}
\end{align}
```

For examples, see the [test suite](test-suite/sovs).
