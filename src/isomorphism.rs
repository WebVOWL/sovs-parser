use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use itertools::Itertools;
use radguy::{
    Arguments, PairUniverse, System, Universe, Visited,
    arena::Key,
    extension::TermSystem,
    set::bitset::{BitSet, BitsetRelation},
};
use radguy_ccs::systems::bool::{BoolSystem, BoolSystemImpl, BoolTerm};

use crate::{Properties, Specification};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default, Debug)]
pub struct VarKey(usize);
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default, Debug)]
pub struct TermKey(usize);

impl From<usize> for VarKey {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Key for VarKey {
    fn index(&self) -> usize {
        self.0
    }
}

impl From<usize> for TermKey {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Key for TermKey {
    fn index(&self) -> usize {
        self.0
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum VarName {
    Node(String, String),
    Edge(String, String),
}

impl Default for VarName {
    fn default() -> Self {
        Self::Node(String::new(), String::new())
    }
}

#[derive(Debug)]
pub struct GraphSystem {
    bool_system: RefCell<BoolSystemImpl<VarKey, TermKey, VarName>>,
    left_spec: Specification,
    right_spec: Specification,
    locked: bool,
}

impl GraphSystem {
    #[must_use]
    pub fn new(left_spec: Specification, right_spec: Specification) -> Self {
        Self {
            bool_system: RefCell::default(),
            left_spec,
            right_spec,
            locked: false,
        }
    }

    #[must_use]
    pub fn node_variable(&self, left: String, right: String) -> VarKey {
        self.bool_system
            .borrow_mut()
            .names
            .get_or_insert_key(VarName::Node(left, right))
    }

    fn expand(&self, key: VarKey) {
        let name = self.bool_system.borrow().names.get_value(key).clone();
        let definition = self.build_definition(&name);
        let term = self
            .bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(definition);
        self.bool_system.borrow_mut().definitions.insert(key, term);
    }

    fn build_definition(&self, var: &VarName) -> BoolTerm<VarKey, TermKey> {
        match var {
            VarName::Node(l, r) => {
                let left_props = &self
                    .left_spec
                    .nodes
                    .get(l)
                    .expect("node should have properties")
                    .properties;
                let right_props = &self
                    .right_spec
                    .nodes
                    .get(r)
                    .expect("node should have properties")
                    .properties;

                if !left_props
                    .unmapped()
                    .eq_ignore_case(&right_props.unmapped())
                    || self.left_spec.in_edges(l).len() != self.right_spec.in_edges(r).len()
                    || self.left_spec.out_edges(l).len() != self.right_spec.out_edges(r).len()
                {
                    return BoolTerm::True;
                }
                let ins = self.edges_term(
                    &self.left_spec.in_edges(l).into_iter().collect::<Vec<_>>(),
                    &self.right_spec.in_edges(r).into_iter().collect::<Vec<_>>(),
                );
                let outs = self.edges_term(
                    &self.left_spec.out_edges(l).into_iter().collect::<Vec<_>>(),
                    &self.right_spec.out_edges(r).into_iter().collect::<Vec<_>>(),
                );
                let mapped = self.node_mapping_term(left_props, right_props);
                BoolTerm::Or(vec![ins, outs, mapped])
            }
            VarName::Edge(l, r) => {
                let left_edge = self.left_spec.edges.get(l).expect("left edge should exist");
                let right_edge = self
                    .right_spec
                    .edges
                    .get(r)
                    .expect("right edge should exist");
                if !left_edge
                    .properties
                    .unmapped()
                    .eq_ignore_case(&right_edge.properties.unmapped())
                {
                    return BoolTerm::True;
                }
                let mut bool_system = self.bool_system.borrow_mut();
                let to = bool_system
                    .names
                    .get_or_insert_key(VarName::Node(left_edge.to.clone(), right_edge.to.clone()));
                let from = bool_system.names.get_or_insert_key(VarName::Node(
                    left_edge.from.clone(),
                    right_edge.from.clone(),
                ));
                let to_term = bool_system.terms.get_or_insert_key(BoolTerm::Variable(to));
                let from_term = bool_system
                    .terms
                    .get_or_insert_key(BoolTerm::Variable(from));
                drop(bool_system);
                let mapped_term =
                    self.edge_mapping_term(&left_edge.properties, &right_edge.properties);

                BoolTerm::Or(vec![to_term, from_term, mapped_term])
            }
        }
    }

    fn edges_term(&self, left_edges: &[&str], right_edges: &[&str]) -> TermKey {
        let pairing_terms = matchings(left_edges, right_edges)
            .map(|pairing| {
                let term = BoolTerm::Or(
                    pairing
                        .into_iter()
                        .map(|(l, r)| self.edge_pair_to_term_key(l.to_string(), r.to_string()))
                        .collect(),
                );
                self.bool_system.borrow_mut().terms.get_or_insert_key(term)
            })
            .collect();
        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::And(pairing_terms))
    }

    /// Returns a term corresponding to matching the mappings of node properties (e.g.
    /// `equivalentTo`)
    fn node_mapping_term(&self, left_props: &Properties, right_props: &Properties) -> TermKey {
        let left_mapped = left_props.node_mapped();
        let right_mapped = right_props.node_mapped();

        let mut bool_system = self.bool_system.borrow_mut();

        if left_mapped.0.keys().cloned().collect::<HashSet<_>>()
            != right_mapped.0.keys().cloned().collect::<HashSet<_>>()
        {
            return bool_system.terms.get_or_insert_key(BoolTerm::True);
        }

        let terms = left_mapped
            .0
            .into_iter()
            .map(|(key, left_prop)| {
                let right_prop = right_mapped
                    .0
                    .get(&key)
                    .expect("right node should have matching properties")
                    .clone();

                let left_vals = left_prop.iter().cloned().collect::<Vec<_>>();
                let right_vals = right_prop.iter().cloned().collect::<Vec<_>>();

                let prop_terms = matchings(&left_vals, &right_vals)
                    .map(|m| {
                        let vars = m
                            .into_iter()
                            .map(|(l, r)| {
                                let name = bool_system.names.get_or_insert_key(VarName::Node(l, r));
                                bool_system
                                    .terms
                                    .get_or_insert_key(BoolTerm::Variable(name))
                            })
                            .collect();
                        bool_system.terms.get_or_insert_key(BoolTerm::Or(vars))
                    })
                    .collect();

                bool_system
                    .terms
                    .get_or_insert_key(BoolTerm::And(prop_terms))
            })
            .collect();
        bool_system.terms.get_or_insert_key(BoolTerm::Or(terms))
    }

    /// Returns a term corresponding to matching the mappings of edge properties (e.g.
    /// `inverseOf`)
    fn edge_mapping_term(&self, left_props: &Properties, right_props: &Properties) -> TermKey {
        let left_mapped = left_props.edge_mapped();
        let right_mapped = right_props.edge_mapped();

        let mut bool_system = self.bool_system.borrow_mut();

        if left_mapped.0.keys().cloned().collect::<HashSet<_>>()
            != right_mapped.0.keys().cloned().collect::<HashSet<_>>()
        {
            return bool_system.terms.get_or_insert_key(BoolTerm::True);
        }

        let terms = left_mapped
            .0
            .into_iter()
            .map(|(key, left_prop)| {
                let right_prop = right_mapped
                    .0
                    .get(&key)
                    .expect("right node should have matching properties")
                    .clone();

                let left_vals = left_prop.iter().cloned().collect::<Vec<_>>();
                let right_vals = right_prop.iter().cloned().collect::<Vec<_>>();

                let prop_terms = matchings(&left_vals, &right_vals)
                    .map(|m| {
                        let vars = m
                            .into_iter()
                            .map(|(l, r)| {
                                let name = bool_system.names.get_or_insert_key(VarName::Edge(l, r));
                                bool_system
                                    .terms
                                    .get_or_insert_key(BoolTerm::Variable(name))
                            })
                            .collect();
                        bool_system.terms.get_or_insert_key(BoolTerm::Or(vars))
                    })
                    .collect();

                bool_system
                    .terms
                    .get_or_insert_key(BoolTerm::And(prop_terms))
            })
            .collect();
        bool_system.terms.get_or_insert_key(BoolTerm::Or(terms))
    }

    fn edge_pair_to_term_key(&self, left: String, right: String) -> TermKey {
        let name = VarName::Edge(left, right);
        let key = self.bool_system.borrow_mut().names.get_or_insert_key(name);
        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::Variable(key))
    }

    fn ensure_variable_defined(&self, variable: VarKey) {
        let term_key = {
            let sys = self.bool_system.borrow();
            sys.definitions.get(variable).copied()
        };

        if term_key.is_none() {
            self.expand(variable);
        }
    }
}

impl System<VarKey, bool> for GraphSystem {
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, bool>) -> bool {
        self.ensure_variable_defined(key);
        self.bool_system.borrow().evaluate(key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, bool> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.locked = true;
    }

    fn unlock(&mut self) {
        self.locked = false;
    }
}

impl Universe<BitSet<VarKey>> for GraphSystem {
    fn universe(&self) -> BitSet<VarKey> {
        self.bool_system.borrow().universe()
    }
}

impl PairUniverse<BitsetRelation<VarKey, VarKey>> for GraphSystem {
    fn pair_universe(&self) -> BitsetRelation<VarKey, VarKey> {
        self.bool_system.borrow().pair_universe()
    }
}

impl Arguments<VarKey, HashSet<VarKey>> for GraphSystem {
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        self.bool_system.borrow().arguments(key)
    }
}

impl Visited<BitSet<VarKey>> for GraphSystem {
    fn visited(&self) -> BitSet<VarKey> {
        self.bool_system.borrow().visited()
    }
}

impl TermSystem<VarKey, bool, TermKey> for GraphSystem {
    fn definition(&self, variable: VarKey) -> TermKey {
        self.bool_system.borrow().definition(variable)
    }
}

impl BoolSystem<VarKey, TermKey, VarName> for GraphSystem {
    fn get_term(&self, term_key: TermKey) -> BoolTerm<VarKey, TermKey> {
        self.bool_system.borrow().get_term(term_key)
    }

    fn evaluate_term(
        &self,
        term_key: TermKey,
        assignment: &dyn radguy::Assignment<VarKey, bool>,
    ) -> bool {
        self.bool_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }
}

pub enum PropertyMappingKind {
    Node,
    Edge,
}

pub fn get_property_mapping_kind(key: &str) -> Option<PropertyMappingKind> {
    match key {
        "equivalentTo" => Some(PropertyMappingKind::Node),
        "inverseOf" | "subPropertyOf" => Some(PropertyMappingKind::Edge),
        _ => None,
    }
}

pub fn matchings<T: Clone, U: Clone>(left: &[T], right: &[U]) -> impl Iterator<Item = Vec<(T, U)>> {
    left.iter()
        .cloned()
        .permutations(left.len())
        .map(|lefts| lefts.into_iter().zip(right.iter().cloned()).collect())
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_matchings() {
        let left = vec![1, 2, 3];
        let right = vec![4, 5, 6];
        let pairs: Vec<_> = matchings(&left, &right)
            .map(|mut p| {
                p.sort_unstable();
                p
            })
            .sorted_unstable()
            .collect();
        let expected: Vec<_> = [
            vec![(1, 4), (2, 5), (3, 6)],
            vec![(1, 5), (2, 6), (3, 4)],
            vec![(1, 6), (2, 4), (3, 5)],
            vec![(1, 5), (2, 4), (3, 6)],
            vec![(1, 6), (2, 5), (3, 4)],
            vec![(1, 4), (2, 6), (3, 5)],
        ]
        .into_iter()
        .map(|mut p| {
            p.sort_unstable();
            p
        })
        .sorted_unstable()
        .collect();

        assert_eq!(pairs, expected);
    }

    fn compare_specs(a: &str, b: &str, eq: bool) {
        let a = Specification::parse(a).expect("spec a should parse");
        let b = Specification::parse(b).expect("spec b should parse");
        assert_eq!(eq, a.is_isomorphic_to(&b));
    }

    #[test]
    fn single_node() {
        compare_specs("node a {}", "node b {}", true);
    }

    #[test]
    fn single_edge() {
        compare_specs(
            r"
                node a {}
                node b {}
                edge e from a to b {}
            ",
            r"
                node x {}
                node y {}
                edge z from x to y {}
                ",
            true,
        );
    }

    #[test]
    fn single_node_different_props() {
        compare_specs(
            r#"
                node a { text: "a"; }
                "#,
            r#"
                node a { text: "b"; }
                "#,
            false,
        );
    }

    #[test]
    fn single_node_same_props() {
        compare_specs(
            r#"
                node a { text: "a"; kind: "owl:class"; }
                "#,
            r#"
                node a { kind: "owl:class"; text: "a"; }
                "#,
            true,
        );
    }

    #[test]
    fn single_edge_different_props() {
        compare_specs(
            r#"
                node a {}
                node b {}
                edge e from a to b { text: "a"; }
            "#,
            r#"
                node x {}
                node y {}
                edge z from x to y { text: "b"; }
                "#,
            false,
        );
    }

    #[test]
    fn single_edge_different_on_from() {
        compare_specs(
            r#"
                node a { text: "a"; }
                node b { text: "c"; }
                edge e from a to b { text: "a"; }
            "#,
            r#"
                node x { text: "b"; }
                node y { text: "c"; }
                edge z from x to y { text: "a"; }
                "#,
            false,
        );
    }

    #[test]
    fn single_edge_different_on_to() {
        compare_specs(
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                edge e from a to b { text: "a"; }
            "#,
            r#"
                node x { text: "a"; }
                node y { text: "c"; }
                edge z from x to y { text: "a"; }
                "#,
            false,
        );
    }

    #[test]
    fn chain_with_in() {
        compare_specs(
            r"
                node a {}
                node b {}
                node c {}
                node d {}
                node e {}
                edge e1 from a to b {}
                edge e2 from b to c {}
                edge e3 from c to d {}
                edge e4 from e to b {}
                ",
            r"
                node a {}
                node b {}
                node c {}
                node d {}
                node e {}
                edge e1 from a to b {}
                edge e2 from b to c {}
                edge e3 from c to d {}
                edge e4 from e to c {}
                ",
            false,
        );
    }

    #[test]
    fn self_cycle_pos() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                "#,
            r#"
                node b { text: "a"; }
                edge e1 from b to b { text: "a"; }
                "#,
            true,
        );
    }

    #[test]
    fn self_cycle_neg_node() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                "#,
            r#"
                node b { text: "b"; }
                edge e1 from b to b { text: "a"; }
                "#,
            false,
        );
    }

    #[test]
    fn self_cycle_multiple_edges_pos() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                edge e2 from a to a { text: "a"; }
                edge e3 from a to a { text: "b"; }
                "#,
            r#"
                node b { text: "a"; }
                edge e1 from b to b { text: "a"; }
                edge e2 from b to b { text: "a"; }
                edge e3 from b to b { text: "b"; }
                "#,
            true,
        );
    }

    #[test]
    fn self_cycle_multiple_edges_neg_node() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                edge e2 from a to a { text: "a"; }
                edge e3 from a to a { text: "b"; }
                "#,
            r#"
                node b { text: "b"; }
                edge e1 from b to b { text: "a"; }
                edge e2 from b to b { text: "a"; }
                edge e3 from b to b { text: "b"; }
                "#,
            false,
        );
    }

    #[test]
    fn self_cycle_multiple_edges_neg_edge() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                edge e2 from a to a { text: "a"; }
                edge e3 from a to a { text: "b"; }
                "#,
            r#"
                node b { text: "a"; }
                edge e1 from b to b { text: "a"; }
                edge e2 from b to b { text: "a"; }
                edge e3 from b to b { text: "c"; }
                "#,
            false,
        );
    }

    #[test]
    fn self_cycle_multiple_edges_neg_edge_count() {
        compare_specs(
            r#"
                node a { text: "a"; }
                edge e1 from a to a { text: "a"; }
                edge e2 from a to a { text: "a"; }
                edge e3 from a to a { text: "a"; }
                "#,
            r#"
                node b { text: "a"; }
                edge e1 from b to b { text: "a"; }
                edge e2 from b to b { text: "a"; }
                "#,
            false,
        );
    }

    #[test]
    fn cycle_2() {
        compare_specs(
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                edge e1 from a to b { text: "a"; }
                edge e2 from b to a { text: "b"; }
                "#,
            r#"
                node b { text: "a"; }
                node a { text: "b"; }
                edge e1 from a to b { text: "b"; }
                edge e2 from b to a { text: "a"; }
                "#,
            true,
        );
    }

    #[test]
    fn cycle_3() {
        compare_specs(
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                node c { text: "c"; }
                edge e1 from a to b { text: "a"; }
                edge e2 from b to c { text: "b"; }
                edge e3 from c to a { text: "c"; }
                "#,
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                node c { text: "c"; }
                edge e1 from a to b { text: "a"; }
                edge e2 from b to c { text: "b"; }
                edge e3 from c to a { text: "c"; }
                "#,
            true,
        );
    }

    #[test]
    fn multiple_components() {
        compare_specs(
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                node c { text: "c"; }
                edge e1 from a to b { text: "a"; }
                "#,
            r#"
                node a { text: "a"; }
                node b { text: "b"; }
                node c { text: "d"; }
                edge e1 from a to b { text: "a"; }
                "#,
            false,
        );
    }

    #[test]
    fn multiple_edges_same_props_pos() {
        compare_specs(
            r#"
            node a {}
            node b {}
            edge e1 from a to b { text: "a"; }
            edge e2 from a to b { text: "a"; }
            "#,
            r#"
            node a {}
            node b {}
            edge e1 from b to a { text: "a"; }
            edge e2 from b to a { text: "a"; }
            "#,
            true,
        );
    }

    #[test]
    fn multiple_edges_same_props_neg() {
        compare_specs(
            r#"
            node a {}
            node b {}
            edge e1 from a to b { text: "a"; }
            edge e2 from a to b { text: "a"; }
            "#,
            r#"
            node a { text: "a"; }
            node b {}
            edge e1 from b to a { text: "a"; }
            edge e2 from b to a { text: "a"; }
            "#,
            false,
        );
    }

    #[test]
    fn multiple_edges_different_props_pos() {
        compare_specs(
            r#"
            node a {}
            node b {}
            edge e1 from a to b { text: "a"; }
            edge e2 from a to b { text: "b"; }
            "#,
            r#"
            node a {}
            node b {}
            edge e1 from b to a { text: "a"; }
            edge e2 from b to a { text: "b"; }
            "#,
            true,
        );
    }

    #[test]
    fn multiple_edges_different_props_neg_edge() {
        compare_specs(
            r#"
            node a {}
            node b {}
            edge e1 from a to b { text: "a"; }
            edge e2 from a to b { text: "b"; }
            "#,
            r#"
            node a {}
            node b {}
            edge e1 from b to a { text: "a"; }
            edge e2 from b to a { text: "c"; }
            "#,
            false,
        );
    }

    #[test]
    fn multiple_edges_different_props_neg_node() {
        compare_specs(
            r#"
            node a {}
            node b {}
            edge e1 from a to b { text: "a"; }
            edge e2 from a to b { text: "b"; }
            "#,
            r#"
            node a { text: "b"; }
            node b {}
            edge e1 from b to a { text: "a"; }
            edge e2 from b to a { text: "b"; }
            "#,
            false,
        );
    }

    #[test]
    fn node_properties_case_insensitive() {
        compare_specs(
            r#"
            node a { text: "A"; }
            "#,
            r#"
            node a { text: "a"; }
            "#,
            true,
        );
    }

    #[test]
    fn edge_properties_case_insensitive() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b {}
            edge e from a to b { text: "B"; }
            "#,
            r#"
            node a { text: "A"; }
            node b {}
            edge e from a to b { text: "b"; }
            "#,
            true,
        );
    }

    #[test]
    fn mapped_node_properties_pos() {
        compare_specs(
            r#"
            node a { text: "A"; equivalentTo: "b"; }
            node b { text: "B"; }
            node c { text: "C"; }
        "#,
            r#"
            node x { text: "A"; equivalentTo: "y"; }
            node y { text: "B"; }
            node z { text: "C"; }
        "#,
            true,
        );
    }

    #[test]
    fn mapped_node_properties_neg() {
        compare_specs(
            r#"
            node a { text: "A"; equivalentTo: "b"; }
            node b { text: "B"; }
            node c { text: "C"; }
        "#,
            r#"
            node x { text: "A"; equivalentTo: "z"; }
            node y { text: "B"; }
            node z { text: "C"; }
        "#,
            false,
        );
    }

    #[test]
    fn mapped_edge_properties_pos() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge i from a to b { text: "I"; inverseOf: "e"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge y from a to b { text: "I"; inverseOf: "x"; }
        "#,
            true,
        );
    }

    #[test]
    fn mapped_edge_properties_neg() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge f from a to b { text: "F"; }
            edge i from a to b { text: "I"; inverseOf: "e"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge w from a to b { text: "F"; }
            edge y from a to b { text: "I"; inverseOf: "w"; }
        "#,
            false,
        );
    }

    #[test]
    fn mapped_edge_properties_multiple_pos() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge f from a to b { text: "F"; }
            edge g from a to b { text: "G"; }
            edge i from a to b { text: "I"; inverseOf: "e"; inverseOf: "f"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge w from a to b { text: "F"; }
            edge u from a to b { text: "G"; }
            edge y from a to b { text: "I"; inverseOf: "x"; inverseOf: "w"; }
        "#,
            true,
        );
    }

    #[test]
    fn mapped_edge_properties_multiple_neg() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge f from a to b { text: "F"; }
            edge g from a to b { text: "G"; }
            edge i from a to b { text: "I"; inverseOf: "e"; inverseOf: "f"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge w from a to b { text: "F"; }
            edge u from a to b { text: "G"; }
            edge y from a to b { text: "I"; inverseOf: "x"; inverseOf: "u"; }
        "#,
            false,
        );
    }

    #[test]
    fn mapped_edge_properties_multiple_different_pos() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge f from a to b { text: "F"; }
            edge g from a to b { text: "G"; }
            edge i from a to b { text: "I"; inverseOf: "e"; subPropertyOf: "f"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge w from a to b { text: "F"; }
            edge u from a to b { text: "G"; }
            edge y from a to b { text: "I"; inverseOf: "x"; subPropertyOf: "w"; }
        "#,
            true,
        );
    }

    #[test]
    fn mapped_edge_properties_multiple_different_neg() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge e from a to b { text: "E"; }
            edge f from a to b { text: "F"; }
            edge g from a to b { text: "G"; }
            edge i from a to b { text: "I"; inverseOf: "e"; subPropertyOf: "f"; }
        "#,
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            edge x from a to b { text: "E"; }
            edge w from a to b { text: "F"; }
            edge u from a to b { text: "G"; }
            edge y from a to b { text: "I"; inverseOf: "x"; subPropertyOf: "u"; }
        "#,
            false,
        );
    }

    #[test]
    fn mapped_node_properties_different_sets() {
        compare_specs(
            r#"
            node a { text: "A"; }
            node b { text: "B"; }
            node c { text: "C"; }
        "#,
            r#"
            node x { text: "A"; equivalentTo: "z"; }
            node y { text: "B"; }
            node z { text: "C"; }
        "#,
            false,
        );
    }
}
