use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use itertools::Itertools;
use radguy::{
    Arguments, PairUniverse, System, Universe, Visited,
    arena::Key,
    set::bitset::{BitSet, BitsetRelation},
};
use radguy_ccs::systems::bool::{BoolSystemImpl, BoolTerm};

use crate::Specification;

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
enum VarName {
    Node(String, String),
    Edge(String, String),
}

impl Default for VarName {
    fn default() -> Self {
        Self::Node(String::new(), String::new())
    }
}

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
                if self
                    .left_spec
                    .nodes
                    .get(l)
                    .expect("node should have properties")
                    != self
                        .right_spec
                        .nodes
                        .get(r)
                        .expect("node should have properties")
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
                BoolTerm::Or(vec![ins, outs])
            }
            VarName::Edge(l, r) => {
                let left_edge = self.left_spec.edges.get(l).expect("left edge should exist");
                let right_edge = self
                    .right_spec
                    .edges
                    .get(r)
                    .expect("rihgt edge should exist");
                if left_edge.properties != right_edge.properties {
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

                BoolTerm::Or(vec![to_term, from_term])
            }
        }
    }

    fn edges_term(&self, left_edges: &[&str], right_edges: &[&str]) -> TermKey {
        let pairing_terms = pairings(left_edges, right_edges)
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

fn pairings<T: Clone, U: Clone>(left: &[T], right: &[U]) -> impl Iterator<Item = Vec<(T, U)>> {
    left.iter()
        .cloned()
        .permutations(left.len())
        .map(|lefts| lefts.into_iter().zip(right.iter().cloned()).collect())
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_pairings() {
        let left = vec![1, 2, 3];
        let right = vec![4, 5, 6];
        let pairs: Vec<_> = pairings(&left, &right)
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
}
