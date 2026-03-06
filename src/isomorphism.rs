use crate::NodeKey;
use crate::Specification;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use itertools::iproduct;

impl Specification {
    // Implementation of VF2 algorithm for graph isomorphism
    #[must_use]
    pub fn match_graphs(
        &self,
        other: &Self,
        matching: &HashMap<NodeKey, NodeKey>,
    ) -> Option<HashMap<NodeKey, NodeKey>> {
        if matching.len() == self.nodes.len() {
            return Some(matching.clone());
        }

        let candidates = self.compute_pairs(other, matching);

        for (a, b) in candidates
            .iter()
            .filter(|(a, b)| self.is_node_matching_feasible(other, a, b))
        {
            let mut m = matching.clone();
            m.insert(a.clone(), b.clone());
            if let Some(new_matching) = self.match_graphs(other, &m) {
                return Some(new_matching);
            }
        }

        None
    }

    fn compute_pairs(
        &self,
        other: &Self,
        matching: &HashMap<NodeKey, NodeKey>,
    ) -> HashSet<(NodeKey, NodeKey)> {
        let in_candidates = matching.iter().flat_map(|(a, b)| {
            let self_in = self
                .in_edges(a)
                .into_iter()
                .map(|e| &self.edges.get(e).expect("self in edge should exist").from)
                .filter(|from| !matching.contains_key(*from))
                .collect::<Vec<_>>();
            let other_in = self
                .in_edges(b)
                .into_iter()
                .map(|e| &other.edges.get(e).expect("other in edge should exist").from)
                .filter(|from| !matching.values().any(|matched| *from == matched))
                .collect::<Vec<_>>();
            iproduct!(self_in, other_in)
        });
        let out_candidates = matching.iter().flat_map(|(a, b)| {
            let self_out = self
                .out_edges(a)
                .into_iter()
                .map(|e| &self.edges.get(e).expect("self out edge should exist").to)
                .filter(|to| !matching.contains_key(*to))
                .collect::<Vec<_>>();
            let other_out = self
                .out_edges(b)
                .into_iter()
                .map(|e| {
                    &other
                        .edges
                        .get(e)
                        .expect("other out edge should exist")
                        .from
                })
                .filter(|to| !matching.values().any(|matched| *to == matched))
                .collect::<Vec<_>>();
            iproduct!(self_out, other_out)
        });
        let ret: HashSet<(NodeKey, NodeKey)> = in_candidates
            .chain(out_candidates)
            .map(|(a, b)| (a.clone(), b.clone()))
            .collect();

        if !ret.is_empty() {
            return ret;
        }

        // if there are no candidates, match an arbitrary unmatched node from other with all unmatched nodes from self
        let other_node = other
            .nodes
            .keys()
            .find(|n| !matching.values().any(|matched| *n == matched))
            .expect("other candidate should exist");
        self.nodes
            .keys()
            .filter(|n| !matching.contains_key(*n))
            .map(|n| (n.clone(), other_node.clone()))
            .collect()
    }

    fn is_node_matching_feasible(&self, other: &Self, a: &str, b: &str) -> bool {
        let self_node = self.nodes.get(a).expect("self node should exist");
        let other_node = other.nodes.get(b).expect("other node should exist");
        if self_node.properties != other_node.properties {
            return false;
        }

        let self_in = self.in_edges(a).into_iter().collect::<Vec<_>>();
        let self_out = self.out_edges(a).into_iter().collect::<Vec<_>>();
        let other_in = other.in_edges(b).into_iter().collect::<Vec<_>>();
        let other_out = other.out_edges(b).into_iter().collect::<Vec<_>>();

        if self_in.len() != other_in.len() || self_out.len() != other_out.len() {
            return false;
        }

        matchings(&self_in, &other_in).any(|m| {
            m.into_iter()
                .map(|(l, r)| {
                    (
                        self.edges.get(l).expect("self edge should exist"),
                        other.edges.get(r).expect("other edge should exist"),
                    )
                })
                .all(|(l, r)| l.properties == r.properties)
        }) && matchings(&self_out, &other_out).any(|m| {
            m.into_iter()
                .map(|(l, r)| {
                    (
                        self.edges.get(l).expect("self edge should exist"),
                        other.edges.get(r).expect("other edge should exist"),
                    )
                })
                .all(|(l, r)| l.properties == r.properties)
        })
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
}
