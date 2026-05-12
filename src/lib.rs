//! Reference implementation for the Simple Ontology Visualization Specification (SOVS) language.
//!
//! The main type of this crate is the [`Specification`], which represents a SOVS graph.
//!
//! # Test suite
//! `sovs-parser` ships with a suite of tests designed to match the behavior of the [VOWL](https://web.archive.org/web/20160120220406/http://vowl.visualdataweb.org/v2/) specification.
//! These can be found in the [`test_suite`] module, which enabled through the `test-suite` feature.
//! Note that enabling this feature will cause the test suite to be embedded into the binary,
//! so it should probably only be enabled in testing environments.
use hashbag::HashBag;
use lalrpop_util::{ParseError, lalrpop_mod};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

mod isomorphism;
#[cfg(feature = "test-suite")]
mod test_suite;

#[cfg(feature = "test-suite")]
pub use test_suite::{TestCase, test_cases};

use crate::isomorphism::{GraphSystem, PropertyMappingKind, get_property_mapping_kind};

lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::nursery, clippy::unwrap_used)]
    #[rustfmt::skip]
    grammar
);

/// The properties on a node or edge.
/// Note that properties have bag semantics, i.e. a property with the same key and value may
/// appear multiple times, and the number of times it appears matters.
#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct Properties(pub HashMap<String, HashBag<String>>);

impl Properties {
    /// Create an empty set of properties
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a property
    pub fn insert(&mut self, key: String, value: String) {
        self.0.entry(key).or_default().insert(value);
    }

    /// Get the value of a property with a single value.
    /// Returns `None` if the key is not defined, or if the property has multiple values, including
    /// duplicates
    ///
    /// # Examples
    /// ```rust
    /// # use sovs_parser::Properties;
    /// let mut props = Properties::new();
    /// props.insert("key1".to_string(), "value".to_string());
    /// props.insert("key2".to_string(), "duplicate_value".to_string());
    /// props.insert("key2".to_string(), "duplicate_value".to_string());
    ///
    /// assert_eq!(props.get_single("key1"), Some("value"));
    /// assert_eq!(props.get_single("key2"), None);
    /// assert_eq!(props.get_single("unknown_key"), None);
    /// ```
    pub fn get_single(&self, key: &str) -> Option<&str> {
        let bag = self.0.get(key)?;
        if bag.len() != 1 {
            return None;
        }
        bag.iter().next().map(String::as_ref)
    }

    /// Check whether two sets of properties are equal, ignoring case.
    ///
    /// Note that case is only ignored in the values; keys are still case-sensitive.
    ///
    /// # Examples
    /// ```rust
    /// # use sovs_parser::Properties;
    /// let mut p1 = Properties::new();
    /// let mut p2 = Properties::new();
    /// let mut p3 = Properties::new();
    /// p1.insert("key".to_string(), "hello world".to_string());
    /// p2.insert("key".to_string(), "hElLo WoRLd".to_string());
    /// p3.insert("KEY".to_string(), "hElLo WoRLd".to_string());
    ///
    /// assert!(p1.eq_ignore_case(&p2));
    /// assert!(!p1.eq_ignore_case(&p3));
    /// assert!(!p2.eq_ignore_case(&p3));
    /// ```
    #[must_use]
    pub fn eq_ignore_case(&self, other: &Self) -> bool {
        self.to_lowercase() == other.to_lowercase()
    }

    /// Get the properties that are not mapped, i.e. the ones that do not correspond to a node or
    /// edge id. This is μ<sub>0</sub> in the math.
    #[must_use]
    pub fn unmapped(&self) -> Self {
        let mut unmapped = self.clone();
        unmapped
            .0
            .retain(|k, _| get_property_mapping_kind(k).is_none());
        unmapped
    }

    /// Get the properties that are edge mapped, i.e. the ones that correspond to an edge id.
    /// This is μ<sub>e</sub> in the math.
    #[must_use]
    pub fn edge_mapped(&self) -> Self {
        let mut mapped = self.clone();
        mapped.0.retain(|k, _| {
            matches!(
                get_property_mapping_kind(k),
                Some(PropertyMappingKind::Edge)
            )
        });
        mapped
    }

    /// Get the properties that are node mapped, i.e. the ones that correspond to a node id.
    /// This is μ<sub>v</sub> in the math.
    #[must_use]
    pub fn node_mapped(&self) -> Self {
        let mut mapped = self.clone();
        mapped.0.retain(|k, _| {
            matches!(
                get_property_mapping_kind(k),
                Some(PropertyMappingKind::Node)
            )
        });
        mapped
    }

    fn to_lowercase(&self) -> Self {
        let self_lower = self
            .0
            .iter()
            .map(|(k, vs)| (k.clone(), vs.iter().map(|v| v.to_lowercase()).collect()))
            .collect();
        Self(self_lower)
    }
}

impl<const N: usize> From<[(&str, &str); N]> for Properties {
    fn from(value: [(&str, &str); N]) -> Self {
        let mut props = Self::default();
        for (key, value) in value {
            props.insert(key.to_string(), value.to_string());
        }
        props
    }
}

type NodeKey = String;
type EdgeKey = String;

#[derive(Default, PartialEq, Eq, Clone, Debug)]
pub(crate) struct Definitions {
    nodes: HashMap<NodeKey, NodeDefinition>,
    edges: HashMap<EdgeKey, EdgeDefinition>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) enum Definition {
    Node(NodeKey, NodeDefinition),
    Edge(EdgeKey, EdgeDefinition),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct NodeDefinition {
    pub properties: Properties,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct EdgeDefinition {
    pub from: NodeKey,
    pub to: NodeKey,
    pub properties: Properties,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Specification {
    pub nodes: HashMap<NodeKey, NodeDefinition>,
    pub edges: HashMap<EdgeKey, EdgeDefinition>,
}

impl Specification {
    /// Parse a specification
    ///
    /// # Errors
    /// This function returns an error if:
    /// - `input` is not valid SOVS syntax,
    /// - The specification contains duplicate node or edge ids, or
    /// - Any edge refers to an undefined node
    pub fn parse(input: &str) -> Result<Self, SovsError> {
        let parser = grammar::SpecParser::new();
        let definitions = parser.parse(input).map_err(|e| match e {
            ParseError::User { error } => error,
            err => SovsError::ParseError(err.to_string()),
        })?;
        Self::try_from(definitions)
    }

    /// Get the set of edges going into the node with id `node`
    #[must_use]
    pub fn in_edges(&self, node: &str) -> HashSet<&str> {
        self.edges
            .iter()
            .filter(|(_, edge)| edge.to == node)
            .map(|(key, _)| key.as_ref())
            .collect()
    }

    /// Get the set of edges going out of the node with id `node`
    #[must_use]
    pub fn out_edges(&self, node: &str) -> HashSet<&str> {
        self.edges
            .iter()
            .filter(|(_, edge)| edge.from == node)
            .map(|(key, _)| key.as_ref())
            .collect()
    }

    /// Check whether two specifications are isomorphic, i.e. whether they are the same graphs but
    /// with different labelings
    ///
    /// # Warning
    /// This method can be quite slow on bigger graphs, so try to keep your test cases as small as
    /// possible.
    ///
    /// # Examples
    /// ```rust
    /// # use sovs_parser::{Specification, SovsError};
    /// let a = Specification::parse(r#"
    ///     node a { text: "A"; }
    ///     node b { text: "B"; }
    ///     edge e from a to b { text: "E"; }
    /// "#)?;
    /// let b = Specification::parse(r#"
    ///     edge z from y to x { text: "E"; }
    ///     node x { text: "B"; }
    ///     node y { text: "A"; }
    /// "#)?;
    /// assert!(a.is_isomorphic_to(&b));
    /// # Ok::<(), SovsError>(())
    /// ```
    #[must_use]
    pub fn is_isomorphic_to(&self, other: &Self) -> bool {
        if self.nodes.len() != other.nodes.len() || self.edges.len() != other.edges.len() {
            return false;
        }

        let self_nodes = self.nodes.keys().cloned().collect::<Vec<_>>();
        let other_nodes = other.nodes.keys().cloned().collect::<Vec<_>>();

        let mut system = GraphSystem::new(self.clone(), other.clone());
        let oracle = radguy_ccs::systems::bool::extension::BoolExtension::bitset().as_oracle();

        let matchings = isomorphism::matchings(&self_nodes, &other_nodes);

        // PERF: for optimal performance, this should maybe become a variable in the graph so we
        // can reuse work
        matchings.into_iter().any(|matching| {
            matching.into_iter().all(|(self_node, other_node)| {
                let target = system.node_variable(self_node, other_node);
                !radguy::kleene_local(&mut system, target, &oracle).0
            })
        })
    }
}

impl TryFrom<Definitions> for Specification {
    type Error = SovsError;

    fn try_from(value: Definitions) -> Result<Self, Self::Error> {
        for (edge_id, definition) in &value.edges {
            if !value.nodes.contains_key(&definition.to) {
                return Err(SovsError::UndefinedNode {
                    edge_id: edge_id.clone(),
                    node_id: definition.to.clone(),
                });
            }
            if !value.nodes.contains_key(&definition.from) {
                return Err(SovsError::UndefinedNode {
                    edge_id: edge_id.clone(),
                    node_id: definition.from.clone(),
                });
            }
        }
        Ok(Self {
            nodes: value.nodes,
            edges: value.edges,
        })
    }
}

#[derive(Default, Debug)]
pub struct SpecificationBuilder {
    definitions: Definitions,
}

impl SpecificationBuilder {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node to the specification
    ///
    /// # Errors
    /// This method returns [`SovsError::DuplicateNode`] if a node with the given id already exists
    /// in the specification
    pub fn node(&mut self, id: String, properties: Properties) -> Result<&mut Self, SovsError> {
        if self.definitions.nodes.contains_key(&id) {
            return Err(SovsError::DuplicateNode(id));
        }

        self.definitions
            .nodes
            .insert(id, NodeDefinition { properties });

        Ok(self)
    }

    /// Add an edge to the specification
    ///
    /// # Errors
    /// This method returns [`SovsError::DuplicateEdge`] if an edge with the given id already exists
    /// in the specification
    pub fn edge(
        &mut self,
        id: String,
        from: String,
        to: String,
        properties: Properties,
    ) -> Result<&mut Self, SovsError> {
        if self.definitions.edges.contains_key(&id) {
            return Err(SovsError::DuplicateEdge(id));
        }

        self.definitions.edges.insert(
            id,
            EdgeDefinition {
                from,
                to,
                properties,
            },
        );

        Ok(self)
    }

    /// Build the specification
    ///
    /// # Errors
    /// This method returns [`SovsError::UndefinedNode`] if any edge refers to an undefined node id
    pub fn build(&mut self) -> Result<Specification, SovsError> {
        self.definitions.clone().try_into()
    }
}

#[derive(Error, Debug)]
pub enum SovsError {
    #[error("duplicate node id {0}")]
    DuplicateNode(String),
    #[error("duplicate edge id {0}")]
    DuplicateEdge(String),
    #[error("edge {edge_id} references undefined node {node_id}")]
    UndefinedNode { edge_id: String, node_id: String },
    #[error("could not parse spec: {0}")]
    ParseError(String),
}

#[cfg(test)]
mod test {
    use lalrpop_util::ParseError;

    use super::*;

    #[test]
    fn parse_node() {
        let parser = grammar::SpecParser::new();
        let text = r#"
            node test { text: "test:text with spaces"; }
        "#;
        let defs = parser.parse(text).expect("parser should succeed");
        assert!(defs.edges.is_empty());
        assert_eq!(defs.nodes.len(), 1);
        let node = defs.nodes.get("test").expect("node should exist");

        assert_eq!(node.properties.0.len(), 1);
        let text_prop = node
            .properties
            .0
            .get("text")
            .cloned()
            .expect("node should have text property");
        assert_eq!(
            text_prop,
            std::iter::once("test:text with spaces".to_string()).collect()
        );
    }

    #[test]
    fn parse_edge() {
        let parser = grammar::SpecParser::new();
        let text = r#"
            edge test from x to y { text: "test:text with spaces"; }
        "#;
        let defs = parser.parse(text).expect("parser should succeed");
        assert!(defs.nodes.is_empty());
        assert_eq!(defs.edges.len(), 1);
        let edge = defs.edges.get("test").expect("edge should exist");

        assert_eq!(edge.properties.0.len(), 1);
        let text_prop = edge
            .properties
            .0
            .get("text")
            .cloned()
            .expect("edge should have text property");
        assert_eq!(
            text_prop,
            std::iter::once("test:text with spaces".to_string()).collect()
        );
    }

    #[test]
    fn parse_multiple_properties_same_name() {
        let parser = grammar::SpecParser::new();
        let text = r#"
            edge test from x to y { equivalentTo: "test1"; equivalentTo: "test2"; }
        "#;
        let defs = parser.parse(text).expect("parser should succeed");
        assert!(defs.nodes.is_empty());
        assert_eq!(defs.edges.len(), 1);
        let edge = defs.edges.get("test").expect("edge should exist");

        assert_eq!(edge.properties.0.len(), 1);
        let prop = edge
            .properties
            .0
            .get("equivalentTo")
            .cloned()
            .expect("edge should have equivalentTo property");
        assert_eq!(
            prop,
            ["test1".to_string(), "test2".to_string()]
                .into_iter()
                .collect()
        );
    }

    #[test]
    fn error_on_duplicate_node() {
        let parser = grammar::SpecParser::new();
        let text = r#"
            node not_duplicated { text: "test:text with spaces"; }
            node test { text: "test:text with spaces"; }
            node test { text: "some other text"; }
        "#;
        let res = parser.parse(text);
        match res {
            Err(ParseError::User {
                error: SovsError::DuplicateNode(id),
            }) => assert_eq!(id, "test"),
            _ => panic!("parser should fail"),
        }
    }

    #[test]
    fn error_on_duplicate_edge() {
        let parser = grammar::SpecParser::new();
        let text = r#"
            edge not_duplicated from x to y { text: "test:text with spaces"; }
            edge test from x to y { text: "test:text with spaces"; }
            edge test from x to y { text: "some other text"; }
        "#;
        let res = parser.parse(text);
        match res {
            Err(ParseError::User {
                error: SovsError::DuplicateEdge(id),
            }) => assert_eq!(id, "test"),
            res => panic!("parser should fail with duplicate edge but got {res:#?}"),
        }
    }

    #[test]
    fn error_on_undefined_to_node() {
        let text = r#"
            node n {}
            edge test from n to x { text: "test:text with spaces"; }
        "#;
        let res = Specification::parse(text);
        match res {
            Err(SovsError::UndefinedNode { edge_id, node_id }) => {
                assert_eq!(edge_id, "test", "invalid edge should be 'test'");
                assert_eq!(node_id, "x", "undefined node should be 'x'");
            }
            res => panic!("parsing should fail with undefined node but got {res:#?}"),
        }
    }

    #[test]
    fn error_on_undefined_from_node() {
        let text = r#"
            node n {}
            edge test from x to n { text: "test:text with spaces"; }
        "#;
        let res = Specification::parse(text);
        match res {
            Err(SovsError::UndefinedNode { edge_id, node_id }) => {
                assert_eq!(edge_id, "test", "invalid edge should be 'test'");
                assert_eq!(node_id, "x", "undefined node should be 'x'");
            }
            res => panic!("parsing should fail with undefined node but got {res:#?}"),
        }
    }
}
