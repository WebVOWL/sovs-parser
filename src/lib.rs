use hashbag::HashBag;
use lalrpop_util::{ParseError, lalrpop_mod};
use std::collections::HashMap;
use thiserror::Error;

lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::nursery, clippy::unwrap_used)]
    #[rustfmt::skip]
    grammar
);

pub type Properties = HashMap<String, HashBag<String>>;

#[derive(Default, PartialEq, Eq, Clone, Debug)]
pub(crate) struct Definitions {
    nodes: HashMap<String, NodeDefinition>,
    edges: HashMap<String, EdgeDefinition>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) enum Definition {
    Node(String, NodeDefinition),
    Edge(String, EdgeDefinition),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct NodeDefinition {
    pub properties: Properties,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct EdgeDefinition {
    pub from: String,
    pub to: String,
    pub properties: Properties,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Specification {
    pub nodes: HashMap<String, NodeDefinition>,
    pub edges: HashMap<String, EdgeDefinition>,
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

        assert_eq!(node.properties.len(), 1);
        let text_prop = node
            .properties
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

        assert_eq!(edge.properties.len(), 1);
        let text_prop = edge
            .properties
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

        assert_eq!(edge.properties.len(), 1);
        let prop = edge
            .properties
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
