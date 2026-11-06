//! Rust replay of `vectors/edb_snapshot_set.json` (#2279): `edb_table_hash` reads its rows as a
//! SET. Every case is an equivalence over hashes, so no digest is authored in the vector.

use logos_contract::{edb_table_hash, Goal, GroundLiteral, Hash, RelationTable, Symbol, Term};
use serde_json::Value as Json;

fn load() -> Json {
    // Walk up from the crate dir to the repo root holding the vector file.
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/edb_snapshot_set.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/edb_snapshot_set.json");
    }
    let raw =
        std::fs::read_to_string(dir.join("vectors/edb_snapshot_set.json")).expect("read vector");
    serde_json::from_str(&raw).expect("parse vector")
}

struct Vector {
    pred: Symbol,
    arity: u32,
    doc: Json,
}

impl Vector {
    fn row(&self, name: &str) -> GroundLiteral {
        let args = self.doc["rows"][name]
            .as_array()
            .unwrap_or_else(|| panic!("row {name} is not in `rows`"));
        let terms: Vec<Term> = args
            .iter()
            .map(|a| Term::atom(a.as_str().expect("row args are atoms").as_bytes().to_vec()))
            .collect();
        Goal::new(self.pred.clone(), terms)
            .as_ground()
            .expect("a row of atoms is ground")
    }

    fn rows(&self, list: &Json) -> Vec<GroundLiteral> {
        list.as_array()
            .expect("a row list")
            .iter()
            .map(|n| self.row(n.as_str().expect("a row name")))
            .collect()
    }

    fn hash(&self, list: &Json) -> Hash {
        edb_table_hash(&self.pred, &self.rows(list))
    }
}

fn vector() -> Vector {
    let doc = load();
    let pred = Symbol::new(doc["pred"].as_str().expect("pred").as_bytes().to_vec());
    let arity = doc["arity"].as_u64().expect("arity") as u32;
    Vector { pred, arity, doc }
}

#[test]
fn every_equal_group_hashes_equal() {
    let v = vector();
    let groups = v.doc["equal"].as_array().expect("equal");
    assert!(!groups.is_empty(), "the vector must carry equal groups");
    for group in groups {
        let name = group["name"].as_str().expect("name");
        let lists = group["lists"].as_array().expect("lists");
        let first = v.hash(&lists[0]);
        for list in &lists[1..] {
            assert_eq!(
                v.hash(list),
                first,
                "{name}: {list} hashes differently from {}",
                lists[0]
            );
        }
    }
}

#[test]
fn every_differ_pair_hashes_differently() {
    let v = vector();
    let pairs = v.doc["differ"].as_array().expect("differ");
    assert!(
        !pairs.is_empty(),
        "the vector must carry differ pairs, or a constant hash passes"
    );
    for pair in pairs {
        let name = pair["name"].as_str().expect("name");
        let lists = pair["lists"].as_array().expect("lists");
        assert_ne!(v.hash(&lists[0]), v.hash(&lists[1]), "{name}");
    }
}

#[test]
fn a_snapshot_equals_the_hash_over_its_sealed_table() {
    let v = vector();
    for list in v.doc["table_agrees"].as_array().expect("table_agrees") {
        let rows = v.rows(list);
        let table = RelationTable::new(v.pred.clone(), v.arity, rows.clone());
        assert!(
            table.is_canonical(),
            "{list}: the sealed table is canonical"
        );
        assert_eq!(
            edb_table_hash(&v.pred, &rows),
            edb_table_hash(&v.pred, &table.rows),
            "{list}: the snapshot of the rows and the hash over the table they seal must agree"
        );
    }
}
