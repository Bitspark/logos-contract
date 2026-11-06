//! §2a Reification — `quote` / `reify`. **[STABLE v1 shape · byte form FROZEN v1]**
//!
//! Storing or transmitting a *rule* (a clause with variables) as ordinary data
//! requires turning a term-with-holes into a ground ontos value and back. The
//! *semantic shape* (that `quote` is total and round-trips via `reify`) and the
//! *exact canonical bytes* (the tags below) are now both **frozen** — §9 is
//! settled: `VarId` is **syntactic** (variable names are encoded; no
//! alpha-normalization), so `quote` is the canonical encoding the account codec
//! ([`account`](crate::account)) hashes. Changing a tag is a breaking change
//! shipped as a new version, never an edit.
//!
//! The encoding tags every node with a leading 1-byte atom so the structure is
//! self-describing and `reify` is an unambiguous partial inverse — including a
//! reserved *quoted-variable* shape, distinct from the live `Var` constructor
//! (which is not an ontos value, §1). Because the tagging is uniform, no consumer
//! atom is ever "reserved": ordinary data round-trips through the `ATOM`/`TUPLE`
//! tags and a quoted variable is only ever produced by `quote`.

use crate::term::{Term, VarId};
use ontos_core::Value;

const TAG_ATOM: u8 = 0x00;
const TAG_TUPLE: u8 = 0x01;
const TAG_VAR: u8 = 0x02;

/// Total: maps `Atom`/`Tuple`/`Var` → a ground ontos value (§2a).
///
/// #2275 layer 3: through [`Term::fold`], the shared recursion-bounded rebuild, so a long list
/// (one nesting level per element) is quoted without one native frame per level. The bytes are
/// unchanged: every node is still `Tuple[tag, payload]`, children in order.
pub fn quote(term: &Term) -> Value {
    term.fold(
        |leaf| Some(quote_leaf(leaf)),
        |children| Value::tuple([Value::atom([TAG_TUPLE]), Value::tuple(children)]),
    )
    .expect("quoting a leaf never aborts the fold")
}

/// One leaf of [`quote`]. [`Term::fold`] never hands it a `Tuple`; that arm is the whole quote.
fn quote_leaf(leaf: &Term) -> Value {
    match leaf {
        Term::Atom(bytes) => Value::tuple([Value::atom([TAG_ATOM]), Value::atom(bytes.clone())]),
        Term::Var(id) => Value::tuple([
            Value::atom([TAG_VAR]),
            Value::atom(id.as_str().as_bytes().to_vec()),
        ]),
        Term::Tuple(_) => quote(leaf),
    }
}

/// Partial inverse of [`quote`]: `Some(term)` iff `value` is in the image of
/// `quote`, else `None` (§2a).
///
/// #2275 layer 3: a post-order assembly over an explicit stack, not one native frame per nesting
/// level. Nodes are visited in the same pre-order, so the first malformed node refuses it exactly
/// as the recursion did.
pub fn reify(value: &Value) -> Option<Term> {
    enum Frame<'a> {
        Enter(&'a Value),
        Assemble(usize),
    }
    let mut work: Vec<Frame> = vec![Frame::Enter(value)];
    let mut out: Vec<Term> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            Frame::Enter(node) => {
                let (tag, payload) = tagged(node)?;
                match tag {
                    TAG_ATOM => out.push(Term::Atom(payload.as_atom()?.bytes().to_vec())),
                    TAG_VAR => {
                        let name = std::str::from_utf8(payload.as_atom()?.bytes()).ok()?;
                        out.push(Term::Var(VarId::new(name)));
                    }
                    TAG_TUPLE => {
                        let children = payload.as_tuple()?.items();
                        work.push(Frame::Assemble(children.len()));
                        work.extend(children.iter().rev().map(Frame::Enter));
                    }
                    _ => return None,
                }
            }
            Frame::Assemble(arity) => {
                let children = out.split_off(out.len() - arity);
                out.push(Term::Tuple(children));
            }
        }
    }
    out.pop()
}

/// A quoted node's `(tag, payload)`: `Some` iff `value` is a 2-tuple headed by a 1-byte atom.
fn tagged(value: &Value) -> Option<(u8, &Value)> {
    let items = value.as_tuple()?.items();
    if items.len() != 2 {
        return None;
    }
    let tag = items[0].as_atom()?.bytes();
    if tag.len() != 1 {
        return None;
    }
    Some((tag[0], &items[1]))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trips(term: Term) {
        let quoted = quote(&term);
        assert_eq!(reify(&quoted), Some(term));
    }

    #[test]
    fn quote_reify_round_trips_terms_with_holes() {
        // pair(X, "a") — a term with a hole at depth, quoted to ground data.
        round_trips(Term::tuple([
            Term::atom(*b"pair"),
            Term::var("X"),
            Term::atom(*b"a"),
        ]));
        round_trips(Term::atom(*b"solo"));
        round_trips(Term::var("Y"));
        round_trips(Term::tuple([]));
    }

    #[test]
    fn reify_rejects_non_quoted_values() {
        // A bare atom is not in the image of quote.
        assert_eq!(reify(&Value::atom(*b"x")), None);
        // A wrapper with an unknown tag.
        assert_eq!(
            reify(&Value::tuple([Value::atom([0x09]), Value::atom(*b"x")])),
            None
        );
    }
}
