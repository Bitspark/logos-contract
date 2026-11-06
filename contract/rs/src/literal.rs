//! §1.1 Literal — a predicate application `p(args…)`. **[FIRM]**
//!
//! The logic-level "atom" of Horn logic — deliberately a *different type* from an
//! ontos `Atom(bytes)` (both senses of "atom" are load-bearing, so the logic one
//! is named `Literal`). It is the labeled-compound reading from `ontos/compound`:
//! `p(args…)` ≅ `Tuple[Atom("p"), args…]`.
//!
//! Ground-ness is made a **type**, not just prose:
//! - [`Goal`] = `Literal<Term>` — may contain `Var`s (clause heads/bodies, claims).
//! - [`GroundLiteral`] = `Literal<ontos::Value>` — ground; every derivation-node
//!   conclusion (§3).

use crate::term::{Subst, Term};
use ontos_core::Value;

/// A predicate symbol — an ontos `Atom(bytes)`, by convention a name. Compared by
/// exact bytes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(Vec<u8>);

impl Symbol {
    pub fn new(bytes: impl Into<Vec<u8>>) -> Self {
        Symbol(bytes.into())
    }

    pub fn bytes(&self) -> &[u8] {
        &self.0
    }
}

impl<B: Into<Vec<u8>>> From<B> for Symbol {
    fn from(b: B) -> Self {
        Symbol(b.into())
    }
}

/// THE injective rendering of a name's bytes as text (#1961's ruling; made shared by #2763, and
/// moved beside [`Symbol`] by #2984, since a type's canonical rendering lives with the type):
/// valid UTF-8 verbatim except `%` → `%25`, and every byte outside valid UTF-8 as `%XX`.
///
/// Injective because the inverse is total: `%` only ever appears as the start of an escape, so
/// a decoder can always tell an escaped byte from a literal one. A lossy render (`from_utf8_lossy`)
/// maps every ill-formed byte to U+FFFD, so two identities that differ only there read as one to
/// whoever tells them apart: a span key, a pin-mismatch message. Well-formed text without `%` is
/// unchanged. go (`EscapedName`) and ts (`escapedName`) render the same bytes to the same text,
/// pinned by `vectors/identity_bytes.json`'s `escaped_name` section.
pub fn escaped_name(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    let mut rest = bytes;
    loop {
        match std::str::from_utf8(rest) {
            Ok(valid) => {
                push_escaping_percent(&mut out, valid);
                return out;
            }
            Err(e) => {
                let (good, bad) = rest.split_at(e.valid_up_to());
                // `good` is valid UTF-8 by `valid_up_to`'s contract.
                if let Ok(valid) = std::str::from_utf8(good) {
                    push_escaping_percent(&mut out, valid);
                }
                // `None` = the input ENDS mid-sequence, so every remaining byte is unusable.
                let bad_len = e.error_len().unwrap_or(bad.len());
                for b in &bad[..bad_len] {
                    out.push('%');
                    out.push_str(&format!("{:02X}", b));
                }
                rest = &bad[bad_len..];
            }
        }
    }
}

/// `%` is the escape character, so a literal one must itself escape or the rendering stops
/// being decodable — and two names differing only in a `%` would collide.
fn push_escaping_percent(out: &mut String, s: &str) {
    for ch in s.chars() {
        if ch == '%' {
            out.push_str("%25");
        } else {
            out.push(ch);
        }
    }
}

/// A predicate applied to argument terms, generic over the argument type so the
/// same shape expresses both a `Goal` (`T = Term`) and a `GroundLiteral`
/// (`T = ontos::Value`). Equality is structural (derived).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Literal<T> {
    pub pred: Symbol,
    pub args: Vec<T>,
}

impl<T> Literal<T> {
    pub fn new(pred: impl Into<Symbol>, args: impl IntoIterator<Item = T>) -> Self {
        Literal {
            pred: pred.into(),
            args: args.into_iter().collect(),
        }
    }
}

/// A clause head / body literal / claim-with-holes (§1.1). May contain `Var`s.
pub type Goal = Literal<Term>;

/// A ground literal — the conclusion of every `Derivation` node (§3). Its args are
/// `ontos::Value`s, so ground-ness is guaranteed by the type.
pub type GroundLiteral = Literal<Value>;

impl Goal {
    /// Apply a grounding substitution to every argument (§3, Rule obligation).
    pub fn substitute(&self, subst: &Subst) -> Goal {
        Goal {
            pred: self.pred.clone(),
            args: self.args.iter().map(|t| t.substitute(subst)).collect(),
        }
    }

    /// Erase a fully-ground goal to a [`GroundLiteral`]; `None` if any argument
    /// still contains a `Var`.
    pub fn as_ground(&self) -> Option<GroundLiteral> {
        let mut args = Vec::with_capacity(self.args.len());
        for arg in &self.args {
            args.push(arg.erase_ground()?);
        }
        Some(GroundLiteral {
            pred: self.pred.clone(),
            args,
        })
    }
}

impl GroundLiteral {
    /// Lift a [`GroundLiteral`] back into a [`Goal`] (ground, no holes) — used to
    /// compare a node conclusion against a substituted clause literal.
    pub fn to_goal(&self) -> Goal {
        Goal {
            pred: self.pred.clone(),
            args: self.args.iter().map(Term::from_value).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn substitute_then_ground_matches_expected() {
        // edge(X, Y) with {X: a, Y: b}  ==  edge(a, b)
        let goal = Goal::new("edge", [Term::var("X"), Term::var("Y")]);
        let mut subst: Subst = BTreeMap::new();
        subst.insert("X".into(), Term::atom(*b"a"));
        subst.insert("Y".into(), Term::atom(*b"b"));
        let grounded = goal.substitute(&subst).as_ground().expect("ground");
        let expected = GroundLiteral::new("edge", [Value::atom(*b"a"), Value::atom(*b"b")]);
        assert_eq!(grounded, expected);
    }

    #[test]
    fn unbound_var_stays_non_ground() {
        let goal = Goal::new("edge", [Term::var("X"), Term::var("Y")]);
        let mut subst: Subst = BTreeMap::new();
        subst.insert("X".into(), Term::atom(*b"a"));
        assert_eq!(goal.substitute(&subst).as_ground(), None);
    }
}
