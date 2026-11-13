//! §1 Term — an ontos value, with holes. **[FIRM]**
//!
//! A term mirrors ontos's `Atom(bytes) | Tuple(children)` exactly, but a tuple
//! child **may be a `Var`**, so holes can appear at any depth:
//!
//! ```text
//! Term = Atom(Bytes) | Tuple(Term*) | Var(VarId)
//! ```
//!
//! This is full term algebra with holes (e.g. `pair(X, "a")`), not Datalog's
//! variables-as-whole-arguments. A *ground* term (no `Var`) corresponds exactly to
//! an `ontos::Value` — a bijection witnessed by [`Term::erase_ground`] /
//! [`Term::from_value`]. `Var` is logos's sole addition and is deliberately **not**
//! an ontos value under a reserved label (encoding it as `Tuple(Atom("var"), …)`
//! would force logos to reserve the `"var"` label in consumer data — the leak the
//! model refuses; reification to ground data is the explicit `quote`, §2a).

use ontos_core::Value;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

/// Default cap on **single-term nesting depth** in the trusted `check`/decode path
/// (issue #253). A pathologically deep term — `f(f(f(…)))` nested tens of thousands
/// deep, or a deep cons-chain — would otherwise overflow the OS stack during the
/// recursive term traversals (`erase_ground` / `substitute` / structural `eq` /
/// `Drop` / the account `quote`), aborting the **trusted** checker (a DoS).
///
/// This is distinct from [`CheckLimits::max_depth`](crate::check::CheckLimits), which
/// bounds DAG/premise-chain depth — a single *node's* term can be arbitrarily deep
/// within one node, so the node/depth caps do not bound it.
///
/// **Value, not budget.** Empirically the worst-case single recursive term op
/// (`from_value`) overflows at a nesting depth of ~670 on the ~1 MiB Windows MSVC
/// main-thread stack in an unoptimized debug build (≈1.5 KiB/level); `256` sits at
/// ~38 % of that boundary (a ~2.6× margin even on the smallest debug stack) while
/// giving ~50× headroom over any realistic ground term (real data nests a handful of
/// levels). A consumer that genuinely needs deeper terms raises this *and* the thread
/// stack together — the same discipline the sldnf engine's `max_depth` uses (#243).
pub const MAX_TERM_DEPTH_DEFAULT: usize = 256;

/// A grounding substitution (§3): a map from variable identity to a replacement
/// term. On a `Rule` node it grounds the cited clause's head and body. A
/// well-formed grounding `Subst` is *resolved* (idempotent — its values are
/// themselves ground), so a single substitution pass suffices; `check` does not
/// assume this and simply verifies the substituted result is ground and matches
/// the node's conclusion.
pub type Subst = BTreeMap<VarId, Term>;

/// An opaque variable identity (§1): a name or index. Its only contract is
/// **equality** and **freshness** (the ability to rename apart). logos imposes no
/// numeric/quotient equality — that stays a consumer/theory concern.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(String);

impl VarId {
    pub fn new(name: impl Into<String>) -> Self {
        VarId(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<S: Into<String>> From<S> for VarId {
    fn from(s: S) -> Self {
        VarId(s.into())
    }
}

/// A term: an ontos value with holes (§1).
///
/// Identity is structural and extends ontos identity with `Var(a) == Var(b)` iff
/// `a == b`.
///
/// **#2275 layer 3: `Clone`, `PartialEq`/`Eq`, `Hash` and `Drop` are hand-written, not derived.** A derive
/// recurses once per nesting level, and a surface list `[a, b, ...]` nests one level per element,
/// so an ordinary long list overflowed the native stack. Each impl here recurses only up to
/// [`TERM_RECURSION_BUDGET`] and continues on an explicit heap stack below that, so the common shallow
/// term keeps the plain recursive walk and its speed. Each keeps the derive's behaviour exactly:
/// `Clone` builds the same tree, `==` compares the same structure, and `Hash` feeds the hasher the
/// same sequence of writes (the discriminant, then the payload, a tuple length-prefixed), so it
/// stays consistent with `Eq`. `Debug` stays derived: it is diagnostic output.
#[derive(Debug)]
pub enum Term {
    /// The same bytes as an ontos `Atom`.
    Atom(Vec<u8>),
    /// The same ordered shape as an ontos `Tuple`, but children may contain `Var`.
    Tuple(Vec<Term>),
    /// The unknown — logos's sole addition.
    Var(VarId),
}

/// Why a term erased to no ground `Value`. Its depth variant retired with
/// `VALUE_STACK_DEPTH_LIMIT` when ontos v0.10.0 made `Value`'s own traits iterative (#3596,
/// Bitspark/ontos#340): a value of any depth is now built, walked and dropped on a heap stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EraseError {
    /// The term holds a `Var`, so it has no ground `Value`: what [`Term::erase_ground`]'s `None`
    /// says.
    NotGround,
}

/// The one name for "a term nests deeper than this build can represent as a value" (#2425,
/// `seat:caa`'s ruling on #2275): the native resolver's representation refusal begins with it, and
/// the wasm guest declines with it when a request nests past its decoder's depth. One cause, one
/// token, so a host maps it once. The detail after it names the bound that applied: the guest's
/// decode depth (ontos's default, 1,024). Native logos has no such bound since ontos v0.10.0
/// (#3596): a value of any depth is represented.
pub const VALUE_TOO_DEEP: &str = "value_too_deep";

/// How deep the walks over a [`Term`] recurse on the native stack before continuing on an explicit
/// heap stack (#2275 layer 3). Public so every crate's term walk shares the one budget. Nearly every real term is shallower than this and keeps the plain
/// recursive walk; a deeper one (a long list, one level per element) continues on the heap, so no
/// walk's native-stack use grows with the term.
pub const TERM_RECURSION_BUDGET: usize = 64;

impl Clone for Term {
    fn clone(&self) -> Self {
        clone_at(self, 0)
    }
}

/// #2275 layer 3: dropping a deep term must not recurse once per level either. The drop glue for a
/// `Tuple` drops each child, and a child tuple's glue drops ITS children, one native frame per
/// level: a long list, merely going out of scope, overflowed the stack. So a tuple whose children
/// include a tuple moves them onto a heap stack first and drops them one at a time, each emptied
/// the same way before it goes. A tuple of leaves (nearly every tuple) takes the fast return and
/// the glue drops its atoms and variables directly.
impl Drop for Term {
    fn drop(&mut self) {
        let Term::Tuple(children) = self else {
            return;
        };
        if !children.iter().any(|c| matches!(c, Term::Tuple(_))) {
            return;
        }
        let mut pending = std::mem::take(children);
        while let Some(mut term) = pending.pop() {
            if let Term::Tuple(grandchildren) = &mut term {
                if grandchildren.iter().any(|c| matches!(c, Term::Tuple(_))) {
                    pending.append(grandchildren);
                }
            }
            // `term` drops here with no tuple child left in it, so its own drop returns at once.
        }
    }
}

fn clone_at(term: &Term, depth: usize) -> Term {
    match term {
        Term::Atom(bytes) => Term::Atom(bytes.clone()),
        Term::Var(id) => Term::Var(id.clone()),
        Term::Tuple(children) if depth < TERM_RECURSION_BUDGET => {
            Term::Tuple(children.iter().map(|c| clone_at(c, depth + 1)).collect())
        }
        Term::Tuple(_) => fold_on_heap(term, |leaf| Some(clone_leaf(leaf)), Term::Tuple)
            .expect("cloning a leaf never aborts the fold"),
    }
}

/// A leaf's clone. [`fold_on_heap`] passes only leaves; the `Tuple` arm is the plain clone.
fn clone_leaf(leaf: &Term) -> Term {
    match leaf {
        Term::Atom(bytes) => Term::Atom(bytes.clone()),
        Term::Var(id) => Term::Var(id.clone()),
        Term::Tuple(_) => leaf.clone(),
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        eq_at(self, other, 0)
    }
}

impl Eq for Term {}

fn eq_at(a: &Term, b: &Term, depth: usize) -> bool {
    match (a, b) {
        (Term::Atom(x), Term::Atom(y)) => x == y,
        (Term::Var(x), Term::Var(y)) => x == y,
        (Term::Tuple(xs), Term::Tuple(ys)) if depth < TERM_RECURSION_BUDGET => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| eq_at(x, y, depth + 1))
        }
        (Term::Tuple(_), Term::Tuple(_)) => eq_on_heap(a, b),
        _ => false,
    }
}

/// #2675: `*term == Term::from_value(value)`, decided in place, without lifting `value` into a term
/// first. `from_value` yields only atoms and tuples, never a `Var`, so a variable equals no value.
/// Recursive within [`TERM_RECURSION_BUDGET`], on a heap stack past it, as [`eq_at`] is.
fn eq_value_at(term: &Term, value: &Value, depth: usize) -> bool {
    match (term, value) {
        (Term::Atom(bytes), Value::Atom(atom)) => atom.bytes() == bytes.as_slice(),
        (Term::Tuple(children), Value::Tuple(tuple)) if depth < TERM_RECURSION_BUDGET => {
            let items = tuple.items();
            children.len() == items.len()
                && children
                    .iter()
                    .zip(items)
                    .all(|(child, item)| eq_value_at(child, item, depth + 1))
        }
        (Term::Tuple(_), Value::Tuple(_)) => eq_value_on_heap(term, value),
        _ => false,
    }
}

/// [`eq_value_at`] past the recursion budget: the same comparison over an explicit stack of pairs.
fn eq_value_on_heap(term: &Term, value: &Value) -> bool {
    let mut work: Vec<(&Term, &Value)> = vec![(term, value)];
    while let Some(pair) = work.pop() {
        match pair {
            (Term::Atom(bytes), Value::Atom(atom)) if atom.bytes() == bytes.as_slice() => {}
            (Term::Tuple(children), Value::Tuple(tuple))
                if tuple.items().len() == children.len() =>
            {
                work.extend(children.iter().zip(tuple.items()));
            }
            _ => return false,
        }
    }
    true
}

/// `==` past the recursion budget: the same structural comparison over an explicit stack of pairs.
fn eq_on_heap(a: &Term, b: &Term) -> bool {
    let mut work: Vec<(&Term, &Term)> = vec![(a, b)];
    while let Some(pair) = work.pop() {
        match pair {
            (Term::Atom(x), Term::Atom(y)) if x == y => {}
            (Term::Var(x), Term::Var(y)) if x == y => {}
            (Term::Tuple(xs), Term::Tuple(ys)) if xs.len() == ys.len() => {
                work.extend(xs.iter().zip(ys));
            }
            _ => return false,
        }
    }
    true
}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_at(self, state, 0);
    }
}

/// One node's own writes, in the derive's order: the discriminant, then an atom's bytes, a
/// variable's id, or a tuple's length (its children follow, in order, from the caller).
fn hash_node<H: Hasher>(term: &Term, state: &mut H) {
    std::mem::discriminant(term).hash(state);
    match term {
        Term::Atom(bytes) => bytes.hash(state),
        Term::Var(id) => id.hash(state),
        Term::Tuple(children) => children.len().hash(state),
    }
}

fn hash_at<H: Hasher>(term: &Term, state: &mut H, depth: usize) {
    hash_node(term, state);
    let Term::Tuple(children) = term else {
        return;
    };
    if depth < TERM_RECURSION_BUDGET {
        for child in children {
            hash_at(child, state, depth + 1);
        }
        return;
    }
    // Past the budget: the same pre-order sequence of writes, over an explicit stack.
    let mut work: Vec<&Term> = children.iter().rev().collect();
    while let Some(node) = work.pop() {
        hash_node(node, state);
        if let Term::Tuple(grandchildren) = node {
            work.extend(grandchildren.iter().rev());
        }
    }
}

/// The explicit-stack post-order fold behind every assembling walk over a [`Term`] past
/// [`TERM_RECURSION_BUDGET`] (#2275 layer 3): `Clone`, [`Term::erase_ground`], [`Term::substitute`].
/// It is the shape [`Term::from_value`] established. `leaf` maps an `Atom` or a `Var` (it is never
/// handed a `Tuple`), or aborts the whole fold with `None`; `node` builds a tuple from its children,
/// already folded, in order.
fn fold_on_heap<T>(
    term: &Term,
    mut leaf: impl FnMut(&Term) -> Option<T>,
    mut node: impl FnMut(Vec<T>) -> T,
) -> Option<T> {
    enum Frame<'a> {
        Enter(&'a Term),
        Assemble(usize),
    }
    let mut work: Vec<Frame> = vec![Frame::Enter(term)];
    let mut out: Vec<T> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            Frame::Enter(Term::Tuple(children)) => {
                // The assemble first, then the children: LIFO finishes every child before it.
                work.push(Frame::Assemble(children.len()));
                work.extend(children.iter().rev().map(Frame::Enter));
            }
            Frame::Enter(leaf_term) => out.push(leaf(leaf_term)?),
            Frame::Assemble(arity) => {
                let children = out.split_off(out.len() - arity);
                out.push(node(children));
            }
        }
    }
    out.pop()
}

impl Term {
    pub fn atom(bytes: impl Into<Vec<u8>>) -> Self {
        Term::Atom(bytes.into())
    }

    pub fn tuple(children: impl IntoIterator<Item = Term>) -> Self {
        Term::Tuple(children.into_iter().collect())
    }

    pub fn var(id: impl Into<VarId>) -> Self {
        Term::Var(id.into())
    }

    /// `ground(t)` ⟺ `t` contains no `Var` (normative, §1).
    pub fn is_ground(&self) -> bool {
        !self.any_var(|_| true)
    }

    /// Whether `pred` holds for some variable OCCURRENCE of this term. Occurrences are visited in
    /// pre-order, left to right (so first occurrences come first), and the walk stops at the first
    /// `true`.
    ///
    /// **The one variable walk every collector shares** (#2275 layer 3). Each crate had its own
    /// recursive `collect_vars`, one native frame per nesting level. This one recurses only up to
    /// [`TERM_RECURSION_BUDGET`] and continues on an explicit heap stack in the same order.
    pub fn any_var(&self, mut pred: impl FnMut(&VarId) -> bool) -> bool {
        self.any_var_at(&mut pred, 0)
    }

    fn any_var_at(&self, pred: &mut impl FnMut(&VarId) -> bool, depth: usize) -> bool {
        match self {
            Term::Atom(_) => false,
            Term::Var(id) => pred(id),
            Term::Tuple(children) if depth < TERM_RECURSION_BUDGET => {
                children.iter().any(|c| c.any_var_at(pred, depth + 1))
            }
            Term::Tuple(children) => {
                let mut work: Vec<&Term> = children.iter().rev().collect();
                while let Some(term) = work.pop() {
                    match term {
                        Term::Atom(_) => {}
                        Term::Var(id) => {
                            if pred(id) {
                                return true;
                            }
                        }
                        Term::Tuple(grandchildren) => work.extend(grandchildren.iter().rev()),
                    }
                }
                false
            }
        }
    }

    /// Visit every variable occurrence of this term, in [`any_var`](Self::any_var)'s order.
    pub fn for_each_var(&self, mut f: impl FnMut(&VarId)) {
        self.any_var(|id| {
            f(id);
            false
        });
    }

    /// Whether `t` is an OPEN compound: a `Tuple` containing a `Var` at any depth (#2294,
    /// ruled `seat:caa`). This is THE classification of "compound" the function-free fragment
    /// excludes. A GROUND term, compound or not, is a constant: it carries no variable, so no
    /// variable can bind a strict sub-term of it, and it cannot grow the Herbrand universe. A
    /// string (`utf8-text(..)`), an int, a ground list and `f(a)` are all constants. The
    /// checker's sealed-scope gate and the producer's sealed-clause gate both read this one
    /// function, so the producer declines exactly where `check()` would reject.
    pub fn is_open_compound(&self) -> bool {
        matches!(self, Term::Tuple(_)) && !self.is_ground()
    }

    /// `erase_ground(t)` — the corresponding `ontos::Value`, defined iff
    /// `ground(t)` (normative, §1). Returns `None` for a non-ground term. Recursion is bounded by
    /// [`TERM_RECURSION_BUDGET`] (#2275 layer 3).
    pub fn erase_ground(&self) -> Option<Value> {
        self.fold(
            |leaf| match leaf {
                Term::Atom(bytes) => Some(Value::atom(bytes.clone())),
                Term::Tuple(_) | Term::Var(_) => None,
            },
            Value::tuple,
        )
    }

    /// Fold this term bottom-up: `leaf` maps each `Atom` or `Var` (it is never handed a `Tuple`),
    /// or aborts the whole fold with `None`; `node` builds a tuple from its children, already
    /// folded, in order. Leaves are visited in pre-order, left to right.
    ///
    /// **The one assembling walk** (#2275 layer 3), behind [`erase_ground`](Self::erase_ground),
    /// [`substitute`](Self::substitute) and the engines' own rebuilds such as `copy_term`. It
    /// recurses only up to [`TERM_RECURSION_BUDGET`] and continues on an explicit heap stack in
    /// the same order.
    pub fn fold<T>(
        &self,
        mut leaf: impl FnMut(&Term) -> Option<T>,
        mut node: impl FnMut(Vec<T>) -> T,
    ) -> Option<T> {
        self.fold_at(&mut leaf, &mut node, 0)
    }

    fn fold_at<T, L, N>(&self, leaf: &mut L, node: &mut N, depth: usize) -> Option<T>
    where
        L: FnMut(&Term) -> Option<T>,
        N: FnMut(Vec<T>) -> T,
    {
        match self {
            Term::Tuple(children) if depth < TERM_RECURSION_BUDGET => {
                let mut out = Vec::with_capacity(children.len());
                for child in children {
                    out.push(child.fold_at(leaf, node, depth + 1)?);
                }
                Some(node(out))
            }
            Term::Tuple(_) => fold_on_heap(self, leaf, node),
            leaf_term @ (Term::Atom(_) | Term::Var(_)) => leaf(leaf_term),
        }
    }

    /// The inverse of [`Term::erase_ground`] on ground terms: lift an
    /// `ontos::Value` into the (always ground) corresponding `Term`.
    ///
    /// **Non-recursive (issue #253).** Built with an explicit work stack so a
    /// pathologically deep `Value` cannot overflow the native call stack here at the
    /// decode boundary — this is the one term traversal that must remain total even
    /// for an over-deep input (the depth guard runs *after* a term is in hand, so
    /// constructing it must not itself crash). The post-order assembly reproduces the
    /// recursive shape byte-for-byte.
    pub fn from_value(value: &Value) -> Term {
        // Work item: a borrowed `Value` to lift, paired with how many children of the
        // parent `Tuple` remain to assemble once this subtree is done. We push an
        // `Enter` for each value, then resolve `Tuple`s by popping their finished
        // children off the output stack. Atoms resolve immediately.
        enum Frame<'a> {
            Enter(&'a Value),
            // Assemble a tuple by popping `arity` already-built children.
            Assemble(usize),
        }
        let mut work: Vec<Frame> = vec![Frame::Enter(value)];
        let mut out: Vec<Term> = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                Frame::Enter(Value::Atom(atom)) => out.push(Term::Atom(atom.bytes().to_vec())),
                Frame::Enter(Value::Tuple(tuple)) => {
                    let items = tuple.items();
                    // First schedule the assemble, then the children (LIFO → children
                    // are processed before the assemble, leaving exactly `arity` built
                    // terms on `out` for the assemble to consume, in order).
                    work.push(Frame::Assemble(items.len()));
                    for item in items.iter().rev() {
                        work.push(Frame::Enter(item));
                    }
                }
                Frame::Assemble(arity) => {
                    let start = out.len() - arity;
                    let children = out.split_off(start);
                    out.push(Term::Tuple(children));
                }
            }
        }
        // Exactly one term remains: the lifted root.
        debug_assert_eq!(out.len(), 1);
        out.pop().expect("from_value: empty output")
    }

    /// Match this term against a GROUND `value`, extending `subst`: a `Var` binds to the value's
    /// term (or must equal what it is already bound to), an `Atom` must equal it, and a `Tuple`
    /// must have the same arity with every child matching. `false` on the first mismatch, found
    /// depth-first, left to right; `subst` then holds whatever bound before it.
    ///
    /// **One matcher** (#2275 layer 3) for the certifying producer and the provider's answer
    /// recovery, which each had their own recursive copy. It runs over an explicit stack of pairs,
    /// not one native frame per nesting level.
    ///
    /// #2675: the first pair is matched before any stack exists, so a variable or an atom (nearly
    /// every argument a join matches) allocates nothing, and a tuple continues on the stack, in the
    /// same order as ever. A variable already bound is compared with the value in place; its term
    /// is lifted from the value only to be inserted.
    pub fn match_value(&self, value: &Value, subst: &mut Subst) -> bool {
        let mut work: Vec<(&Term, &Value)> = Vec::new();
        let mut first = Some((self, value));
        while let Some((term, value)) = first.take().or_else(|| work.pop()) {
            match (term, value) {
                (Term::Var(id), _) => match subst.get(id) {
                    Some(existing) => {
                        if !eq_value_at(existing, value, 0) {
                            return false;
                        }
                    }
                    None => {
                        subst.insert(id.clone(), Term::from_value(value));
                    }
                },
                (Term::Atom(bytes), Value::Atom(atom)) if atom.bytes() == bytes.as_slice() => {}
                (Term::Tuple(children), Value::Tuple(tuple))
                    if tuple.items().len() == children.len() =>
                {
                    work.extend(children.iter().zip(tuple.items()).rev());
                }
                _ => return false,
            }
        }
        true
    }

    /// `true` iff this term nests no deeper than `max` levels — measured **iteratively
    /// with an early cutoff** (issue #253), so checking a pathologically deep term's
    /// depth does NOT itself overflow the native stack (a recursive depth-measure
    /// would defeat the purpose). An `Atom`/`Var` has depth 1; a `Tuple` has depth
    /// `1 + max(child depth)`. Returns `false` as soon as a path exceeds `max`,
    /// without descending further.
    ///
    /// The walk carries an explicit `(node, level)` work stack; a `Tuple` at `level`
    /// pushes its children at `level + 1`, and the moment any `level > max` the cutoff
    /// fires — so the work performed before refusing an over-deep term is bounded by
    /// the cutoff, not by the (unbounded) term.
    pub fn depth_le(&self, max: usize) -> bool {
        self.depth_capped(max) <= max
    }

    /// The depth [`depth_le`](Self::depth_le) measures, by the same walk and the same cutoff:
    /// the term's depth when it is at most `max`, else `max + 1`, the first level past `max`, where
    /// the walk stops. `check` reports the deepest term it measured (#3111,
    /// `max_term_depth_reached`), so the measurement is read rather than only compared.
    pub(crate) fn depth_capped(&self, max: usize) -> usize {
        let mut deepest = 0;
        let mut work: Vec<(&Term, usize)> = vec![(self, 1)];
        while let Some((term, level)) = work.pop() {
            if level > max {
                return level;
            }
            deepest = deepest.max(level);
            if let Term::Tuple(children) = term {
                for child in children {
                    work.push((child, level + 1));
                }
            }
        }
        deepest
    }

    /// Apply a grounding substitution (one pass). A `Var` with no binding is left
    /// in place (so the result is non-ground and a subsequent ground check fails). Recursion is
    /// bounded by [`TERM_RECURSION_BUDGET`] (#2275 layer 3).
    pub fn substitute(&self, subst: &Subst) -> Term {
        self.fold(|leaf| Some(substitute_leaf(leaf, subst)), Term::Tuple)
            .expect("substituting a leaf never aborts the fold")
    }
}

/// One leaf of [`Term::substitute`]: a bound `Var` becomes its binding, anything else is itself.
fn substitute_leaf(leaf: &Term, subst: &Subst) -> Term {
    match leaf {
        Term::Var(id) => subst
            .get(id)
            .cloned()
            .unwrap_or_else(|| Term::Var(id.clone())),
        other @ (Term::Atom(_) | Term::Tuple(_)) => other.clone(),
    }
}

/// `true` iff the ontos `value` nests no deeper than `max` levels — the
/// [`Term::depth_le`] analogue for a ground [`Value`] (a `GroundLiteral`'s args are
/// `Value`s, not `Term`s). **Iterative with an early cutoff** (issue #253): the
/// recursive `Value` traversals on the trusted path (structural `eq` against the
/// claim, the canonical `ground_key`/codec encode, `Drop`) would overflow on a
/// pathologically deep value, so the trusted checker measures depth without recursing
/// and rejects an over-deep value before any of them runs.
pub fn value_depth_le(value: &Value, max: usize) -> bool {
    value_depth_capped(value, max) <= max
}

/// The depth [`value_depth_le`] measures, by the same walk and the same cutoff: the value's
/// depth when it is at most `max`, else `max + 1`, where the walk stops ([`Term::depth_capped`]'s
/// analogue, #3111).
pub(crate) fn value_depth_capped(value: &Value, max: usize) -> usize {
    let mut deepest = 0;
    let mut work: Vec<(&Value, usize)> = vec![(value, 1)];
    while let Some((v, level)) = work.pop() {
        if level > max {
            return level;
        }
        deepest = deepest.max(level);
        if let Value::Tuple(tuple) = v {
            for child in tuple.items() {
                work.push((child, level + 1));
            }
        }
    }
    deepest
}

// ===========================================================================
// account-v2 list canonicalization (cons ↔ `list`) — the BIJECTION on ground
// proper lists used by the reify-aware account-equality (#277). **[FIRM]**
// ===========================================================================
//
// The logos surface lowers list syntax to Prolog-style **cons cells** (`[]` =
// `Atom("[]")`, `[H|T]` = `Tuple[Atom("."), H, T]`); the ontos/data L2 profile
// instead carries a sequence as the **flat** `list` embedding
// `Tuple[Atom("list"), e0, …, e_{n-1}]` (ontos-data §5.5). These are two spellings
// of the *same datum*. The opt-in account-emit reification (`reify_lists`, #159)
// rewrites cons → `list`. #277 made `check` treat the two spellings as account-equal;
// **#3022 withdrew that**: every certified literal claim is exact, `check` compares
// structurally, and this canonicalization is the PRESENTATION equivalence (two spellings
// present one list), never a certification equivalence.
//
// [`canonicalize_lists`] is the single canonical retraction both sides use: it maps
// every ground **proper** cons-list to its `list` embedding (and leaves the `list`
// embedding fixed), so a cons-form clause head and a reified `list()` conclusion
// canonicalize to the *same* value and compare equal — while never conflating two
// terms that denote different data.
//
// THE BIJECTION (why this is sound). On ground proper lists, cons-form `[e0,…,e_{n-1}]`
// and the `list` embedding `list(e0,…,e_{n-1})` are in one-to-one correspondence:
// the spine `.(e0, .(e1, … .(e_{n-1}, []) …))` determines exactly `(e0,…,e_{n-1})` and
// vice versa (a proper cons-chain has a unique element sequence; `list(…)` has a
// unique child sequence; the empty case is handled below). `canonicalize_lists`
// chooses the `list` embedding as the canonical representative of each such class and
// is the IDENTITY on every other value. Consequences:
//   * **Idempotent / a retraction** — re-canonicalizing a `list(…)` value is a no-op
//     (it is headed by `list`, not `.`, so it is not a cons cell), and its children
//     are already canonical.
//   * **No conflation** — two values canonicalize to the same result ONLY when they
//     are the cons-form and `list`-form of the *same* sequence (the intended account
//     equality). Distinct sequences have distinct element tuples, hence distinct
//     canonical forms; a non-list value is untouched, so it can never collapse onto a
//     different non-list value.
//
// EDGE CASES (each kept distinct — no conflation):
//   * **Empty list** — a bare nil `Atom("[]")` is an *atom*, not a `.`/2 cons cell, so
//     it is LEFT as `Atom("[]")` (never rewritten to `list()`). The `list`-embedding
//     empty list `Tuple[Atom("list")]` is likewise left fixed. So `[]` and `list()`
//     are DISTINCT canonical forms — which is correct: the reifier (`reify_lists`)
//     never produces `list()` from a bare `[]`, so a reified empty list IS `Atom("[]")`
//     and already matches the cons-form `[]` without any rewrite; and a program that
//     genuinely carries a `list()` datum keeps it.
//   * **Improper `[a|b]`** = `.(a, b)` with `b` a non-`[]`, non-cons value — NOT a
//     proper list, so the `.` tuple is kept (children canonicalized).
//   * **Partial `[a|X]`** cannot reach here: a [`Value`] contains no `Var`, so every
//     tail is determined (every cons spine is either proper or improper).
//   * **`list` atom vs `list(…)` embedding** — an existing `Tuple[Atom("list"), …]`
//     is headed by `list`, not `.`, so it is never treated as a cons cell; only its
//     children are canonicalized (no double-wrapping).
//   * **`list` used as a genuine data functor** — `Tuple[Atom("list"), a, b]` IS, by
//     the ontos/data profile, the canonical sequence `[a, b]`; treating it as account-
//     equal to `.(a,.(b,[]))` is the *intended* semantics of the reification, not a
//     conflation. (A consumer that does not want list semantics simply does not opt
//     into reification and never emits a `list(…)` conclusion; the default cons
//     identity is unchanged.)

/// The cons functor `.` (a `[H|T]` cell head), as raw bytes.
const CONS_LABEL: &[u8] = b".";
/// The nil atom `[]` (the cons-chain terminator), as raw bytes.
const NIL_LABEL: &[u8] = b"[]";

/// Canonicalize every **ground proper cons-list** anywhere inside `value` to the
/// ontos/data flat `list` embedding (`Tuple[Atom("list"), e0, …]`), bottom-up — the
/// single canonical retraction of the presentation equivalence (#277; since #3022 `check`
/// never applies it). The IDENTITY on every non-(proper-cons-list) value. See the
/// module note above for the bijection / no-conflation argument and the edge cases.
///
/// Semantically identical to the producer-side [`reify_lists`](crate::engine::reify_lists)
/// (which delegates here), so a reified emission and its checker canonicalization agree
/// by construction (dual-conformance). Total and deterministic. The spine walk is
/// iterative (no per-cell recursion); element/child recursion is bounded by the term-
/// nesting depth the trusted path already gated (`max_term_depth`) before this runs.
pub fn canonicalize_lists(value: &Value) -> Value {
    // A proper cons-list anywhere is canonicalized to the flat `list` embedding. The
    // test runs on the RAW value (before any child rewrite): the spine threads through
    // `.`/`[]` cells, so canonicalizing a child first would dissolve the spine the top
    // of the chain must walk. We collect the raw element values off the intact spine,
    // then canonicalize EACH element (so nested lists are normalized too).
    //
    // #2275 layer 3: a post-order assembly over an explicit stack, not one native frame per
    // nesting level. That covers a deeply nested element, and also an IMPROPER spine, which is
    // not a list and so is walked as ordinary tuples, one cell inside the next.
    enum Frame<'a> {
        Enter(&'a Value),
        List(usize),
        Tuple(usize),
    }
    let mut work: Vec<Frame> = vec![Frame::Enter(value)];
    let mut out: Vec<Value> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            Frame::Enter(node) => {
                if let Some(elements) = proper_cons_elements(node) {
                    work.push(Frame::List(elements.len()));
                    work.extend(elements.into_iter().rev().map(Frame::Enter));
                    continue;
                }
                match node {
                    Value::Atom(_) => out.push(node.clone()),
                    // A non-list tuple (an ordinary compound, an existing `list(…)`
                    // embedding): keep the shape, canonicalize each child.
                    Value::Tuple(tuple) => {
                        work.push(Frame::Tuple(tuple.items().len()));
                        work.extend(tuple.items().iter().rev().map(Frame::Enter));
                    }
                }
            }
            Frame::List(arity) => {
                let elements = out.split_off(out.len() - arity);
                out.push(ontos_data::encode_list(&elements));
            }
            Frame::Tuple(arity) => {
                let items = out.split_off(out.len() - arity);
                out.push(Value::tuple(items));
            }
        }
    }
    out.pop().expect("the root is assembled last")
}

/// If `value` is a cons cell `Tuple[Atom("."), H, T]` whose spine is a *proper* list
/// (ends in the nil atom `[]`), return the **raw** (un-canonicalized) element values in
/// order, borrowed; otherwise `None`. Iterative over the tail (no spine recursion) so a long
/// list does not grow the stack.
fn proper_cons_elements(value: &Value) -> Option<Vec<&Value>> {
    // A standalone nil atom `[]` is NOT a list — only an actual `.`/2 cons cell starts
    // a list. (Canonicalizing a bare `[]` to `list()` would re-encode a legitimate atom
    // and break the empty-list edge case.)
    match value {
        Value::Tuple(t) if is_cons_cell(t.items()) => {}
        Value::Atom(_) | Value::Tuple(_) => return None,
    }
    let mut cursor: &Value = value;
    let mut elems = Vec::new();
    loop {
        match cursor {
            // Proper terminator: the spine ends in the nil atom `[]`.
            Value::Atom(a) if a.bytes() == NIL_LABEL => return Some(elems),
            // A cons cell: take its head as the next element, descend into its tail.
            Value::Tuple(t) if is_cons_cell(t.items()) => {
                let items = t.items();
                elems.push(&items[1]);
                cursor = &items[2];
            }
            // Anything else BEFORE reaching `[]` (a non-`[]` atom, a non-cons tuple):
            // not a proper list (the original value is not a list, or the spine is
            // improper). Either way it does not canonicalize as a list.
            Value::Atom(_) | Value::Tuple(_) => return None,
        }
    }
}

/// Whether `items` are exactly the items of a cons cell: arity 3, headed by `Atom(".")`.
fn is_cons_cell(items: &[Value]) -> bool {
    items.len() == 3 && matches!(&items[0], Value::Atom(a) if a.bytes() == CONS_LABEL)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ground_term_round_trips_through_value() {
        let t = Term::tuple([Term::atom(*b"pair"), Term::atom(*b"a"), Term::atom(*b"b")]);
        assert!(t.is_ground());
        let v = t.erase_ground().expect("ground");
        assert_eq!(Term::from_value(&v), t);
    }

    #[test]
    fn a_hole_at_depth_makes_a_term_non_ground() {
        // pair(X, "a") — a hole inside a tuple, not a whole-argument variable.
        let t = Term::tuple([Term::atom(*b"pair"), Term::var("X"), Term::atom(*b"a")]);
        assert!(!t.is_ground());
        assert_eq!(t.erase_ground(), None);
    }

    #[test]
    fn var_identity_is_by_id() {
        assert_eq!(Term::var("X"), Term::var("X"));
        assert_ne!(Term::var("X"), Term::var("Y"));
    }

    // ===================== issue #253: term-nesting depth bound =====================

    /// Build a `Value` nested `depth` levels deep iteratively (so the *fixture* never
    /// overflows). `f(f(…f(a)…))` — a single-child cons-like chain, the worst case.
    fn deep_value(depth: usize) -> Value {
        let mut v = Value::atom(*b"a");
        for _ in 0..depth {
            v = Value::tuple([Value::atom(*b"f"), v]);
        }
        v
    }

    /// Leak a deeply-nested value/term instead of dropping it. The derived `Drop` for
    /// `ontos::Value` / `Term` is RECURSIVE (a frozen external impl for `Value`), so
    /// dropping a depth-50_000 fixture would itself overflow the stack — the very DoS
    /// this bound guards against, but on the test's own cleanup path. Leaking in a
    /// short-lived test process is harmless and keeps the assertion honest (we still
    /// constructed + traversed the pathological value). Production never holds such a
    /// value: the decode boundaries refuse it before it is fully materialized.
    fn leak_deep<T>(t: T) {
        std::mem::forget(t);
    }

    #[test]
    fn depth_le_counts_atom_and_var_as_one() {
        assert!(Term::atom(*b"a").depth_le(1));
        assert!(Term::var("X").depth_le(1));
        // depth 0 admits nothing (every term is at least depth 1).
        assert!(!Term::atom(*b"a").depth_le(0));
    }

    #[test]
    fn depth_le_measures_nesting_at_the_boundary() {
        // pair(a, b) is depth 2: the tuple (1) + its atom children (2).
        let t = Term::tuple([Term::atom(*b"pair"), Term::atom(*b"a"), Term::atom(*b"b")]);
        assert!(t.depth_le(2));
        assert!(!t.depth_le(1));
        // A hole at depth does not change the structural depth.
        let with_hole = Term::tuple([Term::atom(*b"pair"), Term::var("X")]);
        assert!(with_hole.depth_le(2));
        assert!(!with_hole.depth_le(1));
    }

    #[test]
    fn depth_le_is_iterative_and_does_not_overflow_on_a_pathological_term() {
        // A term FAR past the default bound — a recursive measure would overflow the
        // native stack here. `from_value` (iterative) builds it; `depth_le`
        // (iterative) measures it; both survive. The fixture value + term are leaked
        // (their derived Clone/Drop are recursive and would themselves overflow).
        let v = deep_value(50_000);
        let deep = Term::from_value(&v);
        assert!(!deep.depth_le(MAX_TERM_DEPTH_DEFAULT));
        leak_deep(v);
        leak_deep(deep);
        // And a term exactly at the bound is admitted (depth = atom + tuples). These
        // are within a safely-droppable depth, so they drop normally.
        let at_bound = Term::from_value(&deep_value(MAX_TERM_DEPTH_DEFAULT - 1));
        assert!(at_bound.depth_le(MAX_TERM_DEPTH_DEFAULT));
        let over = Term::from_value(&deep_value(MAX_TERM_DEPTH_DEFAULT + 5));
        assert!(!over.depth_le(MAX_TERM_DEPTH_DEFAULT));
    }

    #[test]
    fn value_depth_le_mirrors_term_depth_le() {
        assert!(value_depth_le(&Value::atom(*b"a"), 1));
        assert!(!value_depth_le(&Value::atom(*b"a"), 0));
        // The same pathological depth, measured on the Value directly. Leak it: the
        // derived recursive `Drop` for `ontos::Value` would overflow on cleanup.
        let deep = deep_value(50_000);
        assert!(!value_depth_le(&deep, MAX_TERM_DEPTH_DEFAULT));
        leak_deep(deep);
        assert!(value_depth_le(
            &deep_value(MAX_TERM_DEPTH_DEFAULT - 1),
            MAX_TERM_DEPTH_DEFAULT
        ));
    }

    #[test]
    fn from_value_is_non_recursive_on_a_pathological_value() {
        // The decode boundary must not overflow building a deep term from a deep
        // value (a recursive `from_value` aborts the process at ~670 on a ~1 MiB
        // debug stack). 50_000 is ~75× past that; the iterative build survives.
        let v = deep_value(50_000);
        let t = Term::from_value(&v);
        // Assert it built the deep tuple WITHOUT recursing into it (is_ground/depth_le
        // are fine — depth_le is iterative; is_ground is recursive so we avoid it).
        assert!(matches!(t, Term::Tuple(_)));
        assert!(!t.depth_le(MAX_TERM_DEPTH_DEFAULT));
        leak_deep(v);
        leak_deep(t);
        // Round-trip a within-bound value to confirm the iterative build is faithful
        // (byte-for-byte equal to the recursive shape).
        let small = deep_value(10);
        let lifted = Term::from_value(&small);
        assert_eq!(lifted.erase_ground().expect("ground"), small);
    }

    // ---- #2675: the fast path is observationally identical to the matcher it replaced ----

    /// `match_value` as it was before #2675, verbatim: the oracle.
    fn reference_match_value(term: &Term, value: &Value, subst: &mut Subst) -> bool {
        let mut work: Vec<(&Term, &Value)> = vec![(term, value)];
        while let Some((term, value)) = work.pop() {
            match (term, value) {
                (Term::Var(id), _) => {
                    let bound = Term::from_value(value);
                    match subst.get(id) {
                        Some(existing) if *existing != bound => return false,
                        Some(_) => {}
                        None => {
                            subst.insert(id.clone(), bound);
                        }
                    }
                }
                (Term::Atom(bytes), Value::Atom(atom)) if atom.bytes() == bytes.as_slice() => {}
                (Term::Tuple(children), Value::Tuple(tuple))
                    if tuple.items().len() == children.len() =>
                {
                    work.extend(children.iter().zip(tuple.items()).rev());
                }
                _ => return false,
            }
        }
        true
    }

    fn at(bytes: &str) -> Value {
        Value::atom(bytes.as_bytes().to_vec())
    }

    #[test]
    fn match_value_agrees_with_the_matcher_it_replaced_2675() {
        let deep_v = deep_value(TERM_RECURSION_BUDGET * 2);
        let deep_term = Term::from_value(&deep_v);
        let other_deep = deep_value(TERM_RECURSION_BUDGET * 2 + 1);
        let pair = |a: Term, b: Term| Term::tuple([a, b]);
        let terms = [
            Term::var("X"),
            Term::atom(b"a".to_vec()),
            Term::atom(b"b".to_vec()),
            pair(Term::var("X"), Term::var("X")),
            pair(Term::var("X"), Term::var("Y")),
            pair(Term::var("X"), Term::atom(b"b".to_vec())),
            Term::tuple([Term::var("X"), pair(Term::var("Y"), Term::var("X"))]),
            Term::tuple([Term::atom(b"a".to_vec())]),
            deep_term.clone(),
        ];
        let values = [
            at("a"),
            at("b"),
            Value::tuple(vec![at("a"), at("a")]),
            Value::tuple(vec![at("a"), at("b")]),
            Value::tuple(vec![at("a"), Value::tuple(vec![at("b"), at("a")])]),
            Value::tuple(vec![at("a"), Value::tuple(vec![at("b"), at("c")])]),
            Value::tuple(vec![at("a")]),
            Value::tuple(vec![]),
            deep_v.clone(),
            other_deep,
        ];
        // Starting substitutions: empty, and ones that bind X (to an atom, a tuple and a deep term)
        // so the already-bound comparison runs, past the recursion budget included.
        let bindings: Vec<Subst> = vec![
            Subst::new(),
            Subst::from([(VarId::new("X"), Term::atom(b"a".to_vec()))]),
            Subst::from([(VarId::new("X"), Term::atom(b"b".to_vec()))]),
            Subst::from([(
                VarId::new("X"),
                Term::tuple([Term::atom(b"a".to_vec()), Term::atom(b"a".to_vec())]),
            )]),
            Subst::from([(VarId::new("X"), deep_term)]),
            Subst::from([(VarId::new("X"), Term::var("Z"))]),
        ];
        let mut agreed_true = 0;
        let mut agreed_false = 0;
        for term in &terms {
            for value in &values {
                for start in &bindings {
                    let (mut ours, mut theirs) = (start.clone(), start.clone());
                    let got = term.match_value(value, &mut ours);
                    let want = reference_match_value(term, value, &mut theirs);
                    assert_eq!(got, want, "{term:?} against {value:?} from {start:?}");
                    assert_eq!(
                        ours, theirs,
                        "{term:?} against {value:?} from {start:?}: the bindings"
                    );
                    if got {
                        agreed_true += 1;
                    } else {
                        agreed_false += 1;
                    }
                }
            }
        }
        assert!(
            agreed_true > 0 && agreed_false > 0,
            "the control: both outcomes occur ({agreed_true} matched, {agreed_false} refused)"
        );
    }
}
