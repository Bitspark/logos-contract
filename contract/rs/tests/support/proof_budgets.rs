use logos_contract::{CheckLimits, ProofBudgetCount};

/// Read the conformance target once, checking both the protocol and this test host's capacity.
pub(super) fn r3_raised() -> usize {
    let raw = include_str!("../../../../vectors/allowances.json");
    let table: serde_json::Value =
        serde_json::from_str(raw).expect("vectors/allowances.json parses");
    let raised = table["raised"].as_u64().expect("raised is a count");
    let count = ProofBudgetCount::new("raised", raised).expect("portable conformance budget");
    usize::try_from(count.get()).expect("conformance budget fits the test host")
}

/// R3's variants at the checker (#2733, `seat:caa`'s ruling on 3b, C2): each budget raised to
/// at least `to` alone, then every budget together, labelled by the budget's name (or `every`).
/// A budget already at or above `to` is left alone, and a variant equal to `limits` is dropped,
/// so a raise is never a no-op and never a lowering.
pub(super) fn each_budget_raised(
    limits: CheckLimits,
    to: usize,
) -> Vec<(&'static str, CheckLimits)> {
    let mut out = Vec::new();
    let mut every = limits;
    for (i, (name, value)) in limits.budgets().into_iter().enumerate() {
        if value >= to {
            continue;
        }
        let mut one = limits;
        *one.budgets_mut()[i].1 = to;
        *every.budgets_mut()[i].1 = to;
        out.push((name, one));
    }
    if out.len() > 1 {
        out.push(("every", every));
    }
    out
}
