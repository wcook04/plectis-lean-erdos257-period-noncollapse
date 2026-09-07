#!/usr/bin/env python3
"""Idempotently append r4 revision exact_results into the Erdős 257 packet."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ERDOS257 = Path(__file__).resolve().parents[1]
PACKET = ERDOS257 / "research_packet.json"
LEAN = ERDOS257 / "SignedFinitePeriodNoncollapse.lean"
NOTE_COVER = ERDOS257 / "CoverFirstLogarithmicMoment.md"
NOTE_DEN = ERDOS257 / "FiniteDenominatorRealisation.md"
NOTE_LAB = ERDOS257 / "SupportWordStructureLab.md"
SCRIPT = ERDOS257 / "scripts" / "check_signed_finite_period_r4.py"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    data = json.loads(PACKET.read_text())
    existing = {row.get("id") for row in data.get("exact_results", [])}
    new_rows = [
        {
            "id": "signed_finite_period_unit_coeff",
            "status": "lean_source_landed_focused_compile_pending_occupancy",
            "statement": "For nonempty finite F of positive integers, b≥2, and ε_n in {±1}, the reduced denominator D of ∑_{n∈F} ε_n/(b^n-1) is coprime to b and satisfies ord_D(b)=lcm(F). Arbitrary nonzero integer coefficients fail: 1/(2-1)+3/(2^2-1)=2.",
            "source_path": "Erdos257/SignedFinitePeriodNoncollapse.lean",
            "source_sha256": sha256(LEAN),
            "source_declarations": [
                "ErdosProblems.Erdos257.signed_finite_period_noncollapse",
                "ErdosProblems.Erdos257.lcm_lt_den_signedFiniteErdosSum",
                "ErdosProblems.Erdos257.one_plus_three_over_three_eq_two",
            ],
            "claim_boundary": "Does not close universal #257 or the rational targets 1/2, 1/21. Unsigned finite_period_noncollapse_rat_den remains the existing finite-period flagship statement. Focused lean_fast_build of this new module was occupancy-queued (exit 75) after a first compile failure; source fixes are on disk.",
            "validation": "scripts/check_signed_finite_period_r4.py --quick",
            "next_consumer_effect": "Does not replace reciprocal_summable_supports_base_two.",
            "surviving_obligation": "Consume the occupancy future for a focused PASS. Universal #257 remains open.",
        },
        {
            "id": "cyclotomic_prime_full_val_exact_order",
            "status": "lean_source_landed_focused_compile_pending_occupancy",
            "statement": "If ℓ | Φ_n(b) and e=v_ℓ(b^n-1) for b≥2, n≥2, then ord_{ℓ^e}(b)=n. In particular ExactOrderPrimePowerWitness exists with the full cyclotomic valuation. Φ_6(2)=3 and ord_9(2)=6.",
            "source_path": "Erdos257/SignedFinitePeriodNoncollapse.lean",
            "source_sha256": sha256(LEAN),
            "source_declarations": [
                "ErdosProblems.Erdos257.cyclotomic_prime_dvd_imp_exactOrder_full_val",
                "ErdosProblems.Erdos257.exactOrder_two_mod_nine",
                "ErdosProblems.Erdos257.signed_divisibility_maximal_cyclotomic_den_val",
            ],
            "claim_boundary": "Identifies the full valuation for a given cyclotomic prime; exists_exactOrderPrimePowerWitness already produced some (q,s). Product of R_b(n) over a maximal antichain remains ordinary.",
            "validation": "scripts/check_signed_finite_period_r4.py --quick (Phi_6(2)=3, ord_9(2)=6, ord_21(2)=6)",
            "next_consumer_effect": "Does not replace reciprocal_summable_supports_base_two.",
            "surviving_obligation": "Focused Lean occupancy. A.3 product statement stays ordinary.",
        },
        {
            "id": "supportword_nonmersenne_prime_den_false",
            "status": "rejected_exactly_as_live_equality",
            "statement": "The SupportWordStructureLab claim that a non-Mersenne prime admits no finite Mersenne sum is false: 1/3+1/15=2/5. The lab table already listed q=5 with 2/5, 7/5. Replacement is a necessary-condition theorem, not a classification.",
            "source_path": "Erdos257/SupportWordStructureLab.md",
            "source_sha256": sha256(NOTE_LAB),
            "lean_source": "Erdos257/SignedFinitePeriodNoncollapse.lean",
            "source_declarations": [
                "ErdosProblems.Erdos257.one_div_three_add_one_div_fifteen_eq_two_div_five",
                "ErdosProblems.Erdos257.five_is_nonMersenne_finite_mersenne_denominator",
            ],
            "claim_boundary": "Does not classify all prime denominators. Does not decide 1/2 or 1/21.",
            "validation": "scripts/check_signed_finite_period_r4.py --quick two_fifths row",
            "next_consumer_effect": "Lab prose corrected. Not a Palomar lead.",
            "surviving_obligation": "Universal #257 remains open.",
        },
        {
            "id": "finite_period_ordinary_noncancellation_and_order6_repair",
            "status": "ordinary_proof",
            "statement": "Finite-period noncancellation is a unique-valuation argument at a divisibility-maximal exponent. The r3 written gap is supplied. Order 6 is not only from 9: ord_9(2)=6 for F={2,6} and ord_21(2)=lcm(2,3)=6 for F={2,3}. Cyclotomic lower bounds on D_F make rational-difference lower bounds smaller, not larger, and do not prove the actual selector inequality.",
            "source_path": "Erdos257/FiniteDenominatorRealisation.md",
            "source_sha256": sha256(NOTE_DEN),
            "claim_boundary": "Ordinary unsigned bridge. Signed unit-coefficient form is the sibling Lean module. Does not close 1/2, 1/21, or universal #257. A.3 product of R_b(n) stays ordinary except the one-prime Lean identity.",
            "validation": "Independent ordinary reading plus the r4 checker order-6 and signed-support rows.",
            "next_consumer_effect": "Unblocks r3 blocked_external cyclotomic_noncancellation_bridge as ordinary. Does not replace reciprocal_summable_supports_base_two.",
            "surviving_obligation": "Actual-selector inequality (D.2) remains open.",
        },
        {
            "id": "cover_first_log_moment_divisor_cube_and_A_W",
            "status": "ordinary_proof",
            "statement": "Every strengthened positive cover obeys K ≥ E Ψ(f_F) ≥ e E log^+ f_F. Divisor-cube frames have K_* = (e+o(1))S/q. There is a weighted support A_W in W but not V, while r3 A* is in V but not W, so the classes are incomparable. Base displacements satisfy Δ_{b,A}(N) ≤ Δ_{2,A}(N) in ordinary mathematics. r3 A* / new variable-exponent cost remains ordinary.",
            "source_path": "Erdos257/CoverFirstLogarithmicMoment.md",
            "source_sha256": sha256(NOTE_COVER),
            "reconstruction": "Erdos257/scripts/check_signed_finite_period_r4.py --quick",
            "reconstruction_sha256": sha256(SCRIPT),
            "claim_boundary": "Ordinary. Does not close the parent, does not prove a union A_W ∪ A* irrational, and does not replace the reciprocal flagship. A_W is not a second A*. Base monotonicity was not Lean-checked this wave.",
            "validation": "Checker Psi gauge, divisor-cube interval shape, and numeric base monotonicity.",
            "next_consumer_effect": "Keep as an enlargement of the cover remainder. Do not promote to Palomar lead.",
            "surviving_obligation": "Universal #257 remains open. A* Lean remains ordinary.",
        },
    ]
    added = []
    for row in new_rows:
        if row["id"] in existing:
            continue
        data["exact_results"].append(row)
        added.append(row["id"])
    delta_extra = (
        " The 2026-09-07 Type B r4 packet is assimilated without changing the paper lead: "
        "reciprocal_summable_supports_base_two remains the Lean-checked Palomar flagship. "
        "Ordinary unique-valuation noncancellation repairs the r3 written finite-period gap; "
        "signed unit-coefficient noncollapse and cyclotomic full-valuation exact-order witnesses "
        "are a focused Lean module pending occupancy. The SupportWord non-Mersenne-prime census "
        "is false (1/3+1/15=2/5). Cover first-log-moment / divisor-cube cost / A_W incomparability "
        "with r3 A* stay ordinary and do not close the parent. Universal #257 and both rational "
        "targets remain open."
    )
    current_delta = data.get("latest_claim_ceiling_delta") or ""
    if "Type B r4 packet" not in current_delta:
        data["latest_claim_ceiling_delta"] = current_delta.rstrip() + delta_extra
    negs = data.setdefault("negative_results", [])
    for item in (
        "SupportWordStructureLab's universal non-Mersenne-prime finite-sum census is false: 1/3+1/15=2/5.",
        "Arbitrary integer coefficients need not preserve finite-period: 1/(2-1)+3/(2^2-1)=2.",
        "Order 6 in a divisor of 63 is not only from 9; ord_21(2)=lcm(2,3)=6.",
    ):
        if not any(item[:40] in str(existing_item) for existing_item in negs):
            negs.append(item)
    PACKET.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"added": added, "packet": str(PACKET)}, indent=2))


if __name__ == "__main__":
    main()
