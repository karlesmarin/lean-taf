/-
  Taf.SmeftTrilinearAudit — formal verification of the structural identities
  in arXiv:2504.05974 "Higgs trilinear coupling in SMEFT at HL-LHC and FCC-ee".

  Phase 4 priority-1 + priority-2 deliverable of the Sócrates audit at
  E:/proyectos/socrates-audit/data/smeft_trilinear/.

  ## Phase 4 P1 (already shipped, commit 8901478)

  - I-1.3 (operator expansion): O_φ = (vh + h²/2)³ = full sextic polynomial.
  - I-1.5 (the disputed ratio): δκ₄ = 6 · δκ₃ when only c_φ contributes.
    Paper line 310 claims δκ₄ = δκ₃ / 6 — INCONSISTENT with paper's own
    eqs I-1.1 + I-1.3, factor of 36 inverse. Likely typo, erratum candidate.

  ## Phase 4 P2 (this file, extended 2026-05-09)

  Adds formal proofs for the remaining structural identities the paper uses:

  - I-1.2: λ_SM = m_h² / (2 v²)            — definition + arithmetic helpers
  - I-1.4 c_φ part (h³ matching):  δκ₃ = -2 v⁴ c_φ / (m_h² Λ²)
  - I-1.4 mirror at h⁴:             δκ₄ = -12 v⁴ c_φ / (m_h² Λ²)
  - I-1.6: κ₃ = 1 + δκ₃                    — trivial relabelling

  ## Out-of-scope for this Lean file

  - I-1.4 c_{φ□} / c_{φD} parts: arise from Alasfar:2023xpc field redefinitions
    (eq 2.5 there), NOT from operator expansion of O_φ. Formalising would
    require encoding the EOM-shift step which is well beyond `ring`. Phase 7.
  - I-5.1/2/3 (UV model + matching): group-theoretic + loop-level claims;
    out of scope for an algebraic-identity Lean module.
  - I-SIA.1 (Δχ² = -2 Δln L): definitional, Bayesian/likelihood theory.
  - C-3.x / R-x numerical claims: empirical fit outputs; verified separately
    by interval arithmetic in concepts/identities.md §VI.

  ## Method

  Pure commutative-ring identities over ℝ. After unfolding noncomputable
  definitions (real division → classical inverse), `ring` and `field_simp`
  close every goal. No `sorry`, no axioms beyond Mathlib core.

  ## References

  - arXiv:2504.05974 v2 (Ter Hoeve, Mantani, Rojo, Rossia, Vryonidou 2025)
  - SymPy verification: socrates-audit/data/smeft_trilinear/audit/verify_i_1_5.py
  - Phase-1.0 derivation: socrates-audit/data/smeft_trilinear/concepts/identities.md §III
  - Mathlib4 tactics used: Mathlib.Tactic.Ring, Mathlib.Tactic.FieldSimp.
-/

import Mathlib

namespace Taf.SmeftTrilinearAudit

/-! ## §1 Operator expansion (I-1.3 full form)

In unitary gauge, φ = (0, (v+h)/√2)ᵀ, so φ†φ - v²/2 = vh + h²/2.
Therefore O_φ ≡ (φ†φ - v²/2)³ = (vh + h²/2)³.
-/

/-- I-1.3 full expansion of O_φ. The paper writes only `⊃ v³h³ + (3v²/2)h⁴`
    (the part that contributes to the trilinear/quartic Higgs vertex); the
    full expansion also has h⁵ and h⁶ pieces relevant for ⟨HHH⟩ at higher
    multiplicity. -/
theorem operator_phi_expansion (v h : ℝ) :
    (v * h + h^2 / 2)^3
      = v^3 * h^3 + (3 * v^2 / 2) * h^4 + (3 * v / 4) * h^5 + h^6 / 8 := by
  ring

/-- I-1.3 paper-stated partial form: the h³ + h⁴ piece is exactly the
    leading two terms of the full expansion. The `⊃` symbol in the paper
    is captured as: full_expansion = (paper_part) + (h⁵ tail). -/
theorem operator_phi_partial (v h : ℝ) :
    (v * h + h^2 / 2)^3
      = (v^3 * h^3 + (3 * v^2 / 2) * h^4) + ((3 * v / 4) * h^5 + h^6 / 8) := by
  ring

/-! ## §2 Standard-Model Higgs-coupling definition (I-1.2)

The paper defines λ_SM via the SM Higgs potential V_SM = (m_h²/2) h² + λ_SM v h³
+ (λ_SM/4) h⁴, equivalent to λ_SM = m_h² / (2 v²) (line 290 parenthetical).
-/

/-- I-1.2: λ_SM as the unique value making the h³ coefficient consistent with
    the standard tree-level Higgs sector. Predicate form. -/
def lambda_SM_relation (lam_SM m_h v : ℝ) : Prop :=
  lam_SM = m_h^2 / (2 * v^2)

/-- λ_SM · v simplification used throughout: λ_SM v = m_h² / (2v). -/
theorem lambda_SM_times_v (lam_SM m_h v : ℝ) (hv : v ≠ 0)
    (h : lambda_SM_relation lam_SM m_h v) :
    lam_SM * v = m_h^2 / (2 * v) := by
  unfold lambda_SM_relation at h
  rw [h]
  field_simp

/-! ## §3 κ-framework labelling (I-1.6)

Trivial relabelling: κ₃ ≡ 1 + δκ₃. Paper line 312. The "kappa-framework"
makes the experimental quantity (κ₃) directly comparable to ATLAS/CMS
observed-ratios, while δκ₃ is the EFT-natural deviation parameter.
-/

def kappa3 (delta_kappa3 : ℝ) : ℝ := 1 + delta_kappa3

theorem kappa3_definition (delta_kappa3 : ℝ) :
    kappa3 delta_kappa3 = 1 + delta_kappa3 := rfl

theorem kappa3_SM_value : kappa3 0 = 1 := by
  unfold kappa3; ring

/-! ## §4 Coefficient matching (I-1.4 c_φ part, I-1.5 c_φ part)

  V_paper(h)        = (m_h²/2) h² + λ_SM(1+δκ₃) v h³ + (λ_SM/4)(1+δκ₄) h⁴
  V_SMEFT_corr(h)   = V_SM(h) - (c_φ/Λ²) · O_φ
                    = (m_h²/2)h² + λ_SM v h³ + (λ_SM/4) h⁴
                      - (c_φ/Λ²)[v³ h³ + (3v²/2) h⁴ + (3v/4) h⁵ + h⁶/8]

Matching h^k coefficients of V_paper and V_SMEFT_corr (with λ_SM = m_h²/(2v²))
fixes δκ₃, δκ₄ in terms of c_φ.
-/

/-- δκ₃ derived from c_φ-only matching (paper I-1.4, c_φ piece). -/
noncomputable def delta_kappa_3_from_c_phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -2 * v^4 * c_phi / (m_h^2 * Λ^2)

/-- δκ₄ derived from c_φ-only matching (Phase-1.0 result; paper claim line 310
    is its 1/6 reciprocal — see `paper_claim_inconsistent_with_h4_matching`
    at the bottom). -/
noncomputable def delta_kappa_4_from_c_phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -12 * v^4 * c_phi / (m_h^2 * Λ^2)

/-- The h³-coefficient matching equation: V_paper's h³ coefficient equals
    V_SMEFT_corr's h³ coefficient when λ_SM = m_h²/(2v²) and δκ₃ takes its
    derived value. This is the algebraic content of paper I-1.4 (c_φ part).

    Statement form: with λ_SM ≡ m_h²/(2v²) substituted in, the matching
    equation `λ_SM v (1 + δκ₃) = λ_SM v - c_φ v³/Λ²` holds exactly. -/
theorem h3_matching_holds
    (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0) (hΛ : Λ ≠ 0) :
    (m_h^2 / (2 * v^2)) * v * (1 + delta_kappa_3_from_c_phi v m_h c_phi Λ)
      = (m_h^2 / (2 * v^2)) * v - c_phi * v^3 / Λ^2 := by
  unfold delta_kappa_3_from_c_phi
  have h2v2 : (2 : ℝ) * v^2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2  : Λ^2   ≠ 0 := pow_ne_zero 2 hΛ
  have hm2  : m_h^2 ≠ 0 := pow_ne_zero 2 hm
  field_simp
  ring

/-- The h⁴-coefficient matching equation: V_paper's h⁴ coefficient equals
    V_SMEFT_corr's h⁴ coefficient. Mirrors `h3_matching_holds` for h⁴. -/
theorem h4_matching_holds
    (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0) (hΛ : Λ ≠ 0) :
    ((m_h^2 / (2 * v^2)) / 4) * (1 + delta_kappa_4_from_c_phi v m_h c_phi Λ)
      = (m_h^2 / (2 * v^2)) / 4 - 3 * c_phi * v^2 / (2 * Λ^2) := by
  unfold delta_kappa_4_from_c_phi
  have h2v2 : (2 : ℝ) * v^2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2  : Λ^2   ≠ 0 := pow_ne_zero 2 hΛ
  have hm2  : m_h^2 ≠ 0 := pow_ne_zero 2 hm
  field_simp
  ring

/-! ## §5 The disputed ratio (I-1.5)

Phase 1.0 / Phase 4 P1 finding: δκ₄ = 6·δκ₃ when only c_φ contributes.
Paper's stated I-1.5 says δκ₄ = δκ₃ / 6 — these are reciprocals (factor of 36).

The next theorem is the original P1 result, kept for backwards compatibility
and citation in the verdict log.
-/

/-- **The key theorem (Phase 4 P1)**: δκ₄ = 6·δκ₃ when only c_φ contributes.
    This contradicts arXiv:2504.05974 line 310, which claims δκ₄ = δκ₃/6.
    The two are reciprocals (factor of 36). At most one can hold; this proof
    settles which. -/
theorem delta_kappa_4_equals_6_delta_kappa_3 (v m_h c_phi Λ : ℝ) :
    delta_kappa_4_from_c_phi v m_h c_phi Λ
      = 6 * delta_kappa_3_from_c_phi v m_h c_phi Λ := by
  unfold delta_kappa_3_from_c_phi delta_kappa_4_from_c_phi
  ring

/-- Stronger statement: the two δκ values do NOT satisfy the paper's claimed
    relation δκ₄ = δκ₃/6 except in the degenerate case δκ₃ = 0 (i.e.
    c_φ = 0, the SM limit). When c_φ ≠ 0, the paper's relation fails. -/
theorem paper_claim_inconsistent_with_h4_matching
    (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0) (hΛ : Λ ≠ 0)
    (hc : c_phi ≠ 0) :
    delta_kappa_4_from_c_phi v m_h c_phi Λ
      ≠ delta_kappa_3_from_c_phi v m_h c_phi Λ / 6 := by
  unfold delta_kappa_3_from_c_phi delta_kappa_4_from_c_phi
  have h2v2 : (2 : ℝ) * v^2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2  : Λ^2   ≠ 0 := pow_ne_zero 2 hΛ
  have hm2  : m_h^2 ≠ 0 := pow_ne_zero 2 hm
  have hv4  : v^4   ≠ 0 := pow_ne_zero 4 hv
  intro habs
  -- After clearing denominators, habs becomes a polynomial equation
  -- whose only solution is c_phi = 0, contradicting hc.
  apply hc
  field_simp at habs
  linarith

/-! ## §6 SM limit consistency

When c_φ = 0 we should recover δκ₃ = δκ₄ = 0 (the SM Higgs sector). Both
sides of the paper's claim and our derived ratio agree trivially in this
limit — that's why the typo is invisible in the SM-limit numerics.
-/

theorem delta_kappa_3_SM_limit (v m_h Λ : ℝ) :
    delta_kappa_3_from_c_phi v m_h 0 Λ = 0 := by
  unfold delta_kappa_3_from_c_phi
  ring

theorem delta_kappa_4_SM_limit (v m_h Λ : ℝ) :
    delta_kappa_4_from_c_phi v m_h 0 Λ = 0 := by
  unfold delta_kappa_4_from_c_phi
  ring

/-! ## §7 Numerical sanity check (I-1.2 with PDG values)

PDG 2024 central values:  m_h ≈ 125.25 GeV,  v ≈ 246.22 GeV.
Then λ_SM = m_h²/(2v²) ≈ 0.1294. We don't formalise the PDG measurements,
but we can prove the relation on rationals exactly to demonstrate that the
algebraic structure does what we expect.
-/

theorem lambda_SM_rational_check :
    (1 : ℝ)^2 / (2 * (1 : ℝ)^2) = 1 / 2 := by
  norm_num

end Taf.SmeftTrilinearAudit
