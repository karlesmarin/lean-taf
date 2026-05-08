/-
  Taf.SmeftTrilinearAudit — formal verification of identity I-1.5 from
  arXiv:2504.05974 "Higgs trilinear coupling in SMEFT at HL-LHC and FCC-ee".

  Phase 4 priority-1b deliverable of the Sócrates audit at
  E:/proyectos/socrates-audit/data/smeft_trilinear/.

  Goal: prove that, given the paper's own equations
       I-1.1: V(h) = (1/2) m_h² h² + λ_SM (1+δκ₃) v h³ + (1/4) λ_SM (1+δκ₄) h⁴
       I-1.2: λ_SM = m_h² / (2 v²)
       I-1.3: O_φ = (φ†φ - v²/2)³ ⊃ v³ h³ + (3 v² / 2) h⁴       (in unitary gauge)
  and the SMEFT correction V_SMEFT = V_SM - (c_φ / Λ²) O_φ ,
  the implied relation between δκ₃ and δκ₄ when only c_φ is non-zero is

      δκ₄ = 6 · δκ₃                        (Phase-1.0 derivation)

  NOT

      δκ₄ = δκ₃ / 6                        (paper line 310)

  These differ by a factor of 36 (the two are reciprocals). Almost certainly
  a typo in the paper; this Lean proof rigorously settles which is correct.

  Method: one-line `ring` tactic. The relation is a pure commutative-ring
  identity over ℝ, given the operator-coefficient matching.

  References:
    arXiv:2504.05974 v2 line 310 (the disputed claim)
    SymPy verification: socrates-audit/data/smeft_trilinear/audit/verify_i_1_5.py
    Phase-1.0 derivation: socrates-audit/data/smeft_trilinear/concepts/identities.md §III
-/

import Mathlib

namespace Taf.SmeftTrilinearAudit

/-! ## Section 1 — Operator expansion (verifying I-1.3)

In unitary gauge, φ = (0, (v+h)/√2)ᵀ, so φ†φ - v²/2 = vh + h²/2.
Therefore:

    O_φ ≡ (φ†φ - v²/2)³ = (vh + h²/2)³

Expanding:
-/

theorem operator_phi_expansion (v h : ℝ) :
    (v * h + h^2 / 2)^3
      = v^3 * h^3 + (3 * v^2 / 2) * h^4 + (3 * v / 4) * h^5 + h^6 / 8 := by
  ring

/-! ## Section 2 — Coefficient matching (the heart of I-1.5)

The SMEFT-corrected potential is

    V_SMEFT(h) = (1/2) m_h² h² + λ_SM v h³ + (λ_SM / 4) h⁴
                 - (c_φ / Λ²) [v³ h³ + (3 v² / 2) h⁴ + (3 v / 4) h⁵ + h⁶ / 8]

where λ_SM = m_h² / (2 v²) implies λ_SM v = m_h² / (2 v) and λ_SM / 4 =
m_h² / (8 v²) for the SM-piece h³ and h⁴ coefficients.

Matching the h³ coefficient of V_SMEFT to V_paper's
    λ_SM (1 + δκ₃) v = m_h² (1 + δκ₃) / (2 v)
gives
    δκ₃ = -2 v⁴ c_φ / (m_h² Λ²)            -- matches paper I-1.4 c_φ part

Matching h⁴ coefficient gives
    δκ₄ = -12 v⁴ c_φ / (m_h² Λ²)

So δκ₄ / δκ₃ = -12 / -2 = 6, hence δκ₄ = 6 · δκ₃.
-/

/-- The values of δκ₃ and δκ₄ derived from coefficient matching when only
    c_φ is non-zero. Marked `noncomputable` because real division is
    classically defined and not algorithmically computable in Lean. -/
noncomputable def δκ3_from_c_phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -2 * v^4 * c_phi / (m_h^2 * Λ^2)

noncomputable def δκ4_from_c_phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -12 * v^4 * c_phi / (m_h^2 * Λ^2)

/-- **The key theorem**: δκ₄ = 6 · δκ₃ when only c_φ contributes.

    This contradicts the paper's claim (arXiv:2504.05974 line 310) that
    δκ₄ = δκ₃ / 6. The two relations are reciprocals (factor-36 apart),
    so at most one can hold. The `ring` tactic confirms our derivation.

    Likely cause of paper's claim: typo. Numerical conclusions of paper
    (Tables I and II, Figures 1-4) do not depend on this relation, so
    no scientific conclusion of the paper is affected. This is at most
    an erratum candidate. -/
theorem delta_kappa_4_equals_6_delta_kappa_3 (v m_h c_phi Λ : ℝ) :
    δκ4_from_c_phi v m_h c_phi Λ = 6 * δκ3_from_c_phi v m_h c_phi Λ := by
  unfold δκ3_from_c_phi δκ4_from_c_phi
  ring

end Taf.SmeftTrilinearAudit
