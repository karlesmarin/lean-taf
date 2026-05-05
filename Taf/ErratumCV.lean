/-
  Taf.ErratumCV — Lean formalization of the algebraic core of the
  erratum to "Predicting How Transformers Attend" §5.2 Theorem 5.2
  (Marín, 2026-05-02, factor-of-3 correction in the heat-capacity
  coefficient at the Hagedorn point).

  Original (wrong):  C_V(γ=1, N) = (log N)² / 4
  Corrected:         C_V(γ=1, N) → (log N)² / 12

  This file formalizes the algebraic chain that reduces both
  derivations of the corrected coefficient (Taylor expansion §2,
  cumulant identity §3) to the L²/12 form. Asymptotic equivalence
  (`→` as N → ∞) is NOT formalized here; that would require
  Mathlib's Asymptotics.IsLittleO machinery + Euler-Maclaurin
  bounds for harmonic-sum approximations. The integral lemma
  `∫ log(x)/x = (log N)²/2` lives in Taf.CvHagedornCorrection.

  Companion: `Taf.RGFlow` (RG-flow algebra including V/β consistency).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace TAF.ErratumCV

-- =============================================================================
-- §3 — cumulant identity at Hagedorn
--
-- Erratum eqs (8)-(10):
--   E[log d] ~ (log N)/2
--   E[(log d)²] ~ (log N)²/3
--   Var(log d) = E[(log d)²] − (E[log d])² = (log N)²/3 − (log N)²/4 = (log N)²/12
--   C_V(γ=1) = γ²·Var(log d) = (log N)²/12  ✓
-- =============================================================================

/-- `(log N)²/3 − ((log N)/2)² = (log N)²/12`. -/
theorem var_log_d_identity (L : ℝ) :
    L^2 / 3 - (L / 2)^2 = L^2 / 12 := by ring

/-- `C_V(γ=1) = γ² · Var(log d) = (log N)²/12`. -/
theorem cv_from_cumulant_at_hagedorn (L : ℝ) :
    (1 : ℝ)^2 * (L^2 / 3 - (L / 2)^2) = L^2 / 12 := by ring

-- =============================================================================
-- §2 — Taylor expansion second-order coefficient
--
-- log Z ≈ log(log N) + u·(log N)/2 + u²·(log N)²/24 + …
-- where 1/24 = 1/6 − 1/8 from log(1+x) = x − x²/2.
-- =============================================================================

/-- `1/6 − 1/8 = 1/24` (the log(1+x) trick). -/
theorem log_one_plus_x_coefficient_24 :
    (1 : ℝ) / 6 - 1 / 8 = 1 / 24 := by norm_num

/-- Scaled by L²: `L²/6 − L²/8 = L²/24`. -/
theorem log_z_quadratic_coefficient (L : ℝ) :
    L^2 / 6 - L^2 / 8 = L^2 / 24 := by ring

/-- `2 · (L²/24) = L²/12` (derivative of the quadratic Taylor term). -/
theorem log_z_to_U_coefficient (L : ℝ) :
    (2 : ℝ) * (L^2 / 24) = L^2 / 12 := by ring

/-- U(γ) corrected: `U_corrected(γ, L) = L/2 + (1−γ)·L²/12`. -/
noncomputable def U_corrected (L γ : ℝ) : ℝ :=
  L / 2 + (1 - γ) * L^2 / 12

/-- Erratum eq (5): `dU/dγ |_{γ=1} = −(log N)²/12`. -/
theorem dU_corrected_at_one (L : ℝ) :
    deriv (fun γ => U_corrected L γ) 1 = -L^2 / 12 := by
  unfold U_corrected
  have h_const : HasDerivAt (fun _ : ℝ => L / 2) 0 1 :=
    hasDerivAt_const 1 (L / 2)
  have h_id : HasDerivAt (fun γ : ℝ => γ) 1 1 := hasDerivAt_id 1
  have h_one_minus : HasDerivAt (fun γ : ℝ => 1 - γ) (-1) 1 := by
    simpa using (hasDerivAt_const 1 (1 : ℝ)).sub h_id
  have h_factor : HasDerivAt (fun γ : ℝ => (1 - γ) * L^2 / 12)
      (-L^2 / 12) 1 := by
    have step1 : HasDerivAt (fun γ : ℝ => (1 - γ) * L^2)
        (-1 * L^2) 1 := h_one_minus.mul_const _
    have step2 := step1.div_const 12
    have h_eq : (-1 * L^2) / 12 = -L^2 / 12 := by ring
    rw [h_eq] at step2
    exact step2
  have h_total := h_const.add h_factor
  have h_eq : (0 + -L^2 / 12) = -L^2 / 12 := by ring
  rw [h_eq] at h_total
  exact h_total.deriv

/-- Erratum eq (6): `C_V(γ=1, N) = −γ²·dU/dγ = (log N)²/12`. -/
theorem cv_corrected_at_hagedorn (L : ℝ) :
    -((1 : ℝ)^2) * (deriv (fun γ => U_corrected L γ) 1) = L^2 / 12 := by
  rw [dU_corrected_at_one]
  ring

-- =============================================================================
-- Original-vs-corrected: factor of 3
-- =============================================================================

/-- The original `(log N)²/4` is exactly THREE TIMES `(log N)²/12`. -/
theorem original_is_three_times_corrected (L : ℝ) :
    L^2 / 4 = 3 * (L^2 / 12) := by ring

/-- The two coefficients are NOT equal except in the trivial case L = 0. -/
theorem original_ne_corrected (L : ℝ) (hL : L ≠ 0) :
    L^2 / 4 ≠ L^2 / 12 := by
  intro h
  have hL2 : L^2 = 0 := by linarith
  have hLz : L = 0 := sq_eq_zero_iff.mp hL2
  exact hL hLz

/-- Phase 8 wrong derivation residual `L²/8 = 3·(L²/24)`. -/
theorem cv_factor_three_decomposition (L : ℝ) :
    L^2 / 8 = 3 * (L^2 / 24) := by ring

end TAF.ErratumCV
