/-
  Taf.ScalingLawIdentities — formal Lean 4 proofs of the TAF scaling-law /
  attention-decay closed-form identities.

  Companion to Taf.Identities and Taf.RGFlow. These nine identities (in the decay
  exponent γ and the dimensionless variable z = T√2/θ) were verified mechanically
  in SymPy/Sage; this file gives formal proofs in dependent type theory. No `sorry`.

  References:
  - Marin 2026, Predicting How Transformers Attend (Zenodo 19826343)
-/
import Mathlib

namespace TAF

/-- **Logistic ↔ β(γ).** With x=(1−γ)/2, the logistic rate x(1−x) = (1−γ²)/4,
    i.e. dx/dt = x(1−x) ⇔ β(γ) = −(1−γ²)/2. -/
theorem logistic_beta (γ : ℝ) : ((1-γ)/2) * (1 - (1-γ)/2) = (1 - γ^2)/4 := by
  ring

/-- **Cayley fixed point.** z* = (√17−3)/2 is the fixed point γ_Padé(z)=z,
    the root of z²+3z−2=0  [γ_Padé(z) = (2−z)/(2+z)]. -/
theorem cayley_fixed_point :
    ((Real.sqrt 17 - 3)/2)^2 + 3*((Real.sqrt 17 - 3)/2) - 2 = 0 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination h/4

/-- **Susceptibility minimal polynomial.** χ(z*) = (5+√17)/4 satisfies 2χ²−5χ+1=0. -/
theorem chi_minimal_poly :
    2*((5 + Real.sqrt 17)/4)^2 - 5*((5 + Real.sqrt 17)/4) + 1 = 0 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination h/8

/-- **Padé[2,2] − Padé[1,1] of e^(−z).** Exact difference of the two decay approximants. -/
theorem pade_22_minus_11 (z : ℝ) (h1 : 2 + z ≠ 0) (h2 : z^2 + 6*z + 12 ≠ 0) :
    (12 - 6*z + z^2)/(z^2 + 6*z + 12) - (2 - z)/(2 + z)
      = 2*z^3 / ((2 + z) * (z^2 + 6*z + 12)) := by
  rw [div_sub_div _ _ h2 h1, div_eq_div_iff (mul_ne_zero h2 h1) (mul_ne_zero h1 h2)]
  ring

/-- **Lévy / fractional-Laplacian index.** With s=(γ−1)/2, the Lévy index 2s = γ−1. -/
theorem levy_index (γ : ℝ) : 2 * ((γ - 1)/2) = γ - 1 := by ring

/-- **Floquet multiplier at the Cayley fixed point.** γ'_Padé(z*) = (√17−9)/8 (|μ|<1),
    in cleared form via (2+z*)² = (9+√17)/2. -/
theorem floquet_multiplier :
    ((Real.sqrt 17 - 9)/8) * (2 + (Real.sqrt 17 - 3)/2)^2 = -4 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination (Real.sqrt 17 - 7)/32 * h

/-- **"2s − d_eff" identity.** (γ²−γ−1)/γ + γ = (2γ+1)(γ−1)/γ, so (γ²−γ−1)/γ = −γ
    iff γ=1 or γ=−1/2. -/
theorem two_s_minus_deff (γ : ℝ) (hγ : γ ≠ 0) :
    (γ^2 - γ - 1)/γ + γ = (2*γ + 1)*(γ - 1)/γ := by
  field_simp
  ring

/-- **β(γ) = −V'(γ).** For the φ⁴-kink potential V(γ)=γ/2−γ³/6, the Wilson–Fisher
    beta function β = −V' = −(1−γ²)/2. -/
theorem beta_eq_neg_Vderiv (x : ℝ) :
    deriv (fun γ : ℝ => γ/2 - γ^3/6) x = (1 - x^2)/2 := by
  have hs : deriv (fun γ : ℝ => γ/2 - γ^3/6) x
      = deriv (fun γ : ℝ => γ/2) x - deriv (fun γ : ℝ => γ^3/6) x := by
    apply deriv_sub <;> fun_prop
  rw [hs]
  simp only [deriv_div_const, deriv_id'']
  rw [(hasDerivAt_pow 3 x).deriv]
  push_cast; ring

/-- **RG-flow trajectory.** γ(t)=tanh(t/2+c) solves the gradient flow γ'(t)=(1−γ²)/2.
    Built from tanh = sinh/cosh + the quotient rule. -/
theorem rg_flow_tanh (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.tanh (s/2 + c))
      ((1 - Real.tanh (t/2 + c)^2)/2) t := by
  have base : ∀ u : ℝ, HasDerivAt Real.tanh (1 - Real.tanh u ^ 2) u := by
    intro u
    have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
    have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u) hc
    have hfun : Real.sinh / Real.cosh = Real.tanh := by
      funext x; rw [Pi.div_apply]; exact (Real.tanh_eq_sinh_div_cosh x).symm
    rw [hfun] at h
    convert h using 1
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  have inner : HasDerivAt (fun s : ℝ => s/2 + c) (1/2) t :=
    ((hasDerivAt_id t).div_const 2).add_const c
  have hcomp := (base (t/2 + c)).comp t inner
  convert hcomp using 1
  ring

end TAF
