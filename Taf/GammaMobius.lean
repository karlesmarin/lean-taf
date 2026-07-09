/-
  Taf.GammaMobius — the Padé γ is a Möbius transform of one reduced variable.

  Central simplification (2026-07-09): the Padé attention-decay exponent
      γ_Padé(θ,T) = (2θ − T√2) / (2θ + T√2)
  collapses to a Cayley/Möbius transform of the single reduced variable
      u = T / (θ√2):        γ = (1 − u)/(1 + u).
  Crucially the √2 is load-bearing: the collapse holds *iff* s² = 2
  (with any other constant the numerator/denominator do not factor).

  Corollaries formalised here:
    * gamma_mobius   : γ_Padé = (1−u)/(1+u)                 (needs s²=2)
    * u_of_gamma     : (1−γ)/(1+γ) = u                       (pure Möbius)
    * d_horizon_eq_T : θ√2·(1−γ)/(1+γ) = T at γ=γ_Padé       (d_horizon is a TAUTOLOGY)
    * beta_in_u      : −(1−γ²)/2 = −2u/(1+u)²                (RG β-function in u)

  s is kept abstract (s>0, s²=2); instantiate s := Real.sqrt 2.

  Reference: Marin 2026, "Predicting How Transformers Attend".
  Sage cross-check: scratchpad/verify_mobius.sage (Pade≡Mobius, dif 0.0).
-/

import Mathlib

namespace TAF.GammaScale

/-- The Padé attention-decay exponent. `s` stands for √2. -/
noncomputable def gammaPade (s θ T : ℝ) : ℝ := (2 * θ - T * s) / (2 * θ + T * s)

/-- Reduced distance variable `u = T / (θ√2)`. -/
noncomputable def uvar (s θ T : ℝ) : ℝ := T / (θ * s)

/-- **Möbius collapse.** With `u = T/(θ√2)`, the Padé γ equals `(1−u)/(1+u)`.
    The `s² = 2` hypothesis is essential (the constant √2 is load-bearing). -/
theorem gamma_mobius {s θ T : ℝ} (hs2 : s ^ 2 = 2) (hs : 0 < s)
    (hθ : 0 < θ) (hT : 0 < T) :
    gammaPade s θ T = (1 - uvar s θ T) / (1 + uvar s θ T) := by
  unfold gammaPade uvar
  have hsne : s ≠ 0 := ne_of_gt hs
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hpos1 : (0 : ℝ) < 2 * θ + T * s := by positivity
  have hpos3 : (0 : ℝ) < θ * s + T := by positivity
  -- cross-multiplied core identity (this is where s²=2 is used)
  have key : (2 * θ - T * s) * (θ * s + T) = (θ * s - T) * (2 * θ + T * s) := by
    linear_combination (-2 * θ * T) * hs2
  -- LHS = (θs−T)/(θs+T)
  have e1 : (2 * θ - T * s) / (2 * θ + T * s) = (θ * s - T) / (θ * s + T) := by
    rw [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos3)]
    linear_combination key
  -- RHS Möbius form = (θs−T)/(θs+T)  (pure algebra, no s²=2)
  have e2 : (1 - T / (θ * s)) / (1 + T / (θ * s)) = (θ * s - T) / (θ * s + T) := by
    rw [div_eq_div_iff (by positivity) (ne_of_gt hpos3)]
    field_simp
  rw [e1, e2]

/-- **Inverse Möbius** (pure algebra): `(1−γ)/(1+γ) = u` when `γ = (1−u)/(1+u)`. -/
theorem u_of_gamma {u : ℝ} (hu : (1 : ℝ) + u ≠ 0) :
    (1 - (1 - u) / (1 + u)) / (1 + (1 - u) / (1 + u)) = u := by
  have hden : (1 : ℝ) + (1 - u) / (1 + u) ≠ 0 := by
    have h : (1 : ℝ) + (1 - u) / (1 + u) = 2 / (1 + u) := by field_simp; ring
    rw [h]; exact div_ne_zero (by norm_num) hu
  rw [div_eq_iff hden]
  field_simp
  ring

/-- **d_horizon is a tautology.** The "information horizon"
    `d_horizon = θ√2·(1−γ)/(1+γ)` evaluated at `γ = γ_Padé` equals `T` exactly:
    it carries no information beyond the training context length. -/
theorem d_horizon_eq_T {s θ T : ℝ} (hs2 : s ^ 2 = 2) (hs : 0 < s)
    (hθ : 0 < θ) (hT : 0 < T) :
    θ * s * ((1 - gammaPade s θ T) / (1 + gammaPade s θ T)) = T := by
  rw [gamma_mobius hs2 hs hθ hT]
  have hsne : s ≠ 0 := ne_of_gt hs
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hu : (1 : ℝ) + uvar s θ T ≠ 0 := by unfold uvar; positivity
  rw [u_of_gamma hu]
  unfold uvar
  field_simp

/-- **RG β-function in the reduced variable.** `−(1−γ²)/2 = −2u/(1+u)²`
    for `γ = (1−u)/(1+u)`. Pure Möbius algebra. -/
theorem beta_in_u {u : ℝ} (hu : (1 : ℝ) + u ≠ 0) :
    -(1 - ((1 - u) / (1 + u)) ^ 2) / 2 = -2 * u / (1 + u) ^ 2 := by
  field_simp
  ring

/-! ### Instantiation at s = √2 (the actual constant in the paper). -/

/-- √2 satisfies the two hypotheses. -/
theorem sqrt_two_props : (Real.sqrt 2) ^ 2 = 2 ∧ 0 < Real.sqrt 2 :=
  ⟨Real.sq_sqrt (by norm_num), Real.sqrt_pos.mpr (by norm_num)⟩

/-- The Möbius collapse for the actual √2. -/
theorem gamma_mobius_sqrt2 {θ T : ℝ} (hθ : 0 < θ) (hT : 0 < T) :
    gammaPade (Real.sqrt 2) θ T
      = (1 - uvar (Real.sqrt 2) θ T) / (1 + uvar (Real.sqrt 2) θ T) :=
  gamma_mobius sqrt_two_props.1 sqrt_two_props.2 hθ hT

#check @gamma_mobius        -- γ_Padé = (1−u)/(1+u)
#check @u_of_gamma          -- (1−γ)/(1+γ) = u
#check @d_horizon_eq_T      -- θ√2·(1−γ)/(1+γ) = T   (tautology)
#check @beta_in_u           -- −(1−γ²)/2 = −2u/(1+u)²

end TAF.GammaScale
