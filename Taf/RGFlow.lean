/-
  Taf.RGFlow — Lean formalization of EXACT-labeled identities from
  "Predicting How Transformers Attend" (Marín 2026) covering the
  Renormalisation-Group flow, Padé approximant, Cayley fixed point,
  and χ susceptibility material.

  Sources:
    - FORMULAS_TOOLKIT.md (§19, §20, §23, §26, §31)
    - FORMULA_TABLE.md (line 13 G-15, line 90-92, line 113)
    - Predicting How Transformers Attend.tex (§5.4)

  Companion modules:
    Taf.Identities                — D-SAGE-1..7, Cardy/PDI
    Taf.AmGmPade                  — AM-GM bound + Padé saturation difference
    Taf.CvHagedornCorrection      — C_V coefficient erratum verification
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace TAF.RGFlow

-- =============================================================================
-- §31 / G-15 — Padé[2,2] − Padé[1,1] = 2z³ / ((z+2)·(z²+6z+12))
-- Source: FORMULA_TABLE.md line 13, label "★ EXACT".
-- =============================================================================

theorem pade_22_minus_pade_11
    (z : ℝ) (h1 : z + 2 ≠ 0) (h2 : z^2 + 6*z + 12 ≠ 0) :
    (12 - 6*z + z^2) / (12 + 6*z + z^2) - (2 - z) / (2 + z)
      = (2 * z^3) / ((z + 2) * (z^2 + 6*z + 12)) := by
  have h2' : (12 + 6*z + z^2) ≠ 0 := by
    have : (12 + 6*z + z^2) = (z^2 + 6*z + 12) := by ring
    rw [this]; exact h2
  have h1' : (2 + z) ≠ 0 := by
    have : (2 + z) = (z + 2) := by ring
    rw [this]; exact h1
  rw [div_sub_div _ _ h2' h1', div_eq_div_iff (mul_ne_zero h2' h1')
        (mul_ne_zero h1 h2)]
  ring

-- =============================================================================
-- Padé[1,1] one-minus form: 1 − (2-z)/(2+z) = 2z/(2+z)
-- Used in θ_eff_Padé derivation (FORMULAS_TOOLKIT.md §4.4).
-- =============================================================================

theorem one_minus_pade_11 (z : ℝ) (h : 2 + z ≠ 0) :
    1 - (2 - z) / (2 + z) = (2 * z) / (2 + z) := by
  field_simp
  ring

-- =============================================================================
-- §4.4 / θ_eff_Padé derivation: T·√2 / (1 − γ_Padé) = θ + T/√2
-- where γ_Padé = (2-z)/(2+z) and z = T·√2/θ.
-- Source: FORMULAS_TOOLKIT.md line 572.
-- =============================================================================

theorem theta_eff_pade
    (θ T : ℝ) (hθ : θ ≠ 0)
    (hT : T ≠ 0)
    (hsum : 2*θ + T * Real.sqrt 2 ≠ 0) :
    T * Real.sqrt 2 / (1 - (2 - T * Real.sqrt 2 / θ) / (2 + T * Real.sqrt 2 / θ))
      = θ + T / Real.sqrt 2 := by
  have hsqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  -- 2 + T·√2/θ ≠ 0:  multiply by θ ≠ 0 → 2θ + T·√2 ≠ 0.
  have h2plus : 2 + T * Real.sqrt 2 / θ ≠ 0 := by
    intro hbad
    apply hsum
    have : θ * (2 + T * Real.sqrt 2 / θ) = θ * 0 := by rw [hbad]
    field_simp at this
    linarith
  field_simp
  ring_nf
  -- Goal contains √2^3.  Rewrite as √2 · √2^2 = √2 · 2.
  have h_cubed : (Real.sqrt 2) ^ 3 = Real.sqrt 2 * 2 := by
    rw [show (3:ℕ) = 1 + 2 from by norm_num, pow_add, pow_one, hsqrt2_sq]
  rw [h_cubed]
  ring

-- =============================================================================
-- §23 — Logistic ODE algebraic step
-- x = (1-γ)/2  ⟹  x(1-x) = (1-γ²)/4
-- Source: FORMULA_TABLE.md line 90, label "✅ ALGEBRAIC EXACT".
-- =============================================================================

theorem logistic_to_beta_algebraic (γ : ℝ) :
    let x := (1 - γ) / 2
    x * (1 - x) = (1 - γ^2) / 4 := by
  simp only
  ring

-- =============================================================================
-- §23 — V(γ) doublewell potential  (FINDING: discrepancy with β)
-- Table FORMULA_TABLE.md line 91 says: V(γ) = γ - γ³/3, β = -V'(γ).
-- Toolkit FORMULAS_TOOLKIT.md §19 line 191: β(γ) = -(1-γ²)/2.
--
-- For V(γ) = γ - γ³/3: V'(γ) = 1 - γ², so -V'(γ) = -(1-γ²) = γ² - 1.
-- This DOES NOT EQUAL the RG paper's β = -(1-γ²)/2.  They differ by
-- a factor of 2.  Lean confirms both facts:
--   (a) V'(γ) = 1 - γ² for the stated V.
--   (b) -V'(γ) ≠ β(γ) generically (only at γ = ±1).
-- Likely cause: V(γ) in the table is missing a 1/2 prefactor.
-- The correct integrated form for β = -(1-γ²)/2 would be V(γ) = γ/2 - γ³/6.
-- =============================================================================

theorem V_derivative (γ : ℝ) :
    deriv (fun x : ℝ => x - x^3 / 3) γ = 1 - γ^2 := by
  have h_id : HasDerivAt (fun x : ℝ => x) 1 γ := hasDerivAt_id γ
  have h_pow : HasDerivAt (fun x : ℝ => x^3) (3 * γ^2) γ := by
    simpa using hasDerivAt_pow 3 γ
  have h_div : HasDerivAt (fun x : ℝ => x^3 / 3) (γ^2) γ := by
    have := h_pow.div_const 3
    simpa using this
  have h := h_id.sub h_div
  simpa using h.deriv

theorem V_derivative_ne_RG_beta (γ : ℝ) (hne1 : γ ≠ 1) (hne2 : γ ≠ -1) :
    -(deriv (fun x : ℝ => x - x^3 / 3) γ) ≠ -(1 - γ^2) / 2 := by
  rw [V_derivative]
  intro h
  -- -(1-γ²) = -(1-γ²)/2  ⟹  (1-γ²) = 0  ⟹  γ = ±1
  have : 1 - γ^2 = 0 := by linarith
  have factored : (1 - γ) * (1 + γ) = 0 := by nlinarith
  rcases mul_eq_zero.mp factored with h1 | h2
  · exact hne1 (by linarith)
  · exact hne2 (by linarith)

-- =============================================================================
-- §20 — Cayley fixed-point equation
-- γ(z) = -(z-2)/(z+2) = z  ⟺  z² + 3z − 2 = 0
-- Source: FORMULAS_TOOLKIT.md line 173.
-- =============================================================================

theorem cayley_fixed_point_iff (z : ℝ) (h : z + 2 ≠ 0) :
    -(z - 2) / (z + 2) = z ↔ z^2 + 3*z - 2 = 0 := by
  rw [div_eq_iff h]
  constructor
  · intro hz; nlinarith
  · intro hz; nlinarith

-- =============================================================================
-- §20 — Cayley FP root: z* = (√17 − 3)/2 satisfies z² + 3z − 2 = 0
-- Source: FORMULAS_TOOLKIT.md line 174.
-- =============================================================================

theorem cayley_root :
    let z := (Real.sqrt 17 - 3) / 2
    z^2 + 3*z - 2 = 0 := by
  have h17 : (Real.sqrt 17)^2 = 17 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  simp only
  have expand : ((Real.sqrt 17 - 3) / 2)^2 = (17 - 6 * Real.sqrt 17 + 9) / 4 := by
    rw [div_pow]
    have : (Real.sqrt 17 - 3)^2 = (Real.sqrt 17)^2 - 6 * Real.sqrt 17 + 9 := by
      ring
    rw [this, h17]
    norm_num
  rw [expand]
  ring

-- =============================================================================
-- §26 — χ polynomial: χ = (5 + √17)/4 satisfies 2χ² − 5χ + 1 = 0
-- Source: FORMULA_TABLE.md line 92, FORMULAS_TOOLKIT.md line 89-91.
-- =============================================================================

theorem chi_root :
    let χ := (5 + Real.sqrt 17) / 4
    2 * χ^2 - 5 * χ + 1 = 0 := by
  have h17 : (Real.sqrt 17)^2 = 17 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  simp only
  have expand : ((5 + Real.sqrt 17) / 4)^2 = (25 + 10 * Real.sqrt 17 + 17) / 16 := by
    rw [div_pow]
    have : (5 + Real.sqrt 17)^2 = 25 + 10 * Real.sqrt 17 + (Real.sqrt 17)^2 := by ring
    rw [this, h17]
    norm_num
  rw [expand]
  ring

-- =============================================================================
-- §3.1 — RoPE β coefficient: σ²(Uniform on [-1, 0]) = 1/12, so σ = 1/√12
-- Source: FORMULAS_TOOLKIT.md line 411 "β = 1/√12 = √3/6".
-- We verify the algebraic equivalence 1/√12 = √3/6.
-- =============================================================================

theorem rope_beta_form : Real.sqrt 3 / 6 = 1 / Real.sqrt 12 := by
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 from by norm_num,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 from by
          rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
  rw [h12]
  have h3_pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3_sq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  field_simp
  nlinarith [h3_sq, h3_pos]

-- =============================================================================
-- §4.1 — Padé form substitution: (2 - z)/(2 + z) = (2θ - T·√2)/(2θ + T·√2)
-- when z = T·√2/θ.
-- Source: FORMULAS_TOOLKIT.md line 456 "γ_Padé canonical form in θ,T".
-- =============================================================================

theorem pade_z_substitution
    (θ T : ℝ) (hθ : θ ≠ 0)
    (hsum_θ : 2*θ + T * Real.sqrt 2 ≠ 0) :
    (2 - T * Real.sqrt 2 / θ) / (2 + T * Real.sqrt 2 / θ)
      = (2*θ - T * Real.sqrt 2) / (2*θ + T * Real.sqrt 2) := by
  field_simp

-- =============================================================================
-- §15 — CFT2 critical exponent identity: ν · (1 - γ) = 1  for ν = 1/(1-γ).
-- Source: FORMULAS_TOOLKIT.md line 265.
-- Trivial inversion identity — confirms ν, β, η definitions are self-consistent.
-- =============================================================================

theorem cft_nu_identity (γ : ℝ) (h : 1 - γ ≠ 0) :
    (1 / (1 - γ)) * (1 - γ) = 1 := by
  field_simp

-- =============================================================================
-- §20 — Cayley FP Floquet multiplier:
--   μ = γ'(z*) where γ(z) = -(z-2)/(z+2), z* = (√17 - 3)/2.
--   Table (line 177) claims μ = -4(√17+1)/(5√17+13).
--   We verify the equivalence with the direct computation form (√17 - 9)/8.
-- =============================================================================

-- =============================================================================
-- §23 — CORRECTED V(γ) that DOES integrate to β = -(1-γ²)/2.
-- We propose V_correct(γ) = γ/2 - γ³/6 (half of the table's V).
-- Lean verifies V'_correct(γ) = (1 - γ²)/2, so -V'_correct = -(1-γ²)/2 = β. ✓
-- This is the consistent integrated form for the RG-paper β function.
-- =============================================================================

theorem V_correct_derivative (γ : ℝ) :
    deriv (fun x : ℝ => x / 2 - x^3 / 6) γ = (1 - γ^2) / 2 := by
  have h_id : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) γ := by
    have := (hasDerivAt_id γ).div_const 2
    simpa using this
  have h_pow : HasDerivAt (fun x : ℝ => x^3) (3 * γ^2) γ := by
    simpa using hasDerivAt_pow 3 γ
  have h_div : HasDerivAt (fun x : ℝ => x^3 / 6) (γ^2 / 2) γ := by
    have := h_pow.div_const 6
    have h_eq : (3 * γ^2) / 6 = γ^2 / 2 := by ring
    rw [h_eq] at this
    exact this
  have h := h_id.sub h_div
  have h_eq : (1 / 2 : ℝ) - γ^2 / 2 = (1 - γ^2) / 2 := by ring
  rw [← h_eq]
  exact h.deriv

-- Sanity check: -V'_correct(γ) IS the RG paper's β.
theorem V_correct_matches_RG_beta (γ : ℝ) :
    -(deriv (fun x : ℝ => x / 2 - x^3 / 6) γ) = -(1 - γ^2) / 2 := by
  rw [V_correct_derivative]; ring

-- =============================================================================

-- =============================================================================
-- Cayley map boundary values: γ(0) = 1, γ(2) = 0.
-- Source: implicit in §20 (γ=1 at z=0 is Hagedorn; γ=0 at z=2 is "MaxEnt zero").
-- =============================================================================

theorem cayley_at_zero : -((0:ℝ) - 2) / (0 + 2) = 1 := by norm_num

theorem cayley_at_two : -((2:ℝ) - 2) / (2 + 2) = 0 := by norm_num

-- =============================================================================
-- z* = (√17 − 3)/2 is positive — confirms the "physical" root choice.
-- Source: implicit in §20 line 174.
-- =============================================================================

theorem cayley_root_positive : (0:ℝ) < (Real.sqrt 17 - 3) / 2 := by
  have h_pos : Real.sqrt 17 > 3 := by
    have : Real.sqrt 9 < Real.sqrt 17 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 9 = 3 from by
          rw [show (9:ℝ) = 3^2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at this
  linarith

-- =============================================================================
-- Floquet multiplier stability: |μ| < 1, where μ = (√17 − 9)/8.
-- Source: FORMULAS_TOOLKIT.md line 178 "|μ| < 1 ⟹ STABLE attractor".
-- =============================================================================

theorem cayley_floquet_stable : |(Real.sqrt 17 - 9) / 8| < 1 := by
  have h17_pos : (0:ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have h17_gt_1 : (1:ℝ) < Real.sqrt 17 := by
    have : Real.sqrt 1 < Real.sqrt 17 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at this
  have h17_lt_5 : Real.sqrt 17 < 5 := by
    have : Real.sqrt 17 < Real.sqrt 25 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 25 = 5 from by
          rw [show (25:ℝ) = 5^2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)] at this
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
  rw [div_lt_one (by norm_num : (0:ℝ) < 8)]
  -- √17 < 5 < 9, so √17 - 9 is negative; |√17 - 9| = 9 - √17 < 8.
  rw [abs_of_neg (by linarith : Real.sqrt 17 - 9 < 0)]
  linarith

-- =============================================================================

theorem cayley_floquet_form_equivalence :
    -4 * (Real.sqrt 17 + 1) / (5 * Real.sqrt 17 + 13)
      = (Real.sqrt 17 - 9) / 8 := by
  have h17 : (Real.sqrt 17)^2 = 17 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  have h17_pos : (0:ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have h17_gt_4 : (4:ℝ) < Real.sqrt 17 := by
    have : Real.sqrt 16 < Real.sqrt 17 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 16 = 4 from by
          rw [show (16:ℝ) = 4^2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at this
  have hdenom : 5 * Real.sqrt 17 + 13 ≠ 0 := by
    intro h
    have : (0:ℝ) < 5 * Real.sqrt 17 + 13 := by
      have : (0:ℝ) < 5 * Real.sqrt 17 := by positivity
      linarith
    linarith
  rw [div_eq_div_iff hdenom (by norm_num : (8:ℝ) ≠ 0)]
  -- Cross-multiply and use √17² = 17.
  nlinarith [h17, h17_pos, sq_nonneg (Real.sqrt 17)]

-- =============================================================================
-- §19 vs §23 trajectory sign issue.
-- §19 trajectory: γ(t) = tanh(t/2 + arctanh γ₀)   ⟹   dγ/dt = +(1-γ²)/2
-- §23 trajectory: γ(l) = -tanh((l + C₀)/2)         ⟹   dγ/dl = -(1-γ²)/2 = β
-- These satisfy ODEs of OPPOSITE sign. They cannot both be the
-- evolution under the stated β = -(1-γ²)/2 unless t and l are
-- opposite-direction flow parameters (i.e. t = -l).
--
-- We capture this algebraically: if a function f satisfies f' = (1-f²)/2,
-- then -f satisfies (-f)' = -(1-f²)/2 = -(1-(-f)²)/2 (using (-f)² = f²).
-- That is: negating the trajectory inverts the sign of the velocity.
-- =============================================================================

theorem trajectory_sign_inversion (γ : ℝ) :
    -((1 - γ^2) / 2) = -(1 - (-γ)^2) / 2 := by
  ring

-- More directly: the §23 form `γ(l) = -tanh((l+C)/2)` and the §19 form
-- `γ(t) = tanh(t/2 + arctanh γ₀)` differ by a sign on the FUNCTION (the
-- leading minus in §23) AND a sign on the FLOW PARAMETER (l vs t). The
-- two sign flips compose to give two trajectories that LOOK different
-- but, under the substitution t = -l + 2·arctanh(γ₀) - C₀, encode the
-- same flow. The notation should be unified to avoid ambiguity.

end TAF.RGFlow
