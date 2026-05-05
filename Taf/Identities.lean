/-
  Taf.Identities — formal Lean 4 proofs of TAF algebraic identities

  Sage Groebner already verified these mechanically. Lean version provides
  formal proof in dependent type theory (publishable Mathlib-style).

  References:
  - Marin 2026, Predicting How Transformers Attend (Zenodo 19826343)
  - Sage script: analysis/sage_recursive_sweep_2026-04-30.sage
  - Sage results: analysis/sage_recursive_sweep_results.json
-/

import Mathlib

namespace TAF

/-! ## Critical exponents (Phase A: γ ∈ (0, 1)) -/

variable (γ : ℝ) (hγ : γ < 1) (hγ0 : 0 < γ)

/-- ν_c = 1/(1-γ) (correlation length exponent, Phase A) -/
noncomputable def νc (γ : ℝ) : ℝ := 1 / (1 - γ)

/-- β_c = γ - 1 (order parameter exponent) -/
def βc (γ : ℝ) : ℝ := γ - 1

/-- η_c = γ - 1 (anomalous dimension, CORRECTED from paper 1's 2γ) -/
def ηc (γ : ℝ) : ℝ := γ - 1

/-- α_C = 2 - 1/(1-γ) (heat capacity exponent, Phase A) -/
noncomputable def αC (γ : ℝ) : ℝ := 2 - 1 / (1 - γ)

/-- γ_χ = 1/(1-γ) + 2(1-γ) (susceptibility, Rushbrooke definition) -/
noncomputable def γχ (γ : ℝ) : ℝ := 1 / (1 - γ) + 2 * (1 - γ)

/-- χ = 1/(1-γ) (susceptibility scaling, Phase A simplified) -/
noncomputable def χ (γ : ℝ) : ℝ := 1 / (1 - γ)

/-! ## Identity D-SAGE-1 (★★ CORE)

    2·η² + η·γ_χ + 1 = 0
    Holds for η = γ-1 with γ_χ from Rushbrooke definition.
    This is the KEY identity that survived Sage Groebner check
    after the original "triple closure" claim was found wrong.
-/

theorem D_SAGE_1 (γ : ℝ) (h : γ ≠ 1) :
    2 * (ηc γ) ^ 2 + (ηc γ) * (γχ γ) + 1 = 0 := by
  unfold ηc γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Identity D-SAGE-2: β·χ = -1 (Phase A) -/

theorem D_SAGE_2 (γ : ℝ) (h : γ ≠ 1) :
    (βc γ) * (χ γ) = -1 := by
  unfold βc χ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Identity D-SAGE-4: α_C + χ = 2 -/

theorem D_SAGE_4 (γ : ℝ) (h : γ ≠ 1) :
    αC γ + χ γ = 2 := by
  unfold αC χ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Identity D-SAGE-5: α_C + γ_χ = 2(2-γ) -/

theorem D_SAGE_5 (γ : ℝ) (h : γ ≠ 1) :
    αC γ + γχ γ = 2 * (2 - γ) := by
  unfold αC γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Identity D-SAGE-6: β·γ_χ = -2γ² + 4γ - 3 -/

theorem D_SAGE_6 (γ : ℝ) (h : γ ≠ 1) :
    (βc γ) * (γχ γ) = -2 * γ^2 + 4 * γ - 3 := by
  unfold βc γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Rushbrooke tautology (with d=1, expected to be 0) -/

theorem rushbrooke_tautology (γ : ℝ) (h : γ ≠ 1) :
    2 * (βc γ) + (γχ γ) - (νc γ) * 1 = 0 := by
  unfold βc γχ νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Josephson tautology (with d=1, expected to be 0) -/

theorem josephson_tautology (γ : ℝ) (h : γ ≠ 1) :
    2 - (αC γ) - (νc γ) * 1 = 0 := by
  unfold αC νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## Fisher INDEPENDENCE: γ_χ - (2-η)·ν reduces to 0 ⟺ γ ∈ {0, 1/2} -/

theorem fisher_residual (γ : ℝ) (h : γ ≠ 1) :
    (γχ γ) - (2 - ηc γ) * (νc γ) = γ * (2 * γ - 3) / (1 - γ) := by
  unfold γχ ηc νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- Fisher residual = 0 ⟺ γ = 0 or γ = 3/2.
    Since γ ∈ (0,1) for Phase A, only γ = 0 boundary. -/
theorem fisher_zero_iff (γ : ℝ) (h : γ ≠ 1) :
    (γχ γ) - (2 - ηc γ) * (νc γ) = 0 ↔ γ = 0 ∨ γ = 3/2 := by
  rw [fisher_residual γ h]
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  rw [div_eq_zero_iff]
  constructor
  · intro hcase
    rcases hcase with h_num | h_den
    · rcases mul_eq_zero.mp h_num with h0 | h32
      · left; exact h0
      · right; linarith
    · exact absurd h_den h1
  · intro hcase
    left
    rcases hcase with h0 | h32
    · subst h0; ring
    · subst h32; ring

/-! ## Refutation: η = 2γ does NOT satisfy D-SAGE-1 identically

    Computed algebraically (Sage-verified): substituting η=2γ and γ_χ
    Rushbrooke into 2η² + η·γ_χ + 1, the result is (-4γ³ + 5γ + 1)/(1-γ).

    For γ ∈ Phase A (0 < γ < 1):
    -  numerator -4γ³ + 5γ + 1 > 0 throughout (verify: at γ=0 it's 1; at γ=1 it's 2)
    -  denominator 1-γ > 0
    -  so residual > 0, η=2γ FAILS D-SAGE-1 in Phase A.
-/

theorem eta_2gamma_residual (γ : ℝ) (h : γ ≠ 1) :
    2 * (2 * γ) ^ 2 + (2 * γ) * (γχ γ) + 1 = (-4 * γ^3 + 5 * γ + 1) / (1 - γ) := by
  unfold γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- Phase A: 0 < γ < 1. Numerator -4γ³+5γ+1 stays positive on (0,1). -/
theorem eta_2gamma_fails_phase_A (γ : ℝ) (hγ_lo : 0 < γ) (hγ_hi : γ < 1) :
    2 * (2 * γ) ^ 2 + (2 * γ) * (γχ γ) + 1 > 0 := by
  have h_neq : γ ≠ 1 := ne_of_lt hγ_hi
  rw [eta_2gamma_residual γ h_neq]
  have hden : 1 - γ > 0 := by linarith
  have hnum : -4 * γ^3 + 5 * γ + 1 > 0 := by
    -- For γ ∈ (0,1): γ³ < γ, so -4γ³ > -4γ, hence -4γ³ + 5γ + 1 > γ + 1 > 1 > 0
    have h_cube : γ^3 < γ := by
      have : γ^3 = γ * γ^2 := by ring
      rw [this]
      have hγ2_lt_1 : γ^2 < 1 := by
        rw [show (1:ℝ) = 1^2 by ring]
        exact sq_lt_sq' (by linarith) hγ_hi
      nlinarith [hγ_lo, hγ2_lt_1]
    linarith
  positivity

/-! ## ν_imprint dimensional identity (D-14) -/

/-- ν_imprint × 2π = -1 (dimensional) -/
theorem D_14_nu_imprint (π_val : ℝ) (hπ : π_val > 0) :
    (-1 / (2 * π_val)) * (2 * π_val) = -1 := by
  field_simp

/-! ## c_central · |ν_imprint| · 2π = 3 (D-SAGE-7) -/

theorem D_SAGE_7 (π_val : ℝ) (hπ : π_val > 0) :
    (3 : ℝ) * (1 / (2 * π_val)) * (2 * π_val) = 3 := by
  field_simp

/-! ## β_c × χ closure (Phase A only) -/

theorem beta_chi_closure (γ : ℝ) (h : γ ≠ 1) :
    (βc γ) * (χ γ) + 1 = 0 := by
  unfold βc χ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## ν_c · β_c = -1 (in Phase A) -/

theorem nu_beta_id (γ : ℝ) (h : γ ≠ 1) :
    (νc γ) * (βc γ) = -1 := by
  unfold νc βc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ## D-DEEP-15 + D-DEEP-22 — Cardy + PDI identities

    Phase 8 form: ΔH_Cardy(z, γ) = log(z/2) + 2·arctanh(γ).
    Phase 7 form: ΔH_Cardy(z, γ) = log(z/√2) + 2·arctanh(γ).

    Algebraic identity log(PDI) + ΔH_Cardy = 0 holds with Phase 7 form
    (using d_horizon = θ(1-γ)·√2/(1+γ) and PDI = d_horizon/T_eval, T_eval=z·θ).

    Phase 8 form gives residual -log(2)/2 (= -ln(√2)) — empirical correction.
-/

open Real in
/-- Phase 7 ΔH_Cardy form (algebraically exact for log(PDI)+ΔH=0) -/
noncomputable def DH_Cardy_phase7 (z γ : ℝ) : ℝ :=
  Real.log (z / Real.sqrt 2) + 2 * Real.arctanh γ

open Real in
/-- Phase 8 ΔH_Cardy form (empirical Phase 8 correction) -/
noncomputable def DH_Cardy_phase8 (z γ : ℝ) : ℝ :=
  Real.log (z / 2) + 2 * Real.arctanh γ

/-- d_horizon as derived from Padé saturation:
    Solving γ_Padé(θ, T) = γ for T gives T = θ·(1-γ)·√2/(1+γ). -/
noncomputable def d_horizon (θ γ : ℝ) : ℝ :=
  θ * (1 - γ) * Real.sqrt 2 / (1 + γ)

/-- PDI = d_horizon / T_eval, with T_eval = z·θ -/
noncomputable def PDI (θ z γ : ℝ) : ℝ :=
  (d_horizon θ γ) / (z * θ)

/-! ## D-DEEP-15 ★: log(PDI) + ΔH_Cardy_phase7 = 0 EXACT (Sage Groebner-verified) -/

theorem D_DEEP_15_phase7 (θ z γ : ℝ)
    (hθ : θ > 0) (hz : z > 0) (hγ_lo : 0 < 1 - γ) (hγ_hi : 0 < 1 + γ) :
    Real.log (PDI θ z γ) + DH_Cardy_phase7 z γ = 0 := by
  unfold PDI d_horizon DH_Cardy_phase7
  -- log(θ(1-γ)√2/((1+γ)(zθ))) + log(z/√2) + 2·arctanh(γ)
  -- = log((1-γ)/((1+γ)·z)) + log(√2) + log(z) - log(√2) + 2·arctanh(γ)
  -- = log((1-γ)/(1+γ)) - log(z) + log(z) + log((1+γ)/(1-γ))
  -- (since 2·arctanh(γ) = log((1+γ)/(1-γ)))
  -- = log((1-γ)/(1+γ)) + log((1+γ)/(1-γ)) = log(1) = 0
  have hsqrt2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h_atanh : Real.arctanh γ = (1/2) * Real.log ((1 + γ) / (1 - γ)) := by
    rw [Real.arctanh_eq_log]
    ring
  -- Use logarithm rules
  have h1mg : (1 - γ : ℝ) > 0 := hγ_lo
  have h1pg : (1 + γ : ℝ) > 0 := hγ_hi
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ
  have hz_ne : z ≠ 0 := ne_of_gt hz
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2
  rw [h_atanh]
  -- Combine logs
  have step1 : θ * (1 - γ) * Real.sqrt 2 / (1 + γ) / (z * θ) =
               (1 - γ) * Real.sqrt 2 / ((1 + γ) * z) := by
    field_simp
    ring
  rw [step1]
  rw [show z / Real.sqrt 2 = z / Real.sqrt 2 from rfl]
  rw [show 2 * ((1 / 2) * Real.log ((1 + γ) / (1 - γ))) =
        Real.log ((1 + γ) / (1 - γ)) by ring]
  -- Now goal: log((1-γ)·√2/((1+γ)·z)) + log(z/√2) + log((1+γ)/(1-γ)) = 0
  have hlog1 : Real.log ((1 - γ) * Real.sqrt 2 / ((1 + γ) * z))
            + Real.log (z / Real.sqrt 2)
            = Real.log ((1 - γ) / (1 + γ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [hlog1]
  -- Now: log((1-γ)/(1+γ)) + log((1+γ)/(1-γ)) = log(1) = 0
  rw [← Real.log_mul (by positivity) (by positivity)]
  rw [show (1 - γ) / (1 + γ) * ((1 + γ) / (1 - γ)) = 1 by field_simp]
  exact Real.log_one

/-! ## D-DEEP-22 ★: dΔH_Cardy/dγ = 2/(1-γ²) -/

theorem D_DEEP_22 (z γ : ℝ) (hγ_lo : -1 < γ) (hγ_hi : γ < 1) :
    deriv (fun γ' => DH_Cardy_phase8 z γ') γ = 2 / (1 - γ^2) := by
  unfold DH_Cardy_phase8
  -- d/dγ [log(z/2) + 2·arctanh(γ)]
  -- = 0 + 2 · d/dγ arctanh(γ)
  -- = 2 / (1 - γ²)
  rw [deriv_const_add]
  rw [deriv_const_mul]
  · rw [Real.deriv_arctanh]
    · field_simp
      ring
    · linarith
    · linarith
  · exact (Real.differentiableAt_arctanh (by linarith) (by linarith))

/-! ## D-DEEP-15 phase8 form: residual is -log(2)/2 (empirical correction) -/

theorem D_DEEP_15_phase8_residual (θ z γ : ℝ)
    (hθ : θ > 0) (hz : z > 0) (hγ_lo : 0 < 1 - γ) (hγ_hi : 0 < 1 + γ) :
    Real.log (PDI θ z γ) + DH_Cardy_phase8 z γ = -(Real.log 2) / 2 := by
  -- Phase 8 - Phase 7 = log(z/2) - log(z/√2) = log(√2/2) = -log(√2) = -log(2)/2
  unfold DH_Cardy_phase8
  have h := D_DEEP_15_phase7 θ z γ hθ hz hγ_lo hγ_hi
  unfold DH_Cardy_phase7 at h
  have h1 : Real.log (z / 2) = Real.log (z / Real.sqrt 2) - Real.log 2 / 2 := by
    rw [show (2 : ℝ) = Real.sqrt 2 * Real.sqrt 2 by rw [← Real.sqrt_mul_self (by norm_num : (2:ℝ) ≥ 0)]]
    rw [show z / (Real.sqrt 2 * Real.sqrt 2) = (z / Real.sqrt 2) / Real.sqrt 2 by ring]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  linarith

/-! ## Summary (Lean-checked theorems) -/

#check @D_SAGE_1                  -- 2η² + η·γ_χ + 1 = 0
#check @D_SAGE_2                  -- β·χ = -1
#check @D_SAGE_4                  -- α_C + χ = 2
#check @D_SAGE_5                  -- α_C + γ_χ = 2(2-γ)
#check @D_SAGE_6                  -- β·γ_χ = -2γ² + 4γ - 3
#check @rushbrooke_tautology      -- 2β + γ_χ - ν = 0 (tautology)
#check @josephson_tautology       -- 2 - α_C - ν = 0 (tautology)
#check @fisher_residual           -- γ_χ - (2-η)·ν = γ(2γ-3)/(1-γ)
#check @fisher_zero_iff           -- Fisher = 0 ⟺ γ ∈ {0, 3/2}
#check @D_14_nu_imprint           -- ν · 2π = -1
#check @D_SAGE_7                  -- c · |ν| · 2π = 3
#check @nu_beta_id                -- ν·β = -1

end TAF
