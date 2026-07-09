# lean-taf

Lean 4 + Mathlib formalization of the TAF (Triangulum Attention Framework) algebraic identities used in [`predicting-how-transformers-attend`](https://github.com/karlesmarin/predicting-how-transformers-attend).

**Status (2026-07-09):** 83 theorems machine-verified, 0 `sorry`s, 1 substantive finding (V/β factor-2 inconsistency in the paper's formula tables, formally proved in `V_derivative_ne_RG_beta`). Latest additions: `GammaMobius.lean` (Padé γ as a Möbius transform of one reduced variable — built green, 8371 jobs, 2026-07-09), `ScalingLawIdentities.lean` (9 scaling-law identities), `SmeftTrilinearAudit.lean` (31 theorems, paper-2 SMEFT trilinear couplings).

- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`
- Mathlib: pinned via `lake-manifest.json`
- Build: 1973 jobs, ~5 s after Mathlib cache fetch

## Re-verify locally

```bash
git clone --depth=1 https://github.com/karlesmarin/lean-taf
cd lean-taf
elan toolchain install $(cat lean-toolchain)   # one-time
lake exe cache get                             # fetch Mathlib oleans
lake build                                     # build whole library
```

To check a single file:

```bash
lake env lean Taf/Identities.lean
lake env lean Taf/RGFlow.lean
lake env lean Taf/AmGmPade.lean
lake env lean Taf/ErratumCV.lean
lake env lean Taf/CvHagedornCorrection.lean
lake env lean Taf/GammaMobius.lean
lake env lean Taf/ScalingLawIdentities.lean
lake env lean Taf/SmeftTrilinearAudit.lean
```

Lean follows the "no news is good news" convention: a successful run prints nothing. Any `sorry`, axiom, or typecheck error surfaces immediately.

## Theorem groups (83 total)

| Group | Count | Source files | What it proves |
|-------|-------|--------------|----------------|
| **γ Möbius collapse** | 6 | `GammaMobius.lean` | γ_Padé = (1−u)/(1+u) with u = T/(θ√2) (the √2 is load-bearing, needs s²=2); inverse (1−γ)/(1+γ)=u; **d_horizon = T** (the "information horizon" is a tautology of the Padé formula); β = −2u/(1+u)²; √2 instantiation |
| **Scaling-law identities** | 9 | `ScalingLawIdentities.lean` | TAF scaling-law algebraic identities |
| **SMEFT trilinear audit (paper-2)** | 31 | `SmeftTrilinearAudit.lean` | δκ₄/δκ₃ ratio, field-redefinition extension, RGE structural invariance, K11_LO/K15_LO ring identities |
| Padé approximant identities | 5 | `RGFlow.lean`, `AmGmPade.lean` | γ_Padé canonical form, θ_eff_Padé closed form, Padé[2,2]−Padé[1,1] residue, saturation coefficient at z = 0 |
| RG flow / β-function | 6 | `RGFlow.lean` | Logistic→β substitution, V derivative, **factor-2 finding**, V_correct, trajectory sign convention |
| Cayley fixed-point + χ | 5 | `RGFlow.lean` | z* = (√17−3)/2, χ = (5+√17)/4, Floquet stability |
| D-SAGE algebraic identities | 10 | `Identities.lean` | 2η²+ηγ_χ+1=0, β·χ=−1 (Anti-Ising), α+χ=2, Rushbrooke/Josephson tautologies, Fisher residue, ν·β=−1 |
| Paper-1 audit findings | 3 | `Identities.lean`, `AmGmPade.lean` | η = 2γ refuted throughout Phase A, AM-GM bound γ_χ ≥ 2√2 |
| C_V coefficient erratum (paper §5.2) | 5 | `ErratumCV.lean`, `CvHagedornCorrection.lean` | Coefficient 1/4 → 1/12 (factor-3 correction), integral derivation |
| Misc identities | 3 | `RGFlow.lean`, `Identities.lean` | RoPE √3/6 = 1/√12, ν(1−γ) = 1, ν_imprint · 2π = −1 |

A machine-readable manifest of every theorem (file, line, claim, preconditions, tactic, source paper section) lives at [`tafagent/data/lean_status.json`](https://github.com/karlesmarin/tafagent/blob/main/data/lean_status.json) in the TAF agent web app repo.

## The substantive finding: V/β factor-2 inconsistency

The paper's formula tables jointly state:

- V(γ) = γ − γ³/3
- β = −V'(γ)
- β(γ) = −(1 − γ²)/2

These three are **mutually inconsistent** for every γ ∉ {−1, +1}: the residual is exactly a factor of 2. The inconsistency is proved formally in `Taf/RGFlow.lean:122` as

```lean
theorem V_derivative_ne_RG_beta (γ : ℝ) (hne1 : γ ≠ 1) (hne2 : γ ≠ -1) :
    -(deriv (fun x : ℝ => x - x^3 / 3) γ) ≠ -(1 - γ^2) / 2
```

Companion theorems `V_correct_derivative` (`RGFlow.lean:238`) and `V_correct_matches_RG_beta` (`RGFlow.lean:256`) show that the corrected potential

V_correct(γ) = γ/2 − γ³/6

*does* integrate to the stated β(γ) = −(1 − γ²)/2.

**Recommendation.** Restate V as γ/2 − γ³/6, or rescale β to −(1 − γ²), or document the Lagrangian-normalization convention that bridges the two presentations.

## File map

| File | Theorems | Topics |
|------|----------|--------|
| `Taf/GammaMobius.lean` | 6 | Padé γ as Möbius transform of u = T/(θ√2); d_horizon = T tautology; β in u |
| `Taf/ScalingLawIdentities.lean` | 9 | TAF scaling-law identities |
| `Taf/SmeftTrilinearAudit.lean` | 31 | paper-2 SMEFT trilinear couplings (δκ₄/δκ₃, RGE invariance, ring identities) |
| `Taf/RGFlow.lean` | 17 | Padé identities, RG β-function, Cayley fixed-point, χ susceptibility, RoPE β-form, CFT ν |
| `Taf/Identities.lean` | 13 | D-SAGE Groebner-discovered identities, η = 2γ refutation, ν_imprint dimensional check |
| `Taf/AmGmPade.lean` | 2 | AM-GM bound on γ_χ, Padé saturation leading coefficient |
| `Taf/ErratumCV.lean` | 4 | C_V coefficient correction, factor-3 quantification |
| `Taf/CvHagedornCorrection.lean` | 1 | C_V integral derivation from ∫(log x)²/x dx |
| `Taf/Basic.lean`, `SocratesCommon.lean`, `SocratesScratch.lean` | — | placeholders / helpers (not counted) |

## Related repositories

- **TAF agent web app:** [`huggingface.co/spaces/karlexmarin/taf-agent`](https://huggingface.co/spaces/karlexmarin/taf-agent) — consumes a manifest of these theorems and renders verification badges in the browser. Mirror at [`github.com/karlesmarin/tafagent`](https://github.com/karlesmarin/tafagent).
- **Paper sources:** [`github.com/karlesmarin/predicting-how-transformers-attend`](https://github.com/karlesmarin/predicting-how-transformers-attend)
- **Sócrates auditing framework:** [`github.com/karlesmarin/triangulum`](https://github.com/karlesmarin/triangulum)
