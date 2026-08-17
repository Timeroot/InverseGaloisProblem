/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Parts

/-!
# The holomorphic derivative and the weighted adjoint

Beside `∂/∂z̄` a function of a complex variable has the holomorphic derivative `∂/∂z`; on a
holomorphic function it is the complex derivative, and on a conjugate it is the conjugate of the
other operator.  Putting the two together with the integration by parts of the previous page gives
the formula that moves `∂/∂z̄` off one factor of a weighted plane integral and onto the other: the
formal adjoint of the Cauchy–Riemann operator against a weight.  That formula is the identity from
which the `L²` estimates for the operator are read off.

## Main definitions

* `Rigidity.RET.dz` — the operator `∂/∂z`.

## Main results

* `Rigidity.RET.dbar_conj`, `Rigidity.RET.dz_conj` — the two operators exchange under conjugation.
* `Rigidity.RET.integral_dz_eq_zero` — the plane integral of `∂F/∂z` vanishes on compactly
  supported functions.
* `Rigidity.RET.integral_dbar_parts` — **the weighted integration by parts**.
-/

open MeasureTheory Set ComplexConjugate

noncomputable section

namespace Rigidity.RET

/-- The **holomorphic derivative** `∂/∂z = ½ (∂/∂x - i ∂/∂y)`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)

/-! ### Conjugation -/

/-- Complex conjugation is smooth as a real map. -/
theorem contDiff_conj {n : WithTop ℕ∞} : ContDiff ℝ n (fun z : ℂ => conj z) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := n)
  simpa using h

/-- The real derivative of a conjugate is the conjugate of the real derivative. -/
theorem fderiv_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ (fun w => conj (f w)) z v = conj (fderiv ℝ f z v) := by
  have h : HasFDerivAt (fun w => conj (f w))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) z := by
    have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt
    simpa [Function.comp_def] using this
  rw [h.fderiv]
  simp

/-- A conjugate is as differentiable as the function itself. -/
theorem differentiableAt_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun w => conj (f w)) z := by
  have := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt).comp z hf
  simpa [Function.comp_def] using this

/-- **The two operators exchange under conjugation**, one way. -/
theorem dbar_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w => conj (f w)) z = conj (dz f z) := by
  simp only [dbar, dz, fderiv_conj hf, map_mul, map_sub, map_inv₀, map_ofNat]
  rw [Complex.conj_I]
  ring

/-- **The two operators exchange under conjugation**, the other way. -/
theorem dz_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w => conj (f w)) z = conj (dbar f z) := by
  simp only [dbar, dz, fderiv_conj hf, map_mul, map_add, map_inv₀, map_ofNat]
  rw [Complex.conj_I]
  ring

/-! ### The operator on compactly supported functions -/

/-- The holomorphic derivative preserves compact support. -/
theorem hasCompactSupport_dz {F : ℂ → ℂ} (hs : HasCompactSupport F) :
    HasCompactSupport (dz F) :=
  HasCompactSupport.comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (2 : ℂ)⁻¹ * (L 1 - Complex.I * L Complex.I))
    (hs.fderiv (𝕜 := ℝ)) (by simp)

/-- The holomorphic derivative preserves continuity. -/
theorem continuous_dz {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (dz F) := by
  have h := hF.continuous_fderiv one_ne_zero
  exact continuous_const.mul
    ((h.clm_apply continuous_const).sub (continuous_const.mul (h.clm_apply continuous_const)))

/-- The holomorphic derivative sends a compactly supported function to an integrable one. -/
theorem integrable_dz {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    Integrable (dz F) :=
  (continuous_dz hF).integrable_of_hasCompactSupport (hasCompactSupport_dz hs)

/-- **The plane integral of `∂F/∂z` vanishes** on continuously differentiable functions of
compact support. -/
theorem integral_dz_eq_zero {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    ∫ z : ℂ, dz F z = 0 := by
  have hcont := hF.continuous_fderiv one_ne_zero
  have h1 : Integrable (fun z : ℂ => fderiv ℝ F z 1) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (hs.fderiv (𝕜 := ℝ)) (by simp))
  have h2 : Integrable (fun z : ℂ => Complex.I * fderiv ℝ F z Complex.I) :=
    ((continuous_const.mul (hcont.clm_apply continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => Complex.I * L Complex.I) (hs.fderiv (𝕜 := ℝ)) (by simp))
  simp only [dz]
  rw [integral_const_mul, integral_sub h1 h2, integral_const_mul,
    integral_fderiv_one hF hs, integral_fderiv_I hF hs]
  simp

/-! ### The weighted adjoint -/

/-- **Weighted integration by parts for the Cauchy–Riemann operator.**  Against a weight `ρ`, the
operator moves off the first factor of a plane integral and onto the conjugated second factor,
at the price of the derivative of the weight. -/
theorem integral_dbar_parts {v w ρ : ℂ → ℂ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (hρ : ContDiff ℝ 1 ρ) (hs : HasCompactSupport w) :
    (∫ z : ℂ, dbar v z * conj (w z) * ρ z)
      = -(∫ z : ℂ, v z * conj (dz w z) * ρ z) - ∫ z : ℂ, v z * conj (w z) * dbar ρ z := by
  classical
  set cw : ℂ → ℂ := fun z => conj (w z) with hcw
  have hcwC : ContDiff ℝ 1 cw := contDiff_conj.comp hw
  have hcwS : HasCompactSupport cw := hs.comp_left (g := fun t : ℂ => conj t) (by simp)
  set F : ℂ → ℂ := fun z => v z * cw z * ρ z with hF
  have hFC : ContDiff ℝ 1 F := (hv.mul hcwC).mul hρ
  have hFS : HasCompactSupport F := (hcwS.mul_left).mul_right
  -- the product rule for the triple product
  have hrule : ∀ z : ℂ, dbar F z
      = dbar v z * cw z * ρ z + v z * conj (dz w z) * ρ z + v z * cw z * dbar ρ z := by
    intro z
    have hdv : DifferentiableAt ℝ v z := hv.differentiable one_ne_zero z
    have hdw : DifferentiableAt ℝ w z := hw.differentiable one_ne_zero z
    have hdcw : DifferentiableAt ℝ cw z := differentiableAt_conj hdw
    have hdρ : DifferentiableAt ℝ ρ z := hρ.differentiable one_ne_zero z
    have h1 : dbar (fun t => v t * cw t) z = v z * dbar cw z + cw z * dbar v z :=
      dbar_mul hdv hdcw
    have h2 : dbar cw z = conj (dz w z) := dbar_conj hdw
    have h3 : dbar F z = (v z * cw z) * dbar ρ z + ρ z * dbar (fun t => v t * cw t) z :=
      dbar_mul (hdv.mul hdcw) hdρ
    rw [h3, h1, h2]
    ring
  -- the three pieces are integrable
  have hi1 : Integrable (fun z : ℂ => dbar v z * cw z * ρ z) :=
    (((continuous_dbar hv).mul hcwC.continuous).mul hρ.continuous).integrable_of_hasCompactSupport
      ((hcwS.mul_left).mul_right)
  have hi2 : Integrable (fun z : ℂ => v z * conj (dz w z) * ρ z) := by
    have hcont : Continuous (fun z : ℂ => conj (dz w z)) :=
      Complex.continuous_conj.comp (continuous_dz hw)
    have hsupp : HasCompactSupport (fun z : ℂ => conj (dz w z)) :=
      (hasCompactSupport_dz hs).comp_left (g := fun t : ℂ => conj t) (by simp)
    exact ((hv.continuous.mul hcont).mul hρ.continuous).integrable_of_hasCompactSupport
      ((hsupp.mul_left).mul_right)
  have hi3 : Integrable (fun z : ℂ => v z * cw z * dbar ρ z) :=
    ((hv.continuous.mul hcwC.continuous).mul
      (continuous_dbar hρ)).integrable_of_hasCompactSupport ((hcwS.mul_left).mul_right)
  have hzero := integral_dbar_eq_zero hFC hFS
  simp_rw [hrule] at hzero
  have hi12 : Integrable
      (fun z : ℂ => dbar v z * cw z * ρ z + v z * conj (dz w z) * ρ z) := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2] at hzero
  linear_combination hzero

end Rigidity.RET

end
