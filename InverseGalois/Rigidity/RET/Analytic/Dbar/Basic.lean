/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Cauchy–Riemann operator

A real-differentiable function of a complex variable has two first-order derivatives, the
holomorphic one and the anti-holomorphic one; the second, `∂/∂z̄`, is the obstruction to being
holomorphic and vanishes exactly on the holomorphic functions.  It is recorded here as an operator
on functions, together with the two computations the rest of the development needs: it kills the
complex-differentiable functions, and, along a ray leaving a point, it is the combination of the
radial and angular derivatives that the change to polar coordinates produces.

## Main definitions

* `Rigidity.RET.dbar` — the operator `∂/∂z̄`.

## Main results

* `Rigidity.RET.dbar_eq_zero` — the operator kills complex-differentiable functions.
* `Rigidity.RET.differentiableAt_of_dbar_eq_zero` — and it kills nothing else.
* `Rigidity.RET.polar_dbar` — the polar form of the operator.
-/

open scoped Real ContDiff

noncomputable section

namespace Rigidity.RET

/-- The **Cauchy–Riemann operator** `∂/∂z̄ = ½ (∂/∂x + i ∂/∂y)`, read off the real derivative of a
function of a complex variable through its values on the two coordinate directions. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- The point `e(θ) = cos θ + i sin θ` of the unit circle. -/
def circPt (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

theorem circPt_eq_exp (θ : ℝ) : circPt θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, circPt, Complex.ofReal_cos, Complex.ofReal_sin]

theorem norm_circPt (θ : ℝ) : ‖circPt θ‖ = 1 := by
  simp [circPt_eq_exp, Complex.norm_exp]

theorem circPt_ne_zero (θ : ℝ) : circPt θ ≠ 0 := by
  intro h
  have := norm_circPt θ
  rw [h] at this
  simp at this

/-- `e(θ)` has inverse `e(-θ)`, the conjugate. -/
theorem circPt_mul_conj (θ : ℝ) : Complex.exp (-(θ : ℂ) * Complex.I) * circPt θ = 1 := by
  rw [circPt_eq_exp, ← Complex.exp_add]
  simp

/-! ### The rules of the operator -/

section Rules

variable {u v : ℂ → ℂ} {z : ℂ}

/-- The operator only sees a function near the point. -/
theorem dbar_congr (h : u =ᶠ[nhds z] v) : dbar u z = dbar v z := by
  simp only [dbar, h.fderiv_eq]

/-- The operator is additive. -/
theorem dbar_add (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbar (fun w => u w + v w) z = dbar u z + dbar v z := by
  have h : fderiv ℝ (fun w => u w + v w) z = fderiv ℝ u z + fderiv ℝ v z :=
    (hu.hasFDerivAt.add hv.hasFDerivAt).fderiv
  simp only [dbar, h, ContinuousLinearMap.add_apply]
  ring

/-- The operator is compatible with negation. -/
theorem dbar_neg (hu : DifferentiableAt ℝ u z) :
    dbar (fun w => -u w) z = -dbar u z := by
  have h : fderiv ℝ (fun w => -u w) z = -fderiv ℝ u z := hu.hasFDerivAt.neg.fderiv
  simp only [dbar, h, ContinuousLinearMap.neg_apply]
  ring

/-- **The product rule for the operator.** -/
theorem dbar_mul (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbar (fun w => u w * v w) z = u z * dbar v z + v z * dbar u z := by
  have h : fderiv ℝ (fun w => u w * v w) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z :=
    (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  simp only [dbar, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The operator preserves smoothness. -/
theorem contDiff_dbar (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (dbar u) := by
  have h : ContDiff ℝ ∞ (fun z => fderiv ℝ u z) := hu.fderiv_right (by simp)
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ u z 1) := h.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ u z Complex.I) := h.clm_apply contDiff_const
  exact contDiff_const.mul (h1.add (contDiff_const.mul h2))

end Rules

/-! ### The operator kills the holomorphic functions -/

/-- A complex-differentiable function is killed by `∂/∂z̄`. -/
theorem dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : dbar f z = 0 := by
  have hre : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ := (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have h1 : fderiv ℝ f z 1 = fderiv ℂ f z 1 := by rw [hre]; rfl
  have h2 : fderiv ℝ f z Complex.I = Complex.I * fderiv ℂ f z 1 := by
    rw [hre]
    show fderiv ℂ f z Complex.I = _
    rw [show Complex.I = Complex.I • (1 : ℂ) by simp, map_smul]
    simp
  rw [dbar, h1, h2]
  ring_nf
  simp [Complex.I_sq]

/-- **A real-differentiable function killed by `∂/∂z̄` is complex-differentiable.**  The vanishing
of the operator says exactly that the real derivative commutes with multiplication by `i`, which is
complex linearity. -/
theorem differentiableAt_of_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (h : dbar f z = 0) : DifferentiableAt ℂ f z := by
  set L := fderiv ℝ f z with hL
  have h2 : (2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I) = 0 := h
  have hzero : L 1 + Complex.I * L Complex.I = 0 := by linear_combination 2 * h2
  have hI : L Complex.I = Complex.I * L 1 := by
    linear_combination (-Complex.I) * hzero + (L Complex.I) * Complex.I_sq
  rw [differentiableAt_iff_restrictScalars ℝ hf]
  refine ⟨(L 1) • ContinuousLinearMap.id ℂ ℂ, ContinuousLinearMap.ext fun v => ?_⟩
  show L 1 * v = L v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  have key : L v = v.re • L 1 + v.im • L Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  have hvv : (v.re : ℂ) + (v.im : ℂ) * Complex.I = v := Complex.re_add_im v
  rw [key, hI, Complex.real_smul, Complex.real_smul]
  linear_combination (-(L 1)) * hvv

/-! ### The polar form -/

/-- **The polar form of `∂/∂z̄`.**  Along the ray of angle `θ`, the operator is half the sum of the
derivative in the direction `e(θ)` — the radial derivative — and `i` times the derivative in the
direction `i·e(θ)` — the angular derivative divided by the radius. -/
theorem polar_dbar (f : ℂ → ℂ) (p : ℂ) (θ : ℝ) :
    Complex.exp (-(θ : ℂ) * Complex.I) * dbar f p
      = (2 : ℂ)⁻¹ * (fderiv ℝ f p (circPt θ)
          + Complex.I * fderiv ℝ f p (Complex.I * circPt θ)) := by
  set L := fderiv ℝ f p with hL
  set a : ℝ := Real.cos θ with ha
  set b : ℝ := Real.sin θ with hb
  have hsplit : circPt θ = (a : ℝ) • (1 : ℂ) + (b : ℝ) • Complex.I := by
    simp [circPt, Complex.real_smul, ha, hb]
  have hsplit' : Complex.I * circPt θ = (-b : ℝ) • (1 : ℂ) + (a : ℝ) • Complex.I := by
    rw [circPt]
    simp only [Complex.real_smul, Complex.ofReal_neg]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hA : L (circPt θ) = (a : ℂ) * L 1 + (b : ℂ) * L Complex.I := by
    rw [hsplit, map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  have hB : L (Complex.I * circPt θ) = (-b : ℂ) * L 1 + (a : ℂ) * L Complex.I := by
    rw [hsplit', map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  have hexp : Complex.exp (-(θ : ℂ) * Complex.I) = (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [show (-(θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [ha, hb, Complex.ext_iff]
  rw [dbar, hA, hB, hexp]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ring_nf
  rw [Complex.I_sq]
  ring

end Rigidity.RET
