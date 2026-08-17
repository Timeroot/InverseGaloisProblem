/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Weight

/-!
# The commutator of the Cauchy–Riemann operator with its weighted adjoint

The two first-order operators `∂/∂z` and `∂/∂z̄` commute on twice continuously differentiable
functions, because the second real derivative is symmetric.  Consequently the commutator of
`∂/∂z̄` with the weighted adjoint `δ = -∂ + (∂φ)` is not a differential operator at all: it is
multiplication by the second derivative `∂∂̄φ` of the weight.  That identity is the pointwise
content of the Bochner–Kodaira formula, and it is where the curvature of the weight enters an
`L²` estimate.

## Main results

* `Rigidity.RET.dbar_dz_comm` — the two operators commute.
* `Rigidity.RET.dbar_deltaOp_sub` — **the commutator identity** for the weighted adjoint.
-/

open ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {v Φ : ℂ → ℂ} {z : ℂ}

/-! ### The second derivative -/

/-- A twice continuously differentiable function has a differentiable derivative. -/
theorem differentiableAt_fderiv_of_contDiff_two (hv : ContDiff ℝ 2 v) :
    DifferentiableAt ℝ (fderiv ℝ v) z :=
  (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z

/-- Reading a directional derivative of the derivative. -/
theorem differentiableAt_fderiv_apply (hc : DifferentiableAt ℝ (fderiv ℝ v) z) (b : ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ v w b) z :=
  hc.clm_apply (differentiableAt_const b)

/-- The second real derivative, read on a pair of directions. -/
theorem fderiv_fderiv_apply (hc : DifferentiableAt ℝ (fderiv ℝ v) z) (a b : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w b) z a = fderiv ℝ (fderiv ℝ v) z a b := by
  have h : fderiv ℝ (fun w => fderiv ℝ v w b) z
      = (fderiv ℝ v z).comp (fderiv ℝ (fun _ : ℂ => b) z)
        + (fderiv ℝ (fderiv ℝ v) z).flip b :=
    fderiv_clm_apply hc (differentiableAt_const b)
  rw [h]
  simp

/-! ### The two operators as combinations of the coordinate derivatives -/

/-- The holomorphic derivative as a combination of the coordinate derivatives. -/
theorem dz_eq_pair (v : ℂ → ℂ) :
    dz v = fun w => (2 : ℂ)⁻¹ * fderiv ℝ v w 1
      + (-((2 : ℂ)⁻¹ * Complex.I)) * fderiv ℝ v w Complex.I := by
  funext w
  simp only [dz]
  ring

/-- The Cauchy–Riemann operator as a combination of the coordinate derivatives. -/
theorem dbar_eq_pair (v : ℂ → ℂ) :
    dbar v = fun w => (2 : ℂ)⁻¹ * fderiv ℝ v w 1
      + ((2 : ℂ)⁻¹ * Complex.I) * fderiv ℝ v w Complex.I := by
  funext w
  simp only [dbar]
  ring

/-- The derivative of such a combination. -/
theorem fderiv_pair (hc : DifferentiableAt ℝ (fderiv ℝ v) z) (c d a : ℂ) :
    fderiv ℝ (fun w => c * fderiv ℝ v w 1 + d * fderiv ℝ v w Complex.I) z a
      = c * fderiv ℝ (fderiv ℝ v) z a 1 + d * fderiv ℝ (fderiv ℝ v) z a Complex.I := by
  have h1 := differentiableAt_fderiv_apply hc 1
  have h2 := differentiableAt_fderiv_apply hc Complex.I
  have hh : HasFDerivAt (fun w => c * fderiv ℝ v w 1 + d * fderiv ℝ v w Complex.I)
      (c • fderiv ℝ (fun w => fderiv ℝ v w 1) z
        + d • fderiv ℝ (fun w => fderiv ℝ v w Complex.I) z) z :=
    (h1.hasFDerivAt.const_mul c).add (h2.hasFDerivAt.const_mul d)
  rw [hh.fderiv]
  simp [fderiv_fderiv_apply hc]

/-- The holomorphic derivative of a twice differentiable function is differentiable. -/
theorem differentiableAt_dz (hc : DifferentiableAt ℝ (fderiv ℝ v) z) :
    DifferentiableAt ℝ (dz v) z := by
  rw [dz_eq_pair]
  exact ((differentiableAt_fderiv_apply hc 1).const_mul _).add
    ((differentiableAt_fderiv_apply hc Complex.I).const_mul _)

/-- The Cauchy–Riemann derivative of a twice differentiable function is differentiable. -/
theorem differentiableAt_dbar (hc : DifferentiableAt ℝ (fderiv ℝ v) z) :
    DifferentiableAt ℝ (dbar v) z := by
  rw [dbar_eq_pair]
  exact ((differentiableAt_fderiv_apply hc 1).const_mul _).add
    ((differentiableAt_fderiv_apply hc Complex.I).const_mul _)

/-! ### Regularity of the operators -/

/-- Each of the two operators costs one degree of smoothness. -/
theorem contDiff_one_dz (hv : ContDiff ℝ 2 v) : ContDiff ℝ 1 (dz v) := by
  have h : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z) := hv.fderiv_right (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z 1) := h.clm_apply contDiff_const
  have h2 : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z Complex.I) := h.clm_apply contDiff_const
  exact contDiff_const.mul (h1.sub (contDiff_const.mul h2))

/-- Each of the two operators costs one degree of smoothness. -/
theorem contDiff_one_dbar (hv : ContDiff ℝ 2 v) : ContDiff ℝ 1 (dbar v) := by
  have h : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z) := hv.fderiv_right (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z 1) := h.clm_apply contDiff_const
  have h2 : ContDiff ℝ 1 (fun z : ℂ => fderiv ℝ v z Complex.I) := h.clm_apply contDiff_const
  exact contDiff_const.mul (h1.add (contDiff_const.mul h2))

/-- The weighted adjoint of a twice differentiable function is continuously differentiable. -/
theorem contDiff_one_deltaOp (hΦ : ContDiff ℝ 2 Φ) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 1 (deltaOp Φ v) :=
  (contDiff_one_dz hv).neg.add ((contDiff_one_dz hΦ).mul (hv.of_le (by norm_num)))

/-- The weighted adjoint preserves compact support. -/
theorem hasCompactSupport_deltaOp (hs : HasCompactSupport v) :
    HasCompactSupport (deltaOp Φ v) :=
  (hasCompactSupport_dz hs).neg.add (hs.mul_left)

/-! ### The two operators commute -/

/-- **The two first-order operators commute** on twice continuously differentiable functions. -/
theorem dbar_dz_comm (hv : ContDiff ℝ 2 v) : dbar (dz v) z = dz (dbar v) z := by
  have hc : DifferentiableAt ℝ (fderiv ℝ v) z := differentiableAt_fderiv_of_contDiff_two hv
  have hsym : fderiv ℝ (fderiv ℝ v) z 1 Complex.I = fderiv ℝ (fderiv ℝ v) z Complex.I 1 :=
    hv.contDiffAt.isSymmSndFDerivAt (by simp) 1 Complex.I
  have e1 : ∀ a : ℂ, fderiv ℝ (dz v) z a
      = (2 : ℂ)⁻¹ * fderiv ℝ (fderiv ℝ v) z a 1
        + (-((2 : ℂ)⁻¹ * Complex.I)) * fderiv ℝ (fderiv ℝ v) z a Complex.I := by
    intro a
    rw [dz_eq_pair]
    exact fderiv_pair hc _ _ a
  have e2 : ∀ a : ℂ, fderiv ℝ (dbar v) z a
      = (2 : ℂ)⁻¹ * fderiv ℝ (fderiv ℝ v) z a 1
        + ((2 : ℂ)⁻¹ * Complex.I) * fderiv ℝ (fderiv ℝ v) z a Complex.I := by
    intro a
    rw [dbar_eq_pair]
    exact fderiv_pair hc _ _ a
  show (2 : ℂ)⁻¹ * (fderiv ℝ (dz v) z 1 + Complex.I * fderiv ℝ (dz v) z Complex.I)
      = (2 : ℂ)⁻¹ * (fderiv ℝ (dbar v) z 1 - Complex.I * fderiv ℝ (dbar v) z Complex.I)
  rw [e1 1, e1 Complex.I, e2 1, e2 Complex.I]
  linear_combination (-(Complex.I / 2)) * hsym

/-! ### The commutator with the weighted adjoint -/

/-- **The commutator of the Cauchy–Riemann operator with its weighted adjoint** is multiplication
by the second derivative of the weight. -/
theorem dbar_deltaOp_sub (hΦ : ContDiff ℝ 2 Φ) (hv : ContDiff ℝ 2 v) :
    dbar (deltaOp Φ v) z - deltaOp Φ (dbar v) z = v z * dbar (dz Φ) z := by
  have hcΦ : DifferentiableAt ℝ (fderiv ℝ Φ) z := differentiableAt_fderiv_of_contDiff_two hΦ
  have hcv : DifferentiableAt ℝ (fderiv ℝ v) z := differentiableAt_fderiv_of_contDiff_two hv
  have hdv : DifferentiableAt ℝ v z := hv.differentiable (by norm_num) z
  have hddzv : DifferentiableAt ℝ (dz v) z := differentiableAt_dz hcv
  have hddzΦ : DifferentiableAt ℝ (dz Φ) z := differentiableAt_dz hcΦ
  have hn : DifferentiableAt ℝ (fun w => -(dz v w)) z := hddzv.neg
  have hm : DifferentiableAt ℝ (fun w => dz Φ w * v w) z := hddzΦ.mul hdv
  have h1 : dbar (deltaOp Φ v) z
      = -(dbar (dz v) z) + (dz Φ z * dbar v z + v z * dbar (dz Φ) z) := by
    rw [show deltaOp Φ v = fun w => (-(dz v w)) + dz Φ w * v w from rfl,
      dbar_add hn hm, dbar_neg hddzv, dbar_mul hddzΦ hdv]
  have h2 : deltaOp Φ (dbar v) z = -(dz (dbar v) z) + dz Φ z * dbar v z := rfl
  rw [h1, h2, dbar_dz_comm hv]
  ring

end Rigidity.RET

end
