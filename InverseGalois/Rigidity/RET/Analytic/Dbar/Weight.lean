/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Adjoint

/-!
# The formal adjoint of the Cauchy–Riemann operator against an exponential weight

The weight of an `L²` estimate for `∂/∂z̄` is an exponential `e^{-φ}` with `φ` real.  Against such
a weight the integration by parts of the previous page takes a closed form: the operator moves off
one factor of the integral and comes back on the other as the first-order operator
`δ v = -∂v + (∂φ) v`.  This page records the chain rule that computes the derivative of the
weight and the resulting adjoint formula.

## Main definitions

* `Rigidity.RET.deltaOp` — the formal adjoint `-∂ + (∂φ)` of the Cauchy–Riemann operator.

## Main results

* `Rigidity.RET.dbar_comp_holo`, `Rigidity.RET.dz_comp_holo` — the chain rule for a holomorphic
  outer function.
* `Rigidity.RET.integral_adjoint` — **the adjoint formula** against an exponential weight.
-/

open MeasureTheory Set ComplexConjugate

noncomputable section

namespace Rigidity.RET

/-! ### The chain rule for a holomorphic outer function -/

/-- The real derivative of a holomorphic function of a real-differentiable one. -/
theorem fderiv_comp_holo {F g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z)
    (hF : DifferentiableAt ℂ F (g z)) (v : ℂ) :
    fderiv ℝ (fun w => F (g w)) z v = deriv F (g z) * fderiv ℝ g z v := by
  have h : HasFDerivAt (fun w => F (g w))
      (((fderiv ℂ F (g z)).restrictScalars ℝ).comp (fderiv ℝ g z)) z := by
    have := (hF.hasFDerivAt.restrictScalars ℝ).comp z hg.hasFDerivAt
    simpa [Function.comp_def] using this
  rw [h.fderiv]
  show (fderiv ℂ F (g z)) (fderiv ℝ g z v) = deriv F (g z) * fderiv ℝ g z v
  have hlin : (fderiv ℂ F (g z)) (fderiv ℝ g z v)
      = (fderiv ℝ g z v) • (fderiv ℂ F (g z)) 1 := by
    rw [← ContinuousLinearMap.map_smul]
    simp
  rw [hlin, smul_eq_mul, mul_comm]
  rfl

/-- **The chain rule for `∂/∂z̄`** with a holomorphic outer function. -/
theorem dbar_comp_holo {F g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z)
    (hF : DifferentiableAt ℂ F (g z)) :
    dbar (fun w => F (g w)) z = deriv F (g z) * dbar g z := by
  simp only [dbar, fderiv_comp_holo hg hF]
  ring

/-- **The chain rule for `∂/∂z`** with a holomorphic outer function. -/
theorem dz_comp_holo {F g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z)
    (hF : DifferentiableAt ℂ F (g z)) :
    dz (fun w => F (g w)) z = deriv F (g z) * dz g z := by
  simp only [dz, fderiv_comp_holo hg hF]
  ring

/-! ### The exponential weight -/

/-- The derivative of an exponential weight. -/
theorem dbar_exp_neg {Φ : ℂ → ℂ} {z : ℂ} (hΦ : DifferentiableAt ℝ Φ z) :
    dbar (fun w => Complex.exp (-(Φ w))) z = -(Complex.exp (-(Φ z))) * dbar Φ z := by
  have hg : DifferentiableAt ℝ (fun w => -(Φ w)) z := hΦ.neg
  have h := dbar_comp_holo (F := Complex.exp) (g := fun w => -(Φ w)) hg
    (Complex.differentiable_exp _)
  have hd : deriv Complex.exp (-(Φ z)) = Complex.exp (-(Φ z)) :=
    (Complex.hasDerivAt_exp _).deriv
  rw [h, hd, dbar_neg hΦ]
  ring

/-- A real-valued function has conjugate derivatives. -/
theorem dbar_eq_conj_dz {Φ : ℂ → ℂ} {z : ℂ} (hΦ : DifferentiableAt ℝ Φ z)
    (hreal : ∀ w, conj (Φ w) = Φ w) : dbar Φ z = conj (dz Φ z) := by
  have h : dbar (fun w => conj (Φ w)) z = conj (dz Φ z) := dbar_conj hΦ
  rwa [show (fun w => conj (Φ w)) = Φ from funext hreal] at h

/-- An exponential weight is as smooth as its exponent. -/
theorem contDiff_exp_neg {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ) :
    ContDiff ℝ 1 (fun w => Complex.exp (-(Φ w))) :=
  (Complex.contDiff_exp (𝕜 := ℝ)).comp hΦ.neg

/-! ### The adjoint -/

/-- **The formal adjoint** of the Cauchy–Riemann operator against the weight `e^{-Φ}`. -/
def deltaOp (Φ v : ℂ → ℂ) (z : ℂ) : ℂ := -(dz v z) + dz Φ z * v z

/-- **The adjoint formula.**  Against the weight `e^{-Φ}` with `Φ` real, the Cauchy–Riemann
operator moves off the first factor of a plane integral and comes back on the second as
`deltaOp Φ`. -/
theorem integral_adjoint {Φ u v : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v) (hreal : ∀ w, conj (Φ w) = Φ w) :
    (∫ z : ℂ, dbar u z * conj (v z) * Complex.exp (-(Φ z)))
      = ∫ z : ℂ, u z * conj (deltaOp Φ v z) * Complex.exp (-(Φ z)) := by
  classical
  set ρ : ℂ → ℂ := fun z => Complex.exp (-(Φ z)) with hρ
  have hρC : ContDiff ℝ 1 ρ := contDiff_exp_neg hΦ
  have hdρ : ∀ z, dbar ρ z = -(ρ z) * conj (dz Φ z) := by
    intro z
    have hdiff : DifferentiableAt ℝ Φ z := hΦ.differentiable one_ne_zero z
    rw [hρ, dbar_exp_neg hdiff, dbar_eq_conj_dz hdiff hreal]
  set A : ℂ → ℂ := fun z => u z * conj (dz v z) * ρ z with hA
  set B : ℂ → ℂ := fun z => u z * conj (v z) * conj (dz Φ z) * ρ z with hB
  have hAi : Integrable A := by
    have hcont : Continuous (fun z : ℂ => conj (dz v z)) :=
      Complex.continuous_conj.comp (continuous_dz hv)
    have hsupp : HasCompactSupport (fun z : ℂ => conj (dz v z)) :=
      (hasCompactSupport_dz hs).comp_left (g := fun t : ℂ => conj t) (by simp)
    exact ((hu.continuous.mul hcont).mul hρC.continuous).integrable_of_hasCompactSupport
      ((hsupp.mul_left).mul_right)
  have hBi : Integrable B := by
    have hcv : Continuous (fun z : ℂ => conj (v z)) := Complex.continuous_conj.comp hv.continuous
    have hsv : HasCompactSupport (fun z : ℂ => conj (v z)) :=
      hs.comp_left (g := fun t : ℂ => conj t) (by simp)
    have hcΦ : Continuous (fun z : ℂ => conj (dz Φ z)) :=
      Complex.continuous_conj.comp (continuous_dz hΦ)
    exact (((hu.continuous.mul hcv).mul hcΦ).mul
      hρC.continuous).integrable_of_hasCompactSupport (((hsv.mul_left).mul_right).mul_right)
  have hparts := integral_dbar_parts hu hv hρC hs
  have hlast : (fun z : ℂ => u z * conj (v z) * dbar ρ z) = fun z => -(B z) := by
    funext z
    rw [hdρ z, hB]
    ring
  rw [hparts, hlast, integral_neg]
  have hsplit : (fun z : ℂ => u z * conj (deltaOp Φ v z) * ρ z) = fun z => -(A z) + B z := by
    funext z
    simp only [deltaOp, map_add, map_neg, map_mul, hA, hB]
    ring
  have hnegA : Integrable (fun z : ℂ => -A z) := hAi.neg
  rw [hsplit, integral_add hnegA hBi, integral_neg]
  ring

end Rigidity.RET

end
