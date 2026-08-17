/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Kernel

/-!
# The Cauchy–Riemann equation is solvable in the plane

Convolution with the Cauchy kernel not only undoes the Cauchy–Riemann operator on a function of
compact support, it also solves the equation: for a continuously differentiable `g` of compact
support the transform of `g` is a function whose anti-holomorphic derivative is `g`.  This is the
lemma of Dolbeault and Grothendieck in its simplest shape, and the base case of every later
solution of the equation.

Both halves of the statement come from the same two facts.  Differentiation passes through a
convolution when the differentiable factor has compact support and the other is locally integrable
— which the Cauchy kernel is, its pole being mild in two real dimensions — and the transform of the
derivative is the function, which is the Cauchy–Pompeiu formula.

## Main results

* `Rigidity.RET.dbar_cauchyTransform` — the transform of `g` solves `∂u/∂z̄ = g`.
* `Rigidity.RET.exists_dbar_eq` — the equation `∂u/∂z̄ = g` is solvable for `g` of compact support.
* `Rigidity.RET.contDiff_cauchyTransform` — the transform is as smooth as the function.
-/

open MeasureTheory

open scoped Real Convolution

noncomputable section

namespace Rigidity.RET

variable {g : ℂ → ℂ}

/-- The multiplication of the plane, read as the bilinear map along which the Cauchy transform is a
convolution. -/
local notation "mulL" => ContinuousLinearMap.mul ℝ ℂ

/-- **The Cauchy transform is as smooth as the function it transforms.** -/
theorem contDiff_cauchyTransform {n : ℕ∞} (hg : ContDiff ℝ n g) (hsupp : HasCompactSupport g) :
    ContDiff ℝ n (cauchyTransform g) := by
  have hfun : cauchyTransform g = cauchyKernel ⋆[mulL, volume] g :=
    funext (cauchyTransform_eq_convolution g)
  rw [hfun]
  exact hsupp.contDiff_convolution_right mulL locallyIntegrable_cauchyKernel hg

/-- The derivative of the Cauchy transform is the transform of the derivative, read one direction
at a time. -/
theorem fderiv_cauchyTransform_apply (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) (w : ℂ)
    (v : ℂ) :
    fderiv ℝ (cauchyTransform g) w v
      = (cauchyKernel ⋆[mulL, volume] fun a => fderiv ℝ g a v) w := by
  have hfun : cauchyTransform g = cauchyKernel ⋆[mulL, volume] g :=
    funext (cauchyTransform_eq_convolution g)
  have hFD : HasFDerivAt (cauchyTransform g)
      ((cauchyKernel ⋆[ContinuousLinearMap.precompR ℂ mulL, volume] fderiv ℝ g) w) w := by
    rw [hfun]
    exact hsupp.hasFDerivAt_convolution_right mulL locallyIntegrable_cauchyKernel hg w
  rw [hFD.fderiv]
  exact convolution_precompR_apply (L := mulL) locallyIntegrable_cauchyKernel (hsupp.fderiv ℝ)
    (hg.continuous_fderiv one_ne_zero) w v

/-- **The Cauchy transform solves the Cauchy–Riemann equation.**  For a continuously differentiable
function of compact support, the anti-holomorphic derivative of its transform is the function. -/
theorem dbar_cauchyTransform (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) (w : ℂ) :
    dbar (cauchyTransform g) w = g w := by
  -- the two directional derivatives are themselves convolutions
  have hcont : ∀ v : ℂ, Continuous fun a => fderiv ℝ g a v := fun v =>
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hex : ∀ v : ℂ, Integrable (fun t : ℂ => cauchyKernel t * fderiv ℝ g (w - t) v) volume :=
    fun v => (hsupp.fderiv_apply ℝ v).convolutionExists_right mulL locallyIntegrable_cauchyKernel
      (hcont v) w
  have hsum : (cauchyKernel ⋆[mulL, volume] fun a => fderiv ℝ g a 1) w
      + Complex.I * (cauchyKernel ⋆[mulL, volume] fun a => fderiv ℝ g a Complex.I) w
      = ∫ t : ℂ, cauchyKernel t
          * (fderiv ℝ g (w - t) 1 + Complex.I * fderiv ℝ g (w - t) Complex.I) := by
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_const_mul, ← integral_add (hex 1) ((hex Complex.I).const_mul Complex.I)]
    congr 1
    funext t
    ring
  calc dbar (cauchyTransform g) w
      = (2 : ℂ)⁻¹ * (fderiv ℝ (cauchyTransform g) w 1
          + Complex.I * fderiv ℝ (cauchyTransform g) w Complex.I) := rfl
    _ = (2 : ℂ)⁻¹ * ((cauchyKernel ⋆[mulL, volume] fun a => fderiv ℝ g a 1) w
          + Complex.I * (cauchyKernel ⋆[mulL, volume] fun a => fderiv ℝ g a Complex.I) w) := by
        rw [fderiv_cauchyTransform_apply hg hsupp w 1,
          fderiv_cauchyTransform_apply hg hsupp w Complex.I]
    _ = (2 : ℂ)⁻¹ * ∫ t : ℂ, cauchyKernel t
          * (fderiv ℝ g (w - t) 1 + Complex.I * fderiv ℝ g (w - t) Complex.I) := by rw [hsum]
    _ = ∫ t : ℂ, cauchyKernel t * dbar g (w - t) := by
        rw [← integral_const_mul]
        congr 1
        funext t
        simp only [dbar]
        ring
    _ = cauchyTransform (dbar g) w := by
        rw [cauchyTransform_eq_convolution, convolution_def]
        simp only [ContinuousLinearMap.mul_apply']
    _ = g w := cauchyTransform_dbar hg hsupp w

/-- **The Cauchy–Riemann equation is solvable in the plane** for data of compact support. -/
theorem exists_dbar_eq (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) :
    ∃ u : ℂ → ℂ, ContDiff ℝ 1 u ∧ ∀ w, dbar u w = g w :=
  ⟨cauchyTransform g, contDiff_cauchyTransform hg hsupp, dbar_cauchyTransform hg hsupp⟩

end Rigidity.RET
