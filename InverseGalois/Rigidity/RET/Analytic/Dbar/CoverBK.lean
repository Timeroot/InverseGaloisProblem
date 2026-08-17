/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverReg
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverParts
import InverseGalois.Rigidity.RET.Analytic.Dbar.Estimate

/-!
# The weighted inner product on the total space of a covering

Integrating the fibre sum of a product against a weight pulled back from the base gives the
covering an inner product, and the integration by parts of the fibre sum turns the pointwise rules
of the Cauchy–Riemann calculus into the adjoint formula: the operator moves off one factor of the
inner product and comes back on the other as the weighted adjoint.  That formula is what the `L²`
theory for the Cauchy–Riemann operator on a covering is built from.

## Main definitions

* `Rigidity.RET.wipY` — the weighted inner product on the total space.

## Main results

* `Rigidity.RET.conj_wipY` — the inner product is conjugate symmetric.
* `Rigidity.RET.wipY_dbarY`, `Rigidity.RET.wipY_deltaOpY` — **the two adjoint formulas**.
-/

open MeasureTheory Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {Φ : ℂ → ℂ}

/-! ### Three more rules for the fibre sum -/

omit [TopologicalSpace Y] in
/-- The fibre sum is compatible with negation. -/
theorem fibreSum_neg (F : Y → ℂ) (z : ℂ) : fibreSum f (fun y => -F y) z = -fibreSum f F z := by
  have h := fibreSum_const_mul (f := f) (z₀ := z) (-1 : ℂ) F
  simpa using h

omit [TopologicalSpace Y] in
/-- The fibre sum is compatible with differences. -/
theorem fibreSum_sub {z : ℂ} (hz : (f ⁻¹' {z}).Finite) (F G : Y → ℂ) :
    fibreSum f (fun y => F y - G y) z = fibreSum f F z - fibreSum f G z := by
  have h := fibreSum_add (f := f) (z₀ := z) hz F (fun y => -G y)
  simp only [← sub_eq_add_neg] at h
  rw [h, fibreSum_neg]
  ring

omit [TopologicalSpace Y] in
/-- The fibre sum commutes with conjugation. -/
theorem fibreSum_conj {z : ℂ} (hz : (f ⁻¹' {z}).Finite) (F : Y → ℂ) :
    conj (fibreSum f F z) = fibreSum f (fun y => conj (F y)) z := by
  have h := map_fibreSum (f := f) (z₀ := z) ((starRingEnd ℂ).toAddMonoidHom) F hz
  simpa using h

/-! ### The weighted inner product -/

/-- **The weighted inner product on the total space of a covering**: the plane integral of the
fibre sum of `u v̄ e^{-φ}`. -/
def wipY (f : Y → ℂ) (Φ : ℂ → ℂ) (u v : Y → ℂ) : ℂ :=
  ∫ z : ℂ, fibreSum f (fun y => u y * conj (v y) * Complex.exp (-(Φ (f y)))) z

section Cover

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hlh : IsLocalHomeomorph f)

include hfin hcov hlh in
/-- The fibre sum of a continuous function of compact support is integrable. -/
theorem integrable_fibreSum_complex {F : Y → ℂ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) : Integrable (fibreSum f F) :=
  (continuous_fibreSum hfin hcov hlh.continuous hFc hFs).integrable_of_hasCompactSupport
    (hasCompactSupport_fibreSum hlh.continuous hFs)

omit [TopologicalSpace Y] in
include hfin in
/-- **The weighted inner product is conjugate symmetric** when the exponent is real. -/
theorem conj_wipY (hreal : ∀ w, conj (Φ w) = Φ w) (u v : Y → ℂ) :
    conj (wipY f Φ u v) = wipY f Φ v u := by
  rw [wipY, wipY, ← integral_conj]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show conj (fibreSum f (fun y => u y * conj (v y) * Complex.exp (-(Φ (f y)))) z) = _
  rw [fibreSum_conj (hfin z)]
  refine finsum_mem_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_conj, conj_exp_neg hreal (f y)]
  ring

include hfin hcov hlh in
/-- **The adjoint formula on the total space of a covering.**  Against the weight `e^{-Φ}` pulled
back from the base, the Cauchy–Riemann operator moves off the first factor of the inner product
and comes back on the second as the weighted adjoint. -/
theorem wipY_dbarY (hΦ : ContDiff ℝ 1 Φ) (hreal : ∀ w, conj (Φ w) = Φ w)
    (hu : ∀ y, IsC1At f u y) (hv : ∀ y, IsC1At f v y) (hs : HasCompactSupport v) :
    wipY f Φ (dbarY hlh u) v = wipY f Φ u (deltaOpY hlh Φ v) := by
  classical
  have hdΦ : ∀ z : ℂ, DifferentiableAt ℝ Φ z := hΦ.differentiable one_ne_zero
  have hcu : Continuous u := continuous_of_isC1At hlh hu
  have hcv : Continuous v := continuous_of_isC1At hlh hv
  have hcρ : Continuous fun z : ℂ => Complex.exp (-(Φ z)) := (contDiff_exp_neg hΦ).continuous
  have hcvs : HasCompactSupport fun y => conj (v y) :=
    hs.comp_left (g := fun t : ℂ => conj t) (by simp)
  -- the function whose derivative is integrated
  have hC1F : ∀ y, IsC1At f (fun y' => u y' * conj (v y') * Complex.exp (-(Φ (f y')))) y :=
    fun y => ((hu y).mul (hv y).conj).mul (isC1At_comp hlh (contDiff_exp_neg hΦ).contDiffAt)
  have hFs : HasCompactSupport fun y => u y * conj (v y) * Complex.exp (-(Φ (f y))) :=
    hcvs.mul_left.mul_right
  -- its derivative is the difference of the two integrands
  have hderiv : ∀ y, IsDbarAt f (fun y' => u y' * conj (v y') * Complex.exp (-(Φ (f y'))))
      (dbarY hlh u y * conj (v y) * Complex.exp (-(Φ (f y)))
        - u y * conj (deltaOpY hlh Φ v y) * Complex.exp (-(Φ (f y)))) y := by
    intro y
    have hdu : IsDiffAt f u y := (hu y).isDiffAt
    have hdv : IsDiffAt f v y := (hv y).isDiffAt
    have hdcv : IsDiffAt f (fun y' => conj (v y')) y := hdv.conj
    have hdρ : IsDiffAt f (fun y' => Complex.exp (-(Φ (f y')))) y :=
      isDiffAt_comp hlh ((contDiff_exp_neg hΦ).differentiable one_ne_zero (f y))
    have hdiff : IsDiffAt f (fun y' => u y' * conj (v y') * Complex.exp (-(Φ (f y')))) y :=
      (hdu.mul hdcv).mul hdρ
    have e1 : dbarY hlh (fun y' => u y' * conj (v y') * Complex.exp (-(Φ (f y')))) y
        = (u y * conj (v y)) * dbarY hlh (fun y' => Complex.exp (-(Φ (f y')))) y
          + Complex.exp (-(Φ (f y))) * dbarY hlh (fun y' => u y' * conj (v y')) y :=
      dbarY_mul (hdu.mul hdcv) hdρ
    have e2 : dbarY hlh (fun y' => Complex.exp (-(Φ (f y')))) y
        = -Complex.exp (-(Φ (f y))) * conj (dz Φ (f y)) := by
      rw [dbarY_comp hlh (fun w => Complex.exp (-(Φ w))) y, dbar_exp_neg (hdΦ (f y)),
        dbar_eq_conj_dz (hdΦ (f y)) hreal]
    have e3 : dbarY hlh (fun y' => u y' * conj (v y')) y
        = u y * conj (dzY hlh v y) + conj (v y) * dbarY hlh u y := by
      rw [dbarY_mul hdu hdcv, dbarY_conj hdv]
    have e4 : conj (deltaOpY hlh Φ v y)
        = -conj (dzY hlh v y) + conj (dz Φ (f y)) * conj (v y) := by
      simp [deltaOpY]
    have key : dbarY hlh (fun y' => u y' * conj (v y') * Complex.exp (-(Φ (f y')))) y
        = dbarY hlh u y * conj (v y) * Complex.exp (-(Φ (f y)))
          - u y * conj (deltaOpY hlh Φ v y) * Complex.exp (-(Φ (f y))) := by
      rw [e1, e2, e3, e4]
      ring
    rw [← key]
    exact hdiff.isDbarAt
  have hzero := integral_fibreSum_dbar hfin hcov hlh.continuous hlh hC1F hderiv hFs
  -- the two integrands are integrable
  have hIP : Integrable
      (fibreSum f fun y => dbarY hlh u y * conj (v y) * Complex.exp (-(Φ (f y)))) :=
    integrable_fibreSum_complex hfin hcov hlh
      (((continuous_dbarY hlh hu).mul (Complex.continuous_conj.comp hcv)).mul
        (hcρ.comp hlh.continuous)) hcvs.mul_left.mul_right
  have hIQ : Integrable
      (fibreSum f fun y => u y * conj (deltaOpY hlh Φ v y) * Complex.exp (-(Φ (f y)))) := by
    refine integrable_fibreSum_complex hfin hcov hlh
      ((hcu.mul (Complex.continuous_conj.comp (continuous_deltaOpY hlh hΦ hv))).mul
        (hcρ.comp hlh.continuous)) ?_
    exact (((hasCompactSupport_deltaOpY hlh hs).comp_left
      (g := fun t : ℂ => conj t) (by simp)).mul_left).mul_right
  have hsplit : ∀ z : ℂ,
      fibreSum f (fun y => dbarY hlh u y * conj (v y) * Complex.exp (-(Φ (f y)))
        - u y * conj (deltaOpY hlh Φ v y) * Complex.exp (-(Φ (f y)))) z
      = fibreSum f (fun y => dbarY hlh u y * conj (v y) * Complex.exp (-(Φ (f y)))) z
        - fibreSum f (fun y => u y * conj (deltaOpY hlh Φ v y) * Complex.exp (-(Φ (f y)))) z :=
    fun z => fibreSum_sub (hfin z) _ _
  simp only [hsplit] at hzero
  rw [integral_sub hIP hIQ] at hzero
  exact sub_eq_zero.1 hzero

include hfin hcov hlh in
/-- **The adjoint formula, conjugated**: the weighted adjoint moves back across the inner product
as the Cauchy–Riemann operator. -/
theorem wipY_deltaOpY (hΦ : ContDiff ℝ 1 Φ) (hreal : ∀ w, conj (Φ w) = Φ w)
    (hu : ∀ y, IsC1At f u y) (hv : ∀ y, IsC1At f v y) (hs : HasCompactSupport v) :
    wipY f Φ v (dbarY hlh u) = wipY f Φ (deltaOpY hlh Φ v) u := by
  have h := congrArg conj (wipY_dbarY hfin hcov hlh hΦ hreal hu hv hs)
  rwa [conj_wipY hfin hreal, conj_wipY hfin hreal] at h

end Cover

end Rigidity.RET

end
