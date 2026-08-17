/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverBK

/-!
# The a priori estimate on the total space of a covering

The two adjoint formulas on a covering combine, exactly as they do on the plane, into an identity
between the weighted quadratic forms of the Cauchy–Riemann operator and of its weighted adjoint,
whose defect is the curvature of the weight integrated against the square of the function.  Read on
a real exponent and dropping the term that carries a sign, the identity becomes the a priori
estimate: the weighted norm of the adjoint dominates the curvature integral.  Because the weight is
pulled back from the base, its curvature is a function of the base point alone.

## Main definitions

* `Rigidity.RET.wnorm2Y` — the weighted square norm on the total space.

## Main results

* `Rigidity.RET.wipY_self` — the inner product of a function with itself is its square norm.
* `Rigidity.RET.bochner_kodairaY`, `Rigidity.RET.bochner_kodaira_realY` — **the Bochner–Kodaira
  identity** on the total space, complex and real.
* `Rigidity.RET.curvature_estimateY` — **the a priori estimate** on the total space.
-/

open MeasureTheory Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {Φ : ℂ → ℂ}

/-! ### Real values in the fibre sum -/

omit [TopologicalSpace Y] in
/-- A real fibre sum, read in the complex numbers. -/
theorem fibreSum_ofReal {z : ℂ} (hz : (f ⁻¹' {z}).Finite) (F : Y → ℝ) :
    ((fibreSum f F z : ℝ) : ℂ) = fibreSum f (fun y => ((F y : ℝ) : ℂ)) z := by
  have h := map_fibreSum (f := f) (z₀ := z) Complex.ofRealHom.toAddMonoidHom F hz
  simpa using h

/-! ### The weighted square norm -/

/-- **The weighted square norm on the total space of a covering.** -/
def wnorm2Y (f : Y → ℂ) (Φ : ℂ → ℂ) (u : Y → ℂ) : ℝ :=
  ∫ z : ℂ, fibreSum f (fun y => ‖u y‖ ^ 2 * Real.exp (-(Φ (f y)).re)) z

omit [TopologicalSpace Y] in
/-- The weighted square norm is nonnegative. -/
theorem wnorm2Y_nonneg (f : Y → ℂ) (Φ : ℂ → ℂ) (u : Y → ℂ) : 0 ≤ wnorm2Y f Φ u :=
  integral_nonneg fun z => fibreSum_nonneg (fun y => by positivity) z

section Cover

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hlh : IsLocalHomeomorph f)

omit [TopologicalSpace Y] in
include hfin in
/-- **The weighted inner product of a function with itself is its weighted square norm.** -/
theorem wipY_self (hreal : ∀ t, conj (Φ t) = Φ t) (u : Y → ℂ) :
    wipY f Φ u u = ((wnorm2Y f Φ u : ℝ) : ℂ) := by
  rw [wipY, wnorm2Y, ← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show fibreSum f (fun y => u y * conj (u y) * Complex.exp (-(Φ (f y)))) z
    = ((fibreSum f (fun y => ‖u y‖ ^ 2 * Real.exp (-(Φ (f y)).re)) z : ℝ) : ℂ)
  rw [fibreSum_ofReal (hfin z)]
  refine finsum_mem_congr rfl fun y _ => ?_
  show u y * conj (u y) * Complex.exp (-(Φ (f y)))
    = ((‖u y‖ ^ 2 * Real.exp (-(Φ (f y)).re) : ℝ) : ℂ)
  rw [Complex.mul_conj, exp_neg_eq_ofReal hreal (f y), Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ### The identity -/

include hfin hcov hlh in
/-- **The Bochner–Kodaira identity on the total space of a covering.**  The difference of the two
weighted quadratic forms is the curvature of the weight, integrated against `|v|²`. -/
theorem bochner_kodairaY (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hv : ∀ y, IsC2At f v y) (hs : HasCompactSupport v) :
    wipY f Φ (deltaOpY hlh Φ v) (deltaOpY hlh Φ v) - wipY f Φ (dbarY hlh v) (dbarY hlh v)
      = ∫ z : ℂ, fibreSum f (fun y => dbar (dz Φ) (f y) * (v y * conj (v y))
          * Complex.exp (-(Φ (f y)))) z := by
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hv1 : ∀ y, IsC1At f v y := fun y => (hv y).isC1At
  have hδ : ∀ y, IsC1At f (deltaOpY hlh Φ v) y := isC1At_deltaOpY hlh hΦ hv
  have hdb : ∀ y, IsC1At f (dbarY hlh v) y := isC1At_dbarY hlh hv
  have h1 := wipY_dbarY hfin hcov hlh hΦ1 hreal hδ hv1 hs
  have h2 := wipY_deltaOpY hfin hcov hlh hΦ1 hreal (u := v) (v := dbarY hlh v) hv1 hdb
    (hasCompactSupport_dbarY hlh hs)
  have hcv : Continuous v := continuous_of_isC1At hlh hv1
  have hcvs : HasCompactSupport fun y => conj (v y) :=
    hs.comp_left (g := fun t : ℂ => conj t) (by simp)
  have hcρ : Continuous fun z : ℂ => Complex.exp (-(Φ z)) := (contDiff_exp_neg hΦ1).continuous
  have hi1 : Integrable (fibreSum f fun y =>
      dbarY hlh (deltaOpY hlh Φ v) y * conj (v y) * Complex.exp (-(Φ (f y)))) :=
    integrable_fibreSum_complex hfin hcov hlh
      (((continuous_dbarY hlh hδ).mul (Complex.continuous_conj.comp hcv)).mul
        (hcρ.comp hlh.continuous)) hcvs.mul_left.mul_right
  have hi2 : Integrable (fibreSum f fun y =>
      deltaOpY hlh Φ (dbarY hlh v) y * conj (v y) * Complex.exp (-(Φ (f y)))) :=
    integrable_fibreSum_complex hfin hcov hlh
      (((continuous_deltaOpY hlh hΦ1 hdb).mul (Complex.continuous_conj.comp hcv)).mul
        (hcρ.comp hlh.continuous)) hcvs.mul_left.mul_right
  rw [← h1, h2, wipY, wipY, ← integral_sub hi1 hi2]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show fibreSum f (fun y =>
        dbarY hlh (deltaOpY hlh Φ v) y * conj (v y) * Complex.exp (-(Φ (f y)))) z
      - fibreSum f (fun y =>
        deltaOpY hlh Φ (dbarY hlh v) y * conj (v y) * Complex.exp (-(Φ (f y)))) z = _
  rw [← fibreSum_sub (hfin z)]
  refine finsum_mem_congr rfl fun y _ => ?_
  linear_combination (conj (v y) * Complex.exp (-(Φ (f y)))) * dbarY_deltaOpY_sub hlh hΦ hv y

include hfin hcov hlh in
/-- **The Bochner–Kodaira identity on the total space**, read on real quadratic forms. -/
theorem bochner_kodaira_realY (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hv : ∀ y, IsC2At f v y) (hs : HasCompactSupport v) :
    wnorm2Y f Φ (deltaOpY hlh Φ v) - wnorm2Y f Φ (dbarY hlh v)
      = ∫ z : ℂ, fibreSum f (fun y => (dbar (dz Φ) (f y)).re * ‖v y‖ ^ 2
          * Real.exp (-(Φ (f y)).re)) z := by
  have hR : (∫ z : ℂ, fibreSum f (fun y => dbar (dz Φ) (f y) * (v y * conj (v y))
        * Complex.exp (-(Φ (f y)))) z)
      = ((∫ z : ℂ, fibreSum f (fun y => (dbar (dz Φ) (f y)).re * ‖v y‖ ^ 2
        * Real.exp (-(Φ (f y)).re)) z : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun z => ?_)
    show fibreSum f (fun y => dbar (dz Φ) (f y) * (v y * conj (v y))
          * Complex.exp (-(Φ (f y)))) z
      = ((fibreSum f (fun y => (dbar (dz Φ) (f y)).re * ‖v y‖ ^ 2
          * Real.exp (-(Φ (f y)).re)) z : ℝ) : ℂ)
    rw [fibreSum_ofReal (hfin z)]
    refine finsum_mem_congr rfl fun y _ => ?_
    show dbar (dz Φ) (f y) * (v y * conj (v y)) * Complex.exp (-(Φ (f y)))
      = (((dbar (dz Φ) (f y)).re * ‖v y‖ ^ 2 * Real.exp (-(Φ (f y)).re) : ℝ) : ℂ)
    have hκ : dbar (dz Φ) (f y) = (((dbar (dz Φ) (f y)).re : ℝ) : ℂ) :=
      (Complex.conj_eq_iff_re.mp (conj_dbar_dz hΦ hreal (f y))).symm
    rw [hκ, Complex.mul_conj, exp_neg_eq_ofReal hreal (f y), Complex.normSq_eq_norm_sq]
    push_cast
    simp only [Complex.ofReal_re]
  have h := bochner_kodairaY hfin hcov hlh hΦ hreal hv hs
  rw [wipY_self hfin hreal, wipY_self hfin hreal, hR] at h
  exact_mod_cast h

/-! ### The estimate -/

include hfin hcov hlh in
/-- **The a priori estimate on the total space of a covering.**  The weighted norm of the adjoint
dominates the curvature of the weight integrated against the square of the function. -/
theorem curvature_estimateY (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hv : ∀ y, IsC2At f v y) (hs : HasCompactSupport v) :
    (∫ z : ℂ, fibreSum f (fun y => (dbar (dz Φ) (f y)).re * ‖v y‖ ^ 2
        * Real.exp (-(Φ (f y)).re)) z) ≤ wnorm2Y f Φ (deltaOpY hlh Φ v) := by
  have hid := bochner_kodaira_realY hfin hcov hlh hΦ hreal hv hs
  have hnn : 0 ≤ wnorm2Y f Φ (dbarY hlh v) := wnorm2Y_nonneg f Φ _
  linarith

end Cover

end Rigidity.RET

end
