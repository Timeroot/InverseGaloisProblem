/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverMeasure

/-!
# A weighted measure on the total space of a covering

A nonnegative continuous weight on the plane turns the fibre-sum functional into another positive
linear functional on the compactly supported continuous functions of the total space, and the
Riesz–Markov–Kakutani representation theorem turns that one into a measure.  Integration against it
is integration of the fibre sum of the function multiplied by the weight, read at the base point;
the weight is therefore carried by the measure rather than by the integrand, which is what the `L²`
theory asks for.

## Main definitions

* `Rigidity.RET.weightFunctional` — the weighted fibre-sum functional.
* `Rigidity.RET.weightMeasure` — the measure it represents.

## Main results

* `Rigidity.RET.integral_weightMeasure_real`, `Rigidity.RET.integral_weightMeasure_complex` —
  integration against the weighted measure is integration of weighted fibre sums over the plane.
-/

open MeasureTheory Topology CompactlySupported

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {z₀ : ℂ}

/-! ### Real and complex parts of an integral -/

/-- The real part of an integral is the integral of the real part. -/
theorem re_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {G : α → ℂ}
    (h : Integrable G μ) : (∫ x, G x ∂μ).re = ∫ x, (G x).re ∂μ :=
  (Complex.reCLM.integral_comp_comm h).symm

/-- The imaginary part of an integral is the integral of the imaginary part. -/
theorem im_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {G : α → ℂ}
    (h : Integrable G μ) : (∫ x, G x ∂μ).im = ∫ x, (G x).im ∂μ :=
  (Complex.imCLM.integral_comp_comm h).symm

/-! ### A real factor pulled back from the base -/

omit [TopologicalSpace Y] in
/-- The fibre sum absorbs a real factor pulled back from the base. -/
theorem fibreSum_mul_comp_real (F : Y → ℝ) (h : ℂ → ℝ) :
    fibreSum f (fun y => F y * h (f y)) z₀ = fibreSum f F z₀ * h z₀ := by
  rw [fibreSum, fibreSum, finsum_mem_mul]
  exact finsum_mem_congr rfl fun y hy => by rw [Set.mem_singleton_iff.mp hy]

/-! ### The weighted functional -/

section Functional

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  {w : ℂ → ℝ} (hw : Continuous w) (hwnn : ∀ z, 0 ≤ w z)

include hfin hcov hf hw in
/-- The weighted fibre sum of a compactly supported continuous function is integrable. -/
theorem integrable_weight_fibreSum {F : Y → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    Integrable (fun z => w z * fibreSum f F z) :=
  (hw.mul (continuous_fibreSum hfin hcov hf hFc hFs)).integrable_of_hasCompactSupport
    (hasCompactSupport_fibreSum hf hFs).mul_left

variable (f w) in
/-- **The weighted fibre-sum functional**: a compactly supported continuous function on the total
space is sent to the plane integral of its fibre sum against the weight. -/
def weightFunctional : C_c(Y, ℝ) →ₚ[ℝ] ℝ where
  toFun H := ∫ z : ℂ, w z * fibreSum f (⇑H) z
  map_add' H₁ H₂ := by
    have hpt : ∀ z, w z * fibreSum f (⇑(H₁ + H₂)) z
        = w z * fibreSum f (⇑H₁) z + w z * fibreSum f (⇑H₂) z := by
      intro z
      have hco : (⇑(H₁ + H₂) : Y → ℝ) = fun y => H₁ y + H₂ y := rfl
      rw [hco, fibreSum_add (hfin z), mul_add]
    simp only [hpt]
    exact integral_add
      (integrable_weight_fibreSum hfin hcov hf hw (map_continuous H₁) H₁.hasCompactSupport)
      (integrable_weight_fibreSum hfin hcov hf hw (map_continuous H₂) H₂.hasCompactSupport)
  map_smul' c H := by
    have hpt : ∀ z, w z * fibreSum f (⇑(c • H)) z = c * (w z * fibreSum f (⇑H) z) := by
      intro z
      have hco : (⇑(c • H) : Y → ℝ) = fun y => c * H y := rfl
      rw [hco, fibreSum_const_mul c]
      ring
    simp only [hpt, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _
  monotone' H₁ H₂ hle := by
    refine integral_mono
      (integrable_weight_fibreSum hfin hcov hf hw (map_continuous H₁) H₁.hasCompactSupport)
      (integrable_weight_fibreSum hfin hcov hf hw (map_continuous H₂) H₂.hasCompactSupport)
      fun z => ?_
    exact mul_le_mul_of_nonneg_left (fibreSum_mono (hfin z) fun y => hle y) (hwnn z)

@[simp]
theorem weightFunctional_apply (H : C_c(Y, ℝ)) :
    weightFunctional f hfin hcov hf w hw hwnn H = ∫ z : ℂ, w z * fibreSum f (⇑H) z := rfl

/-! ### The measure -/

variable [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

variable (f w) in
/-- **The weighted measure of a covering**: the measure that the weighted fibre-sum functional
represents. -/
def weightMeasure : Measure Y :=
  RealRMK.rieszMeasure (weightFunctional f hfin hcov hf w hw hwnn)

instance regular_weightMeasure : (weightMeasure f hfin hcov hf w hw hwnn).Regular :=
  RealRMK.regular_rieszMeasure _

/-- **Integration over the total space is integration of weighted fibre sums over the plane.** -/
theorem integral_weightMeasure (H : C_c(Y, ℝ)) :
    ∫ y, H y ∂(weightMeasure f hfin hcov hf w hw hwnn) = ∫ z : ℂ, w z * fibreSum f (⇑H) z :=
  RealRMK.integral_rieszMeasure _ H

/-- **Integration over the total space is integration of fibre sums of the weighted function.** -/
theorem integral_weightMeasure_real {F : Y → ℝ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) :
    ∫ y, F y ∂(weightMeasure f hfin hcov hf w hw hwnn)
      = ∫ z : ℂ, fibreSum f (fun y => F y * w (f y)) z := by
  have h := integral_weightMeasure hfin hcov hf hw hwnn (⟨⟨F, hFc⟩, hFs⟩ : C_c(Y, ℝ))
  rw [show (fun y => F y) = ⇑(⟨⟨F, hFc⟩, hFs⟩ : C_c(Y, ℝ)) from rfl, h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
    ((fibreSum_mul_comp_real F w).trans (mul_comm _ _)).symm)

omit [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
include hfin hcov hf hw in
/-- The weighted fibre sum of a compactly supported continuous complex function is integrable. -/
theorem integrable_weight_fibreSum_complex {F : Y → ℂ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) :
    Integrable (fun z => fibreSum f (fun y => F y * (w (f y) : ℂ)) z) := by
  have hc : Continuous fun y => F y * (w (f y) : ℂ) :=
    hFc.mul (Complex.continuous_ofReal.comp (hw.comp hf))
  have hs : HasCompactSupport fun y => F y * (w (f y) : ℂ) := hFs.mul_right
  exact (continuous_fibreSum hfin hcov hf hc hs).integrable_of_hasCompactSupport
    (hasCompactSupport_fibreSum hf hs)

/-- **Integration over the total space is integration of fibre sums of the weighted function**,
for a complex-valued function. -/
theorem integral_weightMeasure_complex {F : Y → ℂ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) :
    ∫ y, F y ∂(weightMeasure f hfin hcov hf w hw hwnn)
      = ∫ z : ℂ, fibreSum f (fun y => F y * (w (f y) : ℂ)) z := by
  have hIl : Integrable F (weightMeasure f hfin hcov hf w hw hwnn) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hIr := integrable_weight_fibreSum_complex hfin hcov hf hw hFc hFs
  have hrec : Continuous fun y => (F y).re := Complex.continuous_re.comp hFc
  have hres : HasCompactSupport fun y => (F y).re :=
    hFs.comp_left (g := Complex.re) (by simp)
  have himc : Continuous fun y => (F y).im := Complex.continuous_im.comp hFc
  have hims : HasCompactSupport fun y => (F y).im :=
    hFs.comp_left (g := Complex.im) (by simp)
  refine Complex.ext ?_ ?_
  · rw [re_integral hIl, re_integral hIr,
      integral_weightMeasure_real hfin hcov hf hw hwnn hrec hres]
    refine integral_congr_ae (.of_forall fun z => ?_)
    have h := map_fibreSum (f := f) (z₀ := z) Complex.reAddGroupHom
      (fun y => F y * (w (f y) : ℂ)) (hfin z)
    simp only [Complex.coe_reAddGroupHom] at h
    show fibreSum f (fun y => (F y).re * w (f y)) z
      = (fibreSum f (fun y => F y * (w (f y) : ℂ)) z).re
    rw [h]
    exact finsum_mem_congr rfl fun y _ => by simp
  · rw [im_integral hIl, im_integral hIr,
      integral_weightMeasure_real hfin hcov hf hw hwnn himc hims]
    refine integral_congr_ae (.of_forall fun z => ?_)
    have h := map_fibreSum (f := f) (z₀ := z) Complex.imAddGroupHom
      (fun y => F y * (w (f y) : ℂ)) (hfin z)
    simp only [Complex.coe_imAddGroupHom] at h
    show fibreSum f (fun y => (F y).im * w (f y)) z
      = (fibreSum f (fun y => F y * (w (f y) : ℂ)) z).im
    rw [h]
    exact finsum_mem_congr rfl fun y _ => by simp

end Functional

end Rigidity.RET

end
