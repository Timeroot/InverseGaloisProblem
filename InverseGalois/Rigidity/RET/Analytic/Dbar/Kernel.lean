/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Pompeiu

/-!
# The Cauchy kernel is locally integrable, and the transform is a convolution

The kernel `1/(π z)` of the Cauchy transform has a pole at the origin, but the pole is mild enough
in two real dimensions to leave the kernel integrable on every compact set: in polar coordinates the
Jacobian `r` cancels it exactly, and what is left is the area of a rectangle.  That is the one
analytic fact separating the Cauchy transform from the general theory of convolutions, and with it
the transform is literally a convolution with the kernel, so the results on differentiating a
convolution apply to it.

## Main definitions

* `Rigidity.RET.cauchyKernel` — the function `z ↦ 1/(π z)`.

## Main results

* `Rigidity.RET.locallyIntegrable_cauchyKernel` — the kernel is locally integrable.
* `Rigidity.RET.cauchyTransform_eq_convolution` — the Cauchy transform is convolution with it.
-/

open MeasureTheory Set

open scoped Real Convolution ENNReal

noncomputable section

namespace Rigidity.RET

/-- The kernel of the Cauchy transform: the fundamental solution `1/(π z)` of the Cauchy–Riemann
operator, up to sign. -/
def cauchyKernel (z : ℂ) : ℂ := ((π : ℂ) * z)⁻¹

/-! ### Local integrability -/

/-- **The pole of `1/z` is integrable in two real dimensions.**  In polar coordinates the Jacobian
cancels it, leaving the area of a rectangle. -/
theorem lintegral_enorm_inv_closedBall_ne_top (M : ℝ) :
    (∫⁻ z in Metric.closedBall (0 : ℂ) M, ‖z⁻¹‖ₑ) ≠ ⊤ := by
  have hball : MeasurableSet (Metric.closedBall (0 : ℂ) M) := measurableSet_closedBall
  set F : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) M).indicator (fun z => ‖z⁻¹‖ₑ) with hF
  have hrw : (∫⁻ z in Metric.closedBall (0 : ℂ) M, ‖z⁻¹‖ₑ) = ∫⁻ z, F z :=
    (lintegral_indicator hball _).symm
  set B : Set (ℝ × ℝ) := Ioo (0 : ℝ) (M + 1) ×ˢ Ioo (-π) π with hB
  have hBmeas : MeasurableSet B := measurableSet_Ioo.prod measurableSet_Ioo
  have hkey : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) ≤ B.indicator (fun _ => (1 : ℝ≥0∞)) p := by
    intro p hp
    rw [Complex.polarCoord_target] at hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) M
    · have hle : p.1 ≤ M := by
        rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem
        exact hmem
      have hpB : p ∈ B := ⟨⟨hp1, by linarith⟩, hp.2⟩
      rw [Set.indicator_of_mem hpB, hF, Set.indicator_of_mem hmem]
      have hval : ‖(Complex.polarCoord.symm p)⁻¹‖ₑ = ENNReal.ofReal p.1⁻¹ := by
        rw [← ofReal_norm_eq_enorm, norm_inv, hnorm]
      rw [hval, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le, mul_inv_cancel₀ hp1.ne',
        ENNReal.ofReal_one]
    · rw [hF, Set.indicator_of_notMem hmem, smul_zero]
      exact zero_le _
  have hbound : (∫⁻ z, F z) ≤ volume B := by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    calc (∫⁻ p in Complex.polarCoord.target,
            ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p))
        ≤ ∫⁻ p in Complex.polarCoord.target, B.indicator (fun _ => (1 : ℝ≥0∞)) p :=
          setLIntegral_mono' Complex.polarCoord.open_target.measurableSet hkey
      _ ≤ ∫⁻ p, B.indicator (fun _ => (1 : ℝ≥0∞)) p := setLIntegral_le_lintegral _ _
      _ = volume B := by rw [lintegral_indicator hBmeas]; simp
  have hBfin : volume B ≠ ⊤ := by
    rw [hB, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [hrw]
  exact ne_top_of_le_ne_top hBfin hbound

theorem integrableOn_inv_closedBall (M : ℝ) :
    IntegrableOn (fun z : ℂ => z⁻¹) (Metric.closedBall 0 M) volume := by
  constructor
  · exact (measurable_inv.aestronglyMeasurable).restrict
  · exact lt_top_iff_ne_top.mpr (lintegral_enorm_inv_closedBall_ne_top M)

theorem locallyIntegrable_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  exact (integrableOn_inv_closedBall M).mono_set hM

/-- **The kernel of the Cauchy transform is locally integrable.** -/
theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  have h : cauchyKernel = fun z : ℂ => ((π : ℂ))⁻¹ * z⁻¹ := by
    funext z
    rw [cauchyKernel, mul_inv]
  rw [h]
  exact locallyIntegrable_inv.smul ((π : ℂ))⁻¹

/-! ### The transform is a convolution -/

/-- **The Cauchy transform is convolution with the Cauchy kernel.** -/
theorem cauchyTransform_eq_convolution (g : ℂ → ℂ) (w : ℂ) :
    cauchyTransform g w = (cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g) w := by
  have hneg : (∫ u : ℂ, g (w + u) / u) = - ∫ t : ℂ, g (w - t) / t := by
    have h1 : (∫ t : ℂ, g (w + -t) / -t) = ∫ u : ℂ, g (w + u) / u :=
      integral_neg_eq_self (fun u : ℂ => g (w + u) / u) volume
    rw [← h1, ← integral_neg]
    congr 1
    funext t
    rw [div_neg, ← sub_eq_add_neg]
  rw [cauchyTransform, hneg, convolution_def]
  have hint : ∀ t : ℂ, (ContinuousLinearMap.mul ℝ ℂ) (cauchyKernel t) (g (w - t))
      = ((π : ℂ))⁻¹ * (g (w - t) / t) := by
    intro t
    show cauchyKernel t * g (w - t) = _
    rw [cauchyKernel, mul_inv, div_eq_mul_inv]
    ring
  rw [funext hint, integral_const_mul]
  ring

end Rigidity.RET
