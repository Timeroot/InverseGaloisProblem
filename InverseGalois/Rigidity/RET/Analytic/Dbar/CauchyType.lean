/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic

/-!
# Cauchy-type integrals

Integrating an integrable function against the kernel `1/(w - z)` produces a function of `z` which,
away from the region where the function lives, is as good as a power series: the kernel is
holomorphic in `z` there and bounded together with its derivative, so differentiation passes under
the integral sign.  A Cauchy-type integral is therefore holomorphic off the support of its density,
and in particular is annihilated by the Cauchy–Riemann operator there.

## Main definitions

* `Rigidity.RET.cauchyType` — the Cauchy-type integral of a density.

## Main results

* `Rigidity.RET.hasDerivAt_cauchyType` — differentiation under the integral sign.
* `Rigidity.RET.dbar_cauchyType` — a Cauchy-type integral is annihilated by `∂/∂z̄` off the
  support of its density.
-/

open MeasureTheory Metric

noncomputable section

namespace Rigidity.RET

/-- **The Cauchy-type integral** of a density. -/
def cauchyType (φ : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w : ℂ, φ w / (w - z)

variable {φ : ℂ → ℂ} {z₀ : ℂ} {d : ℝ}

/-- The integrand of a Cauchy-type integral is measurable. -/
theorem aestronglyMeasurable_cauchyTypeIntegrand (hφ : AEStronglyMeasurable φ volume) (z : ℂ) :
    AEStronglyMeasurable (fun w : ℂ => φ w / (w - z)) volume := by
  have hinv : Measurable fun w : ℂ => (w - z)⁻¹ := (measurable_id.sub measurable_const).inv
  simpa only [div_eq_mul_inv] using hφ.mul hinv.aestronglyMeasurable

/-- The integrand of the differentiated Cauchy-type integral is measurable. -/
theorem aestronglyMeasurable_cauchyTypeDeriv (hφ : AEStronglyMeasurable φ volume) (z : ℂ) :
    AEStronglyMeasurable (fun w : ℂ => φ w / (w - z) ^ 2) volume := by
  have hinv : Measurable fun w : ℂ => ((w - z) ^ 2)⁻¹ :=
    ((measurable_id.sub measurable_const).pow_const 2).inv
  simpa only [div_eq_mul_inv] using hφ.mul hinv.aestronglyMeasurable

/-- Away from the region where the density lives, the kernel is bounded. -/
theorem norm_cauchyTypeIntegrand_le (hd : 0 < d) (hvanish : ∀ w, ‖w - z₀‖ < d → φ w = 0)
    {z : ℂ} (hz : ‖z - z₀‖ < d / 2) (w : ℂ) :
    ‖φ w / (w - z)‖ ≤ ‖φ w‖ * (2 / d) := by
  by_cases hw : φ w = 0
  · simp [hw]
  · have hfar : d ≤ ‖w - z₀‖ := by
      by_contra hlt
      exact hw (hvanish w (lt_of_not_ge hlt))
    have hge : d / 2 ≤ ‖w - z‖ := by
      have h1 : ‖w - z₀‖ - ‖z - z₀‖ ≤ ‖w - z‖ := by
        have := norm_sub_norm_le (w - z₀) (z - z₀)
        simpa using this
      linarith
    have hpos : (0 : ℝ) < ‖w - z‖ := lt_of_lt_of_le (by linarith) hge
    rw [norm_div]
    rw [div_le_iff₀ hpos]
    have : ‖φ w‖ * (2 / d) * (d / 2) = ‖φ w‖ := by field_simp
    calc ‖φ w‖ = ‖φ w‖ * (2 / d) * (d / 2) := this.symm
      _ ≤ ‖φ w‖ * (2 / d) * ‖w - z‖ := by
          refine mul_le_mul_of_nonneg_left hge ?_
          positivity

/-- Away from the region where the density lives, the derivative of the kernel is bounded. -/
theorem norm_cauchyTypeDeriv_le (hd : 0 < d) (hvanish : ∀ w, ‖w - z₀‖ < d → φ w = 0)
    {z : ℂ} (hz : ‖z - z₀‖ < d / 2) (w : ℂ) :
    ‖φ w / (w - z) ^ 2‖ ≤ ‖φ w‖ * (2 / d) ^ 2 := by
  by_cases hw : φ w = 0
  · simp [hw]
  · have hfar : d ≤ ‖w - z₀‖ := by
      by_contra hlt
      exact hw (hvanish w (lt_of_not_ge hlt))
    have hge : d / 2 ≤ ‖w - z‖ := by
      have h1 : ‖w - z₀‖ - ‖z - z₀‖ ≤ ‖w - z‖ := by
        have := norm_sub_norm_le (w - z₀) (z - z₀)
        simpa using this
      linarith
    have hpos : (0 : ℝ) < ‖w - z‖ := lt_of_lt_of_le (by linarith) hge
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have hkey : ‖φ w‖ * (2 / d) ^ 2 * (d / 2) ^ 2 = ‖φ w‖ := by field_simp
    calc ‖φ w‖ = ‖φ w‖ * (2 / d) ^ 2 * (d / 2) ^ 2 := hkey.symm
      _ ≤ ‖φ w‖ * (2 / d) ^ 2 * ‖w - z‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hge 2) ?_
          positivity

/-- **Differentiation under the integral sign for a Cauchy-type integral.** -/
theorem hasDerivAt_cauchyType (hφ : Integrable φ) (hd : 0 < d)
    (hvanish : ∀ w, ‖w - z₀‖ < d → φ w = 0) :
    HasDerivAt (cauchyType φ) (∫ w : ℂ, φ w / (w - z₀) ^ 2) z₀ := by
  have hhalf : (0 : ℝ) < d / 2 := by linarith
  have hmem : ∀ z ∈ ball z₀ (d / 2), ‖z - z₀‖ < d / 2 := fun z hz => by
    simpa [Complex.dist_eq] using hz
  have hint : Integrable (fun w : ℂ => φ w / (w - z₀)) volume := by
    refine Integrable.mono' (hφ.norm.mul_const (2 / d))
      (aestronglyMeasurable_cauchyTypeIntegrand hφ.aestronglyMeasurable z₀) ?_
    exact .of_forall fun w =>
      norm_cauchyTypeIntegrand_le hd hvanish (by simpa using hhalf) w
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z w => φ w / (w - z)) (F' := fun z w => φ w / (w - z) ^ 2)
    (bound := fun w => ‖φ w‖ * (2 / d) ^ 2) (ball_mem_nhds z₀ hhalf)
    (.of_forall fun z => aestronglyMeasurable_cauchyTypeIntegrand hφ.aestronglyMeasurable z)
    hint (aestronglyMeasurable_cauchyTypeDeriv hφ.aestronglyMeasurable z₀)
    (.of_forall fun w z hz => norm_cauchyTypeDeriv_le hd hvanish (hmem z hz) w)
    (hφ.norm.mul_const _) (.of_forall fun w z hz => ?_)).2
  by_cases hw : φ w = 0
  · simpa [hw] using hasDerivAt_const z (0 : ℂ)
  · have hfar : d ≤ ‖w - z₀‖ := by
      by_contra hlt
      exact hw (hvanish w (lt_of_not_ge hlt))
    have hne : w - z ≠ 0 := by
      intro h
      have hzw : z = w := by
        have := sub_eq_zero.mp h
        exact this.symm
      rw [hzw] at hz
      have : ‖w - z₀‖ < d / 2 := hmem w hz
      linarith
    have hsub : HasDerivAt (fun z : ℂ => w - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub w
    have hinv : HasDerivAt (fun z : ℂ => (w - z)⁻¹) (-(-1) / (w - z) ^ 2) z := hsub.inv hne
    have hmul := hinv.const_mul (φ w)
    have heq : φ w * (-(-1) / (w - z) ^ 2) = φ w / (w - z) ^ 2 := by
      rw [neg_neg]
      ring
    rw [heq] at hmul
    simpa only [div_eq_mul_inv] using hmul

/-- **A Cauchy-type integral is holomorphic off the support of its density.** -/
theorem differentiableAt_cauchyType (hφ : Integrable φ) (hd : 0 < d)
    (hvanish : ∀ w, ‖w - z₀‖ < d → φ w = 0) :
    DifferentiableAt ℂ (cauchyType φ) z₀ :=
  (hasDerivAt_cauchyType hφ hd hvanish).differentiableAt

/-- **A Cauchy-type integral is annihilated by the Cauchy–Riemann operator** off the support of its
density. -/
theorem dbar_cauchyType (hφ : Integrable φ) (hd : 0 < d)
    (hvanish : ∀ w, ‖w - z₀‖ < d → φ w = 0) :
    dbar (cauchyType φ) z₀ = 0 :=
  dbar_eq_zero (differentiableAt_cauchyType hφ hd hvanish)

end Rigidity.RET

end
