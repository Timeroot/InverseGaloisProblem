/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Lebesgue points in the plane

Almost every point of a locally integrable function of a complex variable is one at which the
function is, on average over small discs, close to its value: the mean deviation over the disc of
radius `r` about the point is `o(1)`, so the total deviation is `o(r²)`.  This is the form in which
the Lebesgue differentiation theorem is used to read the value of a weak solution of the
Cauchy–Riemann equation against an approximate identity concentrated on a small annulus.

## Main definitions

* `Rigidity.RET.IsLebesguePoint` — the property of being such a point.

## Main results

* `Rigidity.RET.ae_isLebesguePoint` — almost every point is one.
* `Rigidity.RET.IsLebesguePoint.tendsto_two` — the same statement for the discs of radius `2ε`.
-/

open MeasureTheory Metric Filter Topology

noncomputable section

namespace Rigidity.RET

variable {u : ℂ → ℂ} {z : ℂ}

/-- **A Lebesgue point** of a function: the deviation of the function from its value there,
integrated over the disc of radius `r` about it, is small compared with `r²`. -/
def IsLebesguePoint (u : ℂ → ℂ) (z : ℂ) : Prop :=
  Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * ∫ y in closedBall z r, ‖u y - u z‖) (𝓝[>] 0) (𝓝 0)

/-- The area of a disc. -/
theorem measureReal_closedBall (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (closedBall z r)).toReal = Real.pi * r ^ 2 := by
  rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- **Almost every point is a Lebesgue point.** -/
theorem ae_isLebesguePoint (hu : LocallyIntegrable u volume) : ∀ᵐ z : ℂ, IsLebesguePoint u z := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hu 1] with z hz
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), z ∈ closedBall z (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [mem_closedBall, dist_self, one_mul]
    exact le_of_lt hr
  have h := hz (fun _ : ℝ => z) (fun r : ℝ => r) tendsto_id hmem
  have hcongr : (fun r : ℝ => (r ^ 2)⁻¹ * ∫ y in closedBall z r, ‖u y - u z‖)
      =ᶠ[𝓝[>] (0 : ℝ)] fun r : ℝ => Real.pi * ⨍ y in closedBall z r, ‖u y - u z‖ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
    rw [setAverage_eq, measureReal_def, measureReal_closedBall z (le_of_lt hr), smul_eq_mul]
    field_simp
  refine Tendsto.congr' hcongr.symm ?_
  simpa using (tendsto_const_nhds (x := Real.pi) (f := 𝓝[>] (0 : ℝ))).mul h

/-- Halving the radius does not affect the estimate. -/
theorem IsLebesguePoint.tendsto_two (h : IsLebesguePoint u z) :
    Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ * ∫ y in closedBall z (2 * ε), ‖u y - u z‖) (𝓝[>] 0) (𝓝 0) := by
  have hbase : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
    exact hc.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 2 * ε ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos two_pos (Set.mem_Ioi.mp hε)
  have hmap : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase hpos
  have hcomp := h.comp hmap
  have hfour : Tendsto (fun ε : ℝ => 4 * (((2 * ε) ^ 2)⁻¹ *
      ∫ y in closedBall z (2 * ε), ‖u y - u z‖)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (4 : ℝ)) (f := 𝓝[>] (0 : ℝ))).mul hcomp
  refine Tendsto.congr' ?_ hfour
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (ε : ℝ) ≠ 0 := ne_of_gt hε
  field_simp
  ring

end Rigidity.RET

end
