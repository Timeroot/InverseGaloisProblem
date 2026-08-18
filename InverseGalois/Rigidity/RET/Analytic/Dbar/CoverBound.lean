/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverGlue
import InverseGalois.Rigidity.RET.Analytic.Dbar.Pointwise

/-!
# A solution with a bound

The solution of the Cauchy–Riemann equation on a covering was assembled from local solutions of
an element of a weighted `L²` space, and the norm of that element was bounded by the estimate.
Combining the two gives a solution carrying a bound: over any disc on which the solution is
holomorphic, its value at the centre is controlled by a single constant, by the area of the disc
and by a lower bound for the weight there.  It is this uniform bound, applied to discs whose size
is dictated by the position of the point, that will produce the growth condition.

## Main definitions

* `Rigidity.RET.HasDiscBound` — the bound carried by the solution.

## Main results

* `Rigidity.RET.differentiableAt_symm_of_isDbarAt_zero` — where the source of the equation
  vanishes, the solution is holomorphic in a coordinate.
* `Rigidity.RET.exists_isDbarAt_bound` — **a solution of the Cauchy–Riemann equation on a
  covering, together with a bound on discs.**
-/

open MeasureTheory Metric Filter Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ} {Φ : ℂ → ℂ}

/-! ### The bound on discs -/

/-- **A bound on discs**: over every disc lying in a coordinate and over which the function is
holomorphic, the value at the centre is bounded by a single constant, divided by the area of the
disc and multiplied by a bound for the reciprocal of the weight. -/
def HasDiscBound (f : Y → ℂ) (Φ : ℂ → ℂ) (u : Y → ℂ) (B : ℝ) : Prop :=
  ∀ e : OpenPartialHomeomorph Y ℂ, f = ⇑e → ∀ (c : ℂ) (R r K : ℝ), 0 < r → r < R →
    ball c R ⊆ e.target →
    (∀ z ∈ ball c R, DifferentiableAt ℂ (fun t : ℂ => u (e.symm t)) z) →
    (∀ z ∈ ball c r, 1 ≤ K * weightOf Φ z) →
    (Real.pi * r ^ 2) * ‖u (e.symm c)‖ ^ 2 ≤ K * B

/-! ### Holomorphy where the source vanishes -/

/-- **Where the source of the equation vanishes the solution is holomorphic**, read in a
coordinate. -/
theorem differentiableAt_symm_of_isDbarAt_zero {u : Y → ℂ} {e : OpenPartialHomeomorph Y ℂ}
    (hfe : f = ⇑e) {z : ℂ} (hz : z ∈ e.target) (h : IsDbarAt f u 0 (e.symm z)) :
    DifferentiableAt ℂ (fun t : ℂ => u (e.symm t)) z := by
  obtain ⟨hd, hval⟩ := h.of_isChartAt (isChartAt_symm hfe hz)
  rw [apply_symm_of_isChartAt hfe hz] at hd hval
  exact differentiableAt_of_dbar_eq_zero hd hval

/-! ### The solution and its bound -/

section Solve

variable [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **A solution of the Cauchy–Riemann equation on a covering, together with a bound on discs.**
On any disc over which the solution is holomorphic, the value at the centre is bounded by a single
constant, divided by the area of the disc and multiplied by a bound for the reciprocal of the
weight. -/
theorem exists_isDbarAt_bound (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hpos : ∀ t, 0 < curv Φ t) (hg1 : ∀ y, IsC1At f g y) (hgs : HasCompactSupport g) :
    ∃ (u : Y → ℂ) (B : ℝ), 0 ≤ B ∧ (∀ y, IsDbarAt f u (g y) y) ∧ HasDiscBound f Φ u B := by
  obtain ⟨U, -, hW⟩ := exists_weak_solution hfin hcov hf hlh hΦ hreal hpos hg1 hgs
  have h := nonempty_localSolData hfin hcov hf hlh hΦ hreal hg1 hW
  refine ⟨glueSol (⇑U) h, ‖U‖ ^ 2, by positivity, isDbarAt_glueSol h, ?_⟩
  intro e hfe c R r K hr hrR hball hholo hK
  have hae : ∀ᵐ z : ℂ, z ∈ ball c R →
      (U : Y → ℂ) (e.symm z) = glueSol (⇑U) h (e.symm z) := by
    filter_upwards [ae_eq_glueSol h hfe] with z hz hzR
    exact hz (hball hzR)
  exact norm_sq_le_of_holo_ball hfin hcov hf hΦ.continuous hfe hr hrR hball hholo hae hK

end Solve

end Rigidity.RET

end
