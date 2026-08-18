/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverWeyl

/-!
# Gluing the local solutions on a covering

In each coordinate the weak solution of the Cauchy–Riemann equation agrees almost everywhere with
a differentiable function solving the equation there.  Two such local solutions agree at every
point they are both defined at: they agree almost everywhere near it, and a nonempty open set of
the plane has positive area, so two continuous functions agreeing almost everywhere near a point
agree at it.  The local values therefore assemble into a single function of the total space, which
solves the Cauchy–Riemann equation everywhere.

## Main definitions

* `Rigidity.RET.IsLocalSol` — a local solution in a coordinate.
* `Rigidity.RET.glueSol` — the function of the total space assembled from the local solutions.

## Main results

* `Rigidity.RET.IsLocalSol.eq_value` — two local solutions take the same value at a common point.
* `Rigidity.RET.exists_isDbarAt` — **a solution of the Cauchy–Riemann equation on a covering.**
-/

open MeasureTheory Metric Filter Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g U : Y → ℂ} {v v₁ v₂ : ℂ → ℂ}
  {e e₁ e₂ : OpenPartialHomeomorph Y ℂ} {s s₁ s₂ : Set ℂ} {Φ : ℂ → ℂ}

/-! ### Local solutions -/

/-- **A local solution of the Cauchy–Riemann equation** in a coordinate: a differentiable function
of an open set of the plane, solving the equation there and agreeing almost everywhere with the
weak solution read in the coordinate. -/
structure IsLocalSol (f g U : Y → ℂ) (v : ℂ → ℂ) (e : OpenPartialHomeomorph Y ℂ) (s : Set ℂ) :
    Prop where
  /-- The set is open. -/
  isOpen : IsOpen s
  /-- The coordinate is a coordinate of the projection. -/
  chart : f = ⇑e
  /-- The set lies in the target of the coordinate. -/
  subset : s ⊆ e.target
  /-- The solution is differentiable. -/
  diff : ∀ z ∈ s, DifferentiableAt ℝ v z
  /-- The solution solves the equation. -/
  dbarEq : ∀ z ∈ s, dbar v z = g (e.symm z)
  /-- The solution represents the weak solution. -/
  aeEq : ∀ᵐ z : ℂ, z ∈ s → U (e.symm z) = v z

theorem IsLocalSol.apply_symm (h : IsLocalSol f g U v e s) {z : ℂ} (hz : z ∈ s) :
    f (e.symm z) = z := apply_symm_of_isChartAt h.chart (h.subset hz)

theorem IsLocalSol.isChartAt (h : IsLocalSol f g U v e s) {z : ℂ} (hz : z ∈ s) :
    IsChartAt f e (e.symm z) := isChartAt_symm h.chart (h.subset hz)

/-- **Two local solutions agree at a point of the total space they are both defined at.** -/
theorem IsLocalSol.eq_value (h₁ : IsLocalSol f g U v₁ e₁ s₁) (h₂ : IsLocalSol f g U v₂ e₂ s₂)
    {z : ℂ} (hz₁ : z ∈ s₁) (hz₂ : z ∈ s₂) (hpt : e₁.symm z = e₂.symm z) : v₁ z = v₂ z := by
  by_contra hne
  set y : Y := e₁.symm z with hy
  have hfy : f y = z := h₁.apply_symm hz₁
  have hc₁ : IsChartAt f e₁ y := h₁.isChartAt hz₁
  have hc₂ : IsChartAt f e₂ y := by
    rw [hpt]
    exact h₂.isChartAt hz₂
  have hsymm : ∀ᶠ w in 𝓝 z, e₁.symm w = e₂.symm w := by
    have h := hc₁.eventuallyEq_symm hc₂
    rw [hfy] at h
    exact h
  have hcont : ContinuousAt (fun w => v₁ w - v₂ w) z :=
    ((h₁.diff z hz₁).sub (h₂.diff z hz₂)).continuousAt
  have hnear : ∀ᶠ w in 𝓝 z, v₁ w ≠ v₂ w := by
    have h := hcont.eventually_ne (sub_ne_zero.2 hne)
    filter_upwards [h] with w hw
    exact sub_ne_zero.mp hw
  have hev : ∀ᶠ w in 𝓝 z, v₁ w ≠ v₂ w ∧ w ∈ s₁ ∧ w ∈ s₂ ∧ e₁.symm w = e₂.symm w := by
    filter_upwards [hnear, h₁.isOpen.mem_nhds hz₁, h₂.isOpen.mem_nhds hz₂, hsymm] with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hpos : 0 < volume {w : ℂ | v₁ w ≠ v₂ w ∧ w ∈ s₁ ∧ w ∈ s₂ ∧ e₁.symm w = e₂.symm w} :=
    Measure.measure_pos_of_mem_nhds volume hev
  have hn₁ : volume {w : ℂ | ¬ (w ∈ s₁ → U (e₁.symm w) = v₁ w)} = 0 := ae_iff.mp h₁.aeEq
  have hn₂ : volume {w : ℂ | ¬ (w ∈ s₂ → U (e₂.symm w) = v₂ w)} = 0 := ae_iff.mp h₂.aeEq
  have hsub : {w : ℂ | v₁ w ≠ v₂ w ∧ w ∈ s₁ ∧ w ∈ s₂ ∧ e₁.symm w = e₂.symm w}
      ⊆ {w : ℂ | ¬ (w ∈ s₁ → U (e₁.symm w) = v₁ w)} ∪
        {w : ℂ | ¬ (w ∈ s₂ → U (e₂.symm w) = v₂ w)} := by
    rintro w ⟨hw, hw₁, hw₂, hwe⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hw (((hcon.1 hw₁).symm.trans (by rw [hwe])).trans (hcon.2 hw₂))
  exact absurd (measure_mono_null hsub (by rw [Set.union_def]; exact measure_union_null hn₁ hn₂))
    (ne_of_gt hpos)

/-! ### The glued solution -/

variable (f g U) in
/-- **A local solution at a point**, together with the coordinate and the open set carrying it. -/
structure LocalSolData (y : Y) where
  /-- The local solution. -/
  v : ℂ → ℂ
  /-- The coordinate. -/
  e : OpenPartialHomeomorph Y ℂ
  /-- The open set of the plane. -/
  s : Set ℂ
  /-- The data is a local solution. -/
  isSol : IsLocalSol f g U v e s
  /-- The point lies over the open set. -/
  mem : f y ∈ s
  /-- The coordinate returns the point. -/
  symm_apply : e.symm (f y) = y

/-- A chosen local solution at each point. -/
def solData (h : ∀ y, Nonempty (LocalSolData f g U y)) (y : Y) : LocalSolData f g U y :=
  Classical.choice (h y)

variable (U) in
/-- **The solution of the Cauchy–Riemann equation on the total space** assembled from the local
solutions. -/
def glueSol (h : ∀ y, Nonempty (LocalSolData f g U y)) (y : Y) : ℂ :=
  (solData h y).v (f y)

/-- **The glued solution is the local one** wherever a local solution is defined. -/
theorem glueSol_eq (h : ∀ y, Nonempty (LocalSolData f g U y)) (hsol : IsLocalSol f g U v e s)
    {z : ℂ} (hz : z ∈ s) : glueSol U h (e.symm z) = v z := by
  have hfy : f (e.symm z) = z := hsol.apply_symm hz
  have hd := solData h (e.symm z)
  rw [glueSol, hfy]
  refine IsLocalSol.eq_value (solData h (e.symm z)).isSol hsol ?_ hz ?_
  · have := (solData h (e.symm z)).mem
    rwa [hfy] at this
  · have := (solData h (e.symm z)).symm_apply
    rwa [hfy] at this

/-- **The glued solution solves the Cauchy–Riemann equation** at every point. -/
theorem isDbarAt_glueSol (h : ∀ y, Nonempty (LocalSolData f g U y)) (y : Y) :
    IsDbarAt f (glueSol U h) (g y) y := by
  obtain ⟨v, e, s, hsol, hmem, hsymm⟩ := solData h y
  have hchart : IsChartAt f e y := by
    have := hsol.isChartAt hmem
    rwa [hsymm] at this
  have hev : (fun w => glueSol U h (e.symm w)) =ᶠ[𝓝 (f y)] v := by
    filter_upwards [hsol.isOpen.mem_nhds hmem] with z hz
    exact glueSol_eq h hsol hz
  refine ⟨e, hchart, hev.differentiableAt_iff.2 (hsol.diff (f y) hmem), ?_⟩
  rw [dbar_congr hev, hsol.dbarEq (f y) hmem, hsymm]

/-! ### The solution on a covering -/

section Solve

variable [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Every point of a covering carries a local solution. -/
theorem nonempty_localSolData (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hg1 : ∀ y, IsC1At f g y)
    {W : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous)}
    (hW : ∀ w : Y → ℂ, (∀ y, IsC2At f w y) → HasCompactSupport w →
      (∫ y, deltaOpY hlh Φ w y * conj (W y)
          ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous)) = wipY f Φ w g)
    (y : Y) : Nonempty (LocalSolData f g (⇑W) y) := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have hchart : IsChartAt f e y := ⟨hy, hfe⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (f y) hchart.mem_target
  have hball : closedBall (f y) (r / 2) ⊆ e.target :=
    (closedBall_subset_ball (by linarith)).trans hrsub
  obtain ⟨v, hv1, hv2, hv3⟩ := exists_local_dbar_solution hfin hcov hf hlh hΦ hreal hg1 hfe hW
    (show (0 : ℝ) < r / 2 by linarith) hball
  refine ⟨⟨v, e, ball (f y) (r / 2 / 8), ⟨isOpen_ball, hfe, ?_, hv1, hv2, hv3⟩, ?_, ?_⟩⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hball
  · exact mem_ball_self (by linarith)
  · exact hchart.symm_apply

/-- **A solution of the Cauchy–Riemann equation on the total space of a covering**, obtained from
the weak solution by regularity in each coordinate. -/
theorem exists_isDbarAt (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hpos : ∀ t, 0 < curv Φ t) (hg1 : ∀ y, IsC1At f g y) (hgs : HasCompactSupport g) :
    ∃ u : Y → ℂ, ∀ y, IsDbarAt f u (g y) y := by
  obtain ⟨W, _, hW⟩ := exists_weak_solution hfin hcov hf hlh hΦ hreal hpos hg1 hgs
  have h := nonempty_localSolData hfin hcov hf hlh hΦ hreal hg1 hW
  exact ⟨glueSol (⇑W) h, isDbarAt_glueSol h⟩

end Solve

end Rigidity.RET

end
