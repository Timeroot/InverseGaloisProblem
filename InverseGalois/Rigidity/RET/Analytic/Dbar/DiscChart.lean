/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Cover

/-!
# Coordinates on a disc

A local homeomorphism has coordinates around each point, but nothing bounds their size from below.
Over a disc a covering has more: a disc is simply connected, so the identity of the disc lifts
through the projection to a section, and a section of a local homeomorphism is a coordinate whose
target is the whole disc.  Coordinates of a prescribed size are what turn an integral bound into a
pointwise bound.

## Main definitions

* `Rigidity.RET.chartOfSection` — the coordinate carried by a section of the projection.

## Main results

* `Rigidity.RET.exists_section_ball` — a covering has a section over a disc of the base.
* `Rigidity.RET.exists_chart_ball` — a covering has, at each point, a coordinate whose target is a
  prescribed disc around its image.
-/

open Metric Topology Set

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {σ : ℂ → Y} {D : Set ℂ}

/-! ### The coordinate carried by a section -/

/-- **The image of a section of a local homeomorphism is open.** -/
theorem isOpen_section_image (hlh : IsLocalHomeomorph f) (hD : IsOpen D)
    (hσ : ContinuousOn σ D) (hfσ : ∀ w ∈ D, f (σ w) = w) : IsOpen (σ '' D) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w₀, hw₀, rfl⟩
  obtain ⟨e, hmem, hfe⟩ := hlh (σ w₀)
  set W : Set ℂ := D ∩ σ ⁻¹' e.source with hW
  have hWopen : IsOpen W := hσ.isOpen_inter_preimage hD e.open_source
  have hw₀W : w₀ ∈ W := ⟨hw₀, hmem⟩
  have hagree : ∀ w ∈ W, σ w = e.symm w := by
    intro w hw
    have hew : e (σ w) = w := by rw [← congrFun hfe (σ w)]; exact hfσ w hw.1
    calc σ w = e.symm (e (σ w)) := (e.left_inv hw.2).symm
      _ = e.symm w := by rw [hew]
  have hWtarget : W ⊆ e.target := by
    intro w hw
    have hew : e (σ w) = w := by rw [← congrFun hfe (σ w)]; exact hfσ w hw.1
    rw [← hew]
    exact e.map_source hw.2
  have hopenW : IsOpen (σ '' W) := by
    rw [image_congr hagree]
    exact e.isOpen_image_symm_of_subset_target hWopen hWtarget
  refine Filter.mem_of_superset (hopenW.mem_nhds ⟨w₀, hw₀W, rfl⟩) ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hw.1, rfl⟩

/-- **The coordinate carried by a section of the projection**: the projection itself, read on the
image of the section. -/
def chartOfSection (f : Y → ℂ) (σ : ℂ → Y) (D : Set ℂ) (hD : IsOpen D) (hf : Continuous f)
    (hσ : ContinuousOn σ D) (hfσ : ∀ w ∈ D, f (σ w) = w) (hopen : IsOpen (σ '' D)) :
    OpenPartialHomeomorph Y ℂ where
  toFun := f
  invFun := σ
  source := σ '' D
  target := D
  map_source' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hfσ w hw]
    exact hw
  map_target' := fun w hw => ⟨w, hw, rfl⟩
  left_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hfσ w hw]
  right_inv' := hfσ
  open_source := hopen
  open_target := hD
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hσ

@[simp] theorem coe_chartOfSection (hD : IsOpen D) (hf : Continuous f) (hσ : ContinuousOn σ D)
    (hfσ : ∀ w ∈ D, f (σ w) = w) (hopen : IsOpen (σ '' D)) :
    ⇑(chartOfSection f σ D hD hf hσ hfσ hopen) = f := rfl

@[simp] theorem chartOfSection_target (hD : IsOpen D) (hf : Continuous f) (hσ : ContinuousOn σ D)
    (hfσ : ∀ w ∈ D, f (σ w) = w) (hopen : IsOpen (σ '' D)) :
    (chartOfSection f σ D hD hf hσ hfσ hopen).target = D := rfl

@[simp] theorem chartOfSection_symm (hD : IsOpen D) (hf : Continuous f) (hσ : ContinuousOn σ D)
    (hfσ : ∀ w ∈ D, f (σ w) = w) (hopen : IsOpen (σ '' D)) (w : ℂ) :
    (chartOfSection f σ D hD hf hσ hfσ hopen).symm w = σ w := rfl

/-! ### Sections over a disc -/

/-- **A covering has a section over a disc of the base** through any prescribed point of the fibre
of its centre. -/
theorem exists_section_ball {T : Set ℂ} (hcov : IsCoveringMapOn f T) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball c r ⊆ T) {y : Y} (hy : f y = c) :
    ∃ σ : ℂ → Y, ContinuousOn σ (ball c r) ∧ (∀ w ∈ ball c r, f (σ w) = w) ∧ σ c = y := by
  classical
  haveI : LocPathConnectedSpace ↥(ball c r) := (isOpen_ball (x := c) (ε := r)).locPathConnectedSpace
  haveI : ContractibleSpace ↥(ball c r) :=
    (convex_ball c r).contractibleSpace ⟨c, mem_ball_self hr⟩
  have hc : c ∈ ball c r := mem_ball_self hr
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨fun w : ↥(ball c r) => (w : ℂ), continuous_subtype_val⟩ : C(↥(ball c r), ℂ))
    (a₀ := ⟨c, hc⟩) (e₀ := y) hy (fun a => hball a.2)
  refine ⟨fun w => if h : w ∈ ball c r then F ⟨w, h⟩ else y, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hres : ((ball c r).restrict fun w => if h : w ∈ ball c r then F ⟨w, h⟩ else y)
        = fun w : ↥(ball c r) => F w := by
      funext w
      simp only [restrict_apply, dif_pos w.2, Subtype.coe_eta]
    rw [hres]
    exact F.continuous
  · intro w hw
    simpa only [dif_pos hw] using congrFun hFlift ⟨w, hw⟩
  · simp only [dif_pos hc]
    exact hF0

/-- **A covering has, at each point, a coordinate whose target is a prescribed disc** around the
image of the point. -/
theorem exists_chart_ball (hf : Continuous f) (hlh : IsLocalHomeomorph f) {T : Set ℂ}
    (hcov : IsCoveringMapOn f T) {c : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T)
    {y : Y} (hy : f y = c) :
    ∃ e : OpenPartialHomeomorph Y ℂ, f = ⇑e ∧ e.target = ball c r ∧ e.symm c = y := by
  obtain ⟨σ, hσ, hfσ, hσc⟩ := exists_section_ball hcov hr hball hy
  have hopen : IsOpen (σ '' ball c r) := isOpen_section_image hlh isOpen_ball hσ hfσ
  exact ⟨chartOfSection f σ (ball c r) isOpen_ball hf hσ hfσ hopen, rfl, rfl, hσc⟩

end Rigidity.RET

end
