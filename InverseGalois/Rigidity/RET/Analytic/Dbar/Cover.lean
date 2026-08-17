/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic
import InverseGalois.Rigidity.RET.Analytic.CoverHolo

/-!
# The Cauchy–Riemann operator on the total space of a covering

The projection of a covering of the plane is itself a system of local coordinates on the total
space, so a first-order operator of the plane may be read on the total space by reading it in that
coordinate.  This page does so for the Cauchy–Riemann operator, in the relational form "`c` is the
value of `∂u/∂z̄` at `y`": the reading does not depend on the coordinate chosen, it is compatible
with sums and products, a function pulled back from the base has the pulled-back derivative, and —
the point of the construction — a function whose operator vanishes everywhere is holomorphic in the
sense the ring of functions of the covering uses.

## Main definitions

* `Rigidity.RET.IsDbarAt` — the value of `∂/∂z̄` at a point of the total space.
* `Rigidity.RET.IsC1At` — continuous differentiability at a point of the total space.

## Main results

* `Rigidity.RET.IsDbarAt.eq` — the value does not depend on the local coordinate.
* `Rigidity.RET.isDbarAt_comp`, `Rigidity.RET.isC1At_comp` — a function pulled back from the base
  pulls back its derivative and its differentiability.
* `Rigidity.RET.IsDbarAt.add`, `Rigidity.RET.IsDbarAt.mul`, `Rigidity.RET.IsDbarAt.sub` — the
  operator is additive and satisfies the product rule.
* `Rigidity.RET.isHolo_of_isDbarAt_zero` — a function killed everywhere by the operator is
  holomorphic.
-/

open Topology

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {a b c : ℂ} {y : Y}

/-- **The Cauchy–Riemann operator on the total space**: `c` is the value of `∂u/∂z̄` at `y`, read
in the local coordinate given by the projection. -/
def IsDbarAt (f u : Y → ℂ) (c : ℂ) (y : Y) : Prop :=
  ∃ e : OpenPartialHomeomorph Y ℂ, IsChartAt f e y ∧
    DifferentiableAt ℝ (fun w => u (e.symm w)) (f y) ∧ dbar (fun w => u (e.symm w)) (f y) = c

/-- **A function on the total space is continuously differentiable at a point** when it is so in
the local coordinate given by the projection. -/
def IsC1At (f u : Y → ℂ) (y : Y) : Prop :=
  ∃ e : OpenPartialHomeomorph Y ℂ, IsChartAt f e y ∧ ContDiffAt ℝ 1 (fun w => u (e.symm w)) (f y)

/-! ### Two transfers along a coordinate -/

/-- Two functions agreeing near a point of the total space agree near the corresponding point of
the plane, in any local coordinate there. -/
theorem eventuallyEq_symm_of_eventuallyEq {e : OpenPartialHomeomorph Y ℂ} (he : IsChartAt f e y)
    (huv : ∀ᶠ y' in 𝓝 y, u y' = v y') :
    (fun w => u (e.symm w)) =ᶠ[𝓝 (f y)] fun w => v (e.symm w) := by
  have htend : Filter.Tendsto e.symm (𝓝 (f y)) (𝓝 y) := by
    have := e.continuousAt_symm he.mem_target
    rwa [ContinuousAt, he.symm_apply] at this
  exact htend.eventually huv

/-- A function pulled back from the base is, in a local coordinate, that function itself. -/
theorem eventuallyEq_comp_symm {e : OpenPartialHomeomorph Y ℂ} (he : IsChartAt f e y)
    (β : ℂ → ℂ) : (fun w => β (f (e.symm w))) =ᶠ[𝓝 (f y)] β := by
  filter_upwards [e.open_target.mem_nhds he.mem_target] with w hw
  rw [congrFun he.2 (e.symm w), e.right_inv hw]

/-! ### Independence of the coordinate -/

/-- **The operator may be read in any local coordinate at the point.** -/
theorem IsDbarAt.of_isChartAt (h : IsDbarAt f u c y) {e : OpenPartialHomeomorph Y ℂ}
    (he : IsChartAt f e y) :
    DifferentiableAt ℝ (fun w => u (e.symm w)) (f y) ∧
      dbar (fun w => u (e.symm w)) (f y) = c := by
  obtain ⟨e', he', hdiff, hval⟩ := h
  have hsymm : (fun w => u (e'.symm w)) =ᶠ[𝓝 (f y)] fun w => u (e.symm w) :=
    (he'.eventuallyEq_symm he).fun_comp u
  exact ⟨(hsymm.differentiableAt_iff).1 hdiff, by rwa [← dbar_congr hsymm]⟩

/-- **The operator has at most one value at a point.** -/
theorem IsDbarAt.eq (h : IsDbarAt f u a y) (h' : IsDbarAt f u b y) : a = b := by
  obtain ⟨e, he, _, hval⟩ := h
  exact hval.symm.trans (h'.of_isChartAt he).2

/-- A function agreeing with another near a point has the same derivative there. -/
theorem IsDbarAt.congr (h : IsDbarAt f u c y) (huv : ∀ᶠ y' in 𝓝 y, u y' = v y') :
    IsDbarAt f v c y := by
  obtain ⟨e, he, hdiff, hval⟩ := h
  have hsymm := eventuallyEq_symm_of_eventuallyEq he huv
  exact ⟨e, he, (hsymm.differentiableAt_iff).1 hdiff, by rwa [← dbar_congr hsymm]⟩

/-- A function continuously differentiable at a point stays so after a change near it. -/
theorem IsC1At.congr (h : IsC1At f u y) (huv : ∀ᶠ y' in 𝓝 y, u y' = v y') : IsC1At f v y := by
  obtain ⟨e, he, hdiff⟩ := h
  exact ⟨e, he, hdiff.congr_of_eventuallyEq (eventuallyEq_symm_of_eventuallyEq he huv).symm⟩

/-! ### The rules of the operator -/

/-- **A function pulled back from the base pulls back its derivative.** -/
theorem isDbarAt_comp (hf : IsLocalHomeomorph f) {β : ℂ → ℂ}
    (hβ : DifferentiableAt ℝ β (f y)) :
    IsDbarAt f (fun y' => β (f y')) (dbar β (f y)) y := by
  obtain ⟨e, hy, hfe⟩ := hf y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  have hsymm := eventuallyEq_comp_symm he β
  exact ⟨e, he, (hsymm.differentiableAt_iff).2 hβ, by rw [dbar_congr hsymm]⟩

/-- **A function pulled back from the base is as differentiable as it is.** -/
theorem isC1At_comp (hf : IsLocalHomeomorph f) {β : ℂ → ℂ} (hβ : ContDiffAt ℝ 1 β (f y)) :
    IsC1At f (fun y' => β (f y')) y := by
  obtain ⟨e, hy, hfe⟩ := hf y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  exact ⟨e, he, hβ.congr_of_eventuallyEq (eventuallyEq_comp_symm he β)⟩

/-- **A function pulled back from the base and holomorphic there is killed by the operator.** -/
theorem isDbarAt_comp_zero (hf : IsLocalHomeomorph f) {β : ℂ → ℂ}
    (hβ : DifferentiableAt ℂ β (f y)) : IsDbarAt f (fun y' => β (f y')) 0 y := by
  have h := isDbarAt_comp (y := y) hf (hβ.restrictScalars ℝ)
  rwa [dbar_eq_zero hβ] at h

/-- **The operator is additive.** -/
theorem IsDbarAt.add (hu : IsDbarAt f u a y) (hv : IsDbarAt f v b y) :
    IsDbarAt f (fun y' => u y' + v y') (a + b) y := by
  obtain ⟨e, he, hdu, hvu⟩ := hu
  obtain ⟨hdv, hvv⟩ := hv.of_isChartAt he
  exact ⟨e, he, hdu.add hdv, by rw [dbar_add hdu hdv, hvu, hvv]⟩

/-- **The operator is compatible with negation.** -/
theorem IsDbarAt.neg (hu : IsDbarAt f u a y) : IsDbarAt f (fun y' => -u y') (-a) y := by
  obtain ⟨e, he, hdu, hvu⟩ := hu
  exact ⟨e, he, hdu.neg, by rw [dbar_neg hdu, hvu]⟩

/-- **The operator is compatible with differences.** -/
theorem IsDbarAt.sub (hu : IsDbarAt f u a y) (hv : IsDbarAt f v b y) :
    IsDbarAt f (fun y' => u y' - v y') (a - b) y := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- **The product rule.** -/
theorem IsDbarAt.mul (hu : IsDbarAt f u a y) (hv : IsDbarAt f v b y) :
    IsDbarAt f (fun y' => u y' * v y') (u y * b + v y * a) y := by
  obtain ⟨e, he, hdu, hvu⟩ := hu
  obtain ⟨hdv, hvv⟩ := hv.of_isChartAt he
  refine ⟨e, he, hdu.mul hdv, ?_⟩
  rw [dbar_mul hdu hdv, hvu, hvv, he.symm_apply]

/-! ### From the equation to holomorphy -/

/-- **A function killed everywhere by the Cauchy–Riemann operator is holomorphic.** -/
theorem isHolo_of_isDbarAt_zero (hf : IsLocalHomeomorph f) (h : ∀ y, IsDbarAt f u 0 y) :
    IsHolo f u := by
  intro y₀
  obtain ⟨e, hy₀, hfe⟩ := hf y₀
  have he : IsChartAt f e y₀ := ⟨hy₀, hfe⟩
  have hdiff : DifferentiableOn ℂ (fun w => u (e.symm w)) e.target := by
    intro w hw
    have hmem : e.symm w ∈ e.source := e.map_target hw
    have hchart : IsChartAt f e (e.symm w) := ⟨hmem, hfe⟩
    have hfw : f (e.symm w) = w := by rw [congrFun hfe (e.symm w), e.right_inv hw]
    obtain ⟨hd, hval⟩ := (h (e.symm w)).of_isChartAt hchart
    rw [hfw] at hd hval
    exact (differentiableAt_of_dbar_eq_zero hd hval).differentiableWithinAt
  exact ⟨e, he, (hdiff.analyticOnNhd e.open_target) (f y₀) he.mem_target⟩

end Rigidity.RET

end
