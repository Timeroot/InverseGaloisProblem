/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Holomorphic functions on a space lying locally homeomorphically over the plane

The total space of a covering of a region of the plane has no complex structure of its own, but it
does not need one: the covering map is a local homeomorphism, so each point of the total space has
a neighbourhood carrying a distinguished coordinate — the covering map itself.  A function on the
total space is holomorphic when it is analytic in that coordinate, and the coordinate is unique
near a point, because two local inverses of the covering map agreeing at a point agree near it.

The reason to have this is the passage from a covering to an equation: the coefficients of the
polynomial whose roots are the values of a function on a fibre are functions of the base, and they
are analytic exactly when the function upstairs is holomorphic.  The first half of that statement —
a function on the total space which is constant on fibres descends to an analytic function on the
base — is proven here.

## Main definitions

* `Rigidity.RET.IsHoloAt` — a function on the total space is analytic at a point in the local
  coordinate given by the projection.
* `Rigidity.RET.IsHolo` — the same at every point.

## Main results

* `Rigidity.RET.IsHoloAt.analyticAt_of_chart` — holomorphy may be tested in any local coordinate.
* `Rigidity.RET.isHoloAt_comp_iff` — a function pulled back from the base is holomorphic exactly
  when it is analytic there.
* `Rigidity.RET.IsHoloAt.comp_homeomorph` — holomorphy is preserved by a symmetry of the total
  space over the base.
* `Rigidity.RET.exists_analytic_of_isHolo_of_invariant` — a holomorphic function constant on the
  fibres descends to an analytic function on the base.
-/

open Topology

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g g₁ g₂ : Y → ℂ} {y : Y}

/-- **A local coordinate at a point of the total space**: a local homeomorphism to the plane which
is the projection itself. -/
def IsChartAt (f : Y → ℂ) (e : OpenPartialHomeomorph Y ℂ) (y : Y) : Prop :=
  y ∈ e.source ∧ f = ⇑e

/-- **A function on the total space is holomorphic at a point** when it is analytic there in the
local coordinate given by the projection. -/
def IsHoloAt (f g : Y → ℂ) (y : Y) : Prop :=
  ∃ e : OpenPartialHomeomorph Y ℂ, IsChartAt f e y ∧ AnalyticAt ℂ (fun w => g (e.symm w)) (f y)

/-- **A function on the total space is holomorphic** when it is holomorphic at every point. -/
def IsHolo (f g : Y → ℂ) : Prop := ∀ y, IsHoloAt f g y

/-- The projection sends a point to a point of the target of any chart at it. -/
theorem IsChartAt.mem_target {e : OpenPartialHomeomorph Y ℂ} (he : IsChartAt f e y) :
    f y ∈ e.target := by
  rw [congrFun he.2 y]; exact e.map_source he.1

/-- A chart at a point inverts the projection there. -/
theorem IsChartAt.symm_apply {e : OpenPartialHomeomorph Y ℂ} (he : IsChartAt f e y) :
    e.symm (f y) = y := by rw [congrFun he.2 y]; exact e.left_inv he.1

/-- **Two local coordinates at the same point agree near it.**  Both invert the projection and both
send the image of the point to the point itself, so they agree wherever both are defined and close
enough. -/
theorem IsChartAt.eventuallyEq_symm {e e' : OpenPartialHomeomorph Y ℂ} (he : IsChartAt f e y)
    (he' : IsChartAt f e' y) : e.symm =ᶠ[𝓝 (f y)] e'.symm := by
  have hcont : ContinuousAt e.symm (f y) := e.continuousAt_symm he.mem_target
  have h1 : ∀ᶠ w in 𝓝 (f y), e.symm w ∈ e'.source :=
    hcont.preimage_mem_nhds (by rw [he.symm_apply]; exact e'.open_source.mem_nhds he'.1)
  have h2 : ∀ᶠ w in 𝓝 (f y), w ∈ e.target := e.open_target.mem_nhds he.mem_target
  filter_upwards [h1, h2] with w hw1 hw2
  have hval : e' (e.symm w) = w := by
    rw [← congrFun he'.2, congrFun he.2]; exact e.right_inv hw2
  exact (e'.left_inv hw1).symm.trans (congrArg (⇑e'.symm) hval)

/-- **Holomorphy may be tested in any local coordinate at the point.** -/
theorem IsHoloAt.analyticAt_of_chart (h : IsHoloAt f g y) {e : OpenPartialHomeomorph Y ℂ}
    (he : IsChartAt f e y) : AnalyticAt ℂ (fun w => g (e.symm w)) (f y) := by
  obtain ⟨e', he', ha⟩ := h
  exact ha.congr ((he'.eventuallyEq_symm he).fun_comp g)

/-- The projection is holomorphic. -/
theorem isHoloAt_self (hf : IsLocalHomeomorph f) (y : Y) : IsHoloAt f f y := by
  obtain ⟨e, hy, he⟩ := hf y
  refine ⟨e, ⟨hy, he⟩, ?_⟩
  have hchart : IsChartAt f e y := ⟨hy, he⟩
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) (f y) := analyticAt_id
  refine hid.congr ?_
  filter_upwards [e.open_target.mem_nhds hchart.mem_target] with w hw
  show w = f (e.symm w)
  rw [congrFun he, e.right_inv hw]

/-- A function pulled back from the base is holomorphic wherever it is analytic. -/
theorem isHoloAt_comp_of_analyticAt {g₀ : ℂ → ℂ} (hf : IsLocalHomeomorph f)
    (h : AnalyticAt ℂ g₀ (f y)) : IsHoloAt f (fun y => g₀ (f y)) y := by
  obtain ⟨e, hy, he⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hy, he⟩
  refine ⟨e, hchart, h.congr ?_⟩
  filter_upwards [e.open_target.mem_nhds hchart.mem_target] with w hw
  rw [congrFun he, e.right_inv hw]

/-- **A function pulled back from the base is holomorphic exactly when it is analytic there.** -/
theorem isHoloAt_comp_iff {g₀ : ℂ → ℂ} (hf : IsLocalHomeomorph f) :
    IsHoloAt f (fun y => g₀ (f y)) y ↔ AnalyticAt ℂ g₀ (f y) := by
  refine ⟨fun h => ?_, fun h => isHoloAt_comp_of_analyticAt hf h⟩
  obtain ⟨e, hy, he⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hy, he⟩
  refine (h.analyticAt_of_chart hchart).congr ?_
  filter_upwards [e.open_target.mem_nhds hchart.mem_target] with w hw
  rw [congrFun he, e.right_inv hw]

/-! ### The algebra of holomorphic functions -/

theorem IsHoloAt.add (h₁ : IsHoloAt f g₁ y) (h₂ : IsHoloAt f g₂ y) :
    IsHoloAt f (fun y => g₁ y + g₂ y) y := by
  obtain ⟨e, he, ha⟩ := h₁
  exact ⟨e, he, ha.add (h₂.analyticAt_of_chart he)⟩

theorem IsHoloAt.mul (h₁ : IsHoloAt f g₁ y) (h₂ : IsHoloAt f g₂ y) :
    IsHoloAt f (fun y => g₁ y * g₂ y) y := by
  obtain ⟨e, he, ha⟩ := h₁
  exact ⟨e, he, ha.mul (h₂.analyticAt_of_chart he)⟩

theorem IsHoloAt.neg (h : IsHoloAt f g y) : IsHoloAt f (fun y => -g y) y := by
  obtain ⟨e, he, ha⟩ := h
  exact ⟨e, he, ha.neg⟩

theorem IsHoloAt.sub (h₁ : IsHoloAt f g₁ y) (h₂ : IsHoloAt f g₂ y) :
    IsHoloAt f (fun y => g₁ y - g₂ y) y := by
  obtain ⟨e, he, ha⟩ := h₁
  exact ⟨e, he, ha.sub (h₂.analyticAt_of_chart he)⟩

theorem isHoloAt_const (hf : IsLocalHomeomorph f) (c : ℂ) (y : Y) :
    IsHoloAt f (fun _ => c) y := by
  obtain ⟨e, hy, he⟩ := hf y
  exact ⟨e, ⟨hy, he⟩, analyticAt_const⟩

/-- Holomorphy is a property of the function, not of the formula for it. -/
theorem IsHoloAt.congr (h : IsHoloAt f g₁ y) (heq : g₁ = g₂) : IsHoloAt f g₂ y := heq ▸ h

/-- A finite sum of holomorphic functions is holomorphic. -/
theorem isHoloAt_finset_sum (hf : IsLocalHomeomorph f) {ι : Type*} (s : Finset ι)
    {G : ι → Y → ℂ} (h : ∀ i ∈ s, IsHoloAt f (G i) y) :
    IsHoloAt f (fun y => ∑ i ∈ s, G i y) y := by
  obtain ⟨e, hy, he⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hy, he⟩
  exact ⟨e, hchart, Finset.analyticAt_fun_sum s fun i hi => (h i hi).analyticAt_of_chart hchart⟩

/-- A finite product of holomorphic functions is holomorphic. -/
theorem isHoloAt_finset_prod (hf : IsLocalHomeomorph f) {ι : Type*} (s : Finset ι)
    {G : ι → Y → ℂ} (h : ∀ i ∈ s, IsHoloAt f (G i) y) :
    IsHoloAt f (fun y => ∏ i ∈ s, G i y) y := by
  obtain ⟨e, hy, he⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hy, he⟩
  exact ⟨e, hchart, Finset.analyticAt_fun_prod s fun i hi => (h i hi).analyticAt_of_chart hchart⟩

/-! ### Symmetries of the total space -/

/-- **A homeomorphism of the total space over the base carries local coordinates to local
coordinates**: composing a chart with the symmetry gives a chart at the preimage point. -/
theorem IsChartAt.comp_homeomorph {e : OpenPartialHomeomorph Y ℂ} {perm : Y ≃ₜ Y}
    (hperm : ∀ y, f (perm y) = f y) (he : IsChartAt f e (perm y)) :
    IsChartAt f (perm.transOpenPartialHomeomorph e) y := by
  refine ⟨by simpa using he.1, ?_⟩
  funext y'
  simp only [Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply]
  rw [← congrFun he.2 (perm y'), hperm y']

/-- **A holomorphic function stays holomorphic when composed with a symmetry of the total space
over the base.**  A deck transformation of a covering is such a symmetry. -/
theorem IsHoloAt.comp_homeomorph {perm : Y ≃ₜ Y} (hperm : ∀ y, f (perm y) = f y)
    (h : IsHoloAt f g (perm y)) : IsHoloAt f (fun y => g (perm y)) y := by
  obtain ⟨e, he, ha⟩ := h
  refine ⟨perm.transOpenPartialHomeomorph e, he.comp_homeomorph hperm, ?_⟩
  have hfun : (fun w => g (perm ((perm.transOpenPartialHomeomorph e).symm w)))
      = fun w => g (e.symm w) := by
    funext w
    simp
  rw [hfun, ← hperm y]
  exact ha

/-! ### Descent along the projection -/

/-- **A holomorphic function constant on the fibres descends to an analytic function on the base.**

The values of the function are the values of a function of the base point alone, and that function
is analytic at every point the projection reaches. -/
theorem exists_analytic_of_isHolo_of_invariant (hf : IsLocalHomeomorph f) (hg : IsHolo f g)
    (hinv : ∀ y y' : Y, f y = f y' → g y = g y') :
    ∃ g₀ : ℂ → ℂ, (∀ y, g y = g₀ (f y)) ∧ ∀ y, AnalyticAt ℂ g₀ (f y) := by
  classical
  have hthrough : Function.FactorsThrough g f := hinv
  have hfac : ∀ y', g y' = Function.extend f g 0 (f y') := fun y' =>
    (hthrough.extend_apply 0 y').symm
  exact ⟨Function.extend f g 0, hfac,
    fun y => (isHoloAt_comp_iff hf).1 ((hg y).congr (funext hfac))⟩

end Rigidity.RET

end
