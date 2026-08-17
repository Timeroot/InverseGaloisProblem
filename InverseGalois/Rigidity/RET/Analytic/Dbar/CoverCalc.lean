/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Cover
import InverseGalois.Rigidity.RET.Analytic.Dbar.Localize

/-!
# The Cauchy–Riemann calculus on the total space of a covering

A local homeomorphism to the plane gives every point of the total space a local coordinate, and
choosing one at each point turns the two first-order operators into honest functions on the total
space.  The choice does not matter: any two coordinates at a point agree near it, and the operators
only see a function near the point.

Read in a coordinate, a function on the total space becomes a function of a complex variable, and
the operators become the plane operators; the rules of the calculus, and the commutator of the
Cauchy–Riemann operator with the weighted adjoint of a weight pulled back from the base, then
follow from the corresponding plane identities.

## Main definitions

* `Rigidity.RET.dbarY`, `Rigidity.RET.dzY` — the two operators on the total space.
* `Rigidity.RET.deltaOpY` — the weighted adjoint of a weight pulled back from the base.
* `Rigidity.RET.IsDiffAt`, `Rigidity.RET.IsC2At` — differentiability in a local coordinate.

## Main results

* `Rigidity.RET.dbarY_eq`, `Rigidity.RET.dzY_eq` — the operators may be read in any coordinate.
* `Rigidity.RET.dbarY_mul`, `Rigidity.RET.dbarY_conj`, `Rigidity.RET.dbarY_comp` — the rules.
* `Rigidity.RET.dbarY_deltaOpY_sub` — the commutator with the weighted adjoint is multiplication
  by the curvature of the weight.
-/

open Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {y : Y} {Φ β : ℂ → ℂ}

/-! ### A coordinate at every point -/

/-- **A local coordinate at a point**, chosen once and for all. -/
def chartOf (hlh : IsLocalHomeomorph f) (y : Y) : OpenPartialHomeomorph Y ℂ :=
  Classical.choose (hlh y)

theorem isChartAt_chartOf (hlh : IsLocalHomeomorph f) (y : Y) : IsChartAt f (chartOf hlh y) y :=
  ⟨(Classical.choose_spec (hlh y)).1, (Classical.choose_spec (hlh y)).2⟩

/-! ### The two operators -/

/-- **The Cauchy–Riemann operator on the total space**, read in the chosen coordinate. -/
def dbarY (hlh : IsLocalHomeomorph f) (u : Y → ℂ) (y : Y) : ℂ :=
  dbar (fun w => u ((chartOf hlh y).symm w)) (f y)

/-- **The holomorphic derivative on the total space**, read in the chosen coordinate. -/
def dzY (hlh : IsLocalHomeomorph f) (u : Y → ℂ) (y : Y) : ℂ :=
  dz (fun w => u ((chartOf hlh y).symm w)) (f y)

variable {hlh : IsLocalHomeomorph f} {e : OpenPartialHomeomorph Y ℂ}

/-- **The operator may be read in any local coordinate at the point.** -/
theorem dbarY_eq (he : IsChartAt f e y) (u : Y → ℂ) :
    dbarY hlh u y = dbar (fun w => u (e.symm w)) (f y) :=
  dbar_congr (((isChartAt_chartOf hlh y).eventuallyEq_symm he).fun_comp u)

/-- **The holomorphic derivative may be read in any local coordinate at the point.** -/
theorem dzY_eq (he : IsChartAt f e y) (u : Y → ℂ) :
    dzY hlh u y = dz (fun w => u (e.symm w)) (f y) :=
  dz_congr (((isChartAt_chartOf hlh y).eventuallyEq_symm he).fun_comp u)

/-- A coordinate is a chart at each point of its source. -/
theorem isChartAt_symm (hfe : f = ⇑e) {w : ℂ} (hw : w ∈ e.target) : IsChartAt f e (e.symm w) :=
  ⟨e.map_target hw, hfe⟩

/-- The projection undoes a coordinate. -/
theorem apply_symm_of_isChartAt (hfe : f = ⇑e) {w : ℂ} (hw : w ∈ e.target) :
    f (e.symm w) = w := by
  rw [congrFun hfe (e.symm w)]
  exact e.right_inv hw

/-- **Read in a coordinate, the operator on the total space is the plane operator.** -/
theorem dbarY_symm_apply (hfe : f = ⇑e) (u : Y → ℂ) {w : ℂ} (hw : w ∈ e.target) :
    dbarY hlh u (e.symm w) = dbar (fun w' => u (e.symm w')) w := by
  rw [dbarY_eq (isChartAt_symm hfe hw) u, apply_symm_of_isChartAt hfe hw]

/-- **Read in a coordinate, the holomorphic derivative on the total space is the plane one.** -/
theorem dzY_symm_apply (hfe : f = ⇑e) (u : Y → ℂ) {w : ℂ} (hw : w ∈ e.target) :
    dzY hlh u (e.symm w) = dz (fun w' => u (e.symm w')) w := by
  rw [dzY_eq (isChartAt_symm hfe hw) u, apply_symm_of_isChartAt hfe hw]

theorem eventuallyEq_dbarY_symm (he : IsChartAt f e y) (u : Y → ℂ) :
    (fun w => dbarY hlh u (e.symm w)) =ᶠ[𝓝 (f y)] dbar (fun w' => u (e.symm w')) := by
  filter_upwards [e.open_target.mem_nhds he.mem_target] with w hw
  exact dbarY_symm_apply he.2 u hw

theorem eventuallyEq_dzY_symm (he : IsChartAt f e y) (u : Y → ℂ) :
    (fun w => dzY hlh u (e.symm w)) =ᶠ[𝓝 (f y)] dz (fun w' => u (e.symm w')) := by
  filter_upwards [e.open_target.mem_nhds he.mem_target] with w hw
  exact dzY_symm_apply he.2 u hw

/-! ### Differentiability in a coordinate -/

/-- **A function on the total space is differentiable at a point** when it is so in the local
coordinate given by the projection. -/
def IsDiffAt (f u : Y → ℂ) (y : Y) : Prop :=
  ∃ e : OpenPartialHomeomorph Y ℂ, IsChartAt f e y ∧
    DifferentiableAt ℝ (fun w => u (e.symm w)) (f y)

/-- **A function on the total space is twice continuously differentiable at a point** when it is so
in the local coordinate given by the projection. -/
def IsC2At (f u : Y → ℂ) (y : Y) : Prop :=
  ∃ e : OpenPartialHomeomorph Y ℂ, IsChartAt f e y ∧ ContDiffAt ℝ 2 (fun w => u (e.symm w)) (f y)

theorem IsDiffAt.of_isChartAt (h : IsDiffAt f u y) (he : IsChartAt f e y) :
    DifferentiableAt ℝ (fun w => u (e.symm w)) (f y) := by
  obtain ⟨e', he', hd⟩ := h
  exact ((he'.eventuallyEq_symm he).fun_comp u).differentiableAt_iff.1 hd

theorem IsC1At.of_isChartAt (h : IsC1At f u y) (he : IsChartAt f e y) :
    ContDiffAt ℝ 1 (fun w => u (e.symm w)) (f y) := by
  obtain ⟨e', he', hc⟩ := h
  exact hc.congr_of_eventuallyEq ((he.eventuallyEq_symm he').fun_comp u)

theorem IsC2At.of_isChartAt (h : IsC2At f u y) (he : IsChartAt f e y) :
    ContDiffAt ℝ 2 (fun w => u (e.symm w)) (f y) := by
  obtain ⟨e', he', hc⟩ := h
  exact hc.congr_of_eventuallyEq ((he.eventuallyEq_symm he').fun_comp u)

theorem IsC1At.isDiffAt (h : IsC1At f u y) : IsDiffAt f u y := by
  obtain ⟨e, he, hc⟩ := h
  exact ⟨e, he, hc.differentiableAt (by norm_num)⟩

theorem IsC2At.isC1At (h : IsC2At f u y) : IsC1At f u y := by
  obtain ⟨e, he, hc⟩ := h
  exact ⟨e, he, hc.of_le (by norm_num)⟩

theorem IsC2At.isDiffAt (h : IsC2At f u y) : IsDiffAt f u y := h.isC1At.isDiffAt

/-- **Read in a coordinate, a twice differentiable function of the total space is a twice
differentiable function of a complex variable.** -/
theorem contDiffAt_symm_of_isC2At (hC2 : ∀ y', IsC2At f u y') (hfe : f = ⇑e) {w : ℂ}
    (hw : w ∈ e.target) : ContDiffAt ℝ 2 (fun w' => u (e.symm w')) w := by
  have h := (hC2 (e.symm w)).of_isChartAt (isChartAt_symm hfe hw)
  rwa [apply_symm_of_isChartAt hfe hw] at h

/-! ### The operator and the relation -/

theorem IsDiffAt.isDbarAt (h : IsDiffAt f u y) : IsDbarAt f u (dbarY hlh u y) y := by
  obtain ⟨e, he, hd⟩ := h
  exact ⟨e, he, hd, (dbarY_eq he u).symm⟩

theorem IsDbarAt.isDiffAt {c : ℂ} (h : IsDbarAt f u c y) : IsDiffAt f u y := by
  obtain ⟨e, he, hd, -⟩ := h
  exact ⟨e, he, hd⟩

theorem IsDbarAt.dbarY_eq {c : ℂ} (h : IsDbarAt f u c y) : dbarY hlh u y = c := by
  obtain ⟨e, he, -, hval⟩ := h
  rw [_root_.Rigidity.RET.dbarY_eq he u, hval]

/-! ### The rules -/

theorem IsDiffAt.add (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    IsDiffAt f (fun y' => u y' + v y') y := by
  obtain ⟨e, he, hd⟩ := hu
  exact ⟨e, he, hd.add (hv.of_isChartAt he)⟩

theorem IsDiffAt.mul (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    IsDiffAt f (fun y' => u y' * v y') y := by
  obtain ⟨e, he, hd⟩ := hu
  exact ⟨e, he, hd.mul (hv.of_isChartAt he)⟩

theorem IsDiffAt.conj (hu : IsDiffAt f u y) : IsDiffAt f (fun y' => conj (u y')) y := by
  obtain ⟨e, he, hd⟩ := hu
  exact ⟨e, he, differentiableAt_conj hd⟩

theorem isDiffAt_comp (hlh : IsLocalHomeomorph f) (hβ : DifferentiableAt ℝ β (f y)) :
    IsDiffAt f (fun y' => β (f y')) y := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  exact ⟨e, he, ((eventuallyEq_comp_symm he β).differentiableAt_iff).2 hβ⟩

theorem IsC1At.add (hu : IsC1At f u y) (hv : IsC1At f v y) :
    IsC1At f (fun y' => u y' + v y') y := by
  obtain ⟨e, he, hc⟩ := hu
  exact ⟨e, he, hc.add (hv.of_isChartAt he)⟩

theorem IsC1At.mul (hu : IsC1At f u y) (hv : IsC1At f v y) :
    IsC1At f (fun y' => u y' * v y') y := by
  obtain ⟨e, he, hc⟩ := hu
  exact ⟨e, he, hc.mul (hv.of_isChartAt he)⟩

theorem IsC1At.conj (hu : IsC1At f u y) : IsC1At f (fun y' => conj (u y')) y := by
  obtain ⟨e, he, hc⟩ := hu
  refine ⟨e, he, ?_⟩
  have h := ((contDiff_conj (n := 1)).contDiffAt).comp (f y) hc
  simpa [Function.comp_def] using h

theorem dbarY_add (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    dbarY hlh (fun y' => u y' + v y') y = dbarY hlh u y + dbarY hlh v y := by
  obtain ⟨e, he, hd⟩ := hu
  simp only [dbarY_eq he]
  exact dbar_add hd (hv.of_isChartAt he)

theorem dbarY_neg (hu : IsDiffAt f u y) : dbarY hlh (fun y' => -u y') y = -dbarY hlh u y := by
  obtain ⟨e, he, hd⟩ := hu
  simp only [dbarY_eq he]
  exact dbar_neg hd

theorem dbarY_mul (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    dbarY hlh (fun y' => u y' * v y') y = u y * dbarY hlh v y + v y * dbarY hlh u y := by
  obtain ⟨e, he, hd⟩ := hu
  simp only [dbarY_eq he]
  rw [dbar_mul hd (hv.of_isChartAt he), he.symm_apply]

theorem dzY_add (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    dzY hlh (fun y' => u y' + v y') y = dzY hlh u y + dzY hlh v y := by
  obtain ⟨e, he, hd⟩ := hu
  simp only [dzY_eq he]
  exact dz_add hd (hv.of_isChartAt he)

theorem dzY_mul (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    dzY hlh (fun y' => u y' * v y') y = u y * dzY hlh v y + v y * dzY hlh u y := by
  obtain ⟨e, he, hd⟩ := hu
  simp only [dzY_eq he]
  rw [dz_mul hd (hv.of_isChartAt he), he.symm_apply]

/-- **The two operators exchange under conjugation.** -/
theorem dbarY_conj (hu : IsDiffAt f u y) :
    dbarY hlh (fun y' => conj (u y')) y = conj (dzY hlh u y) := by
  obtain ⟨e, he, hd⟩ := hu
  rw [dbarY_eq he, dzY_eq he]
  exact dbar_conj hd

/-- **The two operators exchange under conjugation**, the other way. -/
theorem dzY_conj (hu : IsDiffAt f u y) :
    dzY hlh (fun y' => conj (u y')) y = conj (dbarY hlh u y) := by
  obtain ⟨e, he, hd⟩ := hu
  rw [dzY_eq he, dbarY_eq he]
  exact dz_conj hd

/-- **A function pulled back from the base pulls back its derivative.** -/
theorem dbarY_comp (hlh : IsLocalHomeomorph f) (β : ℂ → ℂ) (y : Y) :
    dbarY hlh (fun y' => β (f y')) y = dbar β (f y) := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  rw [dbarY_eq he]
  exact dbar_congr (eventuallyEq_comp_symm he β)

/-- **A function pulled back from the base pulls back its holomorphic derivative.** -/
theorem dzY_comp (hlh : IsLocalHomeomorph f) (β : ℂ → ℂ) (y : Y) :
    dzY hlh (fun y' => β (f y')) y = dz β (f y) := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  rw [dzY_eq he]
  exact dz_congr (eventuallyEq_comp_symm he β)

/-! ### The weighted adjoint -/

/-- **The formal adjoint on the total space** of the Cauchy–Riemann operator against a weight
pulled back from the base. -/
def deltaOpY (hlh : IsLocalHomeomorph f) (Φ : ℂ → ℂ) (v : Y → ℂ) (y : Y) : ℂ :=
  -(dzY hlh v y) + dz Φ (f y) * v y

theorem deltaOpY_symm_apply (hfe : f = ⇑e) (Φ : ℂ → ℂ) (v : Y → ℂ) {w : ℂ} (hw : w ∈ e.target) :
    deltaOpY hlh Φ v (e.symm w) = deltaOp Φ (fun w' => v (e.symm w')) w := by
  simp only [deltaOpY, deltaOp]
  rw [dzY_symm_apply hfe v hw, apply_symm_of_isChartAt hfe hw]

theorem eventuallyEq_deltaOpY_symm (he : IsChartAt f e y) (Φ : ℂ → ℂ) (v : Y → ℂ) :
    (fun w => deltaOpY hlh Φ v (e.symm w)) =ᶠ[𝓝 (f y)] deltaOp Φ (fun w' => v (e.symm w')) := by
  filter_upwards [e.open_target.mem_nhds he.mem_target] with w hw
  exact deltaOpY_symm_apply he.2 Φ v hw

/-- **The commutator of the Cauchy–Riemann operator with its weighted adjoint** is multiplication
by the curvature of the weight. -/
theorem dbarY_deltaOpY_sub (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ)
    (hC2 : ∀ y', IsC2At f v y') (y : Y) :
    dbarY hlh (deltaOpY hlh Φ v) y - deltaOpY hlh Φ (dbarY hlh v) y = v y * dbar (dz Φ) (f y) := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  have h1 : dbarY hlh (deltaOpY hlh Φ v) y = dbar (deltaOp Φ fun w => v (e.symm w)) (f y) := by
    rw [dbarY_eq he]
    exact dbar_congr (eventuallyEq_deltaOpY_symm he Φ v)
  have h2 : deltaOpY hlh Φ (dbarY hlh v) y = deltaOp Φ (dbar fun w => v (e.symm w)) (f y) := by
    simp only [deltaOpY, deltaOp]
    rw [dzY_eq he (dbarY hlh v), dz_congr (eventuallyEq_dbarY_symm he v), dbarY_eq he v]
  rw [h1, h2, dbar_deltaOp_sub_local hΦ e.open_target he.mem_target
    (fun w hw => contDiffAt_symm_of_isC2At hC2 hfe hw), he.symm_apply]

end Rigidity.RET

end
