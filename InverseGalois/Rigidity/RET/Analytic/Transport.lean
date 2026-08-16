/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootRing

/-!
# Functions of moderate growth transport along an isomorphism of coverings

A homeomorphism between two spaces over the plane carries the functions of one to the functions of
the other: a local coordinate on the target becomes one on the source by composition, so
holomorphy is preserved, and the growth conditions only mention the base coordinate, which is
unchanged.  Nothing about a group action is needed for this, and no compatibility beyond the one
square: the homeomorphism commutes with the two projections.

The consequence is the statement the requirement of `RET/Analytic/Wall.lean` really turns on.  On a
covering cut out by an equation the requirement is a theorem (`RET/Analytic/RootRing.lean`), and it
is insensitive to the identification of the covering: a covering merely *homeomorphic over the
plane* to an algebraic one carries the functions it asks for.  So what the requirement asks, for an
arbitrary topological covering, is precisely that the covering is homeomorphic over the plane to an
algebraic one.

## Main results

* `Rigidity.RET.IsHolo.comp_homeo`, `Rigidity.RET.IsModerate.comp_homeo`,
  `Rigidity.RET.mem_coverRing_comp_homeo` — the ring of functions transports.
* `Rigidity.RET.exists_ne_of_homeo_rootTotal` — a covering homeomorphic over the plane to an
  algebraic one has its deck group moved by functions of moderate growth.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

/-! ### Transport along a homeomorphism over the plane -/

section Transport

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y'] {f : Y → ℂ} {f' : Y' → ℂ}
  {g : Y → ℂ} {S : Finset ℂ}

/-- **A local coordinate transports along a homeomorphism over the plane.** -/
theorem IsChartAt.comp_homeo (Φ : Y' ≃ₜ Y) (hcomm : ∀ y', f (Φ y') = f' y')
    {e : OpenPartialHomeomorph Y ℂ} {y' : Y'} (he : IsChartAt f e (Φ y')) :
    IsChartAt f' (Φ.transOpenPartialHomeomorph e) y' := by
  refine ⟨he.1, ?_⟩
  funext y''
  rw [← hcomm y'']
  exact congrFun he.2 (Φ y'')

/-- **Holomorphy at a point transports along a homeomorphism over the plane.** -/
theorem IsHoloAt.comp_homeo (Φ : Y' ≃ₜ Y) (hcomm : ∀ y', f (Φ y') = f' y') {y' : Y'}
    (h : IsHoloAt f g (Φ y')) : IsHoloAt f' (fun y => g (Φ y)) y' := by
  obtain ⟨e, he, hana⟩ := h
  refine ⟨Φ.transOpenPartialHomeomorph e, he.comp_homeo Φ hcomm, ?_⟩
  rw [← hcomm y']
  simpa using hana

/-- **Holomorphy transports along a homeomorphism over the plane.** -/
theorem IsHolo.comp_homeo (Φ : Y' ≃ₜ Y) (hcomm : ∀ y', f (Φ y') = f' y') (h : IsHolo f g) :
    IsHolo f' (fun y => g (Φ y)) := fun y' => (h (Φ y')).comp_homeo Φ hcomm

/-- **Moderate growth transports along a homeomorphism over the plane**: the growth conditions
mention only the base coordinate, which the homeomorphism does not change. -/
theorem IsModerate.comp_homeo (Φ : Y' ≃ₜ Y) (hcomm : ∀ y', f (Φ y') = f' y')
    (h : IsModerate f S g) : IsModerate f' S (fun y => g (Φ y)) where
  punct s hs := by
    obtain ⟨ρ, hρ, C, hC, N, hb⟩ := h.punct s hs
    refine ⟨ρ, hρ, C, hC, N, fun y' hy' => ?_⟩
    rw [← hcomm y'] at hy' ⊢
    exact hb (Φ y') hy'
  infty := by
    obtain ⟨A, R₀, m, hA, hb⟩ := h.infty
    refine ⟨A, R₀, m, hA, fun y' hy' => ?_⟩
    rw [← hcomm y'] at hy' ⊢
    exact hb (Φ y') hy'

/-- **The ring of functions of a covering transports along a homeomorphism over the plane.** -/
theorem mem_coverRing_comp_homeo {hf : IsLocalHomeomorph f} {hf' : IsLocalHomeomorph f'}
    (Φ : Y' ≃ₜ Y) (hcomm : ∀ y', f (Φ y') = f' y') (h : g ∈ coverRing hf S) :
    (fun y => g (Φ y)) ∈ coverRing hf' S :=
  ⟨h.1.comp_homeo Φ hcomm, h.2.comp_homeo Φ hcomm⟩

end Transport

/-! ### A covering that comes from an equation -/

section Algebraic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}
variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}
variable {H : Type*} [Group H] [MulAction H Y]

/-- **A covering homeomorphic over the plane to an algebraic one has its deck group moved by
functions of moderate growth.**

The coordinate of the algebraic model, read on the covering, is a function of moderate growth
there, and it takes distinct values at distinct points of a fibre because a point of the root
variety is its parameter together with its coordinate.  A deck transformation moving some point
therefore moves this one function; faithfulness is the only hypothesis on the group. -/
theorem exists_ne_of_homeo_rootTotal (hf : IsLocalHomeomorph f) (hP : P.Monic)
    (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) (Φ : Y ≃ₜ RootTotal P S)
    (hcomm : ∀ y, rootBase P S (Φ y) = f y) [FaithfulSMul H Y] [IsOverBase H f]
    (a : H) (ha : a ≠ 1) :
    ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y := by
  refine ⟨fun y => rootCoord P S (Φ y),
    mem_coverRing_comp_homeo Φ hcomm (rootCoord_mem_coverRing hP hsep), ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Y, a • y ≠ y := by
    by_contra hcon
    push_neg at hcon
    exact ha (eq_of_smul_eq_smul (α := Y) fun y => by rw [one_smul]; exact hcon y)
  refine ⟨y, fun hval => hy ?_⟩
  have hbase : rootBase P S (Φ (a • y)) = rootBase P S (Φ y) := by
    rw [hcomm, hcomm]
    exact IsOverBase.smul_eq (f := f) a y
  exact Φ.injective (eq_of_rootBase_eq_of_rootCoord_eq hbase hval)

end Algebraic

end Rigidity.RET

end
