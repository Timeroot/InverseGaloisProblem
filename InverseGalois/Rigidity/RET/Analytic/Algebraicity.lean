/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Algebraize
import InverseGalois.Rigidity.RET.Analytic.CoverExtend

/-!
# The requirement is exactly that coverings are algebraic

The requirement of `RET/Analytic/Wall.lean` asks that the functions of moderate growth on a
covering of a punctured plane see its deck group.  One direction of what that amounts to is already
available: the requirement forces the covering to be the root variety of a monic equation away from
finitely many further points of the base (`RET/Analytic/Algebraize.lean`).  The converse direction
is here, and with it the two are the same statement.

The converse is not the transport of functions along a homeomorphism over the plane, because the
model an algebraization produces describes the covering only over the complement of a *larger*
finite set, and the coordinate of the model is not a function on the covering.  Damping the
coordinate by a polynomial vanishing at the discarded parameters and extending by zero repairs this
(`RET/Analytic/CoverExtend.lean`), and the repaired function still separates the fibres over the
parameters the model keeps.

Two hypotheses on the projection appear in the converse that the forward direction does not need:
the projection is separated, and the total space is connected.  Both are properties of a covering
of a punctured plane, and both are needed: the plane with a point doubled is a local homeomorphism
with a faithful transitive deck group and no separating functions at all
(`RET/Analytic/WallSharp.lean`), and it is precisely the separatedness that it fails.

## Main definitions

* `Rigidity.RET.AllCoveringsAlgebraic` — every covering of a punctured plane is the root variety of
  a monic equation, away from finitely many further points of the base.

## Main results

* `Rigidity.RET.forall_ne_iff_exists_algebraic_model` — for a single covering, its functions of
  moderate growth see its deck group exactly when it has an algebraic model.
* `Rigidity.RET.hasEnoughFunctions_iff_allCoveringsAlgebraic` — the requirement of
  `RET/Analytic/Wall.lean` is the statement that every covering of a punctured plane is algebraic.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

section OneCovering

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
  {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
  [FaithfulSMul H Y] [IsOverBase H f]

/-- **A covering of a punctured plane is algebraic exactly when its functions of moderate growth
see its deck group.**

Forwards, the functions that move the deck transformations one at a time combine into one function
separating almost every fibre, and such a function presents the covering as the root variety of a
monic equation over the complement of a larger finite set.  Backwards, the coordinate of that
equation, damped so as to extend across the parameters the equation discards, is a function of
moderate growth on the whole covering which distinguishes the points of every fibre the equation
keeps. -/
theorem forall_ne_iff_exists_algebraic_model (hf : IsLocalHomeomorph f)
    (hsepmap : IsSeparatedMap f) (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ) :
    (∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) ↔
      ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧
        P.natDegree = Nat.card H ∧ (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
        ∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
          ∀ y, rootBase P S' (Φ y) = f (y : Y) := by
  refine ⟨exists_algebraic_model_of_forall_ne (H := H) hf htrans hrange, ?_⟩
  rintro ⟨P, S', hSS, hP, -, hsep, Φ, hcomm⟩ a ha
  exact exists_ne_of_homeo_rootTotal_of_subset (H := H) hf hsepmap hrange hSS hP hsep Φ hcomm a ha

end OneCovering

/-! ### The requirement, restated -/

/-- **Every covering of a punctured plane is cut out by a monic equation**, away from finitely many
further points of the base. -/
def AllCoveringsAlgebraic : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)), IsCoveringMap q →
      Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
        [IsOverBase H fun y => ((q y : ℂ))],
        (∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) →
        ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧
          P.natDegree = Nat.card H ∧ (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
          ∃ Φ : ↥((fun y => ((q y : ℂ))) ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
            ∀ y, rootBase P S' (Φ y) = ((q (y : Y) : ℂ))

/-- The projection of a covering of a punctured plane to the plane is a local homeomorphism. -/
theorem isLocalHomeomorph_val_comp {S : Finset ℂ} {Y : Type*} [TopologicalSpace Y]
    {q : Y → ↥((S : Set ℂ)ᶜ)} (hq : IsCoveringMap q) :
    IsLocalHomeomorph fun y => ((q y : ℂ)) :=
  (S.finite_toSet.isClosed.isOpen_compl.isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
    hq.isLocalHomeomorph

/-- The projection of a covering of a punctured plane to the plane is a separated map. -/
theorem isSeparatedMap_val_comp {S : Finset ℂ} {Y : Type*} [TopologicalSpace Y]
    {q : Y → ↥((S : Set ℂ)ᶜ)} (hq : IsCoveringMap q) :
    IsSeparatedMap fun y => ((q y : ℂ)) :=
  hq.isSeparatedMap.comp_left Subtype.val_injective

/-- **The requirement of `RET/Analytic/Wall.lean` is the statement that coverings are algebraic.**
-/
theorem hasEnoughFunctions_iff_allCoveringsAlgebraic :
    HasEnoughFunctions ↔ AllCoveringsAlgebraic := by
  constructor
  · intro hwall S Y _ _ _ q hq hrange H _ _ _ _ _ _ htrans
    exact exists_algebraic_model_of_hasEnoughFunctions hwall S Y q hq
      (isLocalHomeomorph_val_comp hq) hrange H htrans
  · intro halg S Y _ _ _ q hq hf hrange H _ _ _ _ _ _ htrans a ha
    obtain ⟨P, S', hSS, hP, -, hsep, Φ, hcomm⟩ := halg S Y q hq hrange H htrans
    exact exists_ne_of_homeo_rootTotal_of_subset (H := H) hf (isSeparatedMap_val_comp hq) hrange
      hSS hP hsep Φ hcomm a ha

end Rigidity.RET

end
