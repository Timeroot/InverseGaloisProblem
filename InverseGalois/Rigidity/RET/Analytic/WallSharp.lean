/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Wall

/-!
# The deck group has to act faithfully

The statement the existence direction of the Riemann existence theorem rests on asks that the
functions of moderate growth on a covering of a punctured plane see its deck group: every element
of the group other than the identity moves one of them.  A group element can only be seen by a
function if it moves a point, so the group has to act faithfully — and that is not a formality
about how the statement is phrased, but a hypothesis without which it is false.  Any group at all
acts on the plane by doing nothing, transitively on the fibres of the identity covering, and its
elements move no function whatever.

## Main definitions

* `Rigidity.RET.HasEnoughFunctionsUnfaithful` — the requirement of
  `Rigidity.RET.HasEnoughFunctions` with the faithfulness of the action dropped.

## Main results

* `Rigidity.RET.isCoveringMap_id` — a space covers itself.
* `Rigidity.RET.not_hasEnoughFunctionsUnfaithful` — the requirement without faithfulness is false.
-/

noncomputable section

namespace Rigidity.RET

/-- **A space covers itself.**  The identity is a covering map: the whole space is an evenly
covered neighbourhood of each of its points, with a one-point fibre. -/
theorem isCoveringMap_id {Y : Type*} [TopologicalSpace Y] : IsCoveringMap (id : Y → Y) := by
  intro x
  haveI : Subsingleton ↥(id ⁻¹' {x} : Set Y) :=
    ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
  refine ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_univ,
    ⟨{ toFun := fun y => (⟨y.1, trivial⟩, ⟨x, rfl⟩)
       invFun := fun p => ⟨p.1.1, trivial⟩
       left_inv := fun _ => rfl
       right_inv := fun p => Prod.ext (Subtype.ext rfl) (Subsingleton.elim _ _)
       continuous_toFun := (continuous_subtype_val.subtype_mk _).prodMk continuous_const
       continuous_invFun := (continuous_subtype_val.comp continuous_fst).subtype_mk _ },
    fun _ => rfl⟩⟩

/-- The requirement of `Rigidity.RET.HasEnoughFunctions` with the faithfulness of the deck group
dropped: every element of the group other than the identity is asked to move a function of moderate
growth, whether or not it moves a point. -/
def HasEnoughFunctionsUnfaithful : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)), IsCoveringMap q →
      ∀ hf : IsLocalHomeomorph fun y => ((q y : ℂ)),
        Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
        [IsOverBase H fun y => ((q y : ℂ))],
        (∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) →
        ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y

/-- **Without faithfulness the requirement is false.**  The plane covers itself, the two-element
group acts on it by doing nothing — transitively on the fibres, which are single points — and the
element that is not the identity moves no function at all. -/
theorem not_hasEnoughFunctionsUnfaithful : ¬ HasEnoughFunctionsUnfaithful := by
  intro hwall
  set S : Finset ℂ := ∅ with hS
  set Y : Type := ↥((S : Set ℂ)ᶜ) with hY
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  haveI : Nonempty Y := ⟨⟨0, by simp [hS]⟩⟩
  haveI : PathConnectedSpace Y := pathConnectedSpace_punctured S.finite_toSet.countable
  set H : Type := Multiplicative (ZMod 2) with hH
  letI : MulAction H Y :=
    { smul := fun _ y => y
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have hsmul : ∀ (a : H) (y : Y), a • y = y := fun _ _ => rfl
  haveI : ContinuousConstSMul H Y := ⟨fun _ => continuous_id⟩
  have hf : IsLocalHomeomorph fun y : Y => ((id y : Y) : ℂ) :=
    hX.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  haveI : IsOverBase H fun y : Y => ((id y : Y) : ℂ) := ⟨fun a y => by rw [hsmul]⟩
  have hrange : Set.range (fun y : Y => ((id y : Y) : ℂ)) = (↑S : Set ℂ)ᶜ := Subtype.range_coe
  have htrans : ∀ y y' : Y, ((id y : Y) : ℂ) = ((id y' : Y) : ℂ) → ∃ b : H, y' = b • y := by
    intro y y' hyy
    exact ⟨1, (Subtype.coe_injective hyy).symm⟩
  have ha : (Multiplicative.ofAdd (1 : ZMod 2) : H) ≠ 1 := by decide
  obtain ⟨F, -, y, hy⟩ :=
    hwall S Y id isCoveringMap_id hf hrange H htrans (Multiplicative.ofAdd (1 : ZMod 2)) ha
  exact hy (by rw [hsmul])

end Rigidity.RET

end
