/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverExistence
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureOrder

/-!
# A cover of the punctured plane with monodromy prescribed in a prescribed order

The cover built from a generating product-one tuple enumerates the punctures the way the loops
that meet them do.  Reordering the tuple within its braid class and conjugating the loops matches
that enumeration with any prescribed one (`Rigidity.RET.exists_hom_punctureLoops_ordered`), so the
cover may be built with the punctures named in advance.

This is the branch-cycle description in the shape the algebraic statement asks for: the branch
points come first, and the tuple is the monodromy at them in the order they were listed.

## Main results

* `Rigidity.RET.exists_cover_of_prodOne_ordered` — a connected cover of the plane punctured at a
  prescribed enumeration of points, with prescribed monodromy at each of them in that order and
  trivial monodromy at infinity.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-- **A generating product-one tuple is the monodromy of a connected covering of the punctured
plane at the punctures listed in any prescribed order.**

The loop `δ i` winds once around the prescribed puncture `pt i`, and the monodromy along it is
translation by `h i`; a loop supported at infinity acts trivially, so the cover is unramified
there. -/
theorem exists_cover_of_prodOne_ordered (S : Finset ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ)
    (pt : Fin S.card → ℂ) (hrange : Set.range pt = (S : Set ℂ))
    {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (δ : Fin S.card → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (loopInf : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (D : MonodromyData (X := ((S : Set ℂ))ᶜ) ⟨z₀, hz₀⟩ H),
      (∀ i : Fin S.card, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (δ i)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ loopInf ∧
        IsCoveringMap D.proj ∧ PathConnectedSpace D.Total ∧
        Function.Injective D.deckHom ∧
        (∀ y z : D.Total, D.proj y = D.proj z → ∃ a : H, D.deck a y = z) ∧
        (∀ (i : Fin S.card) (s : D.Fib ⟨z₀, hz₀⟩),
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath (δ i)) (D.basePoint s)
            = D.basePoint ((D.fibEquiv (Path.Homotopic.Quotient.refl _)).symm
                (h i * D.fibEquiv (Path.Homotopic.Quotient.refl _) s))) ∧
        (∀ s : D.Fib ⟨z₀, hz₀⟩,
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath loopInf) (D.basePoint s)
            = D.basePoint s) := by
  classical
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  obtain ⟨δ, loopInf, φ, hloop, hinf, hsurj, hval, hlast⟩ :=
    exists_hom_punctureLoops_ordered S hz₀ pt hrange h hprod hgen
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  refine ⟨δ, loopInf, MonodromyData.ofHom hX φ, hloop, hinf,
    MonodromyData.isCoveringMap_proj_ofHom hX φ,
    MonodromyData.pathConnectedSpace_total_ofHom hX φ hsurj,
    MonodromyData.deckHom_injective_ofHom hX φ, ?_, ?_, ?_⟩
  · intro y z hyz
    exact (MonodromyData.ofHom hX φ).exists_deck_eq_of_proj_eq y z hyz
      (Classical.choice (MonodromyData.nonempty_quotient_of_pathConnected
        (x₀ := (⟨z₀, hz₀⟩ : ↥((S : Set ℂ))ᶜ)) _))
  · intro i s
    rw [MonodromyData.monodromy_basePoint_ofHom hX φ (δ i) s, hval i]
  · intro s
    rw [MonodromyData.monodromy_basePoint_ofHom hX φ loopInf s, hlast, one_mul,
      Equiv.symm_apply_apply]

end Rigidity.RET

end
