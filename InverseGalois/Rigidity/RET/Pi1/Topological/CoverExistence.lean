/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureHom

/-!
# The existence direction of the Riemann Existence Theorem, topologically

A tuple in a finite group whose ordered product is trivial and which generates the group is the
system of branch cycles of a connected covering of the punctured plane: the tuple names a
surjection from the fundamental group of the plane punctured at as many points, sending one loop
around each puncture to the corresponding member of the tuple and the loop at infinity to the
identity, and that surjection is the monodromy of the cover it builds.

Everything in the statement is an honest covering space of the punctured plane: the projection is
a covering map, the total space is path connected, the group acts on it by deck transformations
freely and transitively over each point of the region, and the monodromy along a loop around the
`i`-th puncture is translation by the `i`-th member of the tuple, while the monodromy along the
loop at infinity is the identity — the cover is unramified there.

This is the topological content of the existence direction: what separates it from the statement
over `ℚ̄` is only the passage from a topological cover to an algebraic one.

## Main results

* `Rigidity.RET.exists_cover_of_prodOne` — a connected cover of the punctured plane with
  prescribed monodromy at the punctures and trivial monodromy at infinity.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

namespace MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-- A point of the fibre over the base point, as a point of the space the monodromy acts on. -/
def basePoint (s : D.Fib x₀) : ↥(D.proj ⁻¹' {x₀}) := ⟨⟨x₀, s⟩, rfl⟩

/-- **The monodromy of the cover named by a homomorphism, along a loop, is translation by the
value of the homomorphism on that loop.** -/
theorem monodromy_basePoint_ofHom (hX : IsOpen X) (φ : FundamentalGroup ↥X x₀ →* H)
    (g : FundamentalGroup ↥X x₀) (s : (ofHom hX φ).Fib x₀) :
    (ofHom hX φ).isCoveringMap_proj.monodromy (FundamentalGroup.toPath g)
        ((ofHom hX φ).basePoint s)
      = (ofHom hX φ).basePoint
          ((ofHom hX φ).fibEquiv (Path.Homotopic.Quotient.refl x₀)|>.symm
            (φ g * (ofHom hX φ).fibEquiv (Path.Homotopic.Quotient.refl x₀) s)) := by
  refine (monodromy_apply _ _ _).trans ?_
  refine congrArg (fun t => (ofHom hX φ).basePoint t) ?_
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [fibEquiv_monodromy_ofHom]

end MonodromyData

/-- **A generating product-one tuple in a finite group is the monodromy of a connected covering of
the punctured plane, unramified at infinity.**

The punctures are enumerated by the loops that meet them, one loop for each puncture, in the order
in which their product is read; the last generator, a loop supported at infinity, acts trivially,
which is the statement that the cover is unramified there. -/
theorem exists_cover_of_prodOne (S : Finset ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ)
    {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (pt : Fin S.card → ℂ)
      (γ : Fin (S.card + 1) → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (D : MonodromyData (X := ((S : Set ℂ))ᶜ) ⟨z₀, hz₀⟩ H),
      Function.Injective pt ∧ Set.range pt = (S : Set ℂ) ∧
        (∀ i : Fin S.card, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (γ i.castSucc)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ (γ (Fin.last S.card)) ∧
        IsCoveringMap D.proj ∧ PathConnectedSpace D.Total ∧
        Function.Injective D.deckHom ∧
        (∀ y z : D.Total, D.proj y = D.proj z → ∃ a : H, D.deck a y = z) ∧
        (∀ (i : Fin S.card) (s : D.Fib ⟨z₀, hz₀⟩),
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath (γ i.castSucc)) (D.basePoint s)
            = D.basePoint ((D.fibEquiv (Path.Homotopic.Quotient.refl _)).symm
                (h i * D.fibEquiv (Path.Homotopic.Quotient.refl _) s))) ∧
        (∀ s : D.Fib ⟨z₀, hz₀⟩,
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath (γ (Fin.last S.card)))
            (D.basePoint s) = D.basePoint s) := by
  classical
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  obtain ⟨pt, γ, φ, hinj, hrange, hloop, hinf, hsurj, hval, hlast⟩ :=
    exists_hom_punctureLoops S hz₀ h hprod hgen
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  refine ⟨pt, γ, MonodromyData.ofHom hX φ, hinj, hrange, hloop, hinf,
    MonodromyData.isCoveringMap_proj_ofHom hX φ,
    MonodromyData.pathConnectedSpace_total_ofHom hX φ hsurj,
    MonodromyData.deckHom_injective_ofHom hX φ, ?_, ?_, ?_⟩
  · intro y z hyz
    exact (MonodromyData.ofHom hX φ).exists_deck_eq_of_proj_eq y z hyz
      (Classical.choice (MonodromyData.nonempty_quotient_of_pathConnected
        (x₀ := (⟨z₀, hz₀⟩ : ↥((S : Set ℂ))ᶜ)) _))
  · intro i s
    rw [MonodromyData.monodromy_basePoint_ofHom hX φ (γ i.castSucc) s, hval i]
  · intro s
    rw [MonodromyData.monodromy_basePoint_ofHom hX φ (γ (Fin.last S.card)) s, hlast, one_mul,
      Equiv.symm_apply_apply]

end Rigidity.RET

end
