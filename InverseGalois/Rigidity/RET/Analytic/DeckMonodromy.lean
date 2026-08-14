/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Regular
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy

/-!
# The monodromy group of a Galois covering is its deck group

A group acting on the total space of a covering over the base acts on each fibre, and monodromy
commutes with that action, because lifting a path after moving its starting point by a deck
transformation is the same as moving the lift.  If the action on one fibre is simply transitive —
which is what makes a covering Galois — and the total space is path connected, then the monodromy
group and the acting group are two transitive groups of permutations of the fibre that commute with
each other, so they are isomorphic.

## Main results

* `Rigidity.RET.Analytic.fibreAction` — the action of a group of deck transformations on a fibre.
* `Rigidity.RET.Analytic.monodromyRangeEquiv` — for a path-connected covering with a simply
  transitive group of deck transformations, the monodromy group is isomorphic to that group.
-/

noncomputable section

namespace Rigidity.RET.Analytic

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **A group acting on the total space over the base acts on every fibre.** -/
def fibreAction {G : Type*} [Group G] [MulAction G E]
    (hover : ∀ (g : G) (e : E), p (g • e) = p e) (x : X) : MulAction G ↥(p ⁻¹' {x}) where
  smul g e := ⟨g • (e : E), by
    show p (g • (e : E)) = x
    rw [hover]
    exact e.2⟩
  one_smul e := Subtype.ext (one_smul G (e : E))
  mul_smul a b e := Subtype.ext (mul_smul a b (e : E))

/-- **The monodromy group of a Galois covering is its group of deck transformations.**  The two act
on a fibre transitively and commute with each other, and the deck action is free, so reading off
the deck transformation that matches a monodromy permutation at one point is an isomorphism. -/
def monodromyRangeEquiv (cov : IsCoveringMap p) [PathConnectedSpace E]
    {G : Type*} [Group G] [MulAction G E] (hcont : ∀ g : G, Continuous fun e : E => g • e)
    (hover : ∀ (g : G) (e : E), p (g • e) = p e) {x : X} (e₀ : ↥(p ⁻¹' {x}))
    (hfree : ∀ g : G, g • (e₀ : E) = (e₀ : E) → g = 1)
    (htrans : ∀ e : ↥(p ⁻¹' {x}), ∃ g : G, g • (e₀ : E) = (e : E)) :
    (cov.monodromyHom x).range ≃* G := by
  letI : MulAction G ↥(p ⁻¹' {x}) := fibreAction hover x
  have hsmul : ∀ (g : G) (e : ↥(p ⁻¹' {x})), ((g • e : ↥(p ⁻¹' {x})) : E) = g • (e : E) :=
    fun _ _ => rfl
  refine commutingEquiv (x₀ := e₀) (fun g hg => hfree g (by rw [← hsmul, hg]))
    (fun e => (htrans e).imp fun g hg => Subtype.ext (by rw [hsmul, hg])) _ ?_ ?_
  · -- monodromy commutes with the deck action
    rintro σ ⟨γ, rfl⟩ g e
    refine Subtype.ext ?_
    rw [hsmul]
    have h := cov.monodromy_comp_deck (g := fun e : E => g • e) (hcont g) (hover g) γ.toPath e
    simpa [IsCoveringMap.monodromyHom_apply, hsmul] using h
  · -- monodromy is transitive on the fibre
    intro e
    obtain ⟨γ, hγ⟩ := cov.orbitMap_surjective x e₀ e
    exact ⟨cov.monodromyHom x γ, ⟨γ, rfl⟩, hγ⟩

end Rigidity.RET.Analytic

end
