/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.StructureConstant
import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.CenterlessExtension

/-!
# The rigidity → inner-automorphism bridge

The centerless extension lemma (`RET.CenterlessExtension.extend_surjective_of_inner`) consumes an
**inner-automorphism hypothesis**: that conjugation by each arithmetic element, transported through
the monodromy, is an inner automorphism of `G`.  In the branch-cycle descent this hypothesis is
supplied by *rigidity + rationality*: the Galois-twisted monodromy tuple lies in the same rational
conjugacy classes, and rigidity forces it to be **simultaneously conjugate** to the original tuple —
so the twist is inner.

This file proves that group-theoretic content, **axiom-free**, on top of the already-proven
structure-constant theorem `Rigidity.rigid_card_iff_single_orbit`.  It is the piece that the field
tower feeds into the extension lemma once the branch-cycle formula identifies the Galois twist as
another element of `rigidTuples C`.

## Main results

* `Rigidity.exists_pointwise_conj_of_rigid` — under centerless + the structure-constant condition,
  any two generating product-one tuples in the prescribed classes are related by a single global
  conjugation (the explicit, coordinatewise-conjugation form of `rigid_card_iff_single_orbit`).
* `Rigidity.RET.sphereHom_inner_equiv_of_rigid` — consequently the monodromy homomorphisms
  `SphereGroup r ↠ G` attached to two such tuples differ by an inner automorphism of `G`:
  `sphereHom g₂ = (conj c) ∘ sphereHom g₁`.  This is precisely the "same cover up to inner twist"
  statement the descent needs.
-/

open scoped BigOperators

namespace Rigidity

variable {G : Type*} [Group G]

/-- **Explicit conjugation form of rigidity.**  For a centerless group whose structure constant is
`1` (`Nat.card (rigidTuples C) = Nat.card G`), any two generating product-one tuples `g₁, g₂` in the
prescribed classes `C` are related by a *single* global conjugation: there is `c : G` with
`g₂ i = c * g₁ i * c⁻¹` for all `i`.

This unpacks `rigid_card_iff_single_orbit` (single `ConjAct G`-orbit) into the coordinatewise
conjugation statement the branch-cycle descent uses. -/
theorem exists_pointwise_conj_of_rigid {r : ℕ} {C : Fin r → ConjClasses G} [Finite G]
    (hZ : Subgroup.center G = ⊥) (hrigid : Nat.card (rigidTuples C) = Nat.card G)
    {g₁ g₂ : Fin r → G} (hg₁ : g₁ ∈ rigidTuples C) (hg₂ : g₂ ∈ rigidTuples C) :
    ∃ c : G, ∀ i, g₂ i = c * g₁ i * c⁻¹ := by
  obtain ⟨x, hx⟩ :=
    (rigid_card_iff_single_orbit hZ ⟨g₁, hg₁⟩).mp hrigid g₁ hg₁ g₂ hg₂
  refine ⟨ConjAct.ofConjAct x, fun i => ?_⟩
  have hi : (x • g₁) i = g₂ i := congrFun hx i
  rw [Pi.smul_apply, ConjAct.smul_def] at hi
  exact hi.symm

namespace RET

variable {r : ℕ}

/-- **Monodromy homomorphisms of rigid tuples differ by an inner automorphism.**  If `g₁, g₂` are
generating product-one tuples in the prescribed rational classes `C` of a centerless group with
structure constant `1`, then the induced surjections `sphereHom gᵢ : SphereGroup r ↠ G` satisfy
`sphereHom g₂ = (MulAut.conj c) ∘ sphereHom g₁` for some `c : G`.

This is the "connected cover determined up to inner twist" statement: the branch-cycle descent
produces `g₂` as a Galois twist of `g₁` (in the same rational classes), and this lemma turns
rigidity into the inner-automorphism hypothesis consumed by `extend_surjective_of_inner`. -/
theorem sphereHom_inner_equiv_of_rigid {C : Fin r → ConjClasses G} [Finite G]
    (hZ : Subgroup.center G = ⊥) (hrigid : Nat.card (rigidTuples C) = Nat.card G)
    {g₁ g₂ : Fin r → G} (hg₁ : g₁ ∈ rigidTuples C) (hg₂ : g₂ ∈ rigidTuples C)
    (hg₁prod : (List.ofFn g₁).prod = 1) (hg₂prod : (List.ofFn g₂).prod = 1) :
    ∃ c : G, sphereHom g₂ hg₂prod = (MulAut.conj c).toMonoidHom.comp (sphereHom g₁ hg₁prod) := by
  obtain ⟨c, hc⟩ := exists_pointwise_conj_of_rigid hZ hrigid hg₁ hg₂
  refine ⟨c, ?_⟩
  -- `g₂` equals the coordinatewise `c`-conjugate of `g₁`, so the two homs agree by `sphereHom_conj`.
  have hfun : g₂ = fun i => MulAut.conj c (g₁ i) := by
    funext i; rw [hc i]; rfl
  -- Rewrite the target hom through that function equality (proof-irrelevant `prod = 1` field).
  subst hfun
  exact sphereHom_conj g₁ hg₁prod c

end RET

end Rigidity
