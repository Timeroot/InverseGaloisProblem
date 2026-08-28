/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerCohomology

/-!
# Killing homology classes by shrinking

A homology class of a group with coefficients in a module is represented by a cycle, and a cycle is
a finitely supported function on the tuples of group elements, so it takes only finitely many
values.  A homomorphism of coefficients that kills all of them kills the class.  This mirrors the
argument in cohomology exactly, and turns the counting argument in a layer into a statement about
homology: finitely many prescribed classes with coefficients in a layer of a generic operator group
are annihilated all at once by a suitable surjective shrinking homomorphism.

Having the count in homology as well as in cohomology is what removes the need for Tate cohomology
altogether.  The two degrees in which the count is used are an ordinary cohomological degree and a
negative Tate degree, and the latter is an ordinary homological degree.

## Main results

* `InverseGalois.Shafarevich.homology_map_π_eq_zero` — a morphism of representations killing every
  value of a cycle kills the class of that cycle.
* `InverseGalois.Shafarevich.exists_genericShrink_homology_map_eq_zero` — **finitely many homology
  classes, in any single degree, with coefficients in a layer of a generic operator group are
  annihilated by a surjective shrinking homomorphism**, provided the number of blocks is large
  enough.

## Tags

Shafarevich's theorem, embedding problem, group homology, p-central series
-/

namespace InverseGalois.Shafarevich

open CategoryTheory

/-! ### Killing a class by killing the values of a cycle -/

section Chain

variable {k G : Type} [CommRing k] [Group G] {A B : Rep k G}

/-- The values of a cycle, as a finitely supported function on the tuples of group elements. -/
noncomputable def cycleFun {n : ℕ} (x : groupHomology.cycles A n) : (Fin n → G) →₀ A :=
  groupHomology.iCycles A n x

/-- **A morphism of representations under which every value of a cycle vanishes annihilates the
class of that cycle.** -/
theorem homology_map_π_eq_zero (φ : A ⟶ B) {n : ℕ} (x : groupHomology.cycles A n)
    (h : ∀ g : Fin n → G, φ.hom (cycleFun x g) = 0) :
    groupHomology.map (MonoidHom.id G) φ n (groupHomology.π A n x) = 0 := by
  have hz : groupHomology.cyclesMap (MonoidHom.id G) φ n x = 0 := by
    have hinj : Function.Injective (groupHomology.iCycles B n) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine hinj ?_
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (groupHomology.chainsMap (MonoidHom.id G) φ) n) x
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc, map_zero]
    refine Finsupp.ext fun g => ?_
    simpa using h g
  rw [groupHomology.π_map_apply, hz, map_zero]

end Chain

/-! ### The count in homology -/

section Generic

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Finitely many homology classes with coefficients in a layer of a generic operator group can be
annihilated all at once by a surjective shrinking homomorphism.**  The number of scalar equations to
be solved is the number of classes, times the number of arguments of a chain in the degree in
question, times the dimension of the layer downstairs; the number of blocks has to exceed that,
times one more than the level of the layer. -/
theorem exists_genericShrink_homology_map_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t c : ℕ}
    (hr : (j + 1) * (t * Nat.card U ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (x : Fin t → groupHomology (genericLayer U (r * n) S ℓ j) c) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, groupHomology.map (B := genericLayer U n S ℓ j) (MonoidHom.id U)
        (genericShrinkRep U r n S ℓ j a) c (x ν) = 0 := by
  choose z hz using fun ν =>
    (ModuleCat.epi_iff_surjective (groupHomology.π (genericLayer U (r * n) S ℓ j) c)).1
      inferInstance (x ν)
  have hcard : Nat.card (Fin t × (Fin c → U)) = t * Nat.card U ^ c := by
    simp [Nat.card_prod, Nat.card_fun]
  have hr' : (j + 1) * (Nat.card (Fin t × (Fin c → U)) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by rwa [hcard]
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerMap_eq_zero U r n S hS hr'
    fun q : Fin t × (Fin c → U) => cycleFun (z q.1) q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hz ν]
  exact homology_map_π_eq_zero _ _ fun g => ha (ν, g)

end Generic

end InverseGalois.Shafarevich
