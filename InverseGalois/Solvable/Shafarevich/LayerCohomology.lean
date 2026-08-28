/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerShrink

/-!
# Killing cohomology classes by shrinking

A cohomology class of a finite group with coefficients in a module is represented by a cocycle,
and a cocycle is a function on a finite set, so it takes only finitely many values.  A homomorphism
of coefficients that kills all of them kills the class.  This turns the counting argument in a
layer, which annihilates finitely many prescribed elements of the layer, into a statement about
cohomology: finitely many prescribed classes with coefficients in a layer of a generic operator
group are annihilated all at once by a suitable surjective shrinking homomorphism.

Passing through cocycles this way avoids any appeal to dimension shifting, and hence to Tate
cohomology: the argument is the same in every degree.

## Main definitions

* `InverseGalois.Shafarevich.genericLayer` — a layer of a generic operator group, as a
  representation of the operator group.
* `InverseGalois.Shafarevich.genericShrinkRep` — the morphism of representations induced by a
  shrinking homomorphism.

## Main results

* `InverseGalois.Shafarevich.map_π_eq_zero` — a morphism of representations killing every value of
  a cocycle kills the class of that cocycle.
* `InverseGalois.Shafarevich.exists_genericShrink_map_eq_zero` — **finitely many cohomology
  classes, in any single degree, with coefficients in a layer of a generic operator group are
  annihilated by a surjective shrinking homomorphism**, provided the number of blocks is large
  enough.

## Tags

Shafarevich's theorem, embedding problem, group cohomology, p-central series
-/

namespace InverseGalois.Shafarevich

open CategoryTheory

/-! ### Killing a class by killing the values of a cocycle -/

section Cochain

variable {k G : Type} [CommRing k] [Group G] {A B : Rep k G}

/-- The value of a mapped cochain. -/
theorem cochainsMap_id_apply (φ : A ⟶ B) (n : ℕ)
    (c : (groupCohomology.inhomogeneousCochains A).X n) (g : Fin n → G) :
    (groupCohomology.cochainsMap (MonoidHom.id G) φ).f n c g = φ.hom (c g) := rfl

/-- **A morphism of representations under which every value of a cocycle vanishes annihilates the
class of that cocycle.** -/
theorem map_π_eq_zero (φ : A ⟶ B) {n : ℕ} (x : groupCohomology.cocycles A n)
    (h : ∀ g : Fin n → G, φ.hom (groupCohomology.iCocycles A n x g) = 0) :
    groupCohomology.map (MonoidHom.id G) φ n (groupCohomology.π A n x) = 0 := by
  have hz : groupCohomology.cocyclesMap (MonoidHom.id G) φ n x = 0 := by
    have hinj : Function.Injective (groupCohomology.iCocycles B n) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine hinj ?_
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (groupCohomology.cochainsMap (MonoidHom.id G) φ) n) x
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc, map_zero]
    exact funext fun g => h g
  rw [groupCohomology.π_map_apply, hz, map_zero]

end Cochain

/-! ### The layers of a generic operator group as representations -/

section Generic

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

/-- A layer of a generic operator group, as a representation of the operator group. -/
noncomputable abbrev genericLayer (ℓ j : ℕ) : Rep (ZMod ℓ) U := Rep.of (genericLayerRep U n S ℓ j)

set_option maxRecDepth 4000 in
/-- The morphism of representations induced by a shrinking homomorphism. -/
noncomputable def genericShrinkRep (ℓ j : ℕ) (a : Fin r → ℕ) :
    genericLayer U (r * n) S ℓ j ⟶ genericLayer U n S ℓ j where
  hom := ModuleCat.ofHom (layerLinear ℓ (genericShrink U r n S a) j)
  comm u := by
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    exact layerMap_genericShrink_genericLayerRep U r n S a ℓ j u v

omit [Finite U] [Finite S] in
@[simp]
theorem genericShrinkRep_hom_apply (ℓ j : ℕ) (a : Fin r → ℕ)
    (v : Layer ℓ (Generic U (r * n) S) j) :
    (genericShrinkRep U r n S ℓ j a).hom v = layerMap ℓ (genericShrink U r n S a) j v := rfl

/-- **Finitely many cohomology classes with coefficients in a layer of a generic operator group can
be annihilated all at once by a surjective shrinking homomorphism.**  The number of scalar
equations to be solved is the number of classes, times the number of arguments of a cochain in the
degree in question, times the dimension of the layer downstairs; the number of blocks has to exceed
that, times one more than the level of the layer. -/
theorem exists_genericShrink_map_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t c : ℕ}
    (hr : (j + 1) * (t * Nat.card U ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (x : Fin t → groupCohomology (genericLayer U (r * n) S ℓ j) c) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, groupCohomology.map (MonoidHom.id U) (genericShrinkRep U r n S ℓ j a) c (x ν) = 0 := by
  choose z hz using fun ν =>
    (ModuleCat.epi_iff_surjective (groupCohomology.π (genericLayer U (r * n) S ℓ j) c)).1
      inferInstance (x ν)
  have hcard : Nat.card (Fin t × (Fin c → U)) = t * Nat.card U ^ c := by
    simp [Nat.card_prod, Nat.card_fun]
  have hr' : (j + 1) * (Nat.card (Fin t × (Fin c → U)) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by rwa [hcard]
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerMap_eq_zero U r n S hS hr'
    fun q : Fin t × (Fin c → U) =>
      groupCohomology.iCocycles (genericLayer U (r * n) S ℓ j) c (z q.1) q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hz ν]
  exact map_π_eq_zero _ _ fun g => ha (ν, g)

end Generic

end InverseGalois.Shafarevich
