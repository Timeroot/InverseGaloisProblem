/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Trivial
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.CFT.Units.HasseHom

/-!
# Local triviality at a level of an infinite Galois group

An infinite Galois extension of a number field has no places of its own, but each of its finite
Galois levels is a number field and has them, and an automorphism of the big field is *local at a
place of a level* when its restriction to that level fixes a place there.  The automorphisms local
at some place of a fixed level form the preimage of the union of the decomposition groups of that
level.

A homomorphism into a commutative group which kills the level, that is, kills every automorphism
restricting to the identity there, factors through the Galois group of the level; if it kills every
automorphism local at a place of the level then the induced homomorphism kills every decomposition
group of the level, so it is trivial and the original homomorphism is trivial too.  The level is
where the homomorphism already lives, so the preimages are the decomposition groups themselves as
far as it can see, and no places of the big field are needed.

For coefficients on which the big Galois group acts trivially this is the vanishing of the
everywhere locally trivial classes of the first cohomology: a cocycle is a homomorphism, a
coboundary is trivial, and a smooth cocycle kills a level.

## Main definitions

* `InverseGalois.CFT.levelDecompositionSet`: **the automorphisms whose restriction to a level fixes
  a place of that level.**
* `InverseGalois.CFT.levelDecompositionSetOutside`: the same for the finite places away from a
  finite set of places of the base field.

## Main results

* `InverseGalois.CFT.eq_one_of_levelDecomposition`,
  `InverseGalois.CFT.eq_one_of_levelDecompositionOutside`: **a homomorphism into a commutative
  group which kills a level and every automorphism local at a place of that level is trivial.**
* `InverseGalois.CFT.smoothH1Mk_eq_one_of_levelDecomposition`: **the corresponding class of the
  first cohomology with trivial coefficients is trivial.**

## Tags

number field, infinite Galois theory, level, decomposition group, local-global principle
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

/-! ### The automorphisms local at a place of a level -/

section Definition

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K]
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]

/-- **The automorphisms whose restriction to a level fixes a place of that level.** -/
def levelDecompositionSet : Set Gal(K/k) :=
  {σ | AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ ∈ decompositionSet k ↥L}

omit [NumberField k] [NumberField ↥L] in
variable {L} in
theorem mem_levelDecompositionSet {σ : Gal(K/k)} :
    σ ∈ levelDecompositionSet L ↔
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ ∈ decompositionSet k ↥L := Iff.rfl

omit [NumberField k] [NumberField ↥L] in
variable {L} in
/-- An automorphism whose restriction to a level fixes a finite place of the level is local
there. -/
theorem mem_levelDecompositionSet_of_prime {σ : Gal(K/k)} {v : HeightOneSpectrum (𝓞 ↥L)}
    (hv : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ • v = v) :
    σ ∈ levelDecompositionSet L := Or.inl ⟨v, hv⟩

omit [NumberField k] [NumberField ↥L] in
variable {L} in
/-- An automorphism whose restriction to a level fixes an infinite place of the level is local
there. -/
theorem mem_levelDecompositionSet_of_infinitePlace {σ : Gal(K/k)} {w : InfinitePlace ↥L}
    (hw : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ • w = w) :
    σ ∈ levelDecompositionSet L := Or.inr ⟨w, hw⟩

variable (S : Set (HeightOneSpectrum (𝓞 k)))

/-- The automorphisms whose restriction to a level fixes a finite place of the level whose place
below avoids a prescribed finite set. -/
def levelDecompositionSetOutside : Set Gal(K/k) :=
  {σ | AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ ∈ decompositionSetOutside k ↥L S}

omit [NumberField k] in
variable {L S} in
theorem mem_levelDecompositionSetOutside {σ : Gal(K/k)} :
    σ ∈ levelDecompositionSetOutside L S ↔
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ ∈ decompositionSetOutside k ↥L S :=
  Iff.rfl

end Definition

/-! ### A homomorphism killing a level and its decomposition groups -/

section Hom

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]
  {M : Type*} [CommGroup M] (u : Gal(K/k) →* M) (hker : L.fixingSubgroup ≤ u.ker)

include hker

omit [NumberField k] [NumberField ↥L] in
/-- A homomorphism killing a level is the composition of restriction to that level with a
homomorphism of the Galois group of the level. -/
theorem exists_comp_restrictNormalHom :
    ∃ f : Gal(↥L/k) →* M, ∀ σ : Gal(K/k),
      f (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ) = u σ := by
  obtain ⟨g, hg⟩ := (restrictNormalHom_surjective_level L).hasRightInverse
  have hle : (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L).ker ≤ u.ker := by
    rwa [IntermediateField.restrictNormalHom_ker]
  exact ⟨(AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L).liftOfRightInverse g hg ⟨u, hle⟩,
    fun σ => MonoidHom.liftOfRightInverse_comp_apply _ g hg ⟨u, hle⟩ σ⟩

/-- **A homomorphism into a commutative group which kills a level and every automorphism local at a
place of that level is trivial.** -/
theorem eq_one_of_levelDecomposition (h : ∀ σ ∈ levelDecompositionSet L, u σ = 1)
    (σ : Gal(K/k)) : u σ = 1 := by
  obtain ⟨f, hf⟩ := exists_comp_restrictNormalHom L u hker
  rw [← hf σ]
  refine eq_one_of_forall_mem_decompositionSet f (fun τ hτ => ?_) _
  obtain ⟨x, rfl⟩ := restrictNormalHom_surjective_level L τ
  rw [hf]
  exact h x hτ

/-- **A homomorphism into a commutative group which kills a level and every automorphism local at a
finite place of that level away from a finite set of places of the base field is trivial.** -/
theorem eq_one_of_levelDecompositionOutside {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite)
    (h : ∀ σ ∈ levelDecompositionSetOutside L S, u σ = 1) (σ : Gal(K/k)) : u σ = 1 := by
  obtain ⟨f, hf⟩ := exists_comp_restrictNormalHom L u hker
  rw [← hf σ]
  refine eq_one_of_forall_mem_decompositionSetOutside f hS (fun τ hτ => ?_) _
  obtain ⟨x, rfl⟩ := restrictNormalHom_surjective_level L τ
  rw [hf]
  exact h x hτ

end Hom

/-! ### The classes of the first cohomology that vanish -/

section Cohomology

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M]
  (htriv : ∀ (g : Gal(K/k)) (m : M), g • m = m)
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]

include htriv

/-- **A class of the first cohomology with trivial coefficients represented by a cocycle vanishing
on a level and on the automorphisms local at a place of that level is trivial.** -/
theorem smoothH1Mk_eq_one_of_levelDecomposition {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) (hker : ∀ σ ∈ L.fixingSubgroup, u σ = 1)
    (h : ∀ σ ∈ levelDecompositionSet L, u σ = 1) : smoothH1Mk u hu hs = 1 := by
  rw [smoothH1Mk_eq_one_iff_of_trivial htriv]
  refine funext fun σ => ?_
  show u σ = 1
  exact eq_one_of_levelDecomposition L (cocycleHom htriv hu)
    (fun x hx => MonoidHom.mem_ker.mpr (hker x hx)) (fun x hx => h x hx) σ

/-- **A class of the first cohomology with trivial coefficients represented by a cocycle vanishing
on a level and on the automorphisms local at a finite place of that level away from a finite set of
places of the base field is trivial.** -/
theorem smoothH1Mk_eq_one_of_levelDecompositionOutside {S : Set (HeightOneSpectrum (𝓞 k))}
    (hS : S.Finite) {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u)
    (hker : ∀ σ ∈ L.fixingSubgroup, u σ = 1)
    (h : ∀ σ ∈ levelDecompositionSetOutside L S, u σ = 1) : smoothH1Mk u hu hs = 1 := by
  rw [smoothH1Mk_eq_one_iff_of_trivial htriv]
  refine funext fun σ => ?_
  show u σ = 1
  exact eq_one_of_levelDecompositionOutside L (cocycleHom htriv hu)
    (fun x hx => MonoidHom.mem_ker.mpr (hker x hx)) hS (fun x hx => h x hx) σ

end Cohomology

end InverseGalois.CFT
