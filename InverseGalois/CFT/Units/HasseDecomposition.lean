/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.HasseInflation
import InverseGalois.CFT.Units.InfiniteDecomposition

/-!
# Inflation from the field trivialising the coefficients, from the decomposition subgroups

A class of the first cohomology of the Galois group of an arbitrary Galois extension of a number
field, with coefficients acted on through a finite Galois level, is inflated from that level as
soon as it is locally trivial at every finite Galois level over it.  Local triviality there is a
statement about the places of a level, and what a local-global principle actually provides is a
statement about the decomposition subgroups of the whole group: the class dies on the stabiliser of
every nonzero prime of the ring of integers of the top field.

The two are the same because the Galois group acts transitively on the primes above a given place,
so an automorphism whose restriction to a level fixes a place there agrees, modulo the subgroup
fixing the level, with an automorphism fixing a prime above.  Local triviality at the decomposition
subgroups is in fact the stronger-looking hypothesis, and it gives the vanishing outright, with no
level in sight.

Inflation from a finite level is injective, so the everywhere locally trivial classes of the big
group are a copy of a subgroup of the first cohomology of the level: **the everywhere locally
trivial classes embed in the cohomology of the finite Galois group of the field trivialising the
coefficients.**

## Main results

* `InverseGalois.CFT.eq_one_of_finiteDecompositionOutside_over`: **a cocycle dying on every
  decomposition subgroup vanishes over the field trivialising its coefficients.**
* `InverseGalois.CFT.exists_galInflH1_eq_of_finiteDecomposition`,
  `InverseGalois.CFT.exists_galInflH1_eq_of_finiteDecompositionOutside`: **a class dying on every
  decomposition subgroup is inflated from the field trivialising its coefficients.**
* `InverseGalois.CFT.exists_galInflH1_eq_of_mem_sha1`,
  `InverseGalois.CFT.sha1_le_range_galInflH1`: **an everywhere locally trivial class is inflated
  from the field trivialising its coefficients.**
* `InverseGalois.CFT.shaInflH1_injective`: **an everywhere locally trivial class is determined by
  the class it comes from at that field.**

## Tags

number field, Galois cohomology, inflation, decomposition group, local-global principle
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

open scoped Pointwise

section Bridge

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  [MulDistribMulAction (F ≃ₐ[k] F) M]
  (hπ : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)
  {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u)

include hπ hu

omit [IsSmoothAction Gal(K/k) M] [FiniteDimensional k F] in
/-- **A cocycle whose restriction over the field trivialising the coefficients dies on every
decomposition subgroup at a nonzero prime whose place of that field avoids a finite set vanishes
there.**  Every automorphism over the field agrees, modulo the subgroup fixing a suitable level,
with one fixing a prime. -/
theorem eq_one_of_finiteDecompositionOutside_over
    (L : IntermediateField ↥F K) [NumberField ↥L] [IsGalois ↥F ↥L]
    {S : Set (HeightOneSpectrum (𝓞 ↥F))} (hS : S.Finite)
    (hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (hD : ∀ D ∈ finiteDecompositionSubgroupsOutside ↥F K S, ∀ ρ ∈ D,
      u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) (ρ : K ≃ₐ[↥F] K) :
    u (ρ.restrictScalars k) = 1 :=
  eq_one_of_finiteDecompositionOutside L
    (cocycleHomOver F (fun _ hσ m => smul_eq_self_of_mem_fixingSubgroup F hπ hσ m) hu)
    (fun τ hτ => MonoidHom.mem_ker.mpr (hlev τ hτ)) hS
    (fun D hDmem τ hτ => hD D hDmem τ hτ) ρ

/-- **A class dying on every decomposition subgroup at a nonzero prime whose place of the field
trivialising its coefficients avoids a finite set is inflated from that field.** -/
theorem exists_galInflH1_eq_of_finiteDecompositionOutside (hs : IsSmooth₁ u)
    {S : Set (HeightOneSpectrum (𝓞 ↥F))} (hS : S.Finite)
    (hD : ∀ D ∈ finiteDecompositionSubgroupsOutside ↥F K S, ∀ ρ ∈ D,
      u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs := by
  refine exists_galInflH1_eq_of_forall_level_outside F hπ hu hs hS ?_
  intro L _ _ hlev ρ _
  exact eq_one_of_finiteDecompositionOutside_over F hπ hu L hS hlev hD ρ

/-- **A class dying on every decomposition subgroup at a nonzero prime is inflated from the field
trivialising its coefficients.** -/
theorem exists_galInflH1_eq_of_finiteDecomposition (hs : IsSmooth₁ u)
    (hD : ∀ D ∈ finiteDecompositionSubgroups ↥F K, ∀ ρ ∈ D,
      u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs :=
  exists_galInflH1_eq_of_finiteDecompositionOutside F hπ hu hs Set.finite_empty
    (fun D hDmem => hD D (finiteDecompositionSubgroupsOutside_subset ∅ hDmem))

end Bridge

/-! ### The everywhere locally trivial classes, read at the level -/

section Sha

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  [MulDistribMulAction (F ≃ₐ[k] F) M]
  (hπ : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)

include hπ

/-- **An everywhere locally trivial class of the first cohomology is inflated from the field
trivialising its coefficients.**  An automorphism over that field fixing a prime of the top field
fixes it over the base too, so the primitive of the cocycle on the decomposition subgroup there is
moved to itself by the automorphism and the cocycle vanishes on it. -/
theorem exists_galInflH1_eq_of_mem_sha1 (z : SmoothH1 Gal(K/k) M)
    (hz : z ∈ sha1 M (decompositionSubgroups k K)) :
    ∃ y : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ y = z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  refine exists_galInflH1_eq_of_finiteDecomposition F hπ hu hs ?_
  rintro D ⟨P, hPp, hPbot, rfl⟩ ρ hρ
  obtain ⟨t, ht⟩ := (smoothH1Mk_mem_sha1 hu hs).1 hz (stabilizer Gal(K/k) P)
    (finiteDecompositionSubgroups_subset ⟨P, hPp, hPbot, rfl⟩)
  have hmem : (ρ : K ≃ₐ[↥F] K).restrictScalars k ∈ stabilizer Gal(K/k) P := by
    rw [mem_stabilizer_iff]
    exact mem_stabilizer_iff.1 hρ
  have h1 := ht _ hmem
  rwa [smul_eq_self_of_mem_fixingSubgroup F hπ (restrictScalars_mem_fixingSubgroup F ρ) t,
    div_self', eq_comm] at h1

variable (M) in
/-- **The everywhere locally trivial classes of the first cohomology sit in the image of inflation
from the field trivialising the coefficients.** -/
theorem sha1_le_range_galInflH1 :
    sha1 M (decompositionSubgroups k K) ≤ (galInflH1 F hπ).range :=
  fun z hz => exists_galInflH1_eq_of_mem_sha1 F hπ z hz

variable (M) in
/-- **The everywhere locally trivial classes of the first cohomology, read at the field trivialising
the coefficients**: the class they inflate to, which determines them. -/
noncomputable def shaInflH1 :
    ↥(sha1 M (decompositionSubgroups k K)) →* SmoothH1 (↥F ≃ₐ[k] ↥F) M :=
  ((MonoidHom.ofInjective (galInflH1_injective F hπ)).symm.toMonoidHom).comp
    (Subgroup.inclusion (sha1_le_range_galInflH1 M F hπ))

variable (M) in
/-- Reading an everywhere locally trivial class at the level and inflating it back gives the class
again. -/
theorem galInflH1_shaInflH1 (z : ↥(sha1 M (decompositionSubgroups k K))) :
    galInflH1 F hπ (shaInflH1 M F hπ z) = (z : SmoothH1 Gal(K/k) M) :=
  congrArg Subtype.val
    ((MonoidHom.ofInjective (galInflH1_injective F hπ)).apply_symm_apply
      (Subgroup.inclusion (sha1_le_range_galInflH1 M F hπ) z))

variable (M) in
/-- **An everywhere locally trivial class of the first cohomology is determined by the class it
comes from at the field trivialising the coefficients.** -/
theorem shaInflH1_injective : Function.Injective (shaInflH1 M F hπ) := fun z z' h =>
  Subtype.ext (by
    rw [← galInflH1_shaInflH1 M F hπ z, ← galInflH1_shaInflH1 M F hπ z', h])

end Sha

end InverseGalois.CFT
