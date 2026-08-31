/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.HasseLevel
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.PlaceRestrict

/-!
# The decomposition subgroups of an arbitrary Galois extension of a number field

An infinite Galois extension of a number field has no finite places of its own, but its ring of
integers still has nonzero primes, and the stabiliser of such a prime is the decomposition subgroup
there.  The Galois group acts transitively on the primes above a given prime of any subfield: the
ring of integers of the extension is the ring of invariants of the ring of integers of the base,
the action is continuous for the discrete topology because the stabiliser of an integer is open,
and the Galois group of an arbitrary Galois extension is profinite, so the transitivity statement
for finite quotients passes to the limit.

Transitivity is what turns a statement about the places of a finite level into a statement about
the decomposition subgroups of the whole group.  An automorphism whose restriction to a level fixes
a place there differs, modulo the subgroup fixing the level, from an automorphism fixing a prime of
the big ring of integers above that place; so a homomorphism killing the level and every
decomposition subgroup kills everything.  That is the form in which the local conditions of a
local-global principle are stated: as membership in the subgroup of classes dying on every
decomposition subgroup.

## Main definitions

* `InverseGalois.CFT.finiteDecompositionSubgroups`: **the decomposition subgroups at the finite
  places of an arbitrary Galois extension of a number field**, the stabilisers of the nonzero
  primes of its ring of integers.
* `InverseGalois.CFT.finiteDecompositionSubgroupsOutside`: the same for the primes whose place of
  the base field avoids a prescribed set.
* `InverseGalois.CFT.infiniteDecompositionSubgroups`: **the decomposition subgroups at the infinite
  places of an arbitrary Galois extension of a number field**, the stabilisers of its archimedean
  places.

## Main results

* `InverseGalois.CFT.exists_smul_eq_of_under_eq_ringOfIntegers`: **the Galois group of an arbitrary
  Galois extension acts transitively on the primes of its integers above a prime of the base.**
* `InverseGalois.CFT.exists_stabilizer_prime_restrictNormalHom_eq`: **an automorphism of a level
  fixing a place there is the restriction of an automorphism fixing a prime above.**
* `InverseGalois.CFT.eq_one_of_finiteDecomposition`,
  `InverseGalois.CFT.eq_one_of_finiteDecompositionOutside`: **a homomorphism into a commutative
  group which kills a level and every decomposition subgroup is trivial.**
* `InverseGalois.CFT.eq_one_of_mem_sha1`, `InverseGalois.CFT.eq_one_of_mem_sha1_outside`: **a class
  of the first cohomology with trivial coefficients dying on every decomposition subgroup is
  trivial.**

## Tags

number field, infinite Galois theory, decomposition group, local-global principle, profinite group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

open scoped Pointwise

/-! ### The prime of a subfield below a moved prime -/

section Tower

variable {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K] [IsGalois k F]

variable (F) in
/-- **The prime of the middle field below a moved prime is the moved prime below**, for raw ideals
and with no finiteness anywhere: an element of the middle field lies in one exactly when the
automorphism carries it into the prime of the top field. -/
theorem under_smul_ringOfIntegers (σ : Gal(K/k)) (P : Ideal (𝓞 K)) :
    Ideal.under (𝓞 F) (σ • P) = AlgEquiv.restrictNormalHom F σ • Ideal.under (𝓞 F) P := by
  ext a
  rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap,
    ← map_inv (AlgEquiv.restrictNormalHom F) σ, algebraMap_smul_ringOfIntegers F]

end Tower

/-! ### Transitivity on the primes of an arbitrary Galois extension -/

section Transitive

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [IsGalois F K]

/-- **The ring of integers of an arbitrary Galois extension is invariant over the ring of integers
of the base**: an integer fixed by every automorphism lies in the base field, and being integral it
lies in the ring of integers of the base. -/
theorem isInvariant_ringOfIntegers_of_isGalois :
    Algebra.IsInvariant (𝓞 F) (𝓞 K) Gal(K/F) := by
  refine ⟨fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : K)).2
    fun f => congrArg (algebraMap (𝓞 K) K) (hb f)
  have hyint : IsIntegral ℤ y := by
    rw [← isIntegral_algebraMap_iff (B := K) (algebraMap F K).injective, hy]
    exact b.isIntegral.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  refine ⟨⟨y, hyint⟩, RingOfIntegers.ext ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F K]
  exact hy

omit [IsGalois F K] in
/-- Scalars from the base commute with the Galois action on the ring of integers, the automorphisms
fixing the base field. -/
theorem smulCommClass_ringOfIntegers : SMulCommClass Gal(K/F) (𝓞 F) (𝓞 K) := by
  refine ⟨fun σ a b => ?_⟩
  have hfix : σ • algebraMap (𝓞 F) (𝓞 K) a = algebraMap (𝓞 F) (𝓞 K) a := by
    refine RingOfIntegers.ext ?_
    show σ ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = _
    rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 F) F K]
    exact σ.commutes _
  simp only [Algebra.smul_def, smul_mul', hfix]

/-- The Galois group acts continuously on the ring of integers with its discrete topology, the
stabiliser of an integer being open for the Krull topology. -/
theorem continuousSMul_ringOfIntegers :
    haveI : TopologicalSpace (𝓞 K) := ⊥
    ContinuousSMul Gal(K/F) (𝓞 K) := by
  letI : TopologicalSpace (𝓞 K) := ⊥
  haveI : DiscreteTopology (𝓞 K) := ⟨rfl⟩
  refine continuousSMul_iff_stabilizer_isOpen.2 fun b => ?_
  have hst : (stabilizer Gal(K/F) b : Set Gal(K/F))
      = (stabilizer Gal(K/F) ((b : K)) : Set Gal(K/F)) := by
    ext σ
    simp only [SetLike.mem_coe, mem_stabilizer_iff]
    exact ⟨fun h => congrArg (algebraMap (𝓞 K) K) h, fun h => RingOfIntegers.ext h⟩
  rw [hst]
  exact stabilizer_isOpen_of_isIntegral (b : K)

variable {F K} in
/-- **The Galois group of an arbitrary Galois extension acts transitively on the primes of its
integers above a prime of the integers of the base.**  The ring of integers above is the ring of
invariants of the ring of integers below, the action is continuous for the discrete topology, and
the Galois group is profinite, so transitivity at the finite levels passes to the limit. -/
theorem exists_smul_eq_of_under_eq_ringOfIntegers (P Q : Ideal (𝓞 K)) [P.IsPrime] [Q.IsPrime]
    (h : Ideal.under (𝓞 F) P = Ideal.under (𝓞 F) Q) : ∃ ρ : Gal(K/F), Q = ρ • P := by
  haveI := isInvariant_ringOfIntegers_of_isGalois F K
  haveI := smulCommClass_ringOfIntegers F K
  letI : TopologicalSpace (𝓞 K) := ⊥
  haveI : DiscreteTopology (𝓞 K) := ⟨rfl⟩
  haveI := continuousSMul_ringOfIntegers F K
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite P Q h

end Transitive

/-! ### Lifting an automorphism of a level that fixes a place -/

section Lift

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]

omit [NumberField k] [NumberField ↥L] in
/-- **An automorphism of a level fixing a finite place there is the restriction of an automorphism
of the whole extension fixing a prime of its integers above that place.**  Some prime lies above,
the restriction of any lift of the automorphism carries it to another prime above the same place,
and the Galois group over the level moves the second back to the first. -/
theorem exists_stabilizer_prime_restrictNormalHom_eq {τ : Gal(↥L/k)}
    {v : HeightOneSpectrum (𝓞 ↥L)} (hv : τ • v = v) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.under (𝓞 ↥L) P = v.asIdeal ∧
      ∃ ρ : Gal(K/k), ρ • P = P ∧
        AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L ρ = τ := by
  haveI := v.isPrime
  obtain ⟨P, -, hPp, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := 𝓞 ↥L) (S := 𝓞 K) v.asIdeal ⊥ (by simp)
  haveI := hPp
  have hPunder : Ideal.under (𝓞 ↥L) P = v.asIdeal := hPu
  have hPbot : P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hPunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  obtain ⟨σ₀, hσ₀⟩ := restrictNormalHom_surjective_level L τ
  have h1 : Ideal.under (𝓞 ↥L) (σ₀ • P) = Ideal.under (𝓞 ↥L) P := by
    rw [under_smul_ringOfIntegers ↥L, hσ₀, hPunder, ← asIdeal_smul, hv]
  obtain ⟨ρ₀, hρ₀⟩ := exists_smul_eq_of_under_eq_ringOfIntegers (F := ↥L) (σ₀ • P) P h1
  refine ⟨P, hPp, hPbot, hPunder, ρ₀.restrictScalars k * σ₀, ?_, ?_⟩
  · rw [mul_smul]
    exact hρ₀.symm
  · rw [map_mul, restrictNormalHom_restrictScalars k ↥L ρ₀, one_mul, hσ₀]

end Lift

/-! ### The decomposition subgroups -/

section Family

variable (k K : Type*) [Field k] [NumberField k] [Field K] [Algebra k K]

/-- **The decomposition subgroups at the finite places of an arbitrary Galois extension of a number
field**: the stabilisers of the nonzero primes of its ring of integers. -/
def finiteDecompositionSubgroups : Set (Subgroup Gal(K/k)) :=
  {D | ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ D = stabilizer Gal(K/k) P}

/-- The decomposition subgroups at the nonzero primes whose place of the base field avoids a
prescribed set. -/
def finiteDecompositionSubgroupsOutside (S : Set (HeightOneSpectrum (𝓞 k))) :
    Set (Subgroup Gal(K/k)) :=
  {D | ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
    (∀ q ∈ S, Ideal.under (𝓞 k) P ≠ q.asIdeal) ∧ D = stabilizer Gal(K/k) P}

omit [NumberField k] in
variable {k K} in
/-- Avoiding a set of places of the base field is a restriction on a decomposition subgroup. -/
theorem finiteDecompositionSubgroupsOutside_subset (S : Set (HeightOneSpectrum (𝓞 k))) :
    finiteDecompositionSubgroupsOutside k K S ⊆ finiteDecompositionSubgroups k K :=
  fun _ ⟨P, hPp, hPbot, _, hD⟩ => ⟨P, hPp, hPbot, hD⟩

/-- **The decomposition subgroups at the infinite places of an arbitrary Galois extension of a
number field**: the stabilisers of its archimedean places. -/
def infiniteDecompositionSubgroups : Set (Subgroup Gal(K/k)) :=
  {D | ∃ w : InfinitePlace K, D = stabilizer Gal(K/k) w}

end Family

/-! ### A homomorphism killing every decomposition subgroup -/

section Hom

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]
  {M : Type*} [CommGroup M] (u : Gal(K/k) →* M) (hker : L.fixingSubgroup ≤ u.ker)

include hker

omit [NumberField k] [NumberField ↥L] in
/-- A homomorphism killing a level and the decomposition subgroup at some prime above a place of
that level kills every automorphism whose restriction to the level fixes the place. -/
theorem eq_one_of_restrictNormalHom_smul_eq {x : Gal(K/k)} {v : HeightOneSpectrum (𝓞 ↥L)}
    (hv : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L x • v = v)
    (h : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥L) P = v.asIdeal →
      ∀ σ ∈ stabilizer Gal(K/k) P, u σ = 1) : u x = 1 := by
  obtain ⟨P, hPp, hPbot, hPunder, ρ, hρP, hρres⟩ :=
    exists_stabilizer_prime_restrictNormalHom_eq L hv
  have hu1 : u ρ = 1 := h P hPp hPbot hPunder ρ hρP
  have hfix : x * ρ⁻¹ ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker, map_mul, map_inv, hρres,
      mul_inv_cancel]
  have hsplit : u x = u (x * ρ⁻¹) * u ρ := by rw [← map_mul, inv_mul_cancel_right]
  rw [hsplit, MonoidHom.mem_ker.1 (hker hfix), hu1, one_mul]

/-- **A homomorphism into a commutative group which kills a level and every decomposition subgroup
at a nonzero prime whose place of the base field avoids a finite set is trivial.**  An automorphism
whose restriction to the level fixes a place there agrees, modulo the subgroup fixing the level,
with an automorphism fixing a prime above. -/
theorem eq_one_of_finiteDecompositionOutside {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite)
    (h : ∀ D ∈ finiteDecompositionSubgroupsOutside k K S, ∀ σ ∈ D, u σ = 1) (σ : Gal(K/k)) :
    u σ = 1 := by
  refine eq_one_of_levelDecompositionOutside L u hker hS (fun x hx => ?_) σ
  obtain ⟨v, hvS, hv⟩ := mem_levelDecompositionSetOutside.1 hx
  refine eq_one_of_restrictNormalHom_smul_eq L u hker hv (fun P hPp hPbot hPunder => ?_)
  refine h _ ⟨P, hPp, hPbot, fun q hq hcon => hvS ?_, rfl⟩
  have hunder : Ideal.under (𝓞 k) P = (primeUnder (𝓞 k) v).asIdeal := by
    rw [primeUnder_asIdeal, ← hPunder, Ideal.under_under]
  have heq : primeUnder (𝓞 k) v = q := HeightOneSpectrum.ext (hunder.symm.trans hcon)
  rw [heq]
  exact hq

/-- **A homomorphism into a commutative group which kills a level and every decomposition subgroup
at a nonzero prime is trivial.** -/
theorem eq_one_of_finiteDecomposition
    (h : ∀ D ∈ finiteDecompositionSubgroups k K, ∀ σ ∈ D, u σ = 1) (σ : Gal(K/k)) : u σ = 1 :=
  eq_one_of_finiteDecompositionOutside L u hker Set.finite_empty
    (fun D hD => h D (finiteDecompositionSubgroupsOutside_subset ∅ hD)) σ

end Hom

/-! ### The classes of the first cohomology that die on every decomposition subgroup -/

section Cohomology

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M]
  (htriv : ∀ (g : Gal(K/k)) (m : M), g • m = m)

include htriv

/-- **A class of the first cohomology with trivial coefficients dying on every decomposition
subgroup at a nonzero prime whose place of the base field avoids a finite set is trivial.**  The
class is represented at a finite Galois level, and a cocycle for a trivial action is a
homomorphism. -/
theorem eq_one_of_mem_sha1_outside {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite)
    (z : SmoothH1 Gal(K/k) M) (hz : z ∈ sha1 M (finiteDecompositionSubgroupsOutside k K S)) :
    z = 1 := by
  haveI := isSmoothAction_of_trivial htriv
  obtain ⟨E, hEfin, hEgal, -, u, hu, hs, hcon, rfl⟩ := exists_isGalois_smooth₁ z
  haveI := hEfin
  haveI := hEgal
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  rw [smoothH1Mk_eq_one_iff_of_trivial htriv]
  refine funext fun σ => ?_
  show u σ = 1
  refine eq_one_of_finiteDecompositionOutside E (cocycleHom htriv hu)
    (fun x hx => MonoidHom.mem_ker.2 ?_) hS (fun D hD d hd => ?_) σ
  · have h1 := hcon 1 x hx
    rw [one_mul] at h1
    rw [cocycleHom_apply, h1, map_one_of_isMulCocycle₁ hu]
  · rw [cocycleHom_apply]
    exact (smoothH1Mk_mem_sha1_of_trivial htriv hu hs).1 hz D hD d hd

/-- **A class of the first cohomology with trivial coefficients dying on every decomposition
subgroup at a nonzero prime is trivial.** -/
theorem eq_one_of_mem_sha1 (z : SmoothH1 Gal(K/k) M)
    (hz : z ∈ sha1 M (finiteDecompositionSubgroups k K)) : z = 1 := by
  refine eq_one_of_mem_sha1_outside htriv Set.finite_empty z ?_
  rw [mem_sha1] at hz ⊢
  exact fun D hD => hz D (finiteDecompositionSubgroupsOutside_subset ∅ hD)

end Cohomology

end InverseGalois.CFT
