/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DecompositionLocalPower

/-!
# From a completion back to a decomposition subgroup

A radicand which is a `p`-th power in the completion of the base field below a place of an
arbitrary Galois extension has all of its radicals fixed by the decomposition subgroup at that
place.  This is the direction opposite to the one the descent to a level was written for, and it
needs no new mathematics: the criterion for an extension of number fields is an equivalence, and
the decomposition subgroup of the whole extension maps into the decomposition group of a level, so
the level statement can be read back upstairs.

For a unit of a level the same passage turns a `p`-th power in the completion at a place below into
a `p`-th power in the compositum of the level with the fixed field of the decomposition subgroup.
A radical is fixed by every automorphism over the level lying in the decomposition subgroup; the
automorphisms fixing the compositum are exactly those which fix the level and lie in the
decomposition subgroup, so the radical is fixed by all of them and therefore lies in the compositum,
the fixed field of the subgroup fixing a subfield being that subfield.

Together with the comparison in the other direction this identifies the two readings of a local
condition on a Kummer class: the profinite one, that the class dies on a decomposition subgroup, and
the idelic one, that it dies in the units of a completion.  No approximation of a henselization by a
completion is involved: the extension cut out by a radical is Galois, so one root landing in a
completion drags all of them along.

## Main results

* `InverseGalois.CFT.forall_stabilizer_smul_eq_of_exists_pow_adicCompletion`: **the decomposition
  subgroup at a nonzero prime of the integers of an arbitrary Galois extension fixes a radical as
  soon as the radicand is a `p`-th power in the completion of the base field below.**
* `InverseGalois.CFT.forall_stabilizer_smul_eq_of_exists_pow_infiniteCompletion`: **the same at an
  archimedean place.**
* `InverseGalois.CFT.mem_sup_of_forall_stabilizer_ideal_smul_eq`: an element fixed by every
  automorphism over a level which fixes a prime lies in the compositum of the level with the fixed
  field of the decomposition subgroup at that prime.
* `InverseGalois.CFT.exists_pow_sup_of_exists_pow_adicUnitHom`: **a unit of a level which is a
  `p`-th power in the completion at a place below a prime is a `p`-th power in the compositum of the
  level with the fixed field of the decomposition subgroup at that prime**, provided the whole
  extension contains a radical.
* `InverseGalois.CFT.exists_pow_sup_of_exists_pow_infiniteUnitHom`: **the same at an archimedean
  place.**

## Tags

number field, decomposition group, Kummer theory, completion, local power, compositum
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The finite places -/

section FiniteLevelPower

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {p : ℕ}

/-- **The decomposition subgroup at a nonzero prime of the integers of an arbitrary Galois extension
fixes a radical as soon as the radicand is a `p`-th power in the completion of the base field
below**, the base field containing the `p`-th roots of unity.  The radical lies in a finite Galois
level, the criterion for an extension of number fields applies at that level, and the decomposition
subgroup maps to the decomposition group of the level at the place below the prime. -/
theorem forall_stabilizer_smul_eq_of_exists_pow_adicCompletion {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0) {b : Ω} {a : k}
    (ha : algebraMap k Ω a = b ^ p)
    {v : HeightOneSpectrum (𝓞 k)} (hv : v.asIdeal = Ideal.under (𝓞 k) P)
    (hc : ∃ c : v.adicCompletion k, c ^ p = algebraMap k (v.adicCompletion k) a)
    (σ : ↥(stabilizer Gal(Ω/k) P)) : (σ : Gal(Ω/k)) b = b := by
  obtain ⟨L, hLfin, hLgal, hbL⟩ := exists_isGalois_level_mem k b
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  have hunder : Ideal.under (𝓞 k) (Ideal.under (𝓞 ↥L) P) = v.asIdeal := by
    rw [Ideal.under_under, hv]
  have hbot : Ideal.under (𝓞 ↥L) P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  haveI : (Ideal.under (𝓞 ↥L) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ↥L), w.asIdeal = Ideal.under (𝓞 ↥L) P :=
    ⟨⟨Ideal.under (𝓞 ↥L) P, inferInstance, hbot⟩, rfl⟩
  have hbb : (algebraMap (↥L) Ω) (⟨b, hbL⟩ : ↥L) = b := rfl
  have haL : algebraMap k ↥L a = (⟨b, hbL⟩ : ↥L) ^ p := by
    refine (algebraMap (↥L) Ω).injective ?_
    rw [← IsScalarTower.algebraMap_apply k ↥L Ω, map_pow, hbb, ha]
  have hveq : primeUnder (𝓞 k) w = v :=
    HeightOneSpectrum.ext (by rw [primeUnder_asIdeal, hw, hunder])
  subst hveq
  have hfixL := (forall_stabilizer_smul_eq_iff_exists_pow w hζ hp haL).2 hc
  have h' : ((stabilizerRestrictPrime L hw σ : Gal(↥L/k)) (⟨b, hbL⟩ : ↥L) : Ω) = b := by
    rw [hfixL (stabilizerRestrictPrime L hw σ)]
  rw [coe_stabilizerRestrictPrime, AlgEquiv.restrictNormalHom_apply] at h'
  exact h'

end FiniteLevelPower

/-! ### The infinite places -/

section InfiniteLevelPower

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {p : ℕ}

/-- **The decomposition subgroup at an archimedean place of an arbitrary Galois extension fixes a
radical as soon as the radicand is a `p`-th power in the completion of the base field below**, the
base field containing the `p`-th roots of unity. -/
theorem forall_stabilizer_smul_eq_of_exists_pow_infiniteCompletion {W : InfinitePlace Ω}
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0) {b : Ω} {a : k}
    (ha : algebraMap k Ω a = b ^ p)
    {u : InfinitePlace k} (hu : u = W.comap (algebraMap k Ω))
    (hc : ∃ c : u.Completion, c ^ p = algebraMap k u.Completion a)
    (σ : ↥(stabilizer Gal(Ω/k) W)) : (σ : Gal(Ω/k)) b = b := by
  obtain ⟨L, hLfin, hLgal, hbL⟩ := exists_isGalois_level_mem k b
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  obtain ⟨v, hvdef⟩ : ∃ v : InfinitePlace ↥L, v = W.comap (algebraMap ↥L Ω) := ⟨_, rfl⟩
  have hbb : (algebraMap (↥L) Ω) (⟨b, hbL⟩ : ↥L) = b := rfl
  have haL : algebraMap k ↥L a = (⟨b, hbL⟩ : ↥L) ^ p := by
    refine (algebraMap (↥L) Ω).injective ?_
    rw [← IsScalarTower.algebraMap_apply k ↥L Ω, map_pow, hbb, ha]
  have hvu : v.comap (algebraMap k ↥L) = u := by
    rw [hvdef, ← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq, hu]
  subst hvu
  have hfixL := (forall_stabilizer_smul_eq_iff_exists_pow_infinite v hζ hp haL).2 hc
  have h' : ((stabilizerRestrictInfinitePlace L hvdef σ : Gal(↥L/k)) (⟨b, hbL⟩ : ↥L) : Ω) = b := by
    rw [hfixL (stabilizerRestrictInfinitePlace L hvdef σ)]
  rw [coe_stabilizerRestrictInfinitePlace, AlgEquiv.restrictNormalHom_apply] at h'
  exact h'

end InfiniteLevelPower

/-! ### Descending into the compositum -/

section MemSup

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω}

/-- **An element fixed by every automorphism over a level which lies in a subgroup lies in the
compositum of the level with the fixed field of that subgroup.**  An automorphism fixing the
compositum fixes the level, so it is an automorphism over the level, and it lies in the subgroup;
and a subfield is the fixed field of the automorphisms fixing it. -/
theorem mem_sup_of_forall_restrictScalars_mem {D : Subgroup Gal(Ω/k)}
    (hF : F.fixingSubgroup = D) {b : Ω}
    (hb : ∀ σ : Gal(Ω/↥K), (σ.restrictScalars k) ∈ D → σ b = b) : b ∈ K ⊔ F := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (K ⊔ F), IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, hF] at hτ
  obtain ⟨hτK, hτD⟩ := hτ
  have hrs : (IntermediateField.fixingSubgroupEquiv K ⟨τ, hτK⟩).restrictScalars k = τ :=
    AlgEquiv.ext fun _ => rfl
  exact hb (IntermediateField.fixingSubgroupEquiv K ⟨τ, hτK⟩) (by rw [hrs]; exact hτD)

/-- An element fixed by every automorphism over a level which fixes a prime lies in the compositum
of the level with the fixed field of the decomposition subgroup at that prime. -/
theorem mem_sup_of_forall_stabilizer_ideal_smul_eq {P : Ideal (𝓞 Ω)}
    (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P) {b : Ω}
    (hb : ∀ σ : ↥(stabilizer Gal(Ω/↥K) P), (σ : Gal(Ω/↥K)) b = b) : b ∈ K ⊔ F := by
  refine mem_sup_of_forall_restrictScalars_mem hF fun σ hσ => hb ⟨σ, ?_⟩
  refine mem_stabilizer_iff.mpr ?_
  rw [← smul_restrictScalars_ideal]
  exact mem_stabilizer_iff.mp hσ

/-- An element fixed by every automorphism over a level which fixes an archimedean place lies in the
compositum of the level with the fixed field of the decomposition subgroup at that place. -/
theorem mem_sup_of_forall_stabilizer_infinitePlace_smul_eq {W : InfinitePlace Ω}
    (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) W) {b : Ω}
    (hb : ∀ σ : ↥(stabilizer Gal(Ω/↥K) W), (σ : Gal(Ω/↥K)) b = b) : b ∈ K ⊔ F := by
  refine mem_sup_of_forall_restrictScalars_mem hF fun σ hσ => hb ⟨σ, ?_⟩
  refine mem_stabilizer_iff.mpr ?_
  rw [← smul_restrictScalars_infinitePlace]
  exact mem_stabilizer_iff.mp hσ

end MemSup

/-! ### A single unit -/

section OneUnit

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω} [NumberField ↥K] {p : ℕ} {ζ : ↥K}
  (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
  (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)

omit [IsGalois k Ω] [NumberField ↥K] in
include hj in
/-- A radical of a unit of a level which lies in the compositum of the level with another subfield
exhibits the unit as a `p`-th power there, the radical being nonzero because its power is. -/
theorem exists_pow_sup_of_mem_sup (hp : p ≠ 0) {a : (↥K)ˣ} {b : Ω}
    (hb : b ^ p = algebraMap ↥K Ω (a : ↥K)) (hmem : b ∈ K ⊔ F) :
    ∃ c : (↥(K ⊔ F))ˣ, c ^ p = j a := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h, zero_pow hp] at hb
    exact Units.ne_zero a ((algebraMap ↥K Ω).injective (by rw [map_zero, ← hb]))
  have hxne : (⟨b, hmem⟩ : ↥(K ⊔ F)) ≠ 0 := fun h =>
    hbne ((congrArg (algebraMap ↥(K ⊔ F) Ω) h).trans (map_zero _))
  refine ⟨Units.mk0 ⟨b, hmem⟩ hxne, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  refine (algebraMap ↥(K ⊔ F) Ω).injective ?_
  rw [map_pow]
  show b ^ p = algebraMap ↥(K ⊔ F) Ω ((j a : ↥(K ⊔ F)))
  rw [hb]
  exact (congrArg Units.val (hj a)).symm

include hj in
/-- **A unit of a level which is a `p`-th power in the completion of the level at the place below a
prime is a `p`-th power in the compositum of the level with the fixed field of the decomposition
subgroup at that prime**, provided the whole extension contains a radical.  The radical is fixed by
every automorphism over the level which fixes the prime, and the automorphisms fixing the compositum
are exactly those. -/
theorem exists_pow_sup_of_exists_pow_adicUnitHom (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P)
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P) {a : (↥K)ˣ} {b : Ω}
    (hb : b ^ p = algebraMap ↥K Ω (a : ↥K))
    (hc : ∃ c : (v.adicCompletion ↥K)ˣ, c ^ p = adicUnitHom v a) :
    ∃ c : (↥(K ⊔ F))ˣ, c ^ p = j a := by
  obtain ⟨c, hcv⟩ := hc
  have hc' : ∃ d : v.adicCompletion ↥K, d ^ p = algebraMap ↥K (v.adicCompletion ↥K) (a : ↥K) :=
    ⟨(c : v.adicCompletion ↥K), by rw [← Units.val_pow_eq_pow_val, hcv]; rfl⟩
  exact exists_pow_sup_of_mem_sup j hj hp hb
    (mem_sup_of_forall_stabilizer_ideal_smul_eq hF fun σ =>
      forall_stabilizer_smul_eq_of_exists_pow_adicCompletion (k := ↥K) hζ hp hb.symm hv hc' σ)

include hj in
/-- **A unit of a level which is a `p`-th power in the completion of the level at the place below an
archimedean place is a `p`-th power in the compositum of the level with the fixed field of the
decomposition subgroup at that place**, provided the whole extension contains a radical. -/
theorem exists_pow_sup_of_exists_pow_infiniteUnitHom (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {W : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) W)
    {u : InfinitePlace ↥K} (hu : u = W.comap (algebraMap ↥K Ω)) {a : (↥K)ˣ} {b : Ω}
    (hb : b ^ p = algebraMap ↥K Ω (a : ↥K))
    (hc : ∃ c : u.Completionˣ, c ^ p = infiniteUnitHom u a) :
    ∃ c : (↥(K ⊔ F))ˣ, c ^ p = j a := by
  obtain ⟨c, hcv⟩ := hc
  have hc' : ∃ d : u.Completion, d ^ p = algebraMap ↥K u.Completion (a : ↥K) :=
    ⟨(c : u.Completion), by rw [← Units.val_pow_eq_pow_val, hcv]; rfl⟩
  exact exists_pow_sup_of_mem_sup j hj hp hb
    (mem_sup_of_forall_stabilizer_infinitePlace_smul_eq hF fun σ =>
      forall_stabilizer_smul_eq_of_exists_pow_infiniteCompletion (k := ↥K) hζ hp hb.symm hu hc' σ)

end OneUnit

end InverseGalois.CFT
