/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DecompositionLocalPower
import InverseGalois.CFT.Kummer.LocalPowRepresentatives
import InverseGalois.CFT.Kummer.LocalPowerRange

/-!
# The units of a compositum with a decomposition field, modulo `p`-th powers

Let `K` be a number field inside a Galois extension `Ω` of a base field, let `F` be the fixed field
of the decomposition subgroup at a place of `Ω`, and suppose `K` contains a primitive `p`-th root of
unity and every element of `Ω` has a `p`-th root there.  Then **every unit of the compositum
`K ⊔ F` is a unit of `K` times a `p`-th power of the compositum**: the compositum is no larger than
`K` modulo `p`-th powers.

The proof is local.  The compositum with a decomposition field is, place by place, the fixed field
of the decomposition group, so the criterion for a radical to be fixed by that group turns a
statement about the compositum into a statement about the completion of `K` at the place below.
There the units modulo `p`-th powers form a finite group, and finitely many units of `K` represent
all of its classes; the given unit of the compositum, whose `p`-th root generates the level to work
in, differs from one of those representatives by a `p`-th power locally, hence by a radical which
the criterion places back inside the compositum.

Taking the finitely many representatives **before** choosing the level is what keeps the argument
inside a single finite extension of `K`: the level need only contain a `p`-th root of the given unit
together with `p`-th roots of the representatives, and no further root has to be adjoined once the
local computation has been performed.

Tensoring with coefficients of finite rank over the field with `p` elements preserves the
conclusion: a pure tensor whose left factor is a unit of the compositum is, modulo `p`-th powers,
one whose left factor is a unit of `K`, and a `p`-th power crosses the tensor sign to annihilate the
coefficients.

## Main results

* `InverseGalois.CFT.exists_isGalois_level_subset`: **a finite set of an infinite Galois extension
  lies in a finite Galois level.**
* `InverseGalois.CFT.mem_sup_of_forall_stabilizer_fix_ideal`: **an element fixed by the
  decomposition group at a prime, over a subfield, lies in the compositum of that subfield with the
  decomposition field.**
* `InverseGalois.CFT.exists_mul_pow_eq_sup_of_stabilizer_ideal`: **every unit of the compositum of a
  number field with the decomposition field at a prime is a unit of the number field times a `p`-th
  power.**
* `InverseGalois.CFT.exists_mul_pow_eq_sup_of_stabilizer_infinitePlace`: **the same at an
  archimedean place.**
* `InverseGalois.CFT.surjective_tensor_sup_of_stabilizer_ideal`: **the units of a number field
  tensored with coefficients of finite rank over the prime field surject onto the units of that
  compositum tensored with them.**
* `InverseGalois.CFT.surjective_tensor_sup_of_stabilizer_infinitePlace`: **the same at an
  archimedean place.**

## Tags

number field, decomposition group, compositum, Kummer theory, local power class
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise TensorProduct

/-! ### A finite Galois level containing a finite set -/

section Level

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

variable (k) in
/-- **A finite set of an infinite Galois extension lies in a finite Galois level**, namely the
Galois closure of the subfield the set generates, which is finite over the base because the set
is. -/
theorem exists_isGalois_level_subset (S : Set Ω) (hS : S.Finite) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k ↥L ∧ IsGalois k ↥L ∧ S ⊆ (L : Set Ω) := by
  haveI := hS.to_subtype
  exact ⟨(FiniteGaloisIntermediateField.adjoin k S).toIntermediateField,
    (FiniteGaloisIntermediateField.adjoin k S).finiteDimensional,
    (FiniteGaloisIntermediateField.adjoin k S).isGalois,
    FiniteGaloisIntermediateField.subset_adjoin k S⟩

end Level

/-! ### Membership in the compositum -/

section Sup

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K : IntermediateField k Ω}

/-- **An element of an infinite Galois extension fixed by every automorphism over a subfield whose
restriction lies in a subgroup lies in the compositum of that subfield with the fixed field of the
subgroup.**  The compositum is fixed by exactly the automorphisms fixing both factors, and an
automorphism fixing the subfield is the restriction of an automorphism over it. -/
theorem mem_sup_of_forall_restrictScalars_fix {F : IntermediateField k Ω}
    {D : Subgroup Gal(Ω/k)} (hF : F.fixingSubgroup = D) {b : Ω}
    (hb : ∀ σ : Gal(Ω/↥K), (σ.restrictScalars k) ∈ D → σ b = b) : b ∈ K ⊔ F := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (K ⊔ F), IntermediateField.mem_fixedField_iff]
  intro g hg
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, hF] at hg
  have hgg : ((IntermediateField.fixingSubgroupEquiv K ⟨g, hg.1⟩ : Gal(Ω/↥K)).restrictScalars k)
      = g := rfl
  exact hb (IntermediateField.fixingSubgroupEquiv K ⟨g, hg.1⟩) (by rw [hgg]; exact hg.2)

/-- **An element fixed by the decomposition group at a prime, over a subfield, lies in the
compositum of that subfield with the decomposition field.** -/
theorem mem_sup_of_forall_stabilizer_fix_ideal {F : IntermediateField k Ω} {P : Ideal (𝓞 Ω)}
    (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P) {b : Ω}
    (hb : ∀ σ : ↥(stabilizer Gal(Ω/↥K) P), (σ : Gal(Ω/↥K)) b = b) : b ∈ K ⊔ F :=
  mem_sup_of_forall_restrictScalars_fix hF fun σ hσ =>
    hb ⟨σ, mem_stabilizer_iff.mpr
      (by rw [← smul_restrictScalars_ideal]; exact mem_stabilizer_iff.mp hσ)⟩

/-- **An element fixed by the decomposition group at an archimedean place, over a subfield, lies in
the compositum of that subfield with the decomposition field.** -/
theorem mem_sup_of_forall_stabilizer_fix_infinitePlace {F : IntermediateField k Ω}
    {W : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) W) {b : Ω}
    (hb : ∀ σ : ↥(stabilizer Gal(Ω/↥K) W), (σ : Gal(Ω/↥K)) b = b) : b ∈ K ⊔ F :=
  mem_sup_of_forall_restrictScalars_fix hF fun σ hσ =>
    hb ⟨σ, mem_stabilizer_iff.mpr
      (by rw [← smul_restrictScalars_infinitePlace]; exact mem_stabilizer_iff.mp hσ)⟩

end Sup

/-! ### One unit of the compositum -/

section Surjective

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω} [NumberField ↥K] {p : ℕ} {ζ : ↥K}
  (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
  (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)

set_option maxHeartbeats 1000000 in
include hj in
/-- **Every unit of the compositum of a number field with the decomposition field at a prime is a
unit of the number field times a `p`-th power of the compositum**, the number field containing a
primitive `p`-th root of unity and the ambient extension being closed under `p`-th roots.

A `p`-th root of the given unit, together with `p`-th roots of finitely many units of the number
field representing all the power classes of the completion at the prime below, generates a finite
Galois level.  In that level the given unit is fixed by the decomposition group, so its image in the
completion comes from the completion below; that image is one of the representatives times a `p`-th
power, and the corresponding quotient of roots is a radical whose local `p`-th power comes from
below, hence is fixed by the decomposition group and lies in the compositum. -/
theorem exists_mul_pow_eq_sup_of_stabilizer_ideal (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P)
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P)
    (b : (↥(K ⊔ F))ˣ) :
    ∃ (a : (↥K)ˣ) (c : (↥(K ⊔ F))ˣ), b = j a * c ^ p := by
  classical
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  obtain ⟨T, hTfin, hT⟩ := exists_finite_pow_representatives_adicCompletion (K := ↥K) v hp
  choose s hs using fun a : (↥K)ˣ => hroot (Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
  have hsval : ∀ a : (↥K)ˣ, ((s a : Ω)) ^ p = algebraMap ↥K Ω (a : ↥K) := by
    intro a
    have h := congrArg Units.val (hs a)
    simpa using h
  have hbΩ0 : ((b : ↥(K ⊔ F)) : Ω) ≠ 0 := by
    intro h
    exact b.ne_zero (Subtype.ext h)
  obtain ⟨r, hr⟩ := hroot (Units.mk0 (((b : ↥(K ⊔ F)) : Ω)) hbΩ0)
  have hβval : ((b : ↥(K ⊔ F)) : Ω) = ((r : Ω)) ^ p := by
    have h := congrArg Units.val hr
    simpa using h.symm
  obtain ⟨L, hLfin, hLgal, hLsub⟩ := exists_isGalois_level_subset (↥K)
    (insert ((r : Ω)) ((fun a : (↥K)ˣ => ((s a : Ω))) '' T)) ((hTfin.image _).insert _)
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite ↥K ↥L
  have hrL : (r : Ω) ∈ L := hLsub (Set.mem_insert _ _)
  have hsL : ∀ a ∈ T, ((s a : Ω)) ∈ L := fun a ha =>
    hLsub (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
  have hβmem : ((b : ↥(K ⊔ F)) : Ω) ∈ L := by rw [hβval]; exact pow_mem hrL p
  have hunder : Ideal.under (𝓞 ↥K) (Ideal.under (𝓞 ↥L) P) = v.asIdeal := by
    rw [Ideal.under_under, hv]
  have hbot : Ideal.under (𝓞 ↥L) P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  haveI : (Ideal.under (𝓞 ↥L) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ↥L), w.asIdeal = Ideal.under (𝓞 ↥L) P :=
    ⟨⟨Ideal.under (𝓞 ↥L) P, inferInstance, hbot⟩, rfl⟩
  have hveq : primeUnder (𝓞 ↥K) w = v :=
    HeightOneSpectrum.ext (by rw [primeUnder_asIdeal, hw, hunder])
  subst hveq
  have hinjL : Function.Injective (toAdicCompletion w (K := ↥L)) :=
    (toAdicCompletion w (K := ↥L)).injective
  have htower : ∀ x : ↥K, algebraMap ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K)
      (w.adicCompletion ↥L) (algebraMap ↥K ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K) x)
      = toAdicCompletion w (algebraMap ↥K ↥L x) := by
    intro x
    rw [← IsScalarTower.algebraMap_apply ↥K ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K)
      (w.adicCompletion ↥L), IsScalarTower.algebraMap_apply ↥K ↥L (w.adicCompletion ↥L)]
    rfl
  have hfixL : ∀ σ : ↥(stabilizer Gal(↥L/↥K) w),
      (σ : Gal(↥L/↥K)) (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L)
        = ⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ := by
    intro τ
    obtain ⟨σ, rfl⟩ := stabilizerRestrictPrime_surjective L hw τ
    refine Subtype.ext ?_
    rw [coe_stabilizerRestrictPrime, AlgEquiv.restrictNormalHom_apply]
    exact fix_of_mem_sup_of_mem_stabilizer_ideal hF σ (b : ↥(K ⊔ F)).2
  obtain ⟨η, hη⟩ := exists_algebraMap_eq_toAdicCompletion_of_forall_stabilizer_smul_eq
    (K := ↥K) (M := ↥L) w hfixL
  have hβL0 : (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L) ≠ 0 := by
    intro h
    exact hbΩ0 (congrArg Subtype.val h)
  have hη0 : η ≠ 0 := by
    intro h0
    refine hβL0 (hinjL ?_)
    rw [← hη, h0, map_zero, map_zero]
  obtain ⟨a, haT, δ, hδ⟩ := hT (Units.mk0 η hη0)
  have hδval : η = algebraMap ↥K ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K) (a : ↥K)
      * (δ : (primeUnder (𝓞 ↥K) w).adicCompletion ↥K) ^ p := by
    have h := congrArg Units.val hδ
    simpa using h
  have hsa0 : ((s a : Ω)) ≠ 0 := (s a).ne_zero
  have hcmemL : (r : Ω) / ((s a : Ω)) ∈ L := div_mem hrL (hsL a haT)
  have haK0 : (a : ↥K) ≠ 0 := a.ne_zero
  have haL0 : algebraMap ↥K ↥L (a : ↥K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ↥K ↥L).injective).mpr haK0
  have hX0 : toAdicCompletion w (algebraMap ↥K ↥L (a : ↥K)) ≠ 0 := by
    intro h
    exact haL0 (hinjL (by rw [h, map_zero]))
  have hcLp : (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) ^ p * algebraMap ↥K ↥L (a : ↥K)
      = (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L) := by
    refine Subtype.ext ?_
    push_cast
    rw [← hsval a, hβval, div_pow, div_mul_cancel₀ _ (pow_ne_zero p hsa0)]
  have hmapη : toAdicCompletion w (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L)
      = (algebraMap ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K) (w.adicCompletion ↥L)
            (δ : (primeUnder (𝓞 ↥K) w).adicCompletion ↥K)) ^ p
        * toAdicCompletion w (algebraMap ↥K ↥L (a : ↥K)) := by
    rw [← hη, hδval, map_mul, map_pow, htower, mul_comm]
  have hcpow : (algebraMap ((primeUnder (𝓞 ↥K) w).adicCompletion ↥K) (w.adicCompletion ↥L)
        (δ : (primeUnder (𝓞 ↥K) w).adicCompletion ↥K)) ^ p
      = (toAdicCompletion w (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L)) ^ p := by
    refine mul_right_cancel₀ hX0 ?_
    rw [← hmapη, ← map_pow, ← map_mul, hcLp]
  have hfixc : ∀ σ : ↥(stabilizer Gal(↥L/↥K) w),
      (σ : Gal(↥L/↥K)) (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L)
        = ⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ :=
    forall_stabilizer_smul_eq_of_pow_eq_pow w hζ hp hcpow
  have hfixcΩ : ∀ σ : ↥(stabilizer Gal(Ω/↥K) P),
      (σ : Gal(Ω/↥K)) ((r : Ω) / ((s a : Ω))) = (r : Ω) / ((s a : Ω)) := by
    intro σ
    have h : ((((stabilizerRestrictPrime L hw σ) : Gal(↥L/↥K))
        (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) : ↥L) : Ω)
        = ((⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) : Ω) :=
      congrArg _ (hfixc _)
    rwa [coe_stabilizerRestrictPrime, AlgEquiv.restrictNormalHom_apply] at h
  have hcmem : (r : Ω) / ((s a : Ω)) ∈ K ⊔ F :=
    mem_sup_of_forall_stabilizer_fix_ideal hF hfixcΩ
  have hc'0 : (⟨(r : Ω) / ((s a : Ω)), hcmem⟩ : ↥(K ⊔ F)) ≠ 0 := by
    intro h
    exact div_ne_zero (r.ne_zero) hsa0 (congrArg Subtype.val h)
  have hja : algebraMap ↥(K ⊔ F) Ω ((j a : ↥(K ⊔ F))) = algebraMap ↥K Ω (a : ↥K) :=
    congrArg Units.val (hj a)
  refine ⟨a, Units.mk0 (⟨(r : Ω) / ((s a : Ω)), hcmem⟩ : ↥(K ⊔ F)) hc'0, Units.ext ?_⟩
  refine (algebraMap ↥(K ⊔ F) Ω).injective ?_
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, hja]
  show ((b : ↥(K ⊔ F)) : Ω) = algebraMap ↥K Ω (a : ↥K) * ((r : Ω) / ((s a : Ω))) ^ p
  rw [div_pow, ← hsval a, hβval]
  field_simp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
include hj in
/-- **Every unit of the compositum of a number field with the decomposition field at an archimedean
place is a unit of the number field times a `p`-th power of the compositum.** -/
theorem exists_mul_pow_eq_sup_of_stabilizer_infinitePlace (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
    {V : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) V)
    {u : InfinitePlace ↥K} (hu : u = V.comap (algebraMap ↥K Ω))
    (b : (↥(K ⊔ F))ˣ) :
    ∃ (a : (↥K)ˣ) (c : (↥(K ⊔ F))ˣ), b = j a * c ^ p := by
  classical
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  obtain ⟨T, hTfin, hT⟩ := exists_finite_pow_representatives_infiniteCompletion (K := ↥K) u hp
  choose s hs using fun a : (↥K)ˣ => hroot (Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
  have hsval : ∀ a : (↥K)ˣ, ((s a : Ω)) ^ p = algebraMap ↥K Ω (a : ↥K) := by
    intro a
    have h := congrArg Units.val (hs a)
    simpa using h
  have hbΩ0 : ((b : ↥(K ⊔ F)) : Ω) ≠ 0 := by
    intro h
    exact b.ne_zero (Subtype.ext h)
  obtain ⟨r, hr⟩ := hroot (Units.mk0 (((b : ↥(K ⊔ F)) : Ω)) hbΩ0)
  have hβval : ((b : ↥(K ⊔ F)) : Ω) = ((r : Ω)) ^ p := by
    have h := congrArg Units.val hr
    simpa using h.symm
  obtain ⟨L, hLfin, hLgal, hLsub⟩ := exists_isGalois_level_subset (↥K)
    (insert ((r : Ω)) ((fun a : (↥K)ˣ => ((s a : Ω))) '' T)) ((hTfin.image _).insert _)
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite ↥K ↥L
  have hrL : (r : Ω) ∈ L := hLsub (Set.mem_insert _ _)
  have hsL : ∀ a ∈ T, ((s a : Ω)) ∈ L := fun a ha =>
    hLsub (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
  have hβmem : ((b : ↥(K ⊔ F)) : Ω) ∈ L := by rw [hβval]; exact pow_mem hrL p
  obtain ⟨wL, hwL⟩ : ∃ wL : InfinitePlace ↥L, wL = V.comap (algebraMap ↥L Ω) := ⟨_, rfl⟩
  have hvu : wL.comap (algebraMap ↥K ↥L) = u := by
    rw [hwL, ← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq, hu]
  subst hvu
  have hinjL : Function.Injective (algebraMap ↥L wL.Completion) :=
    (algebraMap ↥L wL.Completion).injective
  have htower : ∀ x : ↥K, algebraMap ((wL.comap (algebraMap ↥K ↥L)).Completion) wL.Completion
      (algebraMap ↥K ((wL.comap (algebraMap ↥K ↥L)).Completion) x)
      = algebraMap ↥L wL.Completion (algebraMap ↥K ↥L x) :=
    fun x => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hfixL : ∀ σ : ↥(stabilizer Gal(↥L/↥K) wL),
      (σ : Gal(↥L/↥K)) (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L)
        = ⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ := by
    intro τ
    obtain ⟨σ, rfl⟩ := stabilizerRestrictInfinitePlace_surjective L hwL τ
    refine Subtype.ext ?_
    rw [coe_stabilizerRestrictInfinitePlace, AlgEquiv.restrictNormalHom_apply]
    exact fix_of_mem_sup_of_mem_stabilizer_infinitePlace hF σ (b : ↥(K ⊔ F)).2
  obtain ⟨η, hη⟩ := exists_algebraMap_eq_of_forall_stabilizer_smul_eq_infinite
    (K := ↥K) (M := ↥L) wL hfixL
  have hβL0 : (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L) ≠ 0 := by
    intro h
    exact hbΩ0 (congrArg Subtype.val h)
  have hη0 : η ≠ 0 := by
    intro h0
    refine hβL0 (hinjL ?_)
    rw [← hη, h0, map_zero, map_zero]
  obtain ⟨a, haT, δ, hδ⟩ := hT (Units.mk0 η hη0)
  have hδval : η = algebraMap ↥K ((wL.comap (algebraMap ↥K ↥L)).Completion) (a : ↥K)
      * (δ : (wL.comap (algebraMap ↥K ↥L)).Completion) ^ p := by
    have h := congrArg Units.val hδ
    simpa using h
  have hsa0 : ((s a : Ω)) ≠ 0 := (s a).ne_zero
  have hcmemL : (r : Ω) / ((s a : Ω)) ∈ L := div_mem hrL (hsL a haT)
  have haK0 : (a : ↥K) ≠ 0 := a.ne_zero
  have haL0 : algebraMap ↥K ↥L (a : ↥K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ↥K ↥L).injective).mpr haK0
  have hX0 : algebraMap ↥L wL.Completion (algebraMap ↥K ↥L (a : ↥K)) ≠ 0 := by
    intro h
    exact haL0 (hinjL (by rw [h, map_zero]))
  have hcLp : (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) ^ p * algebraMap ↥K ↥L (a : ↥K)
      = (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L) := by
    refine Subtype.ext ?_
    push_cast
    rw [← hsval a, hβval, div_pow, div_mul_cancel₀ _ (pow_ne_zero p hsa0)]
  have hmapη : algebraMap ↥L wL.Completion (⟨((b : ↥(K ⊔ F)) : Ω), hβmem⟩ : ↥L)
      = (algebraMap ((wL.comap (algebraMap ↥K ↥L)).Completion) wL.Completion
            (δ : (wL.comap (algebraMap ↥K ↥L)).Completion)) ^ p
        * algebraMap ↥L wL.Completion (algebraMap ↥K ↥L (a : ↥K)) := by
    rw [← hη, hδval, map_mul, map_pow, htower, mul_comm]
  have hcpow : (algebraMap ((wL.comap (algebraMap ↥K ↥L)).Completion) wL.Completion
        (δ : (wL.comap (algebraMap ↥K ↥L)).Completion)) ^ p
      = (algebraMap ↥L wL.Completion (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L)) ^ p := by
    refine mul_right_cancel₀ hX0 ?_
    rw [← hmapη, ← map_pow, ← map_mul, hcLp]
  have hfixc : ∀ σ : ↥(stabilizer Gal(↥L/↥K) wL),
      (σ : Gal(↥L/↥K)) (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L)
        = ⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ :=
    forall_stabilizer_smul_eq_of_pow_eq_pow_infinite wL hζ hp hcpow
  have hfixcΩ : ∀ σ : ↥(stabilizer Gal(Ω/↥K) V),
      (σ : Gal(Ω/↥K)) ((r : Ω) / ((s a : Ω))) = (r : Ω) / ((s a : Ω)) := by
    intro σ
    have h : ((((stabilizerRestrictInfinitePlace L hwL σ) : Gal(↥L/↥K))
        (⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) : ↥L) : Ω)
        = ((⟨(r : Ω) / ((s a : Ω)), hcmemL⟩ : ↥L) : Ω) :=
      congrArg _ (hfixc _)
    rwa [coe_stabilizerRestrictInfinitePlace, AlgEquiv.restrictNormalHom_apply] at h
  have hcmem : (r : Ω) / ((s a : Ω)) ∈ K ⊔ F :=
    mem_sup_of_forall_stabilizer_fix_infinitePlace hF hfixcΩ
  have hc'0 : (⟨(r : Ω) / ((s a : Ω)), hcmem⟩ : ↥(K ⊔ F)) ≠ 0 := by
    intro h
    exact div_ne_zero (r.ne_zero) hsa0 (congrArg Subtype.val h)
  have hja : algebraMap ↥(K ⊔ F) Ω ((j a : ↥(K ⊔ F))) = algebraMap ↥K Ω (a : ↥K) :=
    congrArg Units.val (hj a)
  refine ⟨a, Units.mk0 (⟨(r : Ω) / ((s a : Ω)), hcmem⟩ : ↥(K ⊔ F)) hc'0, Units.ext ?_⟩
  refine (algebraMap ↥(K ⊔ F) Ω).injective ?_
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, hja]
  show ((b : ↥(K ⊔ F)) : Ω) = algebraMap ↥K Ω (a : ↥K) * ((r : Ω) / ((s a : Ω))) ^ p
  rw [div_pow, ← hsval a, hβval]
  field_simp

end Surjective

/-! ### A whole class -/

section Tensor

/-- **A homomorphism of abelian groups whose target is generated by the image together with the
`p`-th powers stays surjective after tensoring with coefficients of finite rank over the field with
`p` elements.**  A pure tensor is rewritten with its left factor split as an image times a `p`-th
power, and the `p`-th power crosses the tensor sign to annihilate the coefficients. -/
theorem surjective_tensor_map_of_forall_exists_mul_pow {A B : Type*} [CommGroup A] [CommGroup B]
    {p d : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module ℤ W]
    (e : W ≃+ (Fin d → ZMod p)) (f : A →* B)
    (hf : ∀ b : B, ∃ (a : A) (c : B), b = f a * c ^ p) :
    Function.Surjective (TensorProduct.map (MonoidHom.toAdditive f).toIntLinearMap
      (LinearMap.id : W →ₗ[ℤ] W)) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x w =>
    obtain ⟨a, c, hc⟩ := hf (Additive.toMul x)
    have hx : x = Additive.ofMul (f a) + p • Additive.ofMul c := by
      rw [← ofMul_pow, ← ofMul_mul, ← hc]
      rfl
    refine ⟨Additive.ofMul a ⊗ₜ[ℤ] w, ?_⟩
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hx, TensorProduct.add_tmul, Tate.nsmul_tmul,
      Tate.nsmul_eq_zero_of_equivPi e, TensorProduct.tmul_zero, add_zero]
    rfl
  | add t t' ht ht' =>
    obtain ⟨s, rfl⟩ := ht
    obtain ⟨s', rfl⟩ := ht'
    exact ⟨s + s', map_add _ _ _⟩

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω} [NumberField ↥K] {p d : ℕ} [Fact p.Prime] {ζ : ↥K}
  {W : Type*} [AddCommGroup W] [Module ℤ W] (e : W ≃+ (Fin d → ZMod p))
  (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
  (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)

include e hj in
/-- **The units of a number field tensored with coefficients of finite rank over the prime field
surject onto the units of its compositum with the decomposition field at a prime tensored with
them.** -/
theorem surjective_tensor_sup_of_stabilizer_ideal (hζ : IsPrimitiveRoot ζ p)
    (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P)
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P) :
    Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : W →ₗ[ℤ] W)) :=
  surjective_tensor_map_of_forall_exists_mul_pow e j
    (exists_mul_pow_eq_sup_of_stabilizer_ideal j hj hζ (Nat.Prime.ne_zero Fact.out) hroot hF hv)

include e hj in
/-- **The units of a number field tensored with coefficients of finite rank over the prime field
surject onto the units of its compositum with the decomposition field at an archimedean place
tensored with them.** -/
theorem surjective_tensor_sup_of_stabilizer_infinitePlace (hζ : IsPrimitiveRoot ζ p)
    (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
    {V : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) V)
    {u : InfinitePlace ↥K} (hu : u = V.comap (algebraMap ↥K Ω)) :
    Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : W →ₗ[ℤ] W)) :=
  surjective_tensor_map_of_forall_exists_mul_pow e j
    (exists_mul_pow_eq_sup_of_stabilizer_infinitePlace j hj hζ (Nat.Prime.ne_zero Fact.out) hroot
      hF hu)

end Tensor

end InverseGalois.CFT
