/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.DecompositionOutside
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.PlaceTower

/-!
# The places splitting completely in an intermediate field

Let `M / K` be a Galois extension of number fields of prime exponent, and let `L` be an intermediate
field.  Among the finite places of `M` whose place below avoids a prescribed finite set, consider
those whose decomposition group over `K` already fixes `L`; these are the places splitting
completely in `L`.  Their decomposition groups generate exactly the subgroup of the Galois group
fixing `L`.

One inclusion is the definition.  For the other, the decomposition groups of the extension `M / L`
at the places away from the prescribed set generate the whole Galois group of `M / L`, that group
being solvable, so it is enough to see that a nontrivial such decomposition group is already the
decomposition group over `K`.  That is where the exponent enters: at an unramified place the
decomposition group over `K` is cyclic, and a cyclic group of exponent a prime `p` has order `1` or
`p`, so a nontrivial subgroup of it is everything.

## Main definitions

* `InverseGalois.CFT.galInclusion`: the inclusion of the Galois group over an intermediate field
  into the Galois group over the base.
* `InverseGalois.CFT.splitPlaces`: the finite places away from a prescribed set whose decomposition
  group fixes the intermediate field.

## Main results

* `InverseGalois.CFT.range_galInclusion`: the image of that inclusion is the subgroup fixing the
  intermediate field.
* `InverseGalois.CFT.closure_stabilizer_splitPlaces`: **the decomposition groups at the places
  splitting completely in an intermediate field generate the subgroup fixing it.**

## Tags

number field, place, decomposition group, splitting, intermediate field, exponent
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section Relative

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (L : IntermediateField K M)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **The inclusion of the Galois group over an intermediate field into the Galois group over the
base.** -/
def galInclusion : Gal(M/↥L) →* Gal(M/K) :=
  (L.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom

omit [NumberField K] [NumberField M] [IsGalois K M] in
/-- The inclusion is compatible with the action on the finite places. -/
theorem galInclusion_smul (σ : Gal(M/↥L)) (v : HeightOneSpectrum (𝓞 M)) :
    (galInclusion L σ) • v = σ • v := rfl

omit [NumberField K] [NumberField M] [IsGalois K M] in
/-- **The image of the inclusion is the subgroup fixing the intermediate field.** -/
theorem range_galInclusion : (galInclusion L).range = L.fixingSubgroup := by
  have h : (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)
  rw [galInclusion, MonoidHom.range_comp, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {L} in
omit [NumberField K] [NumberField M] [IsGalois K M] in
/-- An automorphism over the intermediate field fixes it. -/
theorem mem_fixingSubgroup_galInclusion (σ : Gal(M/↥L)) :
    galInclusion L σ ∈ L.fixingSubgroup :=
  (range_galInclusion L) ▸ ⟨σ, rfl⟩

omit [NumberField K] [NumberField M] [IsGalois K M] in
/-- The inclusion is injective. -/
theorem galInclusion_injective : Function.Injective (galInclusion L) :=
  Subtype.val_injective.comp (MulEquiv.injective _)

omit [NumberField K] [NumberField M] [IsGalois K M] in
/-- Solvability of the Galois group passes to any intermediate field. -/
theorem isSolvable_gal_intermediate [IsSolvable Gal(M/K)] : IsSolvable Gal(M/↥L) :=
  solvable_of_solvable_injective (galInclusion_injective L)

/-- **The finite places of the top field, away from a prescribed set of places of the base, whose
decomposition group already fixes an intermediate field.** -/
def splitPlaces (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 M)) :=
  {w | primeUnder (𝓞 K) w ∉ S ∧ stabilizer Gal(M/K) w ≤ L.fixingSubgroup}

variable {L} in
/-- Only finitely many places of an intermediate field lie above a finite set of places of the
base, each of them being the place below a place of the top field. -/
theorem finite_preimage_primeUnder_intermediate {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) : (primeUnder (𝓞 K) (B := 𝓞 ↥L) ⁻¹' S).Finite := by
  have hM : (primeUnder (𝓞 K) (B := 𝓞 M) ⁻¹' S).Finite :=
    finite_preimage_primeUnder (𝓞 K) (𝓞 M) (G := Gal(M/K)) hS
  refine (hM.image (primeUnder (𝓞 ↥L))).subset fun u hu => ?_
  obtain ⟨w, hw⟩ := exists_primeUnder_eq (𝓞 ↥L) (𝓞 M) u
  refine ⟨w, ?_, hw⟩
  have hunder : primeUnder (𝓞 K) (primeUnder (𝓞 ↥L) w) = primeUnder (𝓞 K) w :=
    primeUnder_primeUnder K ↥L w
  rw [Set.mem_preimage, ← hunder, hw]
  exact hu

variable {L} {p : ℕ}

/-- **The decomposition groups at the places splitting completely in an intermediate field generate
the subgroup fixing that field.**  One inclusion holds by definition; for the other, the
decomposition groups of the extension over the intermediate field generate its Galois group, and a
nontrivial one of those is the whole decomposition group over the base, that group being cyclic of
exponent a prime. -/
theorem closure_stabilizer_splitPlaces [IsSolvable Gal(M/↥L)] (hp : p.Prime)
    (hexp : ∀ σ : Gal(M/K), σ ^ p = 1) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 M), primeUnder (𝓞 K) w ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    Subgroup.closure (⋃ w ∈ splitPlaces L S, (stabilizer Gal(M/K) w : Set Gal(M/K)))
      = L.fixingSubgroup := by
  classical
  set U : Set Gal(M/K) := ⋃ w ∈ splitPlaces L S, (stabilizer Gal(M/K) w : Set Gal(M/K)) with hU
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) ?_
  · rintro σ hσ
    simp only [hU, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hσ
    obtain ⟨w, hw, hσw⟩ := hσ
    exact hw.2 hσw
  · set SL : Set (HeightOneSpectrum (𝓞 ↥L)) := primeUnder (𝓞 K) (B := 𝓞 ↥L) ⁻¹' S with hSL
    have hSLfin : SL.Finite := finite_preimage_primeUnder_intermediate hS
    have htop : decompositionSubgroupOutside (↥L) M SL = ⊤ :=
      decompositionSubgroupOutside_eq_top (↥L) M hSLfin
    have hkey : ∀ σ : Gal(M/↥L), σ ∈ decompositionSetOutside (↥L) M SL →
        galInclusion L σ ∈ Subgroup.closure U := by
      rintro σ ⟨v, hvSL, hvσ⟩
      rcases eq_or_ne (galInclusion L σ) 1 with h1 | h1
      · rw [h1]
        exact one_mem _
      have hvS : primeUnder (𝓞 K) v ∉ S := by
        rw [hSL, Set.mem_preimage] at hvSL
        rwa [← primeUnder_primeUnder K ↥L v]
      have hmem : galInclusion L σ ∈ stabilizer Gal(M/K) v := by
        rw [mem_stabilizer_iff, galInclusion_smul]
        exact hvσ
      haveI hcyc : IsCyclic ↥(stabilizer Gal(M/K) v) :=
        isCyclic_stabilizer_of_isUnramifiedAt v (hunr v hvS)
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hcard : orderOf g = Nat.card ↥(stabilizer Gal(M/K) v) :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      have hgp : orderOf g ∣ p := by
        refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
        push_cast
        exact hexp _
      have hord : orderOf (galInclusion L σ) = p := by
        have hdvd : orderOf (galInclusion L σ) ∣ p := orderOf_dvd_of_pow_eq_one (hexp _)
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1
        · exact h
      have hzle : Subgroup.zpowers (galInclusion L σ) ≤ stabilizer Gal(M/K) v :=
        Subgroup.zpowers_le.mpr hmem
      have hcards : Nat.card ↥(stabilizer Gal(M/K) v)
          ≤ Nat.card ↥(Subgroup.zpowers (galInclusion L σ)) := by
        rw [Nat.card_zpowers, hord, ← hcard]
        exact Nat.le_of_dvd hp.pos hgp
      have heq : Subgroup.zpowers (galInclusion L σ) = stabilizer Gal(M/K) v :=
        Subgroup.eq_of_le_of_card_ge hzle hcards
      have hsplit : v ∈ splitPlaces L S := by
        refine ⟨hvS, ?_⟩
        rw [← heq]
        exact Subgroup.zpowers_le.mpr (mem_fixingSubgroup_galInclusion σ)
      refine Subgroup.subset_closure ?_
      simp only [hU, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
      exact ⟨v, hsplit, hmem⟩
    intro σ hσ
    obtain ⟨τ, rfl⟩ : ∃ τ : Gal(M/↥L), galInclusion L τ = σ := by
      rw [← MonoidHom.mem_range, range_galInclusion]
      exact hσ
    clear hσ
    have hτ : τ ∈ decompositionSubgroupOutside (↥L) M SL := htop ▸ Subgroup.mem_top τ
    induction hτ using Subgroup.closure_induction with
    | mem x hx => exact hkey x hx
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Relative

end InverseGalois.CFT
