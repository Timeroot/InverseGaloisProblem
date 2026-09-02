/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SubcyclotomicSplit
import InverseGalois.CFT.Brauer.TotallyRealInvariantBase

/-!
# Splitting a Brauer class of an arbitrary number field by a cyclic extension

A cyclic extension of number fields splits a Brauer class of the base exactly when the local degree
at every finite place kills the invariant at the place below, and every real place of the extension
splits the class.  Both conditions are read off from the decomposition groups and the archimedean
invariants.

At a finite place the order of the decomposition group is the local degree.  In an extension whose
degree is a power of a prime the order of a decomposition group is a power of that prime, so a
decomposition group that is not killed by a given power of the prime has order at least the next
power, and that power therefore divides the local degree.  A class killed by that power of the
prime is consequently split at such a place.

At an archimedean place the condition is inherited from the base.  A real place of the extension
restricts to a real place of the base, the completion at the restricted place maps into the
completion at the place above it because both are the reals along compatible embeddings, and a
class with trivial invariant at every infinite place of the base is split by the smaller
completion, hence by the larger one.

## Main results

* `InverseGalois.CFT.mem_relative_completion_of_forall_infinitePlaceInvariant`: **a Brauer class of
  a number field with trivial invariant at every infinite place is split by the completion of any
  extension at a real place.**
* `InverseGalois.CFT.card_stabilizer_asIdeal_eq_finrank_adicCompletion_base`: **the order of the
  decomposition group at a finite place is the local degree over the base.**
* `InverseGalois.CFT.primePow_dvd_finrank_adicCompletion_of_not_dvd_base`: **in an extension of
  prime-power degree a power of the prime divides the local degree at a place whose decomposition
  group is not killed by the next smaller power.**
* `InverseGalois.CFT.mem_relative_of_forall_not_dvd_primePow_base`: **a Brauer class of a number
  field killed by a prime power, with trivial invariants at the infinite places, is split by a
  cyclic extension of prime-power degree whose decomposition group at every place carrying a
  nontrivial invariant is not killed by the next smaller power.**

## Tags

Brauer group, relative Brauer group, decomposition group, local degree, infinite place, cyclic
extension, number field
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

open scoped Pointwise

/-! ### The archimedean condition -/

section Archimedean

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- **A Brauer class of a number field with trivial invariant at every infinite place is split by
the completion of any extension at a real place.**  The real place restricts to a real place of the
base, and the completion there embeds into the completion above it over the base, because both are
the reals along the two embeddings and the embeddings are compatible. -/
theorem mem_relative_completion_of_forall_infinitePlaceInvariant
    {x : BrauerGroup.{0, 0} k} (hx : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1)
    {U : InfinitePlace F} (hU : U.IsReal) : x ∈ BrauerGroup.relative k U.Completion := by
  have hu : (U.comap (algebraMap k F)).IsReal := hU.comap _
  have hxu : x ∈ BrauerGroup.relative k (U.comap (algebraMap k F)).Completion :=
    (infinitePlaceInvariant_eq_one_iff k _ x).mp (hx _)
  refine relative_le_relative_of_algHom ?_ hxu
  have hcomm : ∀ r : k,
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hU).symm.toRingHom.comp
        (InfinitePlace.Completion.ringEquivRealOfIsReal hu).toRingHom)
          (algebraMap k (U.comap (algebraMap k F)).Completion r)
        = algebraMap k U.Completion r := by
    intro r
    show (InfinitePlace.Completion.ringEquivRealOfIsReal hU).symm
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hu)
          (algebraMap k (U.comap (algebraMap k F)).Completion r)) = _
    rw [RingEquiv.symm_apply_eq]
    show InfinitePlace.Completion.extensionEmbeddingOfIsReal hu
        (algebraMap k (U.comap (algebraMap k F)).Completion r)
      = InfinitePlace.Completion.extensionEmbeddingOfIsReal hU (algebraMap k U.Completion r)
    have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hu
        (algebraMap k (U.comap (algebraMap k F)).Completion r)
        = InfinitePlace.embedding_of_isReal hu r :=
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu r
    have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hU
        (algebraMap k U.Completion r)
        = InfinitePlace.embedding_of_isReal hU (algebraMap k F r) :=
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hU (algebraMap k F r)
    rw [h1, h2]
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_of_isReal_apply,
      InfinitePlace.comap_embedding_of_isReal (algebraMap k F) hu]
    rfl
  exact { (InfinitePlace.Completion.ringEquivRealOfIsReal hU).symm.toRingHom.comp
      (InfinitePlace.Completion.ringEquivRealOfIsReal hu).toRingHom with
      commutes' := hcomm }

end Archimedean

/-! ### The decomposition group and the local degree over an arbitrary base -/

section LocalDegree

variable {k : Type} [Field k] [NumberField k] (F : Type) [Field F] [NumberField F] [Algebra k F]
  [IsGalois k F]

/-- **The order of the decomposition group at a finite place is the local degree over the base.** -/
theorem card_stabilizer_asIdeal_eq_finrank_adicCompletion_base (w : HeightOneSpectrum (𝓞 F)) :
    Nat.card ↥(stabilizer Gal(F/k) w.asIdeal)
      = finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion F) := by
  rw [← stabilizer_eq_stabilizer_asIdeal (k := k) w, card_stabilizer_eq_finrank_adicCompletion k w]

/-- **In a Galois extension of prime-power degree a power of the prime divides the local degree at
a place whose decomposition group is not killed by the next smaller power.**  The order of the
decomposition group is a power of the prime, and failing to divide the next smaller power puts its
exponent at least as high. -/
theorem primePow_dvd_finrank_adicCompletion_of_not_dvd_base {ℓ d e : ℕ} (hℓ : ℓ.Prime)
    (hcard : Nat.card Gal(F/k) = ℓ ^ d) (w : HeightOneSpectrum (𝓞 F))
    (h : ¬ Nat.card ↥(stabilizer Gal(F/k) w.asIdeal) ∣ ℓ ^ (e - 1)) :
    ℓ ^ e ∣ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion F) := by
  rw [← card_stabilizer_asIdeal_eq_finrank_adicCompletion_base F w]
  have hdvd : Nat.card ↥(stabilizer Gal(F/k) w.asIdeal) ∣ ℓ ^ d := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
  rw [hieq]
  refine pow_dvd_pow ℓ ?_
  by_contra hlt
  exact h (hieq ▸ pow_dvd_pow ℓ (by omega))

end LocalDegree

/-! ### Splitting a class of prime-power order over an arbitrary base -/

section Split

variable {k : Type} [Field k] [NumberField k]

/-- **A Brauer class of a number field killed by a prime power, with trivial invariants at the
infinite places, is split by a cyclic extension of prime-power degree whose decomposition group at
every place carrying a nontrivial invariant is not killed by the next smaller power.**  The order
of such a decomposition group is a multiple of the order of the class, so it kills the local
invariant, and the archimedean places impose nothing because the invariants there are trivial. -/
theorem mem_relative_of_forall_not_dvd_primePow_base {ℓ d e : ℕ} (hℓ : ℓ.Prime)
    {x : BrauerGroup.{0, 0} k} (hx : x ^ ℓ ^ e = 1)
    (harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1)
    (F : Type) [Field F] [NumberField F] [Algebra k F] [IsGalois k F] [IsCyclic Gal(F/k)]
    (hcard : Nat.card Gal(F/k) = ℓ ^ d)
    (hbad : ∀ w : HeightOneSpectrum (𝓞 F), placeInvariant k (primeUnder (𝓞 k) w) x ≠ 1 →
      ¬ Nat.card ↥(stabilizer Gal(F/k) w.asIdeal) ∣ ℓ ^ (e - 1)) :
    x ∈ BrauerGroup.relative k F := by
  rw [mem_relative_iff_forall_pow_placeInvariant]
  refine ⟨fun w => ?_,
    fun U hU => mem_relative_completion_of_forall_infinitePlaceInvariant harch hU⟩
  by_cases hinv : placeInvariant k (primeUnder (𝓞 k) w) x = 1
  · rw [hinv, one_pow]
  · obtain ⟨m, hm⟩ := primePow_dvd_finrank_adicCompletion_of_not_dvd_base (e := e) F hℓ hcard w
      (hbad w hinv)
    have hpow : placeInvariant k (primeUnder (𝓞 k) w) x ^ ℓ ^ e = 1 := by
      rw [← map_pow, hx, map_one]
    rw [hm, pow_mul, hpow, one_pow]

end Split

end InverseGalois.CFT
