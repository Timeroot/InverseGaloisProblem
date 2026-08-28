/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places

/-!
# Decomposition groups at unramified places over a number field base

A Galois extension of number fields acts on the primes of the top ring of integers, and the
stabiliser of a prime — its decomposition group — surjects onto the Galois group of the residue
extension with kernel the inertia group.  At an unramified prime the inertia group is trivial, so
the decomposition group embeds into the Galois group of an extension of finite fields, and is
therefore cyclic.

The base here is an arbitrary number field, not the rationals: the residue field of the prime below
is finite because it embeds in the residue field above, the residue extension is separable because
finite fields are perfect, and the ring of integers of the top field is the ring of invariants of
the ring of integers of the base, an element fixed by the Galois group being a base element that is
integral.

The last statement is transported to the `HeightOneSpectrum` of the ring of integers, the indexing
of the finite places used throughout the idelic development, along which the action is the action on
the underlying ideals.

## Main results

* `InverseGalois.CFT.isInvariant_ringOfIntegers_base`: the ring of integers of the top field is
  invariant over the ring of integers of the base.
* `InverseGalois.CFT.inertia_eq_bot_iff_isUnramifiedAt_base`: the inertia group at a nonzero prime
  is trivial exactly when the prime is unramified.
* `InverseGalois.CFT.isCyclic_stabilizer_of_isUnramifiedAt`: **the decomposition group at an
  unramified finite place is cyclic.**

## Tags

number field, prime, decomposition group, inertia group, Frobenius, unramified, cyclic
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section Invariant

/-- **The ring of integers of a Galois extension of number fields is invariant over the ring of
integers of the base**: an integer fixed by every automorphism lies in the base field, and being
integral it lies in the ring of integers of the base. -/
instance isInvariant_ringOfIntegers_base (k K : Type*) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [IsGalois k K] :
    Algebra.IsInvariant (𝓞 k) (𝓞 K) Gal(K/k) := by
  refine ⟨fun b hb => ?_⟩
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (b : K)).mpr
    fun g => congrArg (algebraMap (𝓞 K) K) (hb g)
  have hqint : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := K) (algebraMap k K).injective, hq]
    exact b.isIntegral.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  refine ⟨⟨q, hqint⟩, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [← IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 k) k K]
  exact hq

end Invariant

section Basic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] [NumberField K] in
/-- The prime of the base below a nonzero prime is nonzero. -/
theorem under_ne_bot_base (P : Ideal (𝓞 K)) (hP : P ≠ ⊥) : P.under (𝓞 k) ≠ ⊥ :=
  Ideal.under_ne_bot (𝓞 k) hP

/-- A nonzero prime of the ring of integers of a number field is maximal. -/
theorem isMaximal_of_ne_bot_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) : P.IsMaximal :=
  Ideal.IsPrime.isMaximal ‹_› hP

/-- The residue field at a nonzero prime is finite. -/
theorem finite_quotient_of_ne_bot_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    Finite (𝓞 K ⧸ P) :=
  haveI := isMaximal_of_ne_bot_base P hP
  inferInstance

omit [NumberField K] in
/-- The prime of the base below a nonzero prime is maximal. -/
theorem isMaximal_under_of_ne_bot_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    (P.under (𝓞 k)).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (under_ne_bot_base (k := k) P hP)

omit [NumberField k] in
/-- The residue field of the prime of the base below a nonzero prime is finite, embedding as it does
in the residue field above. -/
theorem finite_quotient_under_of_ne_bot_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    Finite (𝓞 k ⧸ P.under (𝓞 k)) :=
  haveI := finite_quotient_of_ne_bot_base P hP
  .of_injective _ (Ideal.algebraMap_quotient_injective (R := 𝓞 k) (A := 𝓞 K) (I := P))

/-- The residue extension at a nonzero prime is separable, finite fields being perfect. -/
theorem isSeparable_residue_of_ne_bot_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    Algebra.IsSeparable (𝓞 k ⧸ P.under (𝓞 k)) (𝓞 K ⧸ P) := by
  haveI := isMaximal_of_ne_bot_base P hP
  haveI := isMaximal_under_of_ne_bot_base (k := k) P hP
  haveI := finite_quotient_under_of_ne_bot_base (k := k) P hP
  infer_instance

end Basic

section Inertia

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The inertia group at a nonzero prime is trivial exactly when the prime is unramified**, its
cardinality being the ramification index. -/
theorem inertia_eq_bot_iff_isUnramifiedAt_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.inertia Gal(K/k) P = ⊥ ↔ Algebra.IsUnramifiedAt (𝓞 k) P := by
  haveI := isMaximal_of_ne_bot_base P hP
  haveI := finite_quotient_of_ne_bot_base P hP
  haveI := isMaximal_under_of_ne_bot_base (k := k) P hP
  haveI := isSeparable_residue_of_ne_bot_base (k := k) P hP
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 k) hP, ← Subgroup.card_eq_one,
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/k)) (P.under (𝓞 k))
      (under_ne_bot_base (k := k) P hP) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 k)) P Gal(K/k)]

/-- **At an unramified prime the decomposition group is cyclic**: the reduction map to the
automorphism group of the residue extension has the inertia group as its kernel, hence is injective,
and the Galois group of an extension of finite fields is cyclic. -/
theorem isCyclic_stabilizer_of_inertia_eq_bot (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (hinert : Ideal.inertia Gal(K/k) P = ⊥) : IsCyclic ↥(stabilizer Gal(K/k) P) := by
  haveI := isMaximal_of_ne_bot_base P hP
  haveI := finite_quotient_of_ne_bot_base P hP
  haveI := isMaximal_under_of_ne_bot_base (k := k) P hP
  haveI : P.LiesOver (P.under (𝓞 k)) := ⟨rfl⟩
  refine isCyclic_of_injective (Ideal.Quotient.stabilizerHom P (P.under (𝓞 k)) Gal(K/k)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, hinert]
  simp

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- The stabiliser of a finite place is the stabiliser of the underlying ideal. -/
theorem stabilizer_eq_stabilizer_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    stabilizer Gal(K/k) v = stabilizer Gal(K/k) v.asIdeal := by
  ext σ
  rw [mem_stabilizer_iff, mem_stabilizer_iff, HeightOneSpectrum.ext_iff, asIdeal_smul]

/-- **At an unramified finite place the decomposition group is cyclic.** -/
theorem isCyclic_stabilizer_of_isUnramifiedAt (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) : IsCyclic ↥(stabilizer Gal(K/k) v) := by
  rw [stabilizer_eq_stabilizer_asIdeal]
  exact isCyclic_stabilizer_of_inertia_eq_bot v.asIdeal v.ne_bot
    ((inertia_eq_bot_iff_isUnramifiedAt_base v.asIdeal v.ne_bot).mpr hunr)

end Inertia

end InverseGalois.CFT
