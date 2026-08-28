/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.QuadraticSubfield
import InverseGalois.CFT.Scholz.SplitStep

/-!
# The square root carried by a quadratic split step

At the prime two and with a single layer the new factor of a split step is the quadratic subfield
of the cyclotomic field of the branching prime.  From level two on, the branching prime is
congruent to one modulo four, so the quadratic Gauss sum attached to it squares to the prime itself
and the cyclotomic field contains a square root of it.  That square root generates a quadratic
extension of `ℚ`, and the Galois group of a cyclotomic field of prime conductor is cyclic, hence
has a single subgroup of index two: the field it generates is therefore the new factor, which
consequently contains the square root of its own branching prime.

## Main definitions

* `InverseGalois.CFT.innerOldAlgHom`, `InverseGalois.CFT.innerNewAlgHom`: the two factors of a
  split step, as embeddings into the compositum.

## Main results

* `InverseGalois.CFT.exists_sq_eq_stepPrime`: **the quadratic new factor of a split step at the
  prime two contains a square root of its branching prime**, from level two on.
* `InverseGalois.CFT.sq_eq_algebraMap_map`: a square root of a base element stays one under an
  embedding over the base.

## Tags

Scholz–Reichardt, quadratic subfield, Gauss sum, square root, branching prime
-/

open Module NumberField IsCyclotomicExtension InverseGalois.NumberTheory IntermediateField

namespace InverseGalois.CFT

/-! ### Square roots under an embedding over the base -/

/-- **A square root of a base element stays one under an embedding over the base.** -/
theorem sq_eq_algebraMap_map {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {u : A} {m : F} (hu : u ^ 2 = algebraMap F A m) :
    f u ^ 2 = algebraMap F B m := by
  rw [← map_pow, hu, AlgHom.commutes]

/-! ### The two factors of a split step inside the compositum -/

section Factors

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] {ℓ : ℕ} (hℓ : ℓ.Prime) (N e : ℕ)

/-- The embedding of the old factor of a split step into the compositum. -/
noncomputable def innerOldAlgHom : L →ₐ[ℚ] ↥(stepField L hℓ N e) :=
  (innerOld L hℓ N e).val.comp (innerOldEquiv L hℓ N e).toAlgHom

/-- The embedding of the new factor of a split step into the compositum. -/
noncomputable def innerNewAlgHom :
    ↥(stepAux L hℓ N e) →ₐ[ℚ] ↥(stepField L hℓ N e) :=
  (innerNew L hℓ N e).val.comp (innerNewEquiv L hℓ N e).toAlgHom

end Factors

/-- **The quadratic new factor of a split step at the prime two contains a square root of its
branching prime.**  From level two on, the branching prime is congruent to one modulo four, so a
Gauss sum in the cyclotomic field of that conductor squares to it; the field the Gauss sum
generates has degree two, and so does the new factor, and a cyclic Galois group has only one
subgroup of index two. -/
theorem exists_sq_eq_stepPrime (L : Type*) [Field L] [NumberField L] {N : ℕ} (hN : 2 ≤ N) :
    ∃ w : ↥(stepAux L Nat.prime_two N 1),
      w ^ 2 = algebraMap ℚ ↥(stepAux L Nat.prime_two N 1)
        ((stepPrime L Nat.prime_two N 1 : ℕ) : ℚ) := by
  have hq : (stepPrime L Nat.prime_two N 1).Prime := prime_stepPrime L Nat.prime_two N 1
  haveI : Fact (stepPrime L Nat.prime_two N 1).Prime := fact_prime_stepPrime L Nat.prime_two N 1
  have hq4 : stepPrime L Nat.prime_two N 1 % 4 = 1 := by
    have hdvd : (4 : ℕ) ∣ 2 ^ N := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 hN
    have h4 : stepPrime L Nat.prime_two N 1 ≡ 1 [MOD 4] :=
      Nat.ModEq.of_dvd hdvd (stepPrime_modEq L Nat.prime_two N 1)
    unfold Nat.ModEq at h4
    omega
  haveI : IsGalois ℚ (CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ) :=
    IsCyclotomicExtension.isGalois {stepPrime L Nat.prime_two N 1} ℚ _
  haveI : IsCyclic (ZMod (stepPrime L Nat.prime_two N 1))ˣ := ZMod.isCyclic_units_prime hq
  haveI : IsCyclic Gal(CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ/ℚ) :=
    isCyclic_of_surjective
      (Rat.galEquivZMod (stepPrime L Nat.prime_two N 1)
        (CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ)).symm
      (Rat.galEquivZMod (stepPrime L Nat.prime_two N 1)
        (CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ)).symm.surjective
  obtain ⟨r, hr⟩ := exists_sq_eq_natCast_of_one_mod_four hq hq4
    (CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ)
  have heq : (ℚ⟮r⟯ : IntermediateField ℚ (CyclotomicField (stepPrime L Nat.prime_two N 1) ℚ))
      = stepAux L Nat.prime_two N 1 :=
    intermediateField_eq_of_finrank_eq_two (finrank_adjoin_eq_two_of_sq_eq_natCast hq hr)
      (by rw [finrank_stepAux L Nat.prime_two N 1, pow_one])
  have hmem : r ∈ stepAux L Nat.prime_two N 1 :=
    heq ▸ IntermediateField.mem_adjoin_simple_self ℚ r
  refine ⟨⟨r, hmem⟩, Subtype.ext ?_⟩
  push_cast
  exact hr

end InverseGalois.CFT
