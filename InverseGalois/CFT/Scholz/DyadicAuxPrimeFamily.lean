/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.AuxPrimeFamily
import InverseGalois.CFT.Scholz.DyadicAuxPrime
import InverseGalois.CFT.Scholz.TwoPowerRadical

/-!
# One auxiliary prime for arbitrarily many prescribed dyadic non-residues

A prime congruent to one modulo a high power of two is congruent to one modulo eight, so two is a
square modulo it and no prime can be asked to make two a non-square.  Raising the exponent repairs
this: at the exponent `2 ^ M` the radical field of an odd prime enlarges the cyclotomic field of
two-power conductor by the full factor `2 ^ M`, and the radical field of the prime two still
enlarges it by the factor `2 ^ (M - 1)`, because a square root of two already lies in the
cyclotomic field while a fourth root does not.

The uniform factor `2 ^ (M - 1)` is all the union bound behind the density argument needs, and it
grows with `M` while the number of prescribed primes does not.  So a single auxiliary prime can be
asked to make arbitrarily many prescribed primes non-residues at once, provided the exponent is
raised past their number.

## Main results

* `InverseGalois.CFT.le_finrank_sup_radicalField_two_pow_prime`: **a radical of two-power exponent
  of a prime multiplies the degree of the cyclotomic field of two-power conductor by at least half
  that exponent**, whichever prime it is.
* `InverseGalois.CFT.exists_prime_two_pow_dvd_sub_one_forall_pow_ne_one`: **a prime congruent to
  one modulo a prescribed power of two, modulo which every member of a prescribed set of primes is
  a power non-residue at a chosen lower two-power exponent.**

## Tags

Chebotarev density, radical extension, power residue, auxiliary prime, dyadic, cyclotomic field
-/

open Module NumberField Polynomial InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Roots of unity and a square root of two in a cyclotomic field of two-power conductor -/

section Roots

variable {d M : ℕ}

/-- The roots of unity of a two-power order inside a cyclotomic field of at least that two-power
conductor. -/
theorem exists_isPrimitiveRoot_two_pow_mem_cycSubfield [NeZero ((2 : ℕ) ^ d)] (hMd : M ≤ d) :
    ∃ η : AlgebraicClosure ℚ, IsPrimitiveRoot η (2 ^ M) ∧ η ∈ cycSubfield (2 ^ d) := by
  have hprod : (2 : ℕ) ^ d = 2 ^ (d - M) * 2 ^ M := by
    rw [← pow_add]
    congr 1
    omega
  have hmem : cycRoot ((2 : ℕ) ^ d) ∈ cycSubfield (2 ^ d) :=
    IntermediateField.subset_adjoin ℚ _ rfl
  refine ⟨cycRoot ((2 : ℕ) ^ d) ^ (2 : ℕ) ^ (d - M), ?_, pow_mem hmem _⟩
  exact IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (cycRoot_spec (2 ^ d)) hprod

/-- **A square root of two inside a cyclotomic field of two-power conductor at least eight**, an
explicit one being the sum of a primitive eighth root of unity and its inverse. -/
theorem exists_sq_eq_two_mem_cycSubfield [NeZero ((2 : ℕ) ^ d)] (hd : 3 ≤ d) :
    ∃ s : AlgebraicClosure ℚ, s ∈ cycSubfield (2 ^ d) ∧
      s ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) 2 := by
  obtain ⟨η, hη, hηA⟩ := exists_isPrimitiveRoot_two_pow_mem_cycSubfield (d := d) (M := 3) hd
  have hη8 : IsPrimitiveRoot η 8 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at hη
    exact hη
  have h4 : η ^ 4 = -1 :=
    (hη8.pow (by norm_num) (show (8 : ℕ) = 4 * 2 by norm_num)).eq_neg_one_of_two_right
  refine ⟨η + η ^ 7, add_mem hηA (pow_mem hηA 7), ?_⟩
  rw [show algebraMap ℚ (AlgebraicClosure ℚ) 2 = 2 by norm_num]
  linear_combination (η ^ 2 * (η ^ 8 - η ^ 4 + 1) + 2 * (η ^ 4 - 1)) * h4

end Roots

/-! ### The uniform enlargement factor of a dyadic radical of a prime -/

section Degree

variable {d M : ℕ}

/-- **The enlargement a radical of two-power exponent of a prime makes over a cyclotomic field of
two-power conductor**: the full exponent for an odd prime, and half of it for the prime two, whose
square root is already there while its fourth root is not. -/
theorem le_finrank_sup_radicalField_two_pow_prime [NeZero ((2 : ℕ) ^ d)] (hM : 3 ≤ M)
    (hMd : M ≤ d) {p : ℕ} (hp : p.Prime) :
    2 ^ (M - 1) * finrank ℚ ↥(cycSubfield (2 ^ d))
      ≤ finrank ℚ ↥(cycSubfield (2 ^ d) ⊔ radicalField (2 ^ M) ({((p : ℕ) : ℚ)} : Finset ℚ)) := by
  obtain ⟨η, hη, hηA⟩ := exists_isPrimitiveRoot_two_pow_mem_cycSubfield (d := d) (M := M) hMd
  obtain ⟨i, hi, hiA⟩ := exists_isPrimitiveRoot_four_mem_cycSubfield (e := d) (by omega)
  have hi2 : i ^ 2 = -1 := sq_eq_neg_one_of_isPrimitiveRoot_four hi
  have hp0 : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨s, hsA, hs⟩ := exists_sq_eq_two_mem_cycSubfield (d := d) (by omega)
    refine le_finrank_sup_radicalField_two_pow_of_sq (by omega) hη hηA hiA hi2 hp0 hsA ?_ ?_
    · rw [hs]
      norm_num
    · simpa using forall_mem_cycSubfield_pow_four_ne_two (e := d)
  · have hpow : (2 : ℕ) ^ (M - 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine le_trans (Nat.mul_le_mul hpow le_rfl) ?_
    exact le_finrank_sup_radicalField_two_pow hη hηA hiA hi2 hp0
      (forall_mem_cycSubfield_sq_ne_of_odd_prime hp h2)

end Degree

/-! ### The auxiliary prime for a whole set of prescribed primes -/

section AuxPrime

/-- **A prime congruent to one modulo a prescribed power of two, modulo which every member of a
prescribed set of primes is a power non-residue at a chosen lower two-power exponent.**  The only
constraint is that the set have fewer members than half that exponent: over the cyclotomic field of
the higher conductor the radical field of a prime at the lower exponent multiplies the degree by at
least half the exponent, so the union bound behind the density argument still leaves room. -/
theorem exists_prime_two_pow_dvd_sub_one_forall_pow_ne_one {d M : ℕ} (hM : 3 ≤ M) (hMd : M ≤ d)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hcard : P.card < 2 ^ (M - 1)) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 ^ d ∣ q - 1 ∧
      ∀ p ∈ P, p ≠ q ∧ ((p : ℕ) : ZMod q) ^ ((q - 1) / 2 ^ M) ≠ 1 := by
  classical
  haveI : NeZero ((2 : ℕ) ^ d) := ⟨pow_ne_zero d (by norm_num)⟩
  have hdeg : ∀ p ∈ P, 2 ^ (M - 1) * finrank ℚ ↥(cycSubfield (2 ^ d))
      ≤ finrank ℚ ↥(cycSubfield (2 ^ d) ⊔ radicalField (2 ^ M) ({((p : ℕ) : ℚ)} : Finset ℚ)) :=
    fun p hp => le_finrank_sup_radicalField_two_pow_prime hM hMd (hP p hp)
  have hltcard : ((P.card : ℕ) : ℝ) / (((2 : ℕ) ^ (M - 1) : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast pow_pos (by norm_num : 0 < 2) (M - 1))]
    exact_mod_cast hcard
  obtain ⟨q, hqp, hqT, hqA, hqR⟩ :=
    exists_prime_splitsCompletely_not_radicalField_family_of_le_finrank
      (A := cycSubfield (2 ^ d)) (ℓ := 2 ^ M) (m := fun p : ℕ => ((p : ℕ) : ℚ)) P
      (pow_ne_zero (M - 1) (by norm_num)) hdeg hltcard (insert 2 (P ∪ T))
  have hq2 : q ≠ 2 := fun h => hqT (h ▸ Finset.mem_insert_self _ _)
  have hdvd : 2 ^ d ∣ q - 1 := by
    haveI : Fact q.Prime := ⟨hqp⟩
    have hnd : ¬ q ∣ (2 : ℕ) ^ d := fun h =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h))
    exact (Nat.modEq_iff_dvd' hqp.one_le).mp
      (modEq_of_splitsCompletely ((2 : ℕ) ^ d) ↥(cycSubfield (2 ^ d)) q hnd hqA).symm
  have hdvdM : (2 : ℕ) ^ M ∣ q - 1 := dvd_trans (pow_dvd_pow 2 hMd) hdvd
  refine ⟨q, hqp, fun hc => hqT (Finset.mem_insert_of_mem (Finset.mem_union_right P hc)), hdvd,
    fun p hpP => ⟨?_, fun hpow => hqR p hpP ?_⟩⟩
  · rintro rfl
    exact hqT (Finset.mem_insert_of_mem (Finset.mem_union_left T hpP))
  · have hpp := hP p hpP
    have hpq : p ≠ q := by
      rintro rfl
      exact hqT (Finset.mem_insert_of_mem (Finset.mem_union_left T hpP))
    have hcast : (((p : ℕ) : ℤ) : ℚ) = ((p : ℕ) : ℚ) := by
      push_cast
      ring
    rw [← hcast]
    refine splitsCompletely_radicalField_of_dvd (pow_ne_zero M (by norm_num)) hqp hdvdM ?_ ?_
    · intro hdv
      rw [Int.natCast_dvd_natCast] at hdv
      exact hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp hdv).symm
    · exact_mod_cast hpow

end AuxPrime

end InverseGalois.CFT
