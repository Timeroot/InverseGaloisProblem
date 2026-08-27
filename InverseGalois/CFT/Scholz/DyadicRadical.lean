/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.SqrtCompositum

/-!
# Square roots in the constraint field of the auxiliary primes at the prime two

The constraint field of the auxiliary primes is the field being corrected enlarged by roots of
unity of two-power order, and the correction is obstructed by the rational numbers that become
squares there.  The cyclotomic layer is ramified only at two, so if the field being corrected is
unramified at two the two factors meet in the rationals, and the compositum acquires no square root
of an integer congruent to one modulo four beyond those the field being corrected already has.

## Main results

* `InverseGalois.CFT.mem_of_sq_eq_intCast_auxConstraintField`: **a square root of an integer
  congruent to one modulo four lying in the constraint field of a field unramified at two already
  lies in that field.**

## Tags

Scholz–Reichardt, auxiliary prime, cyclotomic field, square root, ramification
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- Only the prime two ramifies in a cyclotomic field of two-power conductor. -/
theorem ramifiedSet_cycSubfield_two_pow_subset (k : ℕ) [NeZero ((2 : ℕ) ^ k)] :
    ramifiedSet ↥(cycSubfield (2 ^ k)) ⊆ {2} := by
  intro p hp
  have h := ramifiedSet_subset_primeFactors (2 ^ k) ↥(cycSubfield (2 ^ k)) hp
  rw [Finset.mem_coe, Nat.mem_primeFactors] at h
  obtain ⟨hpp, hdvd, -⟩ := h
  exact Set.mem_singleton_iff.mpr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
    (hpp.dvd_of_dvd_pow hdvd))

/-- A field unramified at two meets a cyclotomic field of two-power conductor in the rationals. -/
theorem inf_cycSubfield_two_pow_eq_bot (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥L] (h2 : 2 ∉ ramifiedSet ↥L) (k : ℕ) [NeZero ((2 : ℕ) ^ k)] :
    L ⊓ cycSubfield (2 ^ k) = ⊥ :=
  inf_eq_bot_of_ramifiedSet_disjoint' L (cycSubfield (2 ^ k))
    (Set.disjoint_right.mpr fun p hp hpL => by
      rw [Set.mem_singleton_iff.mp (ramifiedSet_cycSubfield_two_pow_subset k hp)] at hpL
      exact h2 hpL)

/-- **A square root of an integer congruent to one modulo four lying in the constraint field of a
field unramified at two already lies in that field.**  The constraint field is the compositum of
the field being corrected with a cyclotomic field of two-power conductor, which is ramified only at
two, so the two factors meet in the rationals and the comparison of squarefree parts applies. -/
theorem mem_of_sq_eq_intCast_auxConstraintField
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L]
    (h2 : 2 ∉ ramifiedSet ↥L) {k : ℕ} [NeZero ((2 : ℕ) ^ k)] {m : ℤ} (hm : m % 4 = 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ auxConstraintField L 2 k)
    (hxm : x ^ 2 = (m : AlgebraicClosure ℚ)) : x ∈ L := by
  rw [auxConstraintField] at hx
  exact mem_of_sq_eq_intCast_of_inf_eq_bot L (cycSubfield (2 ^ k))
    (inf_cycSubfield_two_pow_eq_bot L h2 k) h2 (ramifiedSet_cycSubfield_two_pow_subset k) hm hx hxm

end InverseGalois.CFT
