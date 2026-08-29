/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionCompact

/-!
# The residue ring of a division algebra over a local field

The integers of a division algebra `D` over a nonarchimedean local field `K` carry a congruence:
two of them are equivalent when their difference has absolute value less than one.  The quotient is
the residue ring of `D`.  It is a ring without zero divisors, because the absolute value is
multiplicative and the elements of absolute value one are exactly those with nonzero residue, and
it is finite, because the integers are covered by finitely many balls of radius one.

A finite ring without zero divisors is a field, by the theorem of Wedderburn, and the nonzero
elements of a finite field are the powers of a single one of them.  Translated back into the
language of absolute values, that says: there is an integer `y` of `D` such that every element of
absolute value one differs from a power of `y` by an element of absolute value less than one.  That
statement is the reason for constructing the residue ring, and it is the only thing about it that is
needed later.

## Main definitions

* `InverseGalois.CFT.divisionResidueCon`: the congruence on the integers of `D`.
* `InverseGalois.CFT.DivisionResidue`: the residue ring.

## Main results

* `InverseGalois.CFT.exists_forall_eq_pow_of_finite_isDomain`: the nonzero elements of a finite ring
  without zero divisors are the powers of a single element.
* `InverseGalois.CFT.exists_pow_divisionNorm_sub_lt_one`: **an integer of `D` whose powers meet
  every element of absolute value one.**

## Tags

division algebra, local field, residue ring, Wedderburn
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open Module

namespace InverseGalois.CFT

/-! ### The nonzero elements of a finite domain -/

/-- **The nonzero elements of a finite ring without zero divisors are the powers of a single
element.**  Such a ring is a field by the theorem of Wedderburn, and the multiplicative group of a
finite field is cyclic. -/
theorem exists_forall_eq_pow_of_finite_isDomain (R : Type*) [Ring R] [IsDomain R] [Finite R] :
    ∃ g : R, ∀ x : R, x ≠ 0 → ∃ i : ℕ, x = g ^ i := by
  classical
  have hF : IsField R := Finite.isDomain_to_isField R
  letI : CommRing R := { (inferInstance : Ring R) with mul_comm := hF.mul_comm }
  haveI : Finite Rˣ := Finite.of_injective (fun u : Rˣ => (u : R)) Units.val_injective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Rˣ)
  refine ⟨(g : R), fun x hx => ?_⟩
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hx
  let u : Rˣ := ⟨x, b, hb, (hF.mul_comm b x).trans hb⟩
  obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hg u)
  refine ⟨i, ?_⟩
  have hval := congrArg (fun v : Rˣ => (v : R)) hi
  simpa using hval.symm

/-! ### The congruence on the integers -/

section Residue

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

variable (K D) in
/-- Two integers of a division algebra over a complete nonarchimedean field are **congruent** when
their difference has absolute value less than one. -/
def divisionResidueCon : RingCon (divisionIntegers K D) where
  r x y := divisionNorm K D ((x : D) - (y : D)) < 1
  iseqv :=
    { refl := fun x => by simp
      symm := fun {_ _} h => by rwa [← divisionNorm_neg, neg_sub]
      trans := fun {x y z} h₁ h₂ => by
        have he : ((x : D) - (z : D)) = ((x : D) - (y : D)) + ((y : D) - (z : D)) :=
          (sub_add_sub_cancel _ _ _).symm
        rw [he]
        exact lt_of_le_of_lt (divisionNorm_isNonarchimedean _ _) (max_lt h₁ h₂) }
  mul' := fun {w x y z} h₁ h₂ => by
    show divisionNorm K D ((↑(w * y) : D) - (↑(x * z) : D)) < 1
    have he : ((↑(w * y) : D) - (↑(x * z) : D))
        = (w : D) * ((y : D) - (z : D)) + ((w : D) - (x : D)) * (z : D) := by
      push_cast
      noncomm_ring
    rw [he]
    refine lt_of_le_of_lt (divisionNorm_isNonarchimedean _ _) (max_lt ?_ ?_)
    · rw [divisionNorm_mul]
      have h₃ : divisionNorm K D (w : D) * divisionNorm K D ((y : D) - (z : D))
          ≤ 1 * divisionNorm K D ((y : D) - (z : D)) :=
        mul_le_mul_of_nonneg_right (mem_divisionIntegers.1 w.2) (divisionNorm_nonneg _)
      linarith
    · rw [divisionNorm_mul]
      have h₃ : divisionNorm K D ((w : D) - (x : D)) * divisionNorm K D (z : D)
          ≤ divisionNorm K D ((w : D) - (x : D)) * 1 :=
        mul_le_mul_of_nonneg_left (mem_divisionIntegers.1 z.2) (divisionNorm_nonneg _)
      linarith
  add' := fun {w x y z} h₁ h₂ => by
    show divisionNorm K D ((↑(w + y) : D) - (↑(x + z) : D)) < 1
    have he : ((↑(w + y) : D) - (↑(x + z) : D))
        = ((w : D) - (x : D)) + ((y : D) - (z : D)) := by
      push_cast
      abel
    rw [he]
    exact lt_of_le_of_lt (divisionNorm_isNonarchimedean _ _) (max_lt h₁ h₂)

variable (K D) in
/-- The **residue ring** of a division algebra over a nonarchimedean local field. -/
abbrev DivisionResidue := (divisionResidueCon K D).Quotient

@[simp]
theorem divisionResidueCon_apply (x y : divisionIntegers K D) :
    divisionResidueCon K D x y ↔ divisionNorm K D ((x : D) - (y : D)) < 1 := Iff.rfl

theorem divisionResidue_eq_iff {x y : divisionIntegers K D} :
    (x : DivisionResidue K D) = (y : DivisionResidue K D) ↔
      divisionNorm K D ((x : D) - (y : D)) < 1 :=
  RingCon.eq _

theorem divisionResidue_eq_zero_iff (x : divisionIntegers K D) :
    (x : DivisionResidue K D) = 0 ↔ divisionNorm K D (x : D) < 1 := by
  have h0 : ((0 : divisionIntegers K D) : DivisionResidue K D) = 0 := rfl
  rw [← h0, divisionResidue_eq_iff]
  simp

instance : Nontrivial (DivisionResidue K D) := by
  refine ⟨⟨((1 : divisionIntegers K D) : DivisionResidue K D), 0, fun h => ?_⟩⟩
  have h1 := (divisionResidue_eq_zero_iff (1 : divisionIntegers K D)).1 h
  simp [divisionNorm_one] at h1

instance : NoZeroDivisors (DivisionResidue K D) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (divisionResidueCon K D).mk'_surjective a
    obtain ⟨y, rfl⟩ := (divisionResidueCon K D).mk'_surjective b
    simp only [RingCon.coe_mk'] at hab ⊢
    rw [← RingCon.coe_mul] at hab
    have hab' := (divisionResidue_eq_zero_iff (x * y)).1 hab
    have hx := mem_divisionIntegers.1 x.2
    have hy := mem_divisionIntegers.1 y.2
    have hmul : divisionNorm K D ((x : D) * (y : D)) < 1 := by simpa using hab'
    rw [divisionNorm_mul] at hmul
    rcases lt_or_ge (divisionNorm K D (x : D)) 1 with h | h
    · exact Or.inl ((divisionResidue_eq_zero_iff x).2 h)
    · refine Or.inr ((divisionResidue_eq_zero_iff y).2 ?_)
      have e1 : divisionNorm K D (x : D) = 1 := le_antisymm hx h
      rw [e1, one_mul] at hmul
      exact hmul

instance : IsDomain (DivisionResidue K D) := NoZeroDivisors.to_isDomain _

instance : Finite (DivisionResidue K D) := by
  classical
  obtain ⟨T, hT1, hT2⟩ := exists_finset_divisionNorm_sub_lt_one K D
  have hsurj : Function.Surjective fun t : T =>
      ((⟨(t : D), mem_divisionIntegers.2 (hT1 _ t.2)⟩ : divisionIntegers K D) :
        DivisionResidue K D) := by
    intro q
    obtain ⟨x, rfl⟩ := (divisionResidueCon K D).mk'_surjective q
    obtain ⟨t, htT, ht⟩ := hT2 (x : D) (mem_divisionIntegers.1 x.2)
    refine ⟨⟨t, htT⟩, ?_⟩
    rw [RingCon.coe_mk']
    refine divisionResidue_eq_iff.2 ?_
    show divisionNorm K D (t - (x : D)) < 1
    rwa [← divisionNorm_neg, neg_sub]
  exact Finite.of_surjective _ hsurj

/-! ### A generator of the units of the residue ring -/

variable (K D) in
/-- **Every element of absolute value one differs from a power of a fixed integer by an element of
absolute value less than one.**  The residue ring is a finite ring without zero divisors, hence a
finite field, and the nonzero elements of a finite field are the powers of a single one of them. -/
theorem exists_pow_divisionNorm_sub_lt_one :
    ∃ y : D, divisionNorm K D y ≤ 1 ∧
      ∀ x : D, divisionNorm K D x = 1 → ∃ i : ℕ, divisionNorm K D (x - y ^ i) < 1 := by
  obtain ⟨g, hg⟩ := exists_forall_eq_pow_of_finite_isDomain (DivisionResidue K D)
  obtain ⟨y, rfl⟩ := (divisionResidueCon K D).mk'_surjective g
  refine ⟨(y : D), mem_divisionIntegers.1 y.2, ?_⟩
  intro x hx
  have hxO : x ∈ divisionIntegers K D := mem_divisionIntegers.2 hx.le
  have hne : ((⟨x, hxO⟩ : divisionIntegers K D) : DivisionResidue K D) ≠ 0 := fun h => by
    have h1 := (divisionResidue_eq_zero_iff (⟨x, hxO⟩ : divisionIntegers K D)).1 h
    simp only at h1
    rw [hx] at h1
    exact absurd h1 (lt_irrefl 1)
  obtain ⟨i, hi⟩ := hg _ hne
  refine ⟨i, ?_⟩
  rw [← map_pow] at hi
  simp only [RingCon.coe_mk'] at hi
  have := divisionResidue_eq_iff.1 hi
  simpa using this

end Residue

end InverseGalois.CFT
