/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Fixed points of an involution of a finite field are squares

A group of order two acting faithfully on a finite field cuts out a subfield over which the field
has degree two, so the cardinality of the field is the square of the cardinality of the subfield.
An element of the subfield is killed by one less than the cardinality of the subfield, and for odd
characteristic that exponent divides half of one less than the cardinality of the whole field, so
Euler's criterion exhibits the element as a square.

## Main results

* `InverseGalois.CFT.isSquare_of_smul_eq_self`: an element of a finite field of odd characteristic
  fixed by a faithful action of a group of order two is a square.
* `InverseGalois.CFT.isSquare_of_ringEquiv_apply_eq`: **an element of a finite field of odd
  characteristic fixed by an involution of the field is a square.**

## Tags

finite field, square, Euler criterion, involution, fixed field
-/

namespace InverseGalois.CFT

section FixedSquare

variable {κ : Type*} [Field κ] [Fintype κ]

/-- **An element of a finite field of odd characteristic fixed by a faithful action of a group of
order two is a square.**  The fixed subfield has cardinality the square root of the cardinality of
the field, so the element is killed by half of one less than the cardinality of the field. -/
theorem isSquare_of_smul_eq_self (G : Type*) [Group G] [Finite G] [MulSemiringAction G κ]
    [FaithfulSMul G κ] (hG : Nat.card G = 2) (hchar : ringChar κ ≠ 2) {x : κ}
    (hx : ∀ g : G, g • x = x) : IsSquare x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by rw [mul_zero]⟩
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hGcard : Fintype.card G = 2 := by rw [← Nat.card_eq_fintype_card]; exact hG
  have hrank : Module.finrank (FixedPoints.subfield G κ) κ = 2 := by
    rw [FixedPoints.finrank_eq_card, hGcard]
  haveI : Fintype (FixedPoints.subfield G κ) := Fintype.ofFinite _
  have hcard : Fintype.card κ = Fintype.card (FixedPoints.subfield G κ) ^ 2 := by
    rw [← hrank]
    exact Module.card_eq_pow_finrank
  have hodd : Fintype.card κ % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hqodd : Fintype.card (FixedPoints.subfield G κ) % 2 = 1 := by
    by_contra h
    have hqe : Even (Fintype.card (FixedPoints.subfield G κ)) := Nat.even_iff.2 (by omega)
    have h2 : Even (Fintype.card (FixedPoints.subfield G κ) ^ 2) :=
      Nat.even_pow.2 ⟨hqe, by norm_num⟩
    rw [← hcard, Nat.even_iff] at h2
    omega
  have hxF : x ∈ FixedPoints.subfield G κ := hx
  have hxpow : x ^ (Fintype.card (FixedPoints.subfield G κ) - 1) = 1 := by
    have hy0 : (⟨x, hxF⟩ : FixedPoints.subfield G κ) ≠ 0 := by
      simpa [Subtype.ext_iff] using hx0
    have h := FiniteField.pow_card_sub_one_eq_one (⟨x, hxF⟩ : FixedPoints.subfield G κ) hy0
    have h' := congrArg (fun z : FixedPoints.subfield G κ => (z : κ)) h
    simpa using h'
  have harith : Fintype.card κ / 2 =
      (Fintype.card (FixedPoints.subfield G κ) - 1) *
        ((Fintype.card (FixedPoints.subfield G κ) + 1) / 2) := by
    obtain ⟨r, hr⟩ : ∃ r, Fintype.card (FixedPoints.subfield G κ) = 2 * r + 1 :=
      ⟨Fintype.card (FixedPoints.subfield G κ) / 2, by omega⟩
    have hcc : Fintype.card κ = 4 * (r * r) + 4 * r + 1 := by rw [hcard, hr]; ring
    have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    have h2 : 2 * r + 1 - 1 = 2 * r := by omega
    have h3 : 2 * r * (r + 1) = 2 * (r * r) + 2 * r := by ring
    rw [hcc, hr, h1, h2, h3]
    omega
  refine (FiniteField.isSquare_iff hchar hx0).2 ?_
  rw [harith, pow_mul, hxpow, one_pow]

/-- **An element of a finite field of odd characteristic fixed by an involution of the field is a
square.**  The involution generates a group of order two acting faithfully. -/
theorem isSquare_of_ringEquiv_apply_eq (hchar : ringChar κ ≠ 2) {τ : κ ≃+* κ}
    (hne : ∃ y : κ, τ y ≠ y) (hinv : ∀ y : κ, τ (τ y) = y) {x : κ} (hx : τ x = x) :
    IsSquare x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : (τ : RingAut κ) ≠ 1 := by
    obtain ⟨y, hy⟩ := hne
    exact fun h => hy (congrArg (fun f : RingAut κ => f y) h)
  have hsq : (τ : RingAut κ) * τ = 1 := by
    refine RingEquiv.ext fun y => ?_
    exact hinv y
  have hord : orderOf (τ : RingAut κ) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne'
  haveI : Finite (Subgroup.zpowers (τ : RingAut κ)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  haveI : FaithfulSMul (Subgroup.zpowers (τ : RingAut κ)) κ :=
    ⟨fun {_ _} h => Subtype.ext (eq_of_smul_eq_smul (α := κ) h)⟩
  refine isSquare_of_smul_eq_self (Subgroup.zpowers (τ : RingAut κ))
    (by rw [Nat.card_zpowers, hord]) hchar fun g => ?_
  have hle : Subgroup.zpowers (τ : RingAut κ) ≤ MulAction.stabilizer (RingAut κ) x :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hx)
  exact hle g.2

end FixedSquare

end InverseGalois.CFT
