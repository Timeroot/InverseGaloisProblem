/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TameCharacter

/-!
# The Frobenius relation on tame inertia, and central images of inertia

At a tamely ramified prime the tame character identifies the inertia group with a subgroup of the
multiplicative group of the residue field, and conjugation by an arithmetic Frobenius raises the
tame character to the power of the cardinality of the residue field of the rational prime below.
Injectivity of the tame character turns this into the relation `F τ F⁻¹ = τ ^ p` inside the
decomposition group.

Applying a homomorphism whose value at `τ` is central makes the conjugation invisible, so that
value is fixed by the `p`-th power map; if it is also killed by an integer coprime to `p - 1` it is
trivial.  This is why a homomorphism from a Galois group to an `ℓ`-group can only be ramified at
primes congruent to one modulo `ℓ` — the arithmetic behind Serre's condition on the primes that a
Scholz realization is allowed to ramify at.

## Main results

* `InverseGalois.CFT.conj_arithFrobAt_eq_pow`: **at a tamely ramified prime, conjugation by an
  arithmetic Frobenius raises an element of the inertia group to the power of the cardinality of
  the residue field below.**
* `InverseGalois.CFT.eq_one_of_mem_center_of_liesOver`: **a central value of a homomorphism at an
  element of tame inertia over the rational prime `p` is trivial as soon as it is killed by an
  integer coprime to `p - 1`.**

## Tags

tame ramification, inertia group, Frobenius, centre, Scholz condition
-/

open NumberField

open scoped Pointwise

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K}

/-- **At a tamely ramified prime, conjugation by an arithmetic Frobenius raises an element of the
inertia group to the power of the cardinality of the residue field of the rational prime below.**
The tame character turns the conjugation into the corresponding power map on the residue field, and
in the tame case it is injective. -/
theorem conj_arithFrobAt_eq_pow [Finite (𝓞 K ⧸ P)] (h : IsUniformizer P π)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P))
    (τ : Ideal.inertia Gal(K/ℚ) P) :
    arithFrobAt ℤ Gal(K/ℚ) P * (τ : Gal(K/ℚ)) * (arithFrobAt ℤ Gal(K/ℚ) P)⁻¹ =
      (τ : Gal(K/ℚ)) ^ Nat.card (ℤ ⧸ P.under ℤ) := by
  have key : (⟨arithFrobAt ℤ Gal(K/ℚ) P * (τ : Gal(K/ℚ)) * (arithFrobAt ℤ Gal(K/ℚ) P)⁻¹,
      conj_mem_inertia (arithFrobAt_mem_stabilizer P) τ.2⟩ : Ideal.inertia Gal(K/ℚ) P) =
      τ ^ Nat.card (ℤ ⧸ P.under ℤ) := by
    refine tameChar_injective h hp ?_
    refine Units.ext ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact tameChar_conj_arithFrobAt h τ
  simpa using congrArg Subtype.val key

variable {G : Type*} [Group G]

/-- **A central value of a homomorphism at an element of tame inertia is fixed by the power map of
the residue field below.**  Conjugation by an arithmetic Frobenius is invisible on a central
element, while on the inertia group it is the power map. -/
theorem pow_card_eq_of_mem_center (h : IsUniformizer P π)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P))
    (φ : Gal(K/ℚ) →* G) (τ : Ideal.inertia Gal(K/ℚ) P)
    (hcen : φ (τ : Gal(K/ℚ)) ∈ Subgroup.center G) :
    φ (τ : Gal(K/ℚ)) ^ Nat.card (ℤ ⧸ P.under ℤ) = φ (τ : Gal(K/ℚ)) := by
  haveI := finite_quotient_of_ne_bot P h.ne_bot
  have hconj := congrArg φ (conj_arithFrobAt_eq_pow h hp τ)
  rw [map_mul, map_mul, map_pow, map_inv] at hconj
  rw [← hconj, (Subgroup.mem_center_iff.mp hcen) (φ (arithFrobAt ℤ Gal(K/ℚ) P)), mul_assoc,
    mul_inv_cancel, mul_one]

/-- **A central value of a homomorphism at an element of tame inertia which is killed by an integer
coprime to the order of the multiplicative group of the residue field below is trivial.** -/
theorem eq_one_of_mem_center (h : IsUniformizer P π)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P))
    (φ : Gal(K/ℚ) →* G) (τ : Ideal.inertia Gal(K/ℚ) P)
    (hcen : φ (τ : Gal(K/ℚ)) ∈ Subgroup.center G) {n : ℕ} (hn : φ (τ : Gal(K/ℚ)) ^ n = 1)
    (hcop : Nat.Coprime n (Nat.card (ℤ ⧸ P.under ℤ) - 1)) :
    φ (τ : Gal(K/ℚ)) = 1 := by
  haveI := finite_quotient_under_of_ne_bot P h.ne_bot
  have hq : 1 ≤ Nat.card (ℤ ⧸ P.under ℤ) := Nat.card_pos
  have hsub : φ (τ : Gal(K/ℚ)) ^ (Nat.card (ℤ ⧸ P.under ℤ) - 1) = 1 := by
    have hstep : φ (τ : Gal(K/ℚ)) ^ (Nat.card (ℤ ⧸ P.under ℤ) - 1) * φ (τ : Gal(K/ℚ)) =
        φ (τ : Gal(K/ℚ)) ^ Nat.card (ℤ ⧸ P.under ℤ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [pow_card_eq_of_mem_center h hp φ τ hcen] at hstep
    exact mul_eq_right.1 hstep
  have hdvd : orderOf (φ (τ : Gal(K/ℚ))) ∣ Nat.gcd n (Nat.card (ℤ ⧸ P.under ℤ) - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hsub)
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop ▸ hdvd))

/-- **A central value of a homomorphism at an element of the inertia group over a rational prime
`p` which does not divide the order of that group, and which is killed by an integer coprime to
`p - 1`, is trivial.** -/
theorem eq_one_of_mem_center_of_liesOver (p : ℕ) (hp : p.Prime) (hP : P.LiesOver
    (Ideal.span {(p : ℤ)})) (htame : ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P))
    (φ : Gal(K/ℚ) →* G) (τ : Ideal.inertia Gal(K/ℚ) P)
    (hcen : φ (τ : Gal(K/ℚ)) ∈ Subgroup.center G) {n : ℕ} (hn : φ (τ : Gal(K/ℚ)) ^ n = 1)
    (hcop : Nat.Coprime n (p - 1)) :
    φ (τ : Gal(K/ℚ)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  obtain ⟨x, hx⟩ := exists_isUniformizer (ne_bot_of_liesOver p P)
  refine eq_one_of_mem_center hx ?_ φ τ hcen hn ?_
  · rwa [ringChar_quotient_eq p hp P]
  · rwa [natCard_quotient_under p P]

end InverseGalois.CFT
