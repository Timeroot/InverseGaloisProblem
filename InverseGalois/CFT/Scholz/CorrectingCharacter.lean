/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.TotallyRamified

/-!
# The character correcting the ramification at one prime

A prime at which a solution of a central embedding problem with kernel of order `ℓ` acquires
unwanted ramification is either `ℓ` itself or congruent to one modulo `ℓ`.  In both cases the
cyclotomic field of a suitable prime-power conductor contains a cyclic extension of `ℚ` of degree
exactly `ℓ` ramified at that prime and nowhere else: for `p ≡ 1 mod ℓ` the conductor is `p`, whose
Galois group has order `p - 1`, and for `p = ℓ` it is `ℓ ^ 2`, whose Galois group has order
`ℓ (ℓ - 1)`.

Since `ℓ` is prime, that extension has a Galois group isomorphic to any prescribed group of order
`ℓ`, and the isomorphism turns it into a character with values in the kernel of the embedding
problem.  Total ramification says exactly that the character is already surjective on the inertia
subgroup at the prime, which is what allows a power of it to cancel the unwanted ramification.

## Main results

* `InverseGalois.CFT.exists_cyclic_totallyRamified_of_prime`: **for an odd prime `ℓ` and a prime
  `p` equal to `ℓ` or congruent to one modulo `ℓ`, there is a cyclic extension of `ℚ` of degree
  `ℓ` unramified away from `p` and totally ramified at `p`.**
* `InverseGalois.CFT.exists_hom_inertia_map_eq`: **the same extension, together with a character
  with values in a prescribed group of order `ℓ` which maps the inertia subgroup at `p` onto that
  whole group.**

## Tags

cyclotomic character, totally ramified, inertia subgroup, embedding problem, Scholz condition
-/

open NumberField InverseGalois.NumberTheory Module

namespace InverseGalois.CFT

variable {ℓ p : ℕ}

/-! ### The arithmetic of the conductor -/

/-- **A cyclic extension of degree `ℓ` ramified exactly at a prescribed prime.**  The prime is
either `ℓ`, and then the conductor is `ℓ ^ 2` and `ℓ` divides `φ (ℓ ^ 2) = ℓ (ℓ - 1)`, or it is
congruent to one modulo `ℓ`, and then the conductor is the prime itself and `ℓ` divides
`φ p = p - 1`. -/
theorem exists_cyclic_totallyRamified_of_prime (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hcond : p = ℓ ∨ ℓ ∣ p - 1) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), ∃ _ : NumberField ↥E,
      IsGalois ℚ ↥E ∧ IsCyclic Gal(↥E/ℚ) ∧ finrank ℚ ↥E = ℓ ∧ ramifiedSet ↥E ⊆ {p} ∧
      ∀ (Q : Ideal (𝓞 ↥E)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
        Ideal.inertia Gal(↥E/ℚ) Q = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hcond with rfl | hdvd
  · refine exists_intermediateField_cyclic_totallyRamified p hℓ2 2 ?_
    rw [Nat.totient_prime_pow hp two_pos]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num)) _
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))
    refine exists_intermediateField_cyclic_totallyRamified p hp2 1 ?_
    rwa [pow_one, Nat.totient_prime hp]

/-! ### The character -/

/-- **The correcting character.**  The Galois group of the cyclic extension of degree `ℓ` totally
ramified at the prime is cyclic of order `ℓ`, hence isomorphic to any prescribed group of that
prime order; composing the isomorphism with the inclusion gives a character whose image is the
prescribed group and which is surjective on every inertia subgroup at the prime. -/
theorem exists_hom_inertia_map_eq (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hcond : p = ℓ ∨ ℓ ∣ p - 1) {G : Type*} [Group G] (C : Subgroup G) (hC : Nat.card ↥C = ℓ) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), ∃ _ : NumberField ↥E, IsGalois ℚ ↥E ∧
      ramifiedSet ↥E ⊆ {p} ∧ ∃ χ : Gal(↥E/ℚ) →* G, χ.range = C ∧
        ∀ (Q : Ideal (𝓞 ↥E)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
          (Ideal.inertia Gal(↥E/ℚ) Q).map χ = C := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨E, hNF, hgal, hcyc, hrank, hram, hinert⟩ :=
    exists_cyclic_totallyRamified_of_prime hℓ hℓ2 hp hcond
  haveI := hNF
  haveI := hgal
  have hcard : Nat.card Gal(↥E/ℚ) = ℓ := by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥E, hrank]
  set χ : Gal(↥E/ℚ) →* G := C.subtype.comp (mulEquivOfPrimeCardEq hcard hC).toMonoidHom with hχ
  have hrange : χ.range = C := by
    rw [hχ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (mulEquivOfPrimeCardEq hcard hC).surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨E, hNF, hgal, hram, χ, hrange, fun Q hQp hQo => ?_⟩
  rw [hinert Q hQp hQo, ← MonoidHom.range_eq_map, hrange]

end InverseGalois.CFT
