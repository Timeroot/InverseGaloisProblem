/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places

/-!
# The orbits of the Galois group on the primes are the primes of the base

For a Galois extension of Dedekind domains the group permutes the primes lying over a fixed prime
of the base transitively, and every prime of the base is lain over.  Passing to the prime below is
therefore constant on orbits and induces a bijection from the set of orbits of the group on the
height one primes of the extension onto the height one primes of the base.

## Main definitions

* `InverseGalois.CFT.orbitPrimeUnder`: **the prime of the base below the primes of an orbit.**
* `InverseGalois.CFT.orbitPrimeUnderEquiv`: **the orbits of the group on the primes of the
  extension are the primes of the base.**

## Main results

* `InverseGalois.CFT.exists_primeUnder_eq`: every prime of the base has a prime above it.
* `InverseGalois.CFT.orbitPrimeUnder_injective`: two primes with the same prime below lie in the
  same orbit.

## Tags

Dedekind domain, height one prime, Galois action, orbit, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction

section OrbitPlaces

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [FaithfulSMul A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

variable (A B) in
/-- **Every height one prime of the base has a height one prime of the extension above it.** -/
theorem exists_primeUnder_eq (p : HeightOneSpectrum A) :
    ∃ P : HeightOneSpectrum B, primeUnder A P = p := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨Q, -, hQ, hQp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal B) (by
      simp [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    refine p.ne_bot ?_
    rw [← hQp, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A B)]
  exact ⟨⟨Q, hQ, hQ0⟩, HeightOneSpectrum.ext hQp⟩

variable (A) in
/-- **The prime of the base below the primes of an orbit.** -/
def orbitPrimeUnder (ω : orbitRel.Quotient G (HeightOneSpectrum B)) : HeightOneSpectrum A :=
  Quotient.liftOn' ω (primeUnder A) fun v w h => by
    obtain ⟨σ, rfl⟩ := h
    exact primeUnder_smul_eq σ w

variable (A) in
omit [FaithfulSMul A B] in
@[simp]
theorem orbitPrimeUnder_mk (v : HeightOneSpectrum B) :
    orbitPrimeUnder A (G := G) (Quotient.mk'' v) = primeUnder A v := rfl

variable (A B) in
omit [FaithfulSMul A B] in
/-- **The prime below determines the orbit**: two primes with the same prime below are conjugate. -/
theorem orbitPrimeUnder_injective [Finite G] [IsGaloisGroup G A B] :
    Function.Injective (orbitPrimeUnder (B := B) A (G := G)) := by
  intro ω ω'
  induction ω using Quotient.inductionOn' with
  | h v =>
    induction ω' using Quotient.inductionOn' with
    | h w =>
      intro h
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_primeUnder_eq (A := A) (G := G) h
      exact Quotient.sound' ⟨σ⁻¹, by rw [← hσ]; exact inv_smul_smul σ v⟩

variable (A B) in
/-- **Every prime of the base is the prime below some orbit.** -/
theorem orbitPrimeUnder_surjective :
    Function.Surjective (orbitPrimeUnder (B := B) A (G := G)) := fun p => by
  obtain ⟨P, hP⟩ := exists_primeUnder_eq A B p
  exact ⟨Quotient.mk'' P, hP⟩

variable (A B) in
omit [SMulCommClass G A B] in
/-- **Only finitely many primes of the extension lie above a given prime of the base**, since they
form a single orbit of a finite group. -/
theorem finite_setOf_primeUnder_eq [Finite G] [IsGaloisGroup G A B] (p : HeightOneSpectrum A) :
    {w : HeightOneSpectrum B | primeUnder A w = p}.Finite := by
  obtain ⟨W, hW⟩ := exists_primeUnder_eq A B p
  refine Set.Finite.subset (Set.finite_range (fun σ : G => σ • W)) fun w hw => ?_
  exact exists_smul_eq_of_primeUnder_eq (A := A) (hW.trans (Set.mem_setOf_eq ▸ hw).symm)

variable (A B) in
omit [SMulCommClass G A B] in
/-- **Only finitely many primes of the extension lie above a finite set of primes of the base.** -/
theorem finite_preimage_primeUnder [Finite G] [IsGaloisGroup G A B]
    {s : Set (HeightOneSpectrum A)} (hs : s.Finite) :
    (primeUnder A (B := B) ⁻¹' s).Finite :=
  (hs.biUnion fun p _ => finite_setOf_primeUnder_eq A B (G := G) p).subset fun _ hw =>
    Set.mem_biUnion hw rfl

variable (A B) in
/-- **The orbits of the Galois group on the height one primes of the extension are the height one
primes of the base.** -/
noncomputable def orbitPrimeUnderEquiv [Finite G] [IsGaloisGroup G A B] :
    orbitRel.Quotient G (HeightOneSpectrum B) ≃ HeightOneSpectrum A :=
  Equiv.ofBijective _ ⟨orbitPrimeUnder_injective A B, orbitPrimeUnder_surjective A B⟩

variable (A B) in
@[simp]
theorem orbitPrimeUnderEquiv_apply [Finite G] [IsGaloisGroup G A B]
    (ω : orbitRel.Quotient G (HeightOneSpectrum B)) :
    orbitPrimeUnderEquiv A B ω = orbitPrimeUnder A ω := rfl

end OrbitPlaces

end InverseGalois.CFT
