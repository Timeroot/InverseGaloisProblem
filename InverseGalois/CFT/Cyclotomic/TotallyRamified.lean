/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.InertiaTransport

/-!
# Cyclic extensions of the rationals totally ramified at a single prescribed prime

The correcting characters of the Scholz–Reichardt construction are cut out of the cyclotomic field
of a *prescribed* prime-power conductor: for a prime `p` and an exponent `k ≥ 1` the field
`ℚ(ζ_{p ^ k})` is unramified away from `p` and totally ramified at `p`, and it is cyclic over `ℚ`
whenever `p` is odd or `k ≤ 2`.  Each of the three properties passes to the subfield of a
prescribed degree `ℓ` dividing `φ (p ^ k)`: cyclicity and unramifiedness because they are inherited
by subextensions, and total ramification because restriction maps an inertia subgroup onto the
inertia subgroup below it and is surjective onto the Galois group of a normal subextension.

The two cases used are `k = 1` with `ℓ ∣ p − 1`, which supplies a character ramified at a tame bad
prime, and `p = ℓ`, `k = 2`, which supplies a character ramified at the residue characteristic.
The second case is where the exponent `k = 2` earns its keep at the prime `2`: the units modulo `8`
are not cyclic, but the units modulo `4` are, so the conductor `ℓ ^ 2` is exactly as large as it
may be taken.

## Main results

* `InverseGalois.CFT.isUnramifiedAt_of_notMem_primePow`: a subfield of a cyclotomic field of
  prime-power conductor is unramified away from that prime.
* `InverseGalois.CFT.isCyclic_units_zmod_primePow`: the units modulo `p ^ k` form a cyclic group
  when `p` is odd or `k ≤ 2`.
* `InverseGalois.CFT.isCyclic_gal_cyclotomic_primePow`: the Galois group of a cyclotomic field of
  prime-power conductor is cyclic under the same condition.
* `InverseGalois.CFT.inertia_eq_top_cyclotomic_primePow`: a cyclotomic field of prime-power
  conductor is totally ramified at that prime.
* `InverseGalois.CFT.exists_cyclic_totallyRamified`: **for a prime `p`, an exponent `k ≥ 1` with
  `p` odd or `k ≤ 2`, and a divisor `ℓ` of `φ (p ^ k)`, there is a cyclic extension of `ℚ` of
  degree `ℓ` unramified away from `p` and totally ramified at `p`.**
* `InverseGalois.CFT.exists_intermediateField_cyclic_totallyRamified`: the same extension, as a
  subfield of a fixed algebraic closure of `ℚ`.

## Tags

cyclotomic field, cyclic extension, totally ramified, inertia subgroup
-/

open NumberField InverseGalois.NumberTheory Module

namespace InverseGalois.CFT

section PrimePower

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The cyclotomic field of prime-power conductor -/

/-- **A subfield of a cyclotomic field of prime-power conductor is unramified away from that
prime.**  A rational prime contained in a ramified prime of the subfield divides the conductor,
hence is the prime itself. -/
theorem isUnramifiedAt_of_notMem_primePow (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p ^ k} ℚ K] {F : Type*} [Field F] [NumberField F] [Algebra F K]
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥) (h : (p : 𝓞 F) ∉ Q) :
    Algebra.IsUnramifiedAt ℤ Q := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  refine isUnramifiedAt_of_forall_prime_not_dvd_of_algebra (p ^ k) K Q hQ ?_
  intro q hq hqQ hdvd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow hdvd)
  exact h hqQ

/-- **A subfield of a cyclotomic field of prime-power conductor ramifies at most at that prime.**
-/
theorem ramifiedSet_subset_singleton_primePow (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p ^ k} ℚ K] (F : Type*) [Field F] [NumberField F] [Algebra F K] :
    ramifiedSet F ⊆ {p} :=
  ramifiedSet_subset_singleton hp.out fun Q _ hQ hmem =>
    isUnramifiedAt_of_notMem_primePow p k K Q hQ hmem

/-- **The units modulo a prime power form a cyclic group** as soon as the prime is odd or the
exponent is at most two, the group of units modulo `4` still being cyclic of order `2`. -/
theorem isCyclic_units_zmod_primePow (k : ℕ) (hp2 : p ≠ 2 ∨ k ≤ 2) :
    IsCyclic (ZMod (p ^ k))ˣ := by
  rcases eq_or_ne p 2 with rfl | h2
  · exact (ZMod.isCyclic_units_two_pow_iff k).mpr (hp2.resolve_left fun h => h rfl)
  · exact ZMod.isCyclic_units_of_prime_pow p hp.out h2 k

/-- **The Galois group of a cyclotomic field of prime-power conductor is cyclic**, being the unit
group of the integers modulo that prime power, as soon as the prime is odd or the exponent is at
most two. -/
theorem isCyclic_gal_cyclotomic_primePow (k : ℕ) (hp2 : p ≠ 2 ∨ k ≤ 2) (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclic Gal(K/ℚ) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  haveI := isCyclic_units_zmod_primePow p k hp2
  exact isCyclic_of_surjective (IsCyclotomicExtension.Rat.galEquivZMod (p ^ k) K).symm
    (IsCyclotomicExtension.Rat.galEquivZMod (p ^ k) K).symm.surjective

/-- **A cyclotomic field of prime-power conductor is totally ramified at that prime**: the order of
the inertia subgroup is `φ (p ^ k)`, the degree of the field. -/
theorem inertia_eq_top_cyclotomic_primePow (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p ^ k} ℚ K] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(K/ℚ) P = ⊤ := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p ^ k} ℚ K
  have hfac : (p ^ k).factorization p = k := by
    simp [Nat.Prime.factorization_pow hp.out]
  rw [← inertia_eq_top_iff_card_eq_finrank, card_inertia_eq_totient (p ^ k) K p P, hfac,
    finrank_cyclotomic (p ^ k) K]

/-! ### The prescribed subfield -/

/-- **A cyclic extension of the rationals of prescribed degree, totally ramified at a prescribed
prime and unramified elsewhere.**  It is the subfield of degree `ℓ` of the cyclotomic field of
conductor `p ^ k`, which exists because that Galois group is cyclic of order `φ (p ^ k)`; the
ramification statements are inherited from the cyclotomic field, total ramification because
restriction maps inertia onto inertia and is surjective. -/
theorem exists_cyclic_totallyRamified {ℓ : ℕ} (k : ℕ) (hp2 : p ≠ 2 ∨ k ≤ 2) (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K] (hdvd : ℓ ∣ Nat.totient (p ^ k)) :
    ∃ F : IntermediateField ℚ K, ∃ _ : NumberField ↥F,
      IsGalois ℚ ↥F ∧ IsCyclic Gal(↥F/ℚ) ∧ finrank ℚ ↥F = ℓ ∧ ramifiedSet ↥F ⊆ {p} ∧
      ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
        Ideal.inertia Gal(↥F/ℚ) Q = ⊤ := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p ^ k} ℚ K
  haveI : IsCyclic Gal(K/ℚ) := isCyclic_gal_cyclotomic_primePow p k hp2 K
  obtain ⟨F, hgal, hcyc, hrank⟩ := IsCyclic.exists_intermediateField_finrank_eq (d := ℓ) ℚ K
    (by rwa [finrank_cyclotomic (p ^ k) K])
  haveI := hgal
  haveI : NumberField ↥F := inferInstance
  refine ⟨F, inferInstance, hgal, hcyc, hrank,
    ramifiedSet_subset_singleton_primePow p k K ↥F, ?_⟩
  intro Q hQp hQo
  haveI := hQp
  haveI := hQo
  have hQ0 : Q ≠ ⊥ := ne_bot_of_liesOver_natCast hp.out inferInstance
  haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 inferInstance
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) Q
  haveI := hPmax
  haveI := hPover
  haveI : P.IsPrime := hPmax.isPrime
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q (Ideal.span {(p : ℤ)})
  have hunder : P.under (𝓞 ↥F) = Q := (Ideal.LiesOver.over (p := Q)).symm
  rw [← hunder]
  exact inertia_eq_top_of_inertia_eq_top F hp.out P (inertia_eq_top_cyclotomic_primePow p k K P)

/-! ### Inside a fixed algebraic closure -/

/-- **A cyclic extension of the rationals of prescribed degree inside a fixed algebraic closure,
totally ramified at a prescribed prime and unramified elsewhere.**  The subfield of the cyclotomic
field is transported into the algebraic closure along the canonical isomorphism, which preserves
the degree, the ramified primes and the total ramification. -/
theorem exists_intermediateField_cyclic_totallyRamified {ℓ : ℕ} (k : ℕ) (hp2 : p ≠ 2 ∨ k ≤ 2)
    (hdvd : ℓ ∣ Nat.totient (p ^ k)) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), ∃ _ : NumberField ↥E,
      IsGalois ℚ ↥E ∧ IsCyclic Gal(↥E/ℚ) ∧ finrank ℚ ↥E = ℓ ∧ ramifiedSet ↥E ⊆ {p} ∧
      ∀ (Q : Ideal (𝓞 ↥E)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
        Ideal.inertia Gal(↥E/ℚ) Q = ⊤ := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  obtain ⟨F, hNF, hgal, hcyc, hrank, hram, hinert⟩ :=
    exists_cyclic_totallyRamified p k hp2 ↥(cycSubfield (p ^ k)) hdvd
  haveI := hNF
  haveI := hgal
  haveI := hcyc
  set e := IntermediateField.liftAlgEquiv F with he
  haveI : FiniteDimensional ℚ ↥(IntermediateField.lift F) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : NumberField ↥(IntermediateField.lift F) := ⟨⟩
  haveI : IsGalois ℚ ↥(IntermediateField.lift F) := IsGalois.of_algEquiv e
  refine ⟨IntermediateField.lift F, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  · rw [← e.toLinearEquiv.finrank_eq]
    exact hrank
  · rwa [← ramifiedSet_eq_of_ringEquiv e.toRingEquiv]
  · intro Q hQp hQo
    haveI := hQp
    haveI := hQo
    exact inertia_eq_top_of_algEquiv e hp.out hinert Q

end PrimePower

end InverseGalois.CFT
