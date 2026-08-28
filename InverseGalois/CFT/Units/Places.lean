/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Fibers
import InverseGalois.Rigidity.RET.Genus.OrdMem
import InverseGalois.Rigidity.RET.Genus.OrdSmul
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# The Galois action on the finite places

A ring automorphism of a Dedekind domain permutes its height one primes, and it carries the
factorisation of a principal fractional ideal onto the factorisation of the image: the order of an
element at a prime is therefore the order of its image at the image of the prime.

For a Galois extension of number fields the primes above a fixed prime of the base form a single
orbit, so the height one primes of the top field are fibred over those of the base, and the
Herbrand quotient of the free lattice on a finite invariant set of them is a product of orders of
decomposition groups.

## Main definitions

* `InverseGalois.CFT.instMulActionHeightOneSpectrum`: the action of a ring automorphism on the
  height one primes.

## Main results

* `InverseGalois.CFT.ord_smul_place`: the order of an element at a prime is the order of its image
  at the image of the prime.
* `InverseGalois.CFT.ord_galSmul`: **the same for an arbitrary element of the field of fractions**,
  under a Galois automorphism of a number field.
* `InverseGalois.CFT.primeUnder_smul_eq`: the prime of the base below a prime of the extension is
  invariant under the Galois group.
* `InverseGalois.CFT.exists_smul_primeAbove_eq`: the Galois group acts transitively on the primes
  above a prime of the base.

## Tags

number field, height one prime, Galois action, order, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

/-! ### The action on the height one primes -/

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

/-- **The action of a ring automorphism on the height one primes.** -/
instance instMulActionHeightOneSpectrum : MulAction G (HeightOneSpectrum B) where
  smul σ v :=
    { asIdeal := σ • v.asIdeal
      isPrime := Ideal.IsPrime.smul (H := v.isPrime) σ
      ne_bot := by
        intro h
        refine v.ne_bot ?_
        have h2 : σ⁻¹ • (σ • v.asIdeal) = σ⁻¹ • (⊥ : Ideal B) := by rw [h]
        rwa [inv_smul_smul, ← Ideal.zero_eq_bot, smul_zero, Ideal.zero_eq_bot] at h2 }
  one_smul v := HeightOneSpectrum.ext (one_smul G v.asIdeal)
  mul_smul σ τ v := HeightOneSpectrum.ext (mul_smul σ τ v.asIdeal)

omit [IsDedekindDomain B] in
@[simp]
theorem asIdeal_smul (σ : G) (v : HeightOneSpectrum B) : (σ • v).asIdeal = σ • v.asIdeal := rfl

/-! ### The order at a moved prime -/

variable {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]

/-- **The order of an element of the domain at a prime is the order of its image at the image of
the prime.**  An automorphism carries the powers of a prime onto the powers of its image, and the
order is pinned by the powers in which the element lies. -/
theorem ord_smul_place (σ : G) (v : HeightOneSpectrum B) (b : B) :
    ord L (σ • v) (algebraMap B L (σ • b)) = ord L v (algebraMap B L b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hσb : σ • b ≠ 0 := fun h => hb (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  have key : ∀ j : ℕ, ((j : ℤ) ≤ ord L (σ • v) (algebraMap B L (σ • b)) ↔
      (j : ℤ) ≤ ord L v (algebraMap B L b)) := fun j => by
    rw [← mem_pow_iff_le_ord (K := L) (σ • v) hσb j, ← mem_pow_iff_le_ord (K := L) v hb j,
      asIdeal_smul, smul_mem_pow_smul_iff]
  have h1 := ord_nonneg (K := L) (σ • v) (σ • b)
  have h2 := ord_nonneg (K := L) v b
  have e1 := (key (ord L v (algebraMap B L b)).toNat).mpr (by omega)
  have e2 := (key (ord L (σ • v) (algebraMap B L (σ • b))).toNat).mp (by omega)
  omega

/-! ### The order at a moved prime of a number field -/

section NumberField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

omit [NumberField K] in
@[simp]
theorem coe_smul_ringOfIntegers (σ : Gal(K/k)) (b : 𝓞 K) : ((σ • b : 𝓞 K) : K) = σ (b : K) := rfl

/-- **The order of an element of a number field at a prime is the order of its image at the image
of the prime.** -/
theorem ord_galSmul (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ord K (σ • v) (σ x) = ord K v x := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hc0 : (c : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨c, hc⟩
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := fun h => hc0 (hinj (by rw [h, map_zero]))
  have hσc0 : (σ • (c : 𝓞 K)) ≠ 0 := fun h => hc0 (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  have hσcK : algebraMap (𝓞 K) K (σ • (c : 𝓞 K)) ≠ 0 :=
    fun h => hσc0 (hinj (by rw [h, map_zero]))
  rcases eq_or_ne (algebraMap (𝓞 K) K b) 0 with hb | hb
  · rw [hb, zero_div, map_zero, ord_zero, ord_zero]
  have hσb : algebraMap (𝓞 K) K (σ • b) ≠ 0 := by
    refine fun h => hb ?_
    have : σ ((b : 𝓞 K) : K) = 0 := h
    simpa using congrArg (fun y => σ⁻¹ y) this
  have hdiv : σ (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c)
      = algebraMap (𝓞 K) K (σ • b) / algebraMap (𝓞 K) K (σ • (c : 𝓞 K)) := by
    rw [map_div₀]
    rfl
  rw [hdiv, ord_div _ hσb hσcK, ord_div _ hb hcK, ord_smul_place σ v b,
    ord_smul_place σ v (c : 𝓞 K)]

end NumberField

/-! ### The primes above a prime of the base field -/

section Extension

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Nontrivial A]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

variable (A) in
/-- **The prime of the base below a height one prime of the extension.** -/
def primeUnder (v : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := Ideal.under A v.asIdeal
  isPrime := Ideal.IsPrime.under A v.asIdeal
  ne_bot := Ideal.under_ne_bot A v.ne_bot

omit [IsDedekindDomain A] [Module.IsTorsionFree A B] in
@[simp]
theorem primeUnder_asIdeal (v : HeightOneSpectrum B) :
    (primeUnder A v).asIdeal = Ideal.under A v.asIdeal := rfl

omit [IsDedekindDomain A] [Module.IsTorsionFree A B] in
/-- **The prime of the base below a prime of the extension is invariant under the group.** -/
theorem primeUnder_smul_eq (σ : G) (v : HeightOneSpectrum B) :
    primeUnder A (σ • v) = primeUnder A v := by
  have hfix : ∀ (τ : G) (a : A), τ • algebraMap A B a = algebraMap A B a := fun τ a => by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  refine HeightOneSpectrum.ext ?_
  ext a
  simp only [primeUnder_asIdeal, Ideal.mem_comap, asIdeal_smul,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, hfix]

omit [IsDedekindDomain A] [IsDedekindDomain B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
  [Nontrivial A] [SMulCommClass G A B] in
/-- **The group acts transitively on the primes above a prime of the base.** -/
theorem exists_smul_primeAbove_eq [Finite G] [IsGaloisGroup G A B] {v w : HeightOneSpectrum B}
    (h : Ideal.under A v.asIdeal = Ideal.under A w.asIdeal) : ∃ σ : G, σ • v = w := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : v.asIdeal.LiesOver (Ideal.under A v.asIdeal) := ⟨rfl⟩
  haveI : w.asIdeal.LiesOver (Ideal.under A v.asIdeal) := ⟨h⟩
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.under A v.asIdeal) v.asIdeal w.asIdeal G
  exact ⟨σ, HeightOneSpectrum.ext hσ⟩

omit [IsDedekindDomain A] [Module.IsTorsionFree A B] [SMulCommClass G A B] in
/-- **The group acts transitively on the primes above a prime of the base**, in terms of the prime
below. -/
theorem exists_smul_eq_of_primeUnder_eq [Finite G] [IsGaloisGroup G A B]
    {v w : HeightOneSpectrum B} (h : primeUnder A v = primeUnder A w) : ∃ σ : G, σ • v = w := by
  refine exists_smul_primeAbove_eq (A := A) ?_
  rw [← primeUnder_asIdeal (A := A) v, ← primeUnder_asIdeal (A := A) w, h]

end Extension

end InverseGalois.CFT
