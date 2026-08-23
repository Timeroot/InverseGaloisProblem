/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.SplitCompletely

/-!
# Reduction modulo a completely split prime

Let `K` be a number field and let `q` be a rational prime which splits completely in `K`.  Then
`K` has a prime `P` above `q` whose residue field is the prime field with `q` elements, so that
reduction modulo `P` is a ring homomorphism `𝓞 K → ZMod q` extending reduction of integers
modulo `q`.

Such a homomorphism transports solvability of equations from the ring of integers down to the
prime field.  Two consequences are recorded here: an `ℓ`-th root of a rational integer in `K`
produces an `ℓ`-th root of its residue in `ZMod q`, and a primitive `n`-th root of unity in `K`
forces the congruence `q ≡ 1 (mod n)` whenever `q` does not divide `n`.  The latter uses the
identity `∏_{k=1}^{n-1} (1 - ζ ^ k) = n`, which shows that the image of `ζ` still has exact
order `n` after reduction.

## Main results

* `InverseGalois.NumberTheory.exists_ringHom_zmod_of_splitsCompletely` — a prime that splits
  completely in a number field admits a ring homomorphism from the ring of integers onto the field
  with `q` elements which is reduction modulo `q` on the rational integers.
* `InverseGalois.NumberTheory.exists_pow_eq_of_splitsCompletely` — an `ℓ`-th root of a rational
  integer in the ring of integers reduces to an `ℓ`-th root modulo a completely split prime.
* `InverseGalois.NumberTheory.exists_pow_eq_of_splitsCompletely_of_mem_field` — the same statement
  with the root taken in the number field itself.
* `InverseGalois.NumberTheory.dvd_sub_one_of_isPrimitiveRoot_of_splitsCompletely` — if a number
  field containing a primitive `n`-th root of unity has a completely split prime `q` not dividing
  `n`, then `n` divides `q - 1`.
-/

open NumberField

namespace InverseGalois.NumberTheory

/-- **Reduction modulo a completely split prime.**  A rational prime which splits completely in a
number field has above it a prime of the ring of integers whose residue field has exactly `q`
elements, hence is the prime field `ZMod q`; the composite of the quotient map with that
identification is a ring homomorphism extending reduction of the rational integers modulo `q`. -/
theorem exists_ringHom_zmod_of_splitsCompletely (K : Type*) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (h : SplitsCompletely K q) :
    ∃ f : 𝓞 K →+* ZMod q, ∀ n : ℤ, f (algebraMap ℤ (𝓞 K) n) = (n : ZMod q) := by
  have hq : q.Prime := Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hq
  obtain ⟨⟨P, hP⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP.2
  have hdeg : (Ideal.span {(q : ℤ)}).inertiaDeg P = 1 := (h P hP).2
  have hnorm : Ideal.absNorm P = q := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P hq, hdeg, pow_one]
  have hcard : Nat.card (𝓞 K ⧸ P) = q := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  haveI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card (𝓞 K ⧸ P) = q := by rw [← Nat.card_eq_fintype_card]; exact hcard
  refine ⟨((ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hq hcard').symm :
    (𝓞 K ⧸ P) ≃+* ZMod q).toRingHom.comp (Ideal.Quotient.mk P), fun n => ?_⟩
  simp [algebraMap_int_eq]

/-- **An `ℓ`-th root of a rational integer descends to the prime field.**  Reduction modulo a
completely split prime is a ring homomorphism to `ZMod q` fixing the residues of the rational
integers, so it carries a solution of `x ^ ℓ = a` in the ring of integers to a solution of the
same equation modulo `q`. -/
theorem exists_pow_eq_of_splitsCompletely (K : Type*) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (h : SplitsCompletely K q) (ℓ : ℕ) (a : ℤ)
    (hx : ∃ x : 𝓞 K, x ^ ℓ = algebraMap ℤ (𝓞 K) a) :
    ∃ y : ZMod q, y ^ ℓ = (a : ZMod q) := by
  obtain ⟨f, hf⟩ := exists_ringHom_zmod_of_splitsCompletely K q h
  obtain ⟨x, hxa⟩ := hx
  exact ⟨f x, by rw [← map_pow, hxa, hf]⟩

/-- **An `ℓ`-th root taken in the number field itself descends to the prime field.**  A root of the
monic integral equation `X ^ ℓ = a` is an algebraic integer, so it already lies in the ring of
integers and the previous reduction applies. -/
theorem exists_pow_eq_of_splitsCompletely_of_mem_field (K : Type*) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (h : SplitsCompletely K q) (ℓ : ℕ) (a : ℤ)
    (hx : ∃ x : K, x ^ ℓ = (a : K)) :
    ∃ y : ZMod q, y ^ ℓ = (a : ZMod q) := by
  obtain ⟨x, hxa⟩ := hx
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  · subst hℓ
    have ha : ((1 : ℤ) : K) = ((a : ℤ) : K) := by simpa using hxa
    have ha' : (1 : ℤ) = a := by exact_mod_cast ha
    exact ⟨1, by rw [← ha']; simp⟩
  · have hint : IsIntegral ℤ x := by
      refine ⟨Polynomial.X ^ ℓ - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hℓ, ?_⟩
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hxa]
      simp
    obtain ⟨y, hy⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 K) |>.mp hint
    refine exists_pow_eq_of_splitsCompletely K q h ℓ a ⟨y, ?_⟩
    apply RingOfIntegers.coe_injective
    rw [map_pow, hy, hxa]
    simp

/-- **A completely split prime is congruent to one modulo the order of a root of unity.**  The
identity `∏_{k=1}^{n-1} (1 - ζ ^ k) = n` shows that no proper power of the reduction of a primitive
`n`-th root of unity can be one, provided `q` does not divide `n`; so the reduction has exact
order `n` in the multiplicative group of the field with `q` elements, whose order is `q - 1`. -/
theorem dvd_sub_one_of_isPrimitiveRoot_of_splitsCompletely (K : Type*) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (h : SplitsCompletely K q) {n : ℕ} {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ n) (hqn : ¬ q ∣ n) : n ∣ q - 1 := by
  obtain ⟨f, -⟩ := exists_ringHom_zmod_of_splitsCompletely K q h
  have hn : n ≠ 0 := by rintro rfl; exact hqn (dvd_zero q)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set y : ZMod q := f ζ with hy
  have hy1 : y ^ (m + 1) = 1 := by rw [hy, ← map_pow, hζ.pow_eq_one, map_one]
  have hprod : ∏ k ∈ Finset.range m, (1 - y ^ (k + 1)) = ((m + 1 : ℕ) : ZMod q) := by
    have := congrArg f hζ.prod_one_sub_pow_eq_order
    rw [map_prod] at this
    simpa [hy] using this
  have hne : ((m + 1 : ℕ) : ZMod q) ≠ 0 := fun hc => hqn ((ZMod.natCast_eq_zero_iff _ _).mp hc)
  have hfac : ∀ k ∈ Finset.range m, (1 : ZMod q) - y ^ (k + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (hprod ▸ hne)
  have hprim : IsPrimitiveRoot y (m + 1) := by
    refine (IsPrimitiveRoot.iff m.succ_pos).mpr ⟨hy1, fun l hl0 hlm hl1 => ?_⟩
    refine hfac (l - 1) (Finset.mem_range.mpr (by omega)) ?_
    rw [show l - 1 + 1 = l by omega, hl1, sub_self]
  have hy0 : y ≠ 0 := fun hc => by
    rw [hc, zero_pow m.succ_ne_zero] at hy1
    exact zero_ne_one hy1
  rw [hprim.eq_orderOf]
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hy0)

end InverseGalois.NumberTheory
