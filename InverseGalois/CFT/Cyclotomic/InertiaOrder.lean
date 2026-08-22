import Mathlib
import InverseGalois.CFT.Decomposition

/-!
# The order of inertia at a rational prime in a cyclotomic field

Let `K = ℚ(ζₙ)` be a cyclotomic extension of `ℚ` and let `p` be a rational prime.  Writing
`p ^ k` for the exact power of `p` dividing `n`, the inertia subgroup of `Gal(K/ℚ)` at any prime
`P` of `𝓞 K` above `p` has order `φ (p ^ k)`, which is `1` exactly when `p` does not divide `n`.
Since Euler's totient function is multiplicative, these local orders multiply to the global
degree `φ n = [K : ℚ]`.  This is the local–global bookkeeping used in the Kronecker–Weber
theorem.

## Main results

* `InverseGalois.CFT.ramificationIdxIn_span_eq_totient`: the ramification index of a rational
  prime `p` in `ℚ(ζₙ)` is `φ (p ^ n.factorization p)`.
* `InverseGalois.CFT.card_inertia_eq_totient`: the inertia subgroup at a prime of `𝓞 ℚ(ζₙ)`
  above `p` has cardinality `φ (p ^ n.factorization p)`.
* `InverseGalois.CFT.card_inertia_eq_one_of_not_dvd` and
  `InverseGalois.CFT.card_inertia_eq_of_dvd`: the two special cases, in explicit form.
* `InverseGalois.CFT.prod_totient_pow_factorization`: the arithmetic identity
  `∏ p ∈ n.primeFactors, φ (p ^ n.factorization p) = φ n`.
* `InverseGalois.CFT.finrank_cyclotomic`: the degree of `ℚ(ζₙ)` over `ℚ` is `φ n`.
* `InverseGalois.CFT.prod_ramificationIdxIn_eq_finrank`: the ramification indices of the primes
  dividing `n` multiply to `[ℚ(ζₙ) : ℚ]`.
-/

open NumberField

namespace InverseGalois.CFT

section Totient

/-- Euler's totient function is recovered from its values at the prime powers exactly dividing
`n`. -/
theorem prod_totient_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, Nat.totient (p ^ n.factorization p) = Nat.totient n :=
  (Nat.multiplicative_factorization Nat.totient (fun _ _ h ↦ Nat.totient_mul h)
    Nat.totient_one hn).symm

end Totient

section Cyclotomic

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The degree of the cyclotomic field `ℚ(ζₙ)` over `ℚ` is `φ n`. -/
theorem finrank_cyclotomic : Module.finrank ℚ K = Nat.totient n :=
  IsCyclotomicExtension.Rat.finrank n K

/-- The ramification index of a rational prime `p` in the cyclotomic field `ℚ(ζₙ)` is
`φ (p ^ k)`, where `p ^ k` is the exact power of `p` dividing `n`. -/
theorem ramificationIdxIn_span_eq_totient (p : ℕ) [Fact (Nat.Prime p)] :
    Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) =
      Nat.totient (p ^ n.factorization p) := by
  by_cases hpn : p ∣ n
  · have hpos : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd Fact.out (NeZero.ne n) hpn
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hself := Nat.ordProj_mul_ordCompl_eq_self n p
    have hm : ¬ p ∣ n / p ^ n.factorization p := Nat.not_dvd_ordCompl Fact.out (NeZero.ne n)
    rw [hj] at hself hm
    rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq n K hself.symm hm, hj,
      Nat.totient_prime_pow_succ Fact.out]
  · rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hpn,
      Nat.factorization_eq_zero_of_not_dvd hpn, pow_zero, Nat.totient_one]

/-- The inertia subgroup of `Gal(ℚ(ζₙ)/ℚ)` at a prime `P` of the ring of integers lying over the
rational prime `p` has order `φ (p ^ k)`, where `p ^ k` is the exact power of `p` dividing `n`. -/
theorem card_inertia_eq_totient (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) = Nat.totient (p ^ n.factorization p) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have hPbot : P ≠ ⊥ := ne_bot_of_liesOver p P
  haveI := isMaximal_of_ne_bot P hPbot
  haveI := isSeparable_residue_of_ne_bot P hPbot
  have hunder : Ideal.span {(p : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) (P.under ℤ) (under_ne_bot P hPbot) P,
    ← hunder, ramificationIdxIn_span_eq_totient n K p]

/-- A rational prime not dividing `n` is unramified in `ℚ(ζₙ)`: its inertia subgroup is
trivial. -/
theorem card_inertia_eq_one_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hpn : ¬ p ∣ n) :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) = 1 := by
  rw [card_inertia_eq_totient n K p P, Nat.factorization_eq_zero_of_not_dvd hpn, pow_zero,
    Nat.totient_one]

/-- If `p ^ (j + 1)` is the exact power of the prime `p` dividing `n`, then the inertia subgroup
of `Gal(ℚ(ζₙ)/ℚ)` at a prime above `p` has order `p ^ j * (p - 1)`. -/
theorem card_inertia_eq_of_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (j : ℕ) (hj : n.factorization p = j + 1) :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) = p ^ j * (p - 1) := by
  rw [card_inertia_eq_totient n K p P, hj, Nat.totient_prime_pow_succ Fact.out]

/-- The ramification indices in `ℚ(ζₙ)` of the primes dividing `n` multiply to the degree
`[ℚ(ζₙ) : ℚ]`. -/
theorem prod_ramificationIdxIn_eq_finrank :
    ∏ p ∈ n.primeFactors, Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) =
      Module.finrank ℚ K := by
  rw [finrank_cyclotomic n K, ← prod_totient_pow_factorization (NeZero.ne n)]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  haveI : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ramificationIdxIn_span_eq_totient n K p

end Cyclotomic

end InverseGalois.CFT
