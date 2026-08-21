import Mathlib

/-!
# Unramified primes in cyclotomic fields and their subfields

This file repackages the cyclotomic ramification computations of
`Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal` in terms of the commutative-algebra predicate
`Algebra.IsUnramifiedAt`, and shows that this predicate descends along a tower of number fields.
Together these give the ramification input to a Kronecker–Weber / Scholz–Reichardt style argument:
an intermediate field of `ℚ(ζₙ)` is unramified away from `n`.

## Main results

* `InverseGalois.CFT.isUnramifiedAt_of_isUnramifiedAt_tower`: for a tower of number fields
  `F ⊆ K`, a nonzero prime `Q` of `𝓞 F` is unramified over `ℤ` as soon as every prime of `𝓞 K`
  lying over `Q` is.

* `InverseGalois.CFT.isUnramifiedAt_of_not_dvd`: if `K = ℚ(ζₙ)` and `p` is a rational prime with
  `¬ p ∣ n`, then every prime `P` of `𝓞 K` above `p` satisfies `Algebra.IsUnramifiedAt ℤ P`.

* `InverseGalois.CFT.isUnramifiedAt_of_forall_prime_not_dvd`: the same conclusion for a nonzero
  prime `P` of `𝓞 ℚ(ζₙ)`, phrased without naming the rational prime underneath it.

* `InverseGalois.CFT.exists_prime_dvd_of_not_isUnramifiedAt`: a nonzero prime of `𝓞 ℚ(ζₙ)` that is
  ramified over `ℤ` contains a rational prime dividing `n`.

* `InverseGalois.CFT.isUnramifiedAt_of_not_dvd_of_algebra`: an intermediate field `F` of the
  cyclotomic field `ℚ(ζₙ)` is unramified at every prime of `𝓞 F` above a rational prime `p` with
  `¬ p ∣ n`.

* `InverseGalois.CFT.isUnramifiedAt_of_forall_prime_not_dvd_of_algebra`: the same statement for an
  arbitrary nonzero prime of `𝓞 F`.
-/

namespace InverseGalois.CFT

open Ideal NumberField

section NeBot

variable {K : Type*} [Field K] [NumberField K]

/-- A prime of the ring of integers of a number field lying above a rational prime is nonzero. -/
theorem ne_bot_of_liesOver_span (p : ℕ) [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.LiesOver (Ideal.span {(p : ℤ)})] : P ≠ ⊥ := by
  intro hP
  have hunder : Ideal.span {(p : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  have hbot : (Ideal.span {(p : ℤ)}) = ⊥ := by
    rw [hunder, hP, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
  simp only [Ideal.span_singleton_eq_bot, Int.natCast_eq_zero] at hbot
  exact hp.out.ne_zero hbot

end NeBot

section Tower

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- Unramifiedness over `ℤ` descends along a tower of number fields: if `Q` is a nonzero prime of
`𝓞 F` and every prime of `𝓞 K` lying over `Q` is unramified over `ℤ`, then so is `Q`. -/
theorem isUnramifiedAt_of_isUnramifiedAt_tower {Q : Ideal (𝓞 F)} [Q.IsPrime] (hQ : Q ≠ ⊥)
    (h : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], P.LiesOver Q → Algebra.IsUnramifiedAt ℤ P) :
    Algebra.IsUnramifiedAt ℤ Q := by
  have hQmax : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ ‹_›
  obtain ⟨P, hPmax, hPQ⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 F) (S := 𝓞 K) Q
  have hPprime : P.IsPrime := hPmax.isPrime
  have : Algebra.IsUnramifiedAt ℤ P := h P hPQ
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ Q P

end Tower

section Cyclotomic

variable (n p : ℕ) [NeZero n] [hp : Fact (Nat.Prime p)]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

/-- If the prime `p` does not divide `n`, then any prime of the ring of integers of `ℚ(ζₙ)` lying
above `p` is unramified over `ℤ`. -/
theorem isUnramifiedAt_of_not_dvd (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hn : ¬ p ∣ n) :
    Algebra.IsUnramifiedAt ℤ P := by
  have hunder : Ideal.span {(p : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (ne_bot_of_liesOver_span p P), ← hunder]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hn

variable {p}

/-- A nonzero prime `P` of the ring of integers of `ℚ(ζₙ)` is unramified over `ℤ` as soon as no
rational prime dividing `n` belongs to `P`. -/
theorem isUnramifiedAt_of_forall_prime_not_dvd (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ∀ q : ℕ, q.Prime → (q : 𝓞 K) ∈ P → ¬ q ∣ n) :
    Algebra.IsUnramifiedAt ℤ P := by
  have : NeZero P := ⟨hP⟩
  have hprime : (Ideal.absNorm (Ideal.under ℤ P)).Prime := Nat.absNorm_under_prime P
  have : Fact (Ideal.absNorm (Ideal.under ℤ P)).Prime := ⟨hprime⟩
  exact isUnramifiedAt_of_not_dvd n _ K P (h _ hprime (Int.absNorm_under_mem P))

/-- A nonzero prime of the ring of integers of `ℚ(ζₙ)` that is ramified over `ℤ` contains a
rational prime dividing `n`. -/
theorem exists_prime_dvd_of_not_isUnramifiedAt (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ¬ Algebra.IsUnramifiedAt ℤ P) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P ∧ q ∣ n := by
  by_contra hcon
  push_neg at hcon
  exact h (isUnramifiedAt_of_forall_prime_not_dvd n K P hP fun q hq hqP ↦ hcon q hq hqP)

end Cyclotomic

section Intermediate

/-- An intermediate field `F` of the cyclotomic field `K = ℚ(ζₙ)` is unramified at every prime of
`𝓞 F` lying above a rational prime `p` that does not divide `n`. -/
theorem isUnramifiedAt_of_not_dvd_of_algebra (n : ℕ) [NeZero n] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {F : Type*} [Field F] [NumberField F]
    [Algebra F K] (p : ℕ) [Fact (Nat.Prime p)] (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] (hn : ¬ p ∣ n) :
    Algebra.IsUnramifiedAt ℤ Q := by
  refine isUnramifiedAt_of_isUnramifiedAt_tower (K := K) (ne_bot_of_liesOver_span p Q) ?_
  intro P _ hPQ
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  exact isUnramifiedAt_of_not_dvd n p K P hn

/-- An intermediate field `F` of the cyclotomic field `K = ℚ(ζₙ)` is unramified at every nonzero
prime of `𝓞 F` that contains no rational prime dividing `n`. -/
theorem isUnramifiedAt_of_forall_prime_not_dvd_of_algebra (n : ℕ) [NeZero n] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {F : Type*} [Field F] [NumberField F]
    [Algebra F K] (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (h : ∀ q : ℕ, q.Prime → (q : 𝓞 F) ∈ Q → ¬ q ∣ n) :
    Algebra.IsUnramifiedAt ℤ Q := by
  have : NeZero Q := ⟨hQ⟩
  have hprime : (Ideal.absNorm (Ideal.under ℤ Q)).Prime := Nat.absNorm_under_prime Q
  have : Fact (Ideal.absNorm (Ideal.under ℤ Q)).Prime := ⟨hprime⟩
  exact isUnramifiedAt_of_not_dvd_of_algebra n K _ Q (h _ hprime (Int.absNorm_under_mem Q))

end Intermediate

end InverseGalois.CFT
