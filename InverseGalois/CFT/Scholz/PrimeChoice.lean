import Mathlib
import InverseGalois.CFT.Scholz.Selector
import InverseGalois.NumberTheory.SplitDensity
import InverseGalois.NumberTheory.SplitReduction
import InverseGalois.NumberTheory.SplitSubfield

/-!
# The primes at which the Scholz–Reichardt induction branches

Each step of the Scholz–Reichardt induction enlarges the field realising a group by a cyclic
extension of degree `ℓ ^ e` ramified at a single new prime `q`, and the whole construction hinges
on choosing that prime well.  Three conditions are required of it: `q` must split completely in
the field already built, so that the two fields are linearly disjoint and the old ramified primes
stay unramified; `ℓ ^ N` must divide `q - 1`, so that the new field has level `N`; and every prime
ramified in the old field must be an `ℓ ^ e`-th power modulo `q`, so that those primes split
completely in the new field.

All three are conditions on the splitting of `q` in one auxiliary Galois number field, the
selector field of `InverseGalois.CFT.Scholz.Selector`: it contains the old field, a primitive
`ℓ ^ N`-th root of unity, and an `ℓ ^ e`-th root of each old ramified prime.  A prime splitting
completely in the selector field splits completely in the old field; reduction modulo it carries
the root of unity to an element of order `ℓ ^ N` in a group of order `q - 1`; and it carries the
radicals to `ℓ ^ e`-th roots modulo `q`.  Since infinitely many primes split completely in a Galois
number field, infinitely many primes have all three properties.

## Main results

* `InverseGalois.CFT.exists_isPrimitiveRoot_ringOfIntegers`: a root of unity of a number field is
  an algebraic integer.
* `InverseGalois.CFT.pow_div_eq_one_of_exists_pow_eq`: an `ℓ`-th power modulo `q` is killed by the
  exponent `(q - 1) / ℓ`.
* `InverseGalois.CFT.infinite_setOf_scholzPrime`: **infinitely many primes split completely in a
  prescribed number field, are congruent to one modulo `ℓ ^ N`, and have a prescribed finite set
  of primes among their `ℓ ^ e`-th power residues.**
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Roots of unity are algebraic integers -/

/-- **A root of unity of a number field lies in its ring of integers.**  It is a root of the monic
polynomial `X ^ n - 1`, hence integral over the integers. -/
theorem exists_isPrimitiveRoot_ringOfIntegers {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (hn : n ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ξ : 𝓞 K, IsPrimitiveRoot ξ n := by
  have hint : IsIntegral ℤ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hζ.pow_eq_one]
    simp
  obtain ⟨ξ, hξ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hint
  refine ⟨ξ, IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 K) K) ?_
    (FaithfulSMul.algebraMap_injective (𝓞 K) K)⟩
  rw [hξ]
  exact hζ

/-! ### Power residues modulo a prime -/

/-- **An `ℓ`-th power residue is killed by the exponent `(q - 1) / ℓ`.**  A nonzero `ℓ`-th power
`y ^ ℓ` raised to that exponent is `y ^ (q - 1)`, which is one by Fermat's little theorem. -/
theorem pow_div_eq_one_of_exists_pow_eq {q ℓ : ℕ} (hq : q.Prime) (hdvd : ℓ ∣ q - 1)
    {a : ZMod q} (ha : a ≠ 0) (h : ∃ y : ZMod q, y ^ ℓ = a) :
    a ^ ((q - 1) / ℓ) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  obtain ⟨y, rfl⟩ := h
  have hy : y ≠ 0 := by
    rintro rfl
    exact ha (zero_pow hℓ)
  rw [← pow_mul, Nat.mul_div_cancel' hdvd, ZMod.pow_card_sub_one_eq_one hy]

/-! ### The choice of the branching prime -/

/-- **The primes the Scholz–Reichardt induction may branch at are infinite in number.**  Given a
number field `L`, a prime `ℓ`, exponents `N` and `e` and a finite set `S` of primes, infinitely
many primes `q` split completely in `L`, satisfy `ℓ ^ N ∣ q - 1`, and have every element of `S`
among their `ℓ ^ e`-th power residues.  All three properties are read off from the splitting of
`q` in the selector field of `L`, `ℓ ^ N`, `ℓ ^ e` and `S`. -/
theorem infinite_setOf_scholzPrime (L : Type*) [Field L] [NumberField L] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (N e : ℕ) (S : Finset ℕ) :
    {q : ℕ | q.Prime ∧ SplitsCompletely L q ∧ ℓ ^ N ∣ q - 1 ∧
      ∀ p ∈ S, ∃ y : ZMod q, y ^ ℓ ^ e = (p : ZMod q)}.Infinite := by
  have hm : ℓ ^ N ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hk : ℓ ^ e ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  refine Set.Infinite.mono ?_
    ((infinite_setOf_prime_splitsCompletely (K := ↥(selectorField L (ℓ ^ N) (ℓ ^ e) S))).diff
      (Set.finite_singleton ℓ))
  rintro q ⟨⟨hq, hsplit⟩, hqℓ⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hqne : q ≠ ℓ := by simpa using hqℓ
  have hnd : ¬ q ∣ ℓ ^ N := fun h =>
    hqne ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow h))
  refine ⟨hq, ?_, ?_, ?_⟩
  · exact splitsCompletely_of_algHom
      (nonempty_algHom_selectorField L (ℓ ^ N) (ℓ ^ e) S hm hk).some hq hsplit
  · obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_selectorField L (ℓ ^ N) (ℓ ^ e) S hm hk
    obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_ringOfIntegers hm hζ
    exact dvd_sub_one_of_isPrimitiveRoot_of_splitsCompletely _ q hsplit hξ hnd
  · intro p hp
    obtain ⟨x, hx⟩ := exists_pow_eq_natCast_selectorField L (ℓ ^ N) (ℓ ^ e) S hm hk hp
    obtain ⟨y, hy⟩ := exists_pow_eq_of_splitsCompletely_of_mem_field _ q hsplit (ℓ ^ e) (p : ℤ)
      ⟨x, by push_cast; exact hx⟩
    exact ⟨y, by push_cast at hy; exact hy⟩

/-- **A branching prime for the field itself.**  Specialising the previous theorem to the finite
set of primes ramified in `L`, and discarding the finitely many primes that ramify in `L`, gives a
prime `q` unramified in `L`, split completely there, congruent to one modulo both `ℓ ^ e` and
`ℓ ^ N`, and having every prime ramified in `L` among its `ℓ ^ e`-th power residues. -/
theorem exists_scholzPrime_notMem (L : Type*) [Field L] [NumberField L] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (N e : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ ramifiedSet L ∧ SplitsCompletely L q ∧ ℓ ^ e ∣ q - 1 ∧
      ℓ ^ N ∣ q - 1 ∧ ∀ p ∈ ramifiedSet L, ∃ y : ZMod q, y ^ ℓ ^ e = (p : ZMod q) := by
  set S := (finite_ramifiedSet L).toFinset with hS
  obtain ⟨q, ⟨hqp, hqsplit, hqdvd, hqres⟩, hqS⟩ :=
    ((infinite_setOf_scholzPrime L hℓ (max N e) e S).diff S.finite_toSet).nonempty
  have hnot : q ∉ ramifiedSet L := by
    intro hc
    exact hqS (by rw [hS, Set.Finite.coe_toFinset]; exact hc)
  refine ⟨q, hqp, hnot, hqsplit, (pow_dvd_pow ℓ (le_max_right N e)).trans hqdvd,
    (pow_dvd_pow ℓ (le_max_left N e)).trans hqdvd, ?_⟩
  exact fun p hp => hqres p (by rw [hS, Set.Finite.mem_toFinset]; exact hp)

end InverseGalois.CFT
