/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.Denominator
import InverseGalois.CFT.Kummer.DyadicSquareClass
import InverseGalois.CFT.Local.PrimeResidueField

/-!
# The four rational square classes at an unramified dyadic place of degree one

A place of a number field over two whose ramification index and residue degree are both one behaves
exactly like the place of the rational field: two is a uniformizer and the residue field has two
elements.  The square-class computation of the previous file therefore applies, and it says that
after multiplication by one of `1, -1, 2, -2` every nonzero element becomes a square times a unit
congruent to one modulo four.

The two hypotheses are converted here.  Ramification index one says that two lies in the place but
not in its square, which pins the valuation of two to that of a uniformizer; residue degree one says
that the rational integers surject onto the residue field, which — since two lies in the place —
leaves only the residues of zero and one.  The second conversion is stated for an arbitrary element
of valuation at most one rather than for an algebraic integer, by clearing a denominator which is a
unit at the place.

## Main results

* `InverseGalois.CFT.notMem_sq_of_ramificationIdx_eq_one`: **an unramified prime does not lie in the
  square of a prime above it.**
* `InverseGalois.CFT.valuation_eq_exp_neg_one_of_ramificationIdx_eq_one`: **an unramified rational
  prime is a uniformizer at a prime above it.**
* `InverseGalois.CFT.valuation_lt_one_or_valuation_sub_one_lt_one`: **at a dyadic place of residue
  degree one every element integral at the place is congruent to zero or to one.**
* `InverseGalois.CFT.exists_isCongrPow_mul_intCast_dyadic`: **the four rational square classes
  `1, -1, 2, -2` exhaust the square classes at an unramified dyadic place of degree one**, modulo
  the units congruent to one modulo four.

## Tags

number field, dyadic place, ramification index, residue degree, uniformizer, square class
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped WithZero

/-! ### Uniformizers in the value group of the integers -/

section Value

variable {Z : Type*} [Field Z] {v : Valuation Z ℤᵐ⁰} {π : Z}

/-- Below a uniformizer there is nothing but the uniformizer and smaller. -/
theorem valuation_le_of_lt_one (hπ : v π = WithZero.exp (-1 : ℤ)) {x : Z} (hx : v x < 1) :
    v x ≤ v π := by
  rcases eq_or_ne (v x) 0 with h | h
  · rw [h]
    exact zero_le'
  · rw [hπ, ← WithZero.exp_log h, WithZero.exp_le_exp]
    have : WithZero.log (v x) < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_log h, WithZero.exp_zero]
      exact hx
    omega

/-- **Every nonzero element is a unit times a power of a uniformizer.** -/
theorem exists_unit_mul_zpow (hπ : v π = WithZero.exp (-1 : ℤ)) {x : Z} (hx : x ≠ 0) :
    ∃ (m : ℤ) (u : Z), v u = 1 ∧ x = u * π ^ m := by
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  have hx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  refine ⟨-WithZero.log (v x), x * π ^ (WithZero.log (v x)), ?_, ?_⟩
  · rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_log hx0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  · rw [mul_assoc, ← zpow_add₀ hπ0]
    simp

end Value

/-! ### Reading the local invariants -/

section Local

variable {Z : Type*} [Field Z] [NumberField Z] {p : ℕ}

open UniqueFactorizationMonoid in
/-- **An unramified prime does not lie in the square of a prime above it.**  Ramification index one
means that the prime below occurs exactly once in the factorisation of its extension. -/
theorem notMem_sq_of_ramificationIdx_eq_one (hp : p.Prime) (P : Ideal (𝓞 Z)) [hPp : P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 Z)) (Ideal.span {(p : ℤ)}) P = 1) :
    ((p : ℕ) : 𝓞 Z) ∉ P ^ 2 := by
  classical
  have hspan : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 Z)) (Ideal.span {(p : ℤ)})
      = Ideal.span {((p : ℕ) : 𝓞 Z)} := by
    rw [Ideal.map_span]
    simp
  have hp0 : Ideal.map (algebraMap ℤ (𝓞 Z)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.cast_ne_zero.mpr hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hPp hP0] at he
  intro hmem
  have hle : Ideal.map (algebraMap ℤ (𝓞 Z)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  rw [← Ideal.dvd_iff_le,
    dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0, normalizedFactors_pow,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hPp).irreducible, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le, he] at hle
  omega

omit [NumberField Z] in
/-- A rational prime lies in every prime of the ring of integers above it. -/
theorem natCast_mem_of_liesOver (P : Ideal (𝓞 Z)) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ((p : ℕ) : 𝓞 Z) ∈ P := by
  have hz : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
  rw [Ideal.LiesOver.over (p := Ideal.span {(p : ℤ)}) (P := P)] at hz
  simpa using hz

/-- **An unramified rational prime is a uniformizer at a prime above it.**  It lies in the prime but
not in its square, so its valuation is neither above nor below that of a uniformizer. -/
theorem valuation_eq_exp_neg_one_of_ramificationIdx_eq_one (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 Z)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 Z)) (Ideal.span {(p : ℤ)}) w.asIdeal = 1) :
    w.valuation Z ((p : ℕ) : Z) = WithZero.exp (-1 : ℤ) := by
  have hcast : ((p : ℕ) : Z) = algebraMap (𝓞 Z) Z ((p : ℕ) : 𝓞 Z) := by
    rw [map_natCast]
  have hle : w.intValuation ((p : ℕ) : 𝓞 Z) ≤ WithZero.exp (-1 : ℤ) := by
    have := (w.intValuation_le_pow_iff_mem ((p : ℕ) : 𝓞 Z) 1).mpr
      (by simpa using natCast_mem_of_liesOver (p := p) w.asIdeal)
    simpa using this
  have hnle : ¬ w.intValuation ((p : ℕ) : 𝓞 Z) ≤ WithZero.exp (-2 : ℤ) := by
    intro h
    exact notMem_sq_of_ramificationIdx_eq_one hp w.asIdeal he
      ((w.intValuation_le_pow_iff_mem ((p : ℕ) : 𝓞 Z) 2).mp (by simpa using h))
  have hne : w.intValuation ((p : ℕ) : 𝓞 Z) ≠ 0 :=
    w.intValuation_ne_zero _ (by exact_mod_cast Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [hcast, HeightOneSpectrum.valuation_of_algebraMap]
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hle
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hnle
  rw [← WithZero.exp_log hne, WithZero.exp_inj]
  omega

/-- **At a dyadic place of residue degree one every element integral at the place is congruent to
zero or to one.**  Clearing the denominator leaves an algebraic integer, which residue degree one
makes congruent to a rational integer, and two lies in the place. -/
theorem valuation_lt_one_or_valuation_sub_one_lt_one
    (w : HeightOneSpectrum (𝓞 Z)) [w.asIdeal.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})]
    (hf : (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg w.asIdeal = 1) {x : Z}
    (hx : w.valuation Z x ≤ 1) :
    w.valuation Z x < 1 ∨ w.valuation Z (x - 1) < 1 := by
  -- an algebraic integer is congruent to zero or to one modulo the place
  have hpar : ∀ y : 𝓞 Z, y ∈ w.asIdeal ∨ y - 1 ∈ w.asIdeal := by
    intro y
    obtain ⟨b, hb⟩ :=
      surjective_intCast_quotient_of_inertiaDeg_eq_one Nat.prime_two w.asIdeal hf
        (Ideal.Quotient.mk _ y)
    have hmem : y - (b : 𝓞 Z) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
        map_intCast (Ideal.Quotient.mk w.asIdeal) b]
      exact hb.symm
    have h2 : ((2 : ℕ) : 𝓞 Z) ∈ w.asIdeal := natCast_mem_of_liesOver (p := 2) w.asIdeal
    rcases Int.even_or_odd b with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine Or.inl ?_
      have : ((b : ℤ) : 𝓞 Z) ∈ w.asIdeal := by
        rw [hc]
        push_cast
        have : ((c : ℤ) : 𝓞 Z) + (c : ℤ) = ((2 : ℕ) : 𝓞 Z) * (c : ℤ) := by push_cast; ring
        rw [this]
        exact w.asIdeal.mul_mem_right _ h2
      simpa using w.asIdeal.add_mem hmem this
    · refine Or.inr ?_
      have : ((b : ℤ) : 𝓞 Z) - 1 ∈ w.asIdeal := by
        rw [hc]
        push_cast
        have : (2 : 𝓞 Z) * (c : ℤ) + 1 - 1 = ((2 : ℕ) : 𝓞 Z) * (c : ℤ) := by push_cast; ring
        rw [this]
        exact w.asIdeal.mul_mem_right _ h2
      have := w.asIdeal.add_mem hmem this
      simpa using this
  -- clear the denominator without touching the place
  obtain ⟨t, htw, r, htr⟩ := exists_notMem_smul_mem w hx
  have hval : ∀ y : 𝓞 Z, y ∈ w.asIdeal → w.valuation Z (algebraMap (𝓞 Z) Z y) < 1 := fun y hy =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem w y).mpr hy
  have ht1 : t - 1 ∈ w.asIdeal := by
    rcases hpar t with h | h
    · exact absurd h htw
    · exact h
  -- so the automorphism-free difference of the numerator and the element is small
  have hdiff : w.valuation Z (algebraMap (𝓞 Z) Z r - x) < 1 := by
    have hfac : algebraMap (𝓞 Z) Z r - x
        = algebraMap (𝓞 Z) Z (t - 1) * x := by
      rw [map_sub, map_one, sub_mul, one_mul, htr]
    rw [hfac, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' hx) (hval _ ht1)
  rcases hpar r with h | h
  · refine Or.inl ?_
    have hrw : x = algebraMap (𝓞 Z) Z r - (algebraMap (𝓞 Z) Z r - x) := by ring
    rw [hrw]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hval _ h) hdiff)
  · refine Or.inr ?_
    have hrw : x - 1 = algebraMap (𝓞 Z) Z (r - 1) - (algebraMap (𝓞 Z) Z r - x) := by
      rw [map_sub, map_one]
      ring
    rw [hrw]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hval _ h) hdiff)

/-! ### The square classes -/

/-- **The four rational square classes `1, -1, 2, -2` exhaust the square classes at an unramified
dyadic place of residue degree one**, modulo the squares and the units congruent to one modulo
four. -/
theorem exists_isCongrPow_mul_intCast_dyadic (w : HeightOneSpectrum (𝓞 Z))
    [w.asIdeal.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})]
    (he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 Z)) (Ideal.span {((2 : ℕ) : ℤ)}) w.asIdeal = 1)
    (hf : (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg w.asIdeal = 1) {β : Z} (hβ : β ≠ 0) :
    ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧
      IsCongrPow 2 (w.valuation Z) (-2) (β * (d : Z)) := by
  have hunif : w.valuation Z 2 = WithZero.exp (-1 : ℤ) := by
    have := valuation_eq_exp_neg_one_of_ramificationIdx_eq_one Nat.prime_two w he
    simpa using this
  have h20 : (2 : Z) ≠ 0 := two_ne_zero
  have hv2 : w.valuation Z 2 < 1 := by
    rw [hunif, ← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp]
    omega
  exact exists_isCongrPow_mul_intCast hv2 h20 (fun _ hx => valuation_le_of_lt_one hunif hx)
    (fun _ hx => exists_unit_mul_zpow hunif hx)
    (fun _ hx => valuation_lt_one_or_valuation_sub_one_lt_one w hf hx) hβ

end Local

end InverseGalois.CFT
