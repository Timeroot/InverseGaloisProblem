/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.Denominator

/-!
# Radicals of radicands congruent to one

A radical extension is unramified away from the exponent and the radicands, and that is enough for
most of Kummer theory.  At a place over the exponent itself a radical extension is usually
ramified, but not always: if the radicand is a unit at the place and congruent to one modulo the
`p`-th power of the different of the `p`-th roots of unity, the extension stays unramified there
too.  This is the criterion which separates the classes of radicands that can ramify a place over
the exponent from those that cannot, and it is the local input of the bound on the inertia group at
the residue characteristic.

The argument is again with the inertia group, but one order of magnitude finer than the argument
away from the exponent.  Write `λ` for `ζ - 1`.  From the congruence the radical `α` is itself
congruent to one modulo `λ`, because the product of the differences `α - ζ ^ i` is the radicand
minus one and all the factors have the same valuation as `α - 1` as soon as that valuation is
smaller than the valuation of `λ`.  So `(α - 1) / λ` is integral at the place, and an element of
the inertia group moves it by something in the place.  But an element of the inertia group
multiplies `α` by a `p`-th root of unity `ζ ^ j`, so it moves `(α - 1) / λ` by `α (ζ ^ j - 1) / λ`,
which is a unit at the place unless `j` is zero.

## Main results

* `InverseGalois.CFT.valuation_sub_lt_one_of_mem_inertia`: **an element of the inertia group at a
  place moves every element integral at that place by something in the place**, not only the
  algebraic integers.
* `InverseGalois.CFT.valuation_sub_one_le_of_pow_sub_one_le`: a radical whose radicand is congruent
  to one modulo the `p`-th power of `ζ - 1` is congruent to one modulo `ζ - 1`.
* `InverseGalois.CFT.eq_of_mem_inertia_of_radical_congr`: **an element of the inertia group fixes a
  radical whose radicand is a unit congruent to one modulo the `p`-th power of `ζ - 1`.**

## Tags

number field, Kummer theory, radical, inertia, unramified, root of unity, congruence
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Inertia on the local ring at a place -/

section Inertia

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- **An element of the inertia group at a place moves an element integral at that place by
something in the place.**  The element is a quotient of two algebraic integers whose denominator is
a unit at the place, and the automorphism moves numerator and denominator inside the place. -/
theorem valuation_sub_lt_one_of_mem_inertia {w : HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Ideal.inertia Gal(L/K) w.asIdeal) {y : L} (hy : w.valuation L y ≤ 1) :
    w.valuation L (σ y - y) < 1 := by
  obtain ⟨t, htw, r, htr⟩ := exists_notMem_smul_mem w hy
  have hunit : ∀ x : 𝓞 L, x ∉ w.asIdeal → w.intValuation x = 1 := fun x hx =>
    le_antisymm (w.intValuation_le_one x)
      (not_lt.mp fun h => hx ((w.intValuation_lt_one_iff_mem x).mp h))
  have hσt : σ • t - t ∈ w.asIdeal := AddSubgroup.mem_inertia.mp hσ t
  have hσr : σ • r - r ∈ w.asIdeal := AddSubgroup.mem_inertia.mp hσ r
  have hσtw : σ • t ∉ w.asIdeal := fun h => htw (by
    have := w.asIdeal.sub_mem h hσt
    simpa using this)
  -- the automorphism moves the quotient by a quotient with numerator in the place
  have hσtr : algebraMap (𝓞 L) L (σ • t) * σ y = algebraMap (𝓞 L) L (σ • r) := by
    have h := congrArg σ htr
    rwa [map_mul, show σ (algebraMap (𝓞 L) L t) = algebraMap (𝓞 L) L (σ • t) from rfl,
      show σ (algebraMap (𝓞 L) L r) = algebraMap (𝓞 L) L (σ • r) from rfl] at h
  have hnum : σ • r * t - r * (σ • t) ∈ w.asIdeal := by
    have hrw : σ • r * t - r * (σ • t) = (σ • r - r) * t - r * (σ • t - t) := by ring
    rw [hrw]
    exact w.asIdeal.sub_mem (w.asIdeal.mul_mem_right _ hσr) (w.asIdeal.mul_mem_left _ hσt)
  have key : (σ y - y) * (algebraMap (𝓞 L) L (σ • t) * algebraMap (𝓞 L) L t)
      = algebraMap (𝓞 L) L (σ • r * t - r * (σ • t)) := by
    rw [map_sub, map_mul, map_mul]
    linear_combination (algebraMap (𝓞 L) L t) * hσtr - (algebraMap (𝓞 L) L (σ • t)) * htr
  have hvkey := congrArg (w.valuation L) key
  rw [map_mul, map_mul, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    hunit t htw, hunit (σ • t) hσtw, mul_one, mul_one] at hvkey
  rw [hvkey]
  exact (w.intValuation_lt_one_iff_mem _).mpr hnum

end Inertia

/-! ### A radical of a radicand congruent to one -/

section Radical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {p : ℕ}

omit [NumberField K] [Algebra K L] in
/-- The valuation of a unit of the ring of integers is one. -/
theorem intValuation_eq_one_of_isUnit {w : HeightOneSpectrum (𝓞 L)} {x : 𝓞 L} (hx : IsUnit x) :
    w.intValuation x = 1 :=
  le_antisymm (w.intValuation_le_one x) (not_lt.mp fun h =>
    w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((w.intValuation_lt_one_iff_mem x).mp h) hx))

omit [NumberField K] [Algebra K L] in
/-- **All the differences of one and a nontrivial `p`-th root of unity have the same valuation**,
being associated as algebraic integers. -/
theorem valuation_pow_sub_one_eq (hp : p.Prime) {ξ : L} (hξ : IsPrimitiveRoot ξ p)
    (w : HeightOneSpectrum (𝓞 L)) {j : ℕ} (hj : ¬ p ∣ j) :
    w.valuation L (ξ ^ j - 1) = w.valuation L (ξ - 1) := by
  set ξ₀ : 𝓞 L := ⟨ξ, hξ.isIntegral hp.pos⟩ with hξ₀def
  have hξ₀ : IsPrimitiveRoot ξ₀ p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hξ
      (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  obtain ⟨u, hu⟩ :=
    hξ₀.associated_sub_one_pow_sub_one_of_coprime (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hj))
  have hmap : ∀ y : 𝓞 L, w.valuation L (algebraMap (𝓞 L) L y) = w.intValuation y := fun y =>
    HeightOneSpectrum.valuation_of_algebraMap w y
  have h1 : algebraMap (𝓞 L) L (ξ₀ ^ j - 1) = ξ ^ j - 1 := by
    rw [map_sub, map_pow, map_one]
    rfl
  have h2 : algebraMap (𝓞 L) L (ξ₀ - 1) = ξ - 1 := by
    rw [map_sub, map_one]
    rfl
  rw [← h1, ← h2, hmap, hmap, ← hu, w.intValuation.map_mul, intValuation_eq_one_of_isUnit u.isUnit,
    mul_one]

omit [NumberField K] [Algebra K L] in
/-- **A radical whose radicand is congruent to one modulo the `p`-th power of `ζ - 1` is congruent
to one modulo `ζ - 1`.**  Otherwise all the differences of the radical and the `p`-th roots of unity
would have the same valuation as the difference of the radical and one, and their product is the
radicand minus one. -/
theorem valuation_sub_one_le_of_pow_sub_one_le (hp : p.Prime) {ξ : L} (hξ : IsPrimitiveRoot ξ p)
    {w : HeightOneSpectrum (𝓞 L)} {α : L}
    (hcongr : w.valuation L (α ^ p - 1) ≤ w.valuation L (ξ - 1) ^ p) :
    w.valuation L (α - 1) ≤ w.valuation L (ξ - 1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hlt
  rw [not_le] at hlt
  -- every difference of the radical and a `p`-th root of unity has the same valuation
  have hfac : ∀ η ∈ Polynomial.nthRootsFinset p (1 : L),
      w.valuation L (α - η * 1) = w.valuation L (α - 1) := by
    intro η hη
    rcases eq_or_ne η 1 with rfl | hne
    · rw [mul_one]
    · obtain ⟨j, hjlt, rfl⟩ :=
        hξ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos (1 : L)).mp hη)
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hne (pow_zero ξ)
      have hvη : w.valuation L (ξ ^ j - 1) = w.valuation L (ξ - 1) :=
        valuation_pow_sub_one_eq hp hξ w fun hd => hj0 (Nat.eq_zero_of_dvd_of_lt hd hjlt)
      have hne' : w.valuation L (α - 1) ≠ w.valuation L (-(ξ ^ j - 1)) := by
        rw [Valuation.map_neg, hvη]
        exact ne_of_gt hlt
      have hsum : α - ξ ^ j * 1 = (α - 1) + -(ξ ^ j - 1) := by ring
      rw [hsum, Valuation.map_add_of_distinct_val _ hne', Valuation.map_neg, hvη,
        max_eq_left hlt.le]
  -- so the radicand minus one has valuation the `p`-th power of that valuation
  have hprod : α ^ p - 1 = ∏ η ∈ Polynomial.nthRootsFinset p (1 : L), (α - η * 1) := by
    have h := hξ.pow_sub_pow_eq_prod_sub_mul (x := α) (y := 1) hp.pos
    simpa using h
  have hval : w.valuation L (α ^ p - 1) = w.valuation L (α - 1) ^ p := by
    rw [hprod, map_prod, Finset.prod_congr rfl hfac, Finset.prod_const, hξ.card_nthRootsFinset]
  rw [hval] at hcongr
  exact absurd hcongr (not_le.mpr (pow_lt_pow_left₀ hlt zero_le' hp.ne_zero))

/-- **An element of the inertia group at a place fixes a radical whose radicand is a unit at the
place and congruent to one modulo the `p`-th power of `ζ - 1`.**  The quotient of the radical minus
one by `ζ - 1` is integral at the place, so the automorphism moves it inside the place; but the
automorphism multiplies the radical by a `p`-th root of unity, and a nontrivial one has the same
valuation as `ζ - 1` after subtracting one. -/
theorem eq_of_mem_inertia_of_radical_congr (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {w : HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Ideal.inertia Gal(L/K) w.asIdeal) {α : L} {a : K} (hpow : α ^ p = algebraMap K L a)
    (hunit : w.valuation L (algebraMap K L a) = 1)
    (hcongr : w.valuation L (algebraMap K L a - 1)
      ≤ w.valuation L (algebraMap K L (ζ - 1)) ^ p) :
    σ α = α := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set ξ : L := algebraMap K L ζ with hξdef
  have hξ : IsPrimitiveRoot ξ p := hζ.map_of_injective (algebraMap K L).injective
  have hlam : algebraMap K L (ζ - 1) = ξ - 1 := by rw [map_sub, map_one]
  have hξ1 : ξ - 1 ≠ 0 := sub_ne_zero.mpr (hξ.ne_one hp.one_lt)
  have hane : algebraMap K L a ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hpow
    exact hane hpow.symm
  -- the radical is a unit at the place
  have hαu : w.valuation L α = 1 := by
    have h1 : w.valuation L α ^ p = 1 := by rw [← map_pow, hpow, hunit]
    rcases lt_trichotomy (w.valuation L α) 1 with h | h | h
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h hp.ne_zero))
    · exact h
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hp.ne_zero))
  -- and it is congruent to one modulo `ζ - 1`
  have hstep : w.valuation L (α - 1) ≤ w.valuation L (ξ - 1) :=
    valuation_sub_one_le_of_pow_sub_one_le hp hξ (by rw [hpow, ← hlam]; exact hcongr)
  have hy : w.valuation L ((α - 1) / (ξ - 1)) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ hstep zero_le'
  have hmove := valuation_sub_lt_one_of_mem_inertia hσ hy
  -- the automorphism multiplies the radical by a root of unity
  have hone : (σ α / α) ^ p = 1 := by
    rw [div_pow, ← map_pow, hpow, AlgEquiv.commutes, div_self hane]
  obtain ⟨j, hjlt, hj⟩ := hξ.eq_pow_of_pow_eq_one hone
  have hσα : σ α = ξ ^ j * α := by
    rw [hξdef, ← AlgEquiv.commutes σ ζ, ← map_pow] at hj ⊢
    rw [hj, div_mul_cancel₀ _ hα0]
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hσα)
  -- a nontrivial root of unity is a unit multiple of `ζ - 1`
  have hvj : w.valuation L (ξ ^ j - 1) = w.valuation L (ξ - 1) :=
    valuation_pow_sub_one_eq hp hξ w fun hd => hj0 (Nat.eq_zero_of_dvd_of_lt hd hjlt)
  -- but then the automorphism moves the quotient by a unit at the place
  have hdiff : σ ((α - 1) / (ξ - 1)) - (α - 1) / (ξ - 1) = α * (ξ ^ j - 1) / (ξ - 1) := by
    have hσξ : σ (ξ - 1) = ξ - 1 := by
      rw [hξdef, ← map_one (algebraMap K L), ← map_sub, AlgEquiv.commutes]
    rw [map_div₀, hσξ, map_sub, map_one, hσα]
    field_simp
    ring
  rw [hdiff, map_div₀, map_mul, hαu, one_mul, hvj,
    div_self ((Valuation.ne_zero_iff (w.valuation L)).mpr hξ1)] at hmove
  exact absurd hmove (lt_irrefl 1)

end Radical

end InverseGalois.CFT
