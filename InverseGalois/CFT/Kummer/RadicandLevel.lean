/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LevelOne

/-!
# Radicands at the cyclotomic place

At a place of residue characteristic `ℓ` where `ζ - 1` is a uniformizer, the residue field is the
field with `ℓ` elements, and an automorphism `δ` of the base raising `ζ` to the power of a
primitive root `g` acts trivially on the residue field, the radicands of an abelian extension of
exponent `ℓ` are severely restricted.  Such a radicand satisfies `δ w = w ^ g` up to an `ℓ`-th
power; comparing valuations shows that its valuation is divisible by `ℓ`, so that modulo `ℓ`-th
powers it is a unit, and Fermat's little theorem then normalises it to a unit congruent to one.
The level of that unit, the power of the uniformizer to which it is congruent to one, satisfies the
congruence `g ^ n ≡ g` recorded in the previous file, so it is either one or at least `ℓ`.

Two radicands of level one differ, after dividing by a power of the first, by a radicand of level
at least two, hence of level at least `ℓ`; and a radicand of level at least `ℓ` is, up to an `ℓ`-th
power, a unit congruent to one modulo the `ℓ`-th power of the uniformizer.  So modulo the radicands
that are congruent to one in that sense, the radicands form a cyclic group of order at most `ℓ`.

## Main definitions

* `InverseGalois.CFT.IsCyclotomicPlace`: the local data at the place: a uniformizer whose
  `ℓ - 1`-st power is `ℓ`, a residue field with `ℓ` elements, and an automorphism in the inertia
  subgroup raising the uniformizer to `g` times itself.
* `InverseGalois.CFT.IsEigenRadicand`: a radicand whose conjugate is its `g`-th power, up to an
  `ℓ`-th power.
* `InverseGalois.CFT.IsCongrPow`: a radicand which is, up to an `ℓ`-th power, a unit congruent to
  one modulo the `ℓ`-th power of the uniformizer.

## Main results

* `InverseGalois.CFT.IsCyclotomicPlace.dvd_of_isEigenRadicand`: **the valuation of a radicand is
  divisible by `ℓ`.**
* `InverseGalois.CFT.IsCyclotomicPlace.exists_unit_congr_one`: **a radicand is, up to an `ℓ`-th
  power, a unit congruent to one.**
* `InverseGalois.CFT.IsCyclotomicPlace.level_eq_or_le`: **the level of such a unit is one or at
  least `ℓ`.**
* `InverseGalois.CFT.IsCyclotomicPlace.isCongrPow_or_exists_div`: **two radicands are dependent
  modulo the radicands congruent to one**, so those form a subgroup of index at most `ℓ`.

## Tags

valuation, uniformizer, level, radicand, Kummer theory, cyclotomic field
-/

namespace InverseGalois.CFT

/-! ### Integers at a place -/

section IntCast

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ)

/-- **An integer has valuation at most one.** -/
theorem valuation_intCast_le_one (m : ℤ) : v (m : R) ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact valuation_natCast_le_one v n
  · rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
    exact valuation_natCast_le_one v n

end IntCast

/-! ### The local data at the cyclotomic place -/

section Place

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- **The local data at a place of residue characteristic `ℓ` carrying the `ℓ`-th roots of
unity.**  The uniformizer `π` is `ζ - 1`, so that its `ℓ - 1`-st power is `ℓ` up to a unit, the
residue field is the field with `ℓ` elements, and the automorphism `δ` lies in the inertia subgroup
and raises `ζ` to the power of a primitive root `g` modulo `ℓ`. -/
structure IsCyclotomicPlace (ℓ g : ℕ) (v : Valuation K Γ) (π : K) (δ : K →+* K) : Prop where
  /-- The residue characteristic is a prime. -/
  prime : ℓ.Prime
  /-- The uniformizer is nonzero. -/
  ne_zero : v π ≠ 0
  /-- The uniformizer lies in the place. -/
  lt_one : v π < 1
  /-- Every valuation is a power of the valuation of the uniformizer. -/
  exists_zpow : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = v π ^ n
  /-- The place is ramified of index `ℓ - 1` over the residue characteristic. -/
  val_natCast : v (ℓ : K) = v π ^ (ℓ - 1)
  /-- The residue field is the field with `ℓ` elements. -/
  exists_natCast : ∀ x : K, v x ≤ 1 → ∃ m : ℕ, v (x - m) < 1
  /-- The automorphism preserves the place. -/
  map_val : ∀ x : K, v (δ x) = v x
  /-- The automorphism lies in the inertia subgroup. -/
  val_sub_lt : ∀ x : K, v x ≤ 1 → v (δ x - x) < 1
  /-- The automorphism raises the uniformizer to `g` times itself. -/
  val_map_sub : v (δ π - g * π) ≤ v π ^ 2
  /-- A primitive root satisfies `g ^ n = g` only for `n = 1` below `ℓ`. -/
  eq_one_of_dvd : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ ℓ → ((ℓ : ℤ) ∣ (g : ℤ) ^ n - g) → n = 1
  /-- A primitive root is not congruent to one. -/
  not_dvd_sub_one : ¬ (ℓ : ℤ) ∣ (g : ℤ) - 1

/-- **A radicand whose conjugate is its `g`-th power up to an `ℓ`-th power.**  The radicands of an
abelian extension of exponent `ℓ` of the field below all have this property. -/
def IsEigenRadicand (ℓ g : ℕ) (δ : K →+* K) (w : K) : Prop :=
  ∃ y : K, y ≠ 0 ∧ δ w = w ^ g * y ^ ℓ

/-- **A radicand which is a unit congruent to one modulo the `ℓ`-th power of the uniformizer**, up
to an `ℓ`-th power.  Such a radicand generates an extension unramified at the place. -/
def IsCongrPow (ℓ : ℕ) (v : Valuation K Γ) (π : K) (w : K) : Prop :=
  ∃ c γ : K, γ ≠ 0 ∧ v c = 1 ∧ v (c - 1) ≤ v π ^ ℓ ∧ w = c * γ ^ ℓ

/-! ### Radicands form a group -/

section Eigen

variable {ℓ g : ℕ} {δ : K →+* K} {w w₁ w₂ : K}

/-- The radicands are closed under multiplication. -/
theorem IsEigenRadicand.mul (h₁ : IsEigenRadicand ℓ g δ w₁) (h₂ : IsEigenRadicand ℓ g δ w₂) :
    IsEigenRadicand ℓ g δ (w₁ * w₂) := by
  obtain ⟨y₁, hy₁, he₁⟩ := h₁
  obtain ⟨y₂, hy₂, he₂⟩ := h₂
  exact ⟨y₁ * y₂, mul_ne_zero hy₁ hy₂, by rw [map_mul, he₁, he₂, mul_pow, mul_pow]; ring⟩

/-- The radicands are closed under inverses. -/
theorem IsEigenRadicand.inv (h : IsEigenRadicand ℓ g δ w) : IsEigenRadicand ℓ g δ w⁻¹ := by
  obtain ⟨y, hy, he⟩ := h
  refine ⟨y⁻¹, inv_ne_zero hy, ?_⟩
  rw [map_inv₀, he, mul_inv, ← inv_pow, ← inv_pow]

/-- The radicands are closed under natural powers. -/
theorem IsEigenRadicand.pow (h : IsEigenRadicand ℓ g δ w) (j : ℕ) :
    IsEigenRadicand ℓ g δ (w ^ j) := by
  induction j with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ j ih => rw [pow_succ]; exact ih.mul h

/-- The radicands are closed under division. -/
theorem IsEigenRadicand.div (h₁ : IsEigenRadicand ℓ g δ w₁) (h₂ : IsEigenRadicand ℓ g δ w₂) :
    IsEigenRadicand ℓ g δ (w₁ / w₂) := by
  rw [div_eq_mul_inv]
  exact h₁.mul h₂.inv

/-- Every `ℓ`-th power is a radicand. -/
theorem isEigenRadicand_pow {γ : K} (hγ : γ ≠ 0) : IsEigenRadicand ℓ g δ (γ ^ ℓ) := by
  refine ⟨δ γ / γ ^ g, div_ne_zero ((map_ne_zero_iff δ δ.injective).mpr hγ) (pow_ne_zero g hγ), ?_⟩
  rw [map_pow, div_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

/-- Multiplying a radicand by an `ℓ`-th power gives a radicand. -/
theorem IsEigenRadicand.mul_pow (h : IsEigenRadicand ℓ g δ w) {γ : K} (hγ : γ ≠ 0) :
    IsEigenRadicand ℓ g δ (w * γ ^ ℓ) :=
  h.mul (isEigenRadicand_pow hγ)

end Eigen

/-- A root of one in a linearly ordered group with zero is one. -/
theorem eq_one_of_pow_eq_one {x : Γ} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have h1 : x ^ n ≤ x ^ 1 := pow_le_pow_right_of_le_one' hlt.le (by omega)
    rw [hx, pow_one] at h1
    exact absurd h1 (not_le.mpr hlt)
  · exact heq
  · have h1 : x ^ 1 ≤ x ^ n := pow_le_pow_right' hgt.le (by omega)
    rw [hx, pow_one] at h1
    exact absurd h1 (not_le.mpr hgt)

/-! ### Consequences of the local data -/

namespace IsCyclotomicPlace

variable {ℓ g : ℕ} {v : Valuation K Γ} {π : K} {δ : K →+* K}

/-- The value group is nontrivial. -/
theorem nontrivial (h : IsCyclotomicPlace ℓ g v π δ) : Nontrivial Γ :=
  ⟨⟨v π, 1, ne_of_lt h.lt_one⟩⟩

/-- The uniformizer is integral. -/
theorem le_one (h : IsCyclotomicPlace ℓ g v π δ) : v π ≤ 1 := h.lt_one.le

/-- The uniformizer is nonzero. -/
theorem pi_ne_zero (h : IsCyclotomicPlace ℓ g v π δ) : π ≠ 0 := by
  haveI := h.nontrivial
  exact (Valuation.ne_zero_iff v).mp h.ne_zero

/-- The valuation of the uniformizer is positive. -/
theorem pos (h : IsCyclotomicPlace ℓ g v π δ) : 0 < v π :=
  lt_of_le_of_ne zero_le' (Ne.symm h.ne_zero)

/-- **The valuation of an element of the place is a positive power of the valuation of the
uniformizer.**  That exponent is the *level* of the element. -/
theorem exists_pow (h : IsCyclotomicPlace ℓ g v π δ) {x : K} (hx0 : x ≠ 0) (hx : v x < 1) :
    ∃ n : ℕ, 1 ≤ n ∧ v x = v π ^ n := by
  obtain ⟨n, hn⟩ := h.exists_zpow x hx0
  have hn1 : (1 : ℤ) ≤ n := by
    by_contra hc
    push_neg at hc
    have hle : v π ^ (0 : ℤ) ≤ v π ^ n :=
      (zpow_le_zpow_iff_right_of_lt_one₀ h.pos h.lt_one).mpr (by omega)
    rw [zpow_zero, ← hn] at hle
    exact absurd hx (not_lt.mpr hle)
  refine ⟨n.toNat, by omega, ?_⟩
  rw [hn, ← zpow_natCast (v π) n.toNat]
  exact congrArg _ (by omega)

/-- **The uniformizer has the largest valuation below one.** -/
theorem val_le_pi (h : IsCyclotomicPlace ℓ g v π δ) {x : K} (hx : v x < 1) : v x ≤ v π := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Valuation.map_zero]
    exact zero_le'
  obtain ⟨n, hn1, hn⟩ := h.exists_pow hx0 hx
  rw [hn]
  calc v π ^ n ≤ v π ^ 1 := pow_le_pow_right_of_le_one' h.le_one hn1
    _ = v π := pow_one _

/-- The residue characteristic lies in the place. -/
theorem val_natCast_lt_one (h : IsCyclotomicPlace ℓ g v π δ) : v (ℓ : K) < 1 := by
  rw [h.val_natCast]
  calc v π ^ (ℓ - 1) ≤ v π ^ 1 :=
        pow_le_pow_right_of_le_one' h.le_one (by have := h.prime.two_le; omega)
    _ = v π := pow_one _
    _ < 1 := h.lt_one

/-- **An integer lies in the place exactly when it is divisible by the residue
characteristic.** -/
theorem val_intCast_lt_one_iff (h : IsCyclotomicPlace ℓ g v π δ) (m : ℤ) :
    v (m : K) < 1 ↔ (ℓ : ℤ) ∣ m := by
  constructor
  · intro hm
    by_contra hc
    obtain ⟨a, b, hab⟩ : IsCoprime ((ℓ : ℤ)) m :=
      (Nat.prime_iff_prime_int.mp h.prime).coprime_iff_not_dvd.mpr hc
    have h1 : v (1 : K) < 1 := by
      have hcast : ((1 : ℤ) : K) = (a : K) * (ℓ : K) + (b : K) * (m : K) := by
        rw [← hab]; push_cast; ring
      rw [Int.cast_one] at hcast
      rw [hcast]
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
      · rw [v.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one v a))
          h.val_natCast_lt_one
      · rw [v.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one v b)) hm
    rw [v.map_one] at h1
    exact absurd h1 (lt_irrefl 1)
  · rintro ⟨k, rfl⟩
    push_cast
    rw [v.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_intCast_le_one v k))
      h.val_natCast_lt_one

/-! ### The level of a radicand -/

/-- **The valuation of a radicand is divisible by `ℓ`.**  Applying the valuation to the equation
defining a radicand gives its valuation raised to `g - 1`, an exponent prime to `ℓ`, as an `ℓ`-th
power. -/
theorem dvd_of_isEigenRadicand (h : IsCyclotomicPlace ℓ g v π δ) {w : K}
    (hw : IsEigenRadicand ℓ g δ w) {a : ℤ} (ha : v w = v π ^ a) : (ℓ : ℤ) ∣ a := by
  obtain ⟨y, hy0, he⟩ := hw
  obtain ⟨b, hb⟩ := h.exists_zpow y hy0
  have h1 : v (δ w) = v w := h.map_val w
  rw [he, v.map_mul, v.map_pow, v.map_pow, ha, hb, ← zpow_natCast (v π ^ a) g,
    ← zpow_natCast (v π ^ b) ℓ, ← zpow_mul, ← zpow_mul, ← zpow_add₀ h.ne_zero] at h1
  have h2 : a * g + b * ℓ = a :=
    zpow_right_injective₀ h.pos (ne_of_lt h.lt_one) h1
  have h3 : (ℓ : ℤ) ∣ a * ((g : ℤ) - 1) := ⟨-b, by linarith⟩
  rcases (Nat.prime_iff_prime_int.mp h.prime).dvd_mul.mp h3 with h4 | h4
  · exact h4
  · exact absurd h4 h.not_dvd_sub_one

/-- **A radicand is a unit congruent to one, up to an `ℓ`-th power.**  Its valuation is divisible
by `ℓ`, so a power of the uniformizer makes it a unit; its residue is then an integer prime to `ℓ`,
and Fermat's little theorem makes the `ℓ`-th power of that integer congruent to it. -/
theorem exists_unit_congr_one (h : IsCyclotomicPlace ℓ g v π δ) {w : K} (hw0 : w ≠ 0)
    (hw : IsEigenRadicand ℓ g δ w) :
    ∃ u γ : K, γ ≠ 0 ∧ w = u * γ ^ ℓ ∧ v u = 1 ∧ v (u - 1) < 1 ∧ IsEigenRadicand ℓ g δ u := by
  haveI := h.nontrivial
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := h.exists_zpow w hw0
  obtain ⟨m, rfl⟩ := h.dvd_of_isEigenRadicand hw ha
  -- scale by a power of the uniformizer to reach a unit
  have hπ0 : π ≠ 0 := h.pi_ne_zero
  have hγ₀ : (π ^ (-m : ℤ)) ≠ 0 := zpow_ne_zero _ hπ0
  have hu₀v : v (w * (π ^ (-m : ℤ)) ^ ℓ) = 1 := by
    rw [v.map_mul, v.map_pow, ha, map_zpow₀, ← zpow_natCast ((v π) ^ (-m : ℤ)) ℓ, ← zpow_mul,
      ← zpow_add₀ h.ne_zero]
    rw [show (ℓ : ℤ) * m + -m * ℓ = 0 by ring, zpow_zero]
  -- scale by the `ℓ`-th power of the residue to reach a unit congruent to one
  obtain ⟨c, hc⟩ := h.exists_natCast _ (le_of_eq hu₀v)
  have hcd : ¬ (ℓ : ℤ) ∣ (c : ℤ) := by
    intro hd
    have hcv : v ((c : K)) < 1 := by
      have := (h.val_intCast_lt_one_iff (c : ℤ)).mpr hd
      rwa [Int.cast_natCast] at this
    have : v (w * (π ^ (-m : ℤ)) ^ ℓ) < 1 := by
      have hrw : w * (π ^ (-m : ℤ)) ^ ℓ = (w * (π ^ (-m : ℤ)) ^ ℓ - c) + c := by ring
      rw [hrw]
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt hc hcv)
    rw [hu₀v] at this
    exact absurd this (lt_irrefl 1)
  have hcv : v ((c : K)) = 1 := by
    refine le_antisymm (valuation_natCast_le_one v c) (not_lt.mp fun hlt => hcd ?_)
    exact (h.val_intCast_lt_one_iff (c : ℤ)).mp (by rwa [Int.cast_natCast])
  have hc0 : (c : K) ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hcv]; exact one_ne_zero)
  obtain ⟨q, hq0, hq⟩ : ∃ q : K, q ≠ 0 ∧ q = π ^ (-m : ℤ) * (c : K)⁻¹ :=
    ⟨_, mul_ne_zero hγ₀ (inv_ne_zero hc0), rfl⟩
  have hsplit : w * q ^ ℓ = w * (π ^ (-m : ℤ)) ^ ℓ * ((c : K)⁻¹) ^ ℓ := by
    rw [hq, mul_pow, ← mul_assoc]
  refine ⟨w * q ^ ℓ, q⁻¹, inv_ne_zero hq0, ?_, ?_, ?_, hw.mul_pow hq0⟩
  · rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
  · rw [hsplit, v.map_mul, hu₀v, v.map_pow, map_inv₀, hcv, one_mul, inv_one, one_pow]
  · -- the unit is congruent to one, by Fermat's little theorem
    have hfermat : v ((c : K) ^ ℓ - c) < 1 := by
      refine (h.val_intCast_lt_one_iff ((c : ℤ) ^ ℓ - c)).mpr ?_ |>.trans_le' (le_of_eq ?_)
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.pow_card, sub_self]
      · push_cast
        ring_nf
    have hinv : ((c : K)⁻¹) ^ ℓ * (c : K) ^ ℓ = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
    have hrw : w * q ^ ℓ - 1
        = ((c : K)⁻¹) ^ ℓ * ((w * (π ^ (-m : ℤ)) ^ ℓ - c) - ((c : K) ^ ℓ - c)) := by
      rw [hsplit]
      linear_combination hinv
    rw [hrw, v.map_mul, v.map_pow, map_inv₀, hcv, inv_one, one_pow, one_mul]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hc hfermat)

/-- **The level of a radicand which is a unit congruent to one is one, or at least `ℓ`.**  Below
`ℓ` the congruence satisfied by the level forces a primitive root to be congruent to a power of
itself with exponent prime to its order. -/
theorem level_eq_or_le (h : IsCyclotomicPlace ℓ g v π δ) {u : K} (hu : v u = 1)
    (hu1 : v (u - 1) < 1) (heig : IsEigenRadicand ℓ g δ u) :
    v (u - 1) ≤ v π ^ ℓ ∨ v (u - 1) = v π := by
  haveI := h.nontrivial
  rcases eq_or_ne (u - 1) 0 with h0 | h0
  · left
    rw [h0, Valuation.map_zero]
    exact zero_le'
  obtain ⟨n, hn1, hn⟩ := h.exists_pow h0 hu1
  by_cases hNℓ : ℓ ≤ n
  · left
    rw [hn]
    exact pow_le_pow_right_of_le_one' h.le_one hNℓ
  · right
    obtain ⟨y, hy0, heq⟩ := heig
    have hy : v y = 1 := by
      have h1 : v (δ u) = v u := h.map_val u
      rw [heq, v.map_mul, v.map_pow, v.map_pow, hu, one_pow, one_mul] at h1
      exact eq_one_of_pow_eq_one h.prime.pos.ne' h1
    have hkey := valuation_natCast_pow_sub_self_le (v := v) (π := π) (δ := δ) (u := u) (y := y)
      (n := n) h.prime h.ne_zero h.lt_one (fun x hx => h.val_le_pi hx) h.val_natCast h.map_val
      h.val_sub_lt h.val_map_sub hu hy heq hn1 (by omega) hn
    have hdvd : (ℓ : ℤ) ∣ (g : ℤ) ^ n - g := by
      refine (h.val_intCast_lt_one_iff _).mp ?_
      have hcast : (((g : ℤ) ^ n - g : ℤ) : K) = (g : K) ^ n - (g : K) := by push_cast; ring
      rw [hcast]
      exact lt_of_le_of_lt hkey h.lt_one
    rw [hn, h.eq_one_of_dvd n hn1 (by omega) hdvd, pow_one]

/-- **Two units of level one differ by a power of the first, up to level two.**  Their residues
generate the same line over the residue field, which has `ℓ` elements. -/
theorem exists_pow_div_level (h : IsCyclotomicPlace ℓ g v π δ) {u₁ u₂ : K}
    (hu₁ : v u₁ = 1) (h₁ : v (u₁ - 1) = v π) (h₂ : v (u₂ - 1) = v π) :
    ∃ j : ℕ, v (u₂ / u₁ ^ j - 1) ≤ v π ^ 2 := by
  haveI := h.nontrivial
  have hu₁0 : u₁ ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hu₁]; exact one_ne_zero)
  have hd0 : u₁ - 1 ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [h₁]; exact h.ne_zero)
  have hdle : v (u₁ - 1) ≤ 1 := by rw [h₁]; exact h.le_one
  have htv : v ((u₂ - 1) / (u₁ - 1)) = 1 := by
    rw [map_div₀, h₁, h₂]
    exact div_self h.ne_zero
  obtain ⟨j, hj⟩ := h.exists_natCast _ (le_of_eq htv)
  refine ⟨j, ?_⟩
  obtain ⟨B, hB, hEq⟩ := exists_valuation_one_add_pow v hdle j
  rw [show (1 : K) + (u₁ - 1) = u₁ by ring] at hEq
  have hnum : u₂ - u₁ ^ j
      = (u₁ - 1) * ((u₂ - 1) / (u₁ - 1) - j) - (u₁ - 1) ^ 2 * B := by
    rw [hEq]
    field_simp
    ring
  have hbound : v (u₂ - u₁ ^ j) ≤ v π ^ 2 := by
    rw [hnum]
    refine v.map_sub_le ?_ ?_
    · rw [v.map_mul, h₁, pow_two]
      exact mul_le_mul' le_rfl (h.val_le_pi hj)
    · rw [v.map_mul, v.map_pow, h₁]
      exact mul_le_of_le_one_right' hB
  have hrw : u₂ / u₁ ^ j - 1 = (u₂ - u₁ ^ j) / u₁ ^ j := by field_simp
  rw [hrw, map_div₀, v.map_pow, hu₁, one_pow, div_one]
  exact hbound

/-- **Two radicands are dependent modulo the radicands congruent to one.**  Either the first is
itself congruent to one, or every other radicand is congruent to one after division by a power of
it: the radicands form a cyclic group of order at most `ℓ` modulo those congruent to one. -/
theorem isCongrPow_or_exists_div (h : IsCyclotomicPlace ℓ g v π δ) {w₁ w₂ : K}
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hw₁ : IsEigenRadicand ℓ g δ w₁)
    (hw₂ : IsEigenRadicand ℓ g δ w₂) :
    IsCongrPow ℓ v π w₁ ∨ ∃ j : ℕ, IsCongrPow ℓ v π (w₂ / w₁ ^ j) := by
  haveI := h.nontrivial
  obtain ⟨u₁, γ₁, hγ₁, hwe₁, hu₁v, hu₁1, hu₁e⟩ := h.exists_unit_congr_one hw₁0 hw₁
  obtain ⟨u₂, γ₂, hγ₂, hwe₂, hu₂v, hu₂1, hu₂e⟩ := h.exists_unit_congr_one hw₂0 hw₂
  rcases h.level_eq_or_le hu₁v hu₁1 hu₁e with hl₁ | hl₁
  · exact Or.inl ⟨u₁, γ₁, hγ₁, hu₁v, hl₁, hwe₁⟩
  rcases h.level_eq_or_le hu₂v hu₂1 hu₂e with hl₂ | hl₂
  · exact Or.inr ⟨0, u₂, γ₂, hγ₂, hu₂v, hl₂, by rw [pow_zero, div_one]; exact hwe₂⟩
  -- both have level one: divide by a power of the first
  obtain ⟨j, hj⟩ := h.exists_pow_div_level hu₁v hl₁ hl₂
  have hu₁0 : u₁ ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hu₁v]; exact one_ne_zero)
  have hu₃v : v (u₂ / u₁ ^ j) = 1 := by
    rw [map_div₀, v.map_pow, hu₁v, hu₂v, one_pow, div_one]
  have hππ : v π ^ 2 ≤ v π := by
    rw [pow_two]
    exact mul_le_of_le_one_right' h.le_one
  have hu₃1 : v (u₂ / u₁ ^ j - 1) < 1 := lt_of_le_of_lt (le_trans hj hππ) h.lt_one
  have hu₃e : IsEigenRadicand ℓ g δ (u₂ / u₁ ^ j) := hu₂e.div (hu₁e.pow j)
  refine Or.inr ⟨j, u₂ / u₁ ^ j, γ₂ / γ₁ ^ j, div_ne_zero hγ₂ (pow_ne_zero j hγ₁), hu₃v, ?_, ?_⟩
  · rcases h.level_eq_or_le hu₃v hu₃1 hu₃e with hl₃ | hl₃
    · exact hl₃
    · exact absurd (le_of_mul_le_mul_right₀ h.ne_zero
        (by rw [one_mul, ← pow_two]; exact hl₃ ▸ hj)) (not_le.mpr h.lt_one)
  · rw [hwe₁, hwe₂, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j ℓ]
    field_simp

end IsCyclotomicPlace

end Place

end InverseGalois.CFT
