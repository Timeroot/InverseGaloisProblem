/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitRootPower

/-!
# Roots of unity over a prime residue field

Over a prime residue field the units of a complete valued field are governed by the multiplicative
group of the prime field, which is cyclic of order `p - 1`.  A root of unity of order `n` reduces
to an element of that cyclic group killed by `n`, and as soon as `n * d` divides `p - 1` such an
element is a `d`-th power there.  Lifting a rational integer representing the root back to the
field turns the congruence into an equation, because a unit congruent to a `d`-th power is a `d`-th
power when `d` is prime to the residue characteristic.

The resulting root is again a root of unity of order prime to the residue characteristic, so every
valuation preserving automorphism fixes it.  This is the local input the Albert-Brauer-Hasse-Noether
theorem needs at a ramified place: a root of unity of the base field becomes, in the completion, a
power with exponent the order of the decomposition group of an element that group fixes.

## Main results

* `InverseGalois.CFT.exists_pow_eq_of_pow_eq_one_of_isCyclic`: in a finite cyclic group an element
  killed by `n` is a `d`-th power whenever `n * d` divides the order.
* `InverseGalois.CFT.valued_intCast_eq_one_iff_not_dvd`: an integer is a unit exactly when the
  residue characteristic does not divide it.
* `InverseGalois.CFT.exists_unit_pow_valued_sub_lt_one`: **over a prime residue field a root of
  unity of order `n` is congruent to a `d`-th power when `n * d` divides `p - 1`.**
* `InverseGalois.CFT.exists_pow_eq_and_map_eq_self_of_mul_dvd`: **over a prime residue field a root
  of unity of order `n` is the `d`-th power of a unit fixed by every valuation preserving
  automorphism, when `n * d` divides `p - 1`.**

## Tags

valued field, prime residue field, root of unity, cyclic group, decomposition group
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### Powers in a finite cyclic group -/

/-- **In a finite cyclic group an element killed by `n` is a `d`-th power whenever `n * d` divides
the order.**  Writing the element as a power of a generator, the exponent is divisible by the order
divided by `n`, hence by `d`. -/
theorem exists_pow_eq_of_pow_eq_one_of_isCyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {n d : ℕ} (hnd : n * d ∣ Nat.card G) {x : G} (hx : x ^ n = 1) : ∃ y : G, y ^ d = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨m, hm⟩ := hnd
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hn : n ≠ 0 := by
    rintro rfl
    omega
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : ((Nat.card G : ℕ) : ℤ) ∣ j * n := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_natCast, hx]
  have hdvd' : ((d : ℤ) * m) * n ∣ j * n := by
    refine dvd_trans ?_ hdvd
    rw [hm]
    push_cast
    exact ⟨1, by ring⟩
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hdj : (d : ℤ) ∣ j := dvd_trans ⟨(m : ℤ), rfl⟩ (mul_dvd_mul_iff_right hn' |>.mp hdvd')
  obtain ⟨i, hi⟩ := hdj
  exact ⟨g ^ i, by rw [← zpow_natCast (g ^ i) d, ← zpow_mul, mul_comm, ← hi]⟩

/-! ### Integers over a prime residue field -/

section Valued

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {p e : ℕ}

/-- The residue characteristic has valuation less than one. -/
theorem valued_residueChar_lt_one (h : HasResidueChar A p e) : Valued.v ((p : ℕ) : A) < 1 := by
  rw [h.val_p, ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by have := h.pos; omega)

/-- **An integer is a unit exactly when the residue characteristic does not divide it.** -/
theorem valued_intCast_eq_one_iff_not_dvd (h : HasResidueChar A p e) {m : ℤ} :
    Valued.v ((m : ℤ) : A) = 1 ↔ ¬ (p : ℤ) ∣ m := by
  constructor
  · rintro hv ⟨t, rfl⟩
    rw [Int.cast_mul, Int.cast_natCast, map_mul] at hv
    have hle : Valued.v ((p : ℕ) : A) * Valued.v ((t : ℤ) : A) < 1 :=
      calc Valued.v ((p : ℕ) : A) * Valued.v ((t : ℤ) : A)
          ≤ Valued.v ((p : ℕ) : A) * 1 := mul_le_mul' le_rfl (valued_intCast_le_one t)
        _ = Valued.v ((p : ℕ) : A) := mul_one _
        _ < 1 := valued_residueChar_lt_one h
    exact absurd hv (ne_of_lt hle)
  · intro hm
    have hnat : ¬ p ∣ m.natAbs := fun hd => hm (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd))
    have hval : Valued.v ((m.natAbs : ℕ) : A) = 1 :=
      valued_natCast_eq_one_of_not_dvd h.prime (valued_residueChar_lt_one h) hnat
    rcases Int.natAbs_eq m with hme | hme
    · rw [hme]
      simpa using hval
    · rw [hme]
      simpa using hval

/-- A power of a difference of small valuation is small. -/
theorem valued_sub_pow_lt_one {x y : A} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hxy : Valued.v (x - y) < 1) (n : ℕ) : Valued.v (x ^ n - y ^ n) < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + y * (x ^ n - y ^ n) := by ring
    rw [hsplit]
    refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow]
      calc Valued.v x ^ n * Valued.v (x - y) ≤ 1 * Valued.v (x - y) :=
            mul_le_mul' (pow_le_one' hx n) le_rfl
        _ = Valued.v (x - y) := one_mul _
        _ < 1 := hxy
    · rw [map_mul]
      calc Valued.v y * Valued.v (x ^ n - y ^ n) ≤ 1 * Valued.v (x ^ n - y ^ n) :=
            mul_le_mul' hy le_rfl
        _ = Valued.v (x ^ n - y ^ n) := one_mul _
        _ < 1 := ih

/-! ### Roots of unity are congruent to powers -/

/-- **Over a prime residue field a root of unity of order `n` is congruent to a `d`-th power when
`n * d` divides `p - 1`.**  The root of unity is congruent to a rational integer, whose residue is
an element of the multiplicative group of the prime field killed by `n`; that group being cyclic of
order `p - 1`, such an element is a `d`-th power there. -/
theorem exists_unit_pow_valued_sub_lt_one (h : HasResidueChar A p e)
    (hres : ∀ x : A, Valued.v x ≤ 1 → ∃ b : ℤ, Valued.v (x - (b : A)) < 1) {n d : ℕ}
    (hnd : n * d ∣ p - 1) {ζ : Aˣ} (hζ : ζ ^ n = 1) :
    ∃ b : Aˣ, Valued.v ((ζ : A) - (b : A) ^ d) < 1 := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hp2 := h.prime.two_le
  have hpos : 0 < p - 1 := by omega
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd (by simpa using hnd)) (by omega)
  have hζval : Valued.v (ζ : A) = 1 := valued_eq_one_of_pow_eq_one hn hζ
  obtain ⟨b, hb⟩ := hres (ζ : A) hζval.le
  -- the integer is prime to the residue characteristic
  have hbunit : Valued.v ((b : ℤ) : A) = 1 := by
    by_contra hne
    have hlt : Valued.v ((b : ℤ) : A) < 1 := lt_of_le_of_ne (valued_intCast_le_one b) hne
    have hζlt : Valued.v (ζ : A) < 1 := by
      have hsum : (ζ : A) = ((ζ : A) - ((b : ℤ) : A)) + ((b : ℤ) : A) := by ring
      rw [hsum]
      exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hb hlt)
    rw [hζval] at hζlt
    exact absurd hζlt (lt_irrefl 1)
  have hpb : ¬ (p : ℤ) ∣ b := (valued_intCast_eq_one_iff_not_dvd h).mp hbunit
  -- its residue is killed by `n`
  have hpow : Valued.v (((b ^ n - 1 : ℤ) : A)) < 1 := by
    have hstep : Valued.v ((ζ : A) ^ n - ((b : ℤ) : A) ^ n) < 1 :=
      valued_sub_pow_lt_one hζval.le hbunit.le hb n
    have hone : (ζ : A) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    rw [hone] at hstep
    have hrw : ((b ^ n - 1 : ℤ) : A) = -(1 - ((b : ℤ) : A) ^ n) := by push_cast; ring
    rw [hrw, Valuation.map_neg]
    exact hstep
  have hdvdb : (p : ℤ) ∣ b ^ n - 1 := by
    by_contra hnd'
    rw [(valued_intCast_eq_one_iff_not_dvd h).mpr hnd'] at hpow
    exact absurd hpow (lt_irrefl 1)
  -- pass to the multiplicative group of the prime field
  have hbz : ((b : ℤ) : ZMod p) ≠ 0 := fun hz =>
    hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hz)
  set x : (ZMod p)ˣ := Units.mk0 ((b : ℤ) : ZMod p) hbz with hxdef
  have hxn : x ^ n = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hxdef, Units.val_mk0, Units.val_one, ← Int.cast_pow,
      ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvdb
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  obtain ⟨y, hy⟩ := exists_pow_eq_of_pow_eq_one_of_isCyclic (hcard ▸ hnd) hxn
  -- lift the root back to the field
  set c : ℤ := ((y : ZMod p).val : ℤ) with hcdef
  have hcz : ((c : ℤ) : ZMod p) = (y : ZMod p) := by
    rw [hcdef, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  have hcb : (p : ℤ) ∣ c ^ d - b := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    rw [Int.cast_sub, Int.cast_pow, hcz, sub_eq_zero]
    exact congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hy
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro hd
    have hz : ((c : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    rw [hcz] at hz
    exact (y : (ZMod p)ˣ).ne_zero hz
  have hcunit : Valued.v ((c : ℤ) : A) = 1 := (valued_intCast_eq_one_iff_not_dvd h).mpr hpc
  refine ⟨Units.mk0 ((c : ℤ) : A) (by
    intro hz
    rw [hz, map_zero] at hcunit
    exact zero_ne_one hcunit), ?_⟩
  have hsplit : (ζ : A) - (((c : ℤ) : A)) ^ d
      = ((ζ : A) - ((b : ℤ) : A)) + -(((c ^ d - b : ℤ) : A)) := by push_cast; ring
  rw [Units.val_mk0, hsplit]
  refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hb ?_)
  rw [Valuation.map_neg]
  by_contra hcon
  have heq : Valued.v (((c ^ d - b : ℤ) : A)) = 1 :=
    le_antisymm (valued_intCast_le_one _) (not_lt.mp hcon)
  exact (valued_intCast_eq_one_iff_not_dvd h).mp heq hcb

/-! ### Roots of unity are powers -/

/-- **Over a prime residue field a root of unity of order `n` is the `d`-th power of a unit fixed
by every valuation preserving automorphism, when `n * d` divides `p - 1`.**  The root of unity is
congruent to a `d`-th power, hence is one, and its `d`-th root is itself a root of unity of order
prime to the residue characteristic. -/
theorem exists_pow_eq_and_map_eq_self_of_mul_dvd [CompleteSpace A] (h : HasResidueChar A p e)
    (hres : ∀ x : A, Valued.v x ≤ 1 → ∃ b : ℤ, Valued.v (x - (b : A)) < 1) {n d : ℕ}
    (hnd : n * d ∣ p - 1) {ζ : Aˣ} (hζ : ζ ^ n = 1) :
    ∃ y : Aˣ, y ^ d = ζ ∧ ∀ σ : A ≃+* A, (∀ x : A, Valued.v (σ x) = Valued.v x) →
      σ (y : A) = (y : A) := by
  have hp2 := h.prime.two_le
  have hpos : 0 < p - 1 := by omega
  have hnd0 : n * d ≠ 0 := by
    rintro hz
    rw [hz] at hnd
    exact absurd (Nat.eq_zero_of_zero_dvd hnd) (by omega)
  have hn : n ≠ 0 := by
    intro hz
    exact hnd0 (by rw [hz, zero_mul])
  have hd : d ≠ 0 := by
    intro hz
    exact hnd0 (by rw [hz, mul_zero])
  have hpn : ¬ p ∣ n := fun hdv => by
    have : p ∣ p - 1 := hdv.trans ((Dvd.intro d rfl).trans hnd)
    have := Nat.le_of_dvd hpos this
    omega
  have hpd : ¬ p ∣ d := fun hdv => by
    have : p ∣ p - 1 := hdv.trans ((Dvd.intro_left n rfl).trans hnd)
    have := Nat.le_of_dvd hpos this
    omega
  obtain ⟨b, hb⟩ := exists_unit_pow_valued_sub_lt_one h hres hnd hζ
  exact exists_pow_eq_and_map_eq_self h hres hd hpd hpn hζ hb

end Valued

end InverseGalois.CFT
