/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicandLevel
import InverseGalois.CFT.Kummer.CongruentRadical
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.PrimeResidueField
import InverseGalois.CFT.Units.Places

/-!
# Constructing the local data at a cyclotomic place

The abstract local data `InverseGalois.CFT.IsCyclotomicPlace` asks for a valued field carrying a
uniformizer whose `ℓ - 1`-st power is `ℓ`, a residue field which is the prime field, an
automorphism `δ` in the inertia subgroup which multiplies the uniformizer by a primitive root `g`
modulo `ℓ`, and a Frobenius automorphism.  This file assembles that data from a number field `K`
containing a primitive `ℓ`-th root of unity `ζ` together with a place `v` above `ℓ` at which

* the residue degree is one, so that the residue field is the prime field, and
* `ζ - 1` is a uniformizer, which is the same as saying that the ramification index is `ℓ - 1`,
  the largest it can be.

The residue field being the prime field makes the identity a Frobenius, so the Frobenius half of
the data is discharged by `RingHom.id`.  The rest is elementary: the product of the differences
`ζ ^ k - 1` for `k` running over the nonzero residues is `ℓ` up to sign, and all those differences
are associated, whence the valuation of `ℓ`; the binomial expansion of `(1 + π) ^ g` gives the
action of `δ` on the uniformizer; and Fermat's little theorem says that raising to the `ℓ`-th
power fixes the residues of the prime field.

## Main results

* `InverseGalois.CFT.exists_primitiveRoot_natCast`: **a primitive root modulo an odd prime**, in
  the two arithmetic forms the local data asks for.
* `InverseGalois.CFT.valuation_natCast_eq_pow`: **the valuation of `ℓ` is the `ℓ - 1`-st power of
  the valuation of `ζ - 1`.**
* `InverseGalois.CFT.exists_natCast_sub_lt_one`: **at a place of residue degree one every integral
  element is congruent to a natural number.**
* `InverseGalois.CFT.valuation_sub_one_eq_exp_neg_one`: **`ζ - 1` is a uniformizer** as soon as the
  ramification index over `ℓ` is at most `ℓ - 1`.
* `InverseGalois.CFT.valuation_map_eq_of_smul_eq`: an automorphism fixing a place preserves its
  valuation.
* `InverseGalois.CFT.isCyclotomicPlace_of_ringHom`: **the local data at such a place.**

## Tags

number field, cyclotomic field, uniformizer, residue degree, primitive root, Frobenius
-/

namespace InverseGalois.CFT

open scoped WithZero

open IsDedekindDomain NumberField

/-! ### A primitive root modulo an odd prime -/

/-- **A primitive root modulo an odd prime**, packaged in the two forms the local data at a
cyclotomic place asks for: it is not congruent to one, and the only power below `ℓ` at which it
reproduces itself is the first. -/
theorem exists_primitiveRoot_natCast {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ∃ g : ℕ, (∀ n : ℕ, 1 ≤ n → n + 1 ≤ ℓ → ((ℓ : ℤ) ∣ (g : ℤ) ^ n - g) → n = 1) ∧
      ¬ ((ℓ : ℤ) ∣ (g : ℤ) - 1) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hl2 : 2 ≤ ℓ := hℓ.two_le
  obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hℓ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hu
  obtain ⟨g, hg⟩ : ∃ g : ℕ, (g : ZMod ℓ) = (u : ZMod ℓ) :=
    ⟨(u : ZMod ℓ).val, ZMod.natCast_rightInverse _⟩
  refine ⟨g, ?_, ?_⟩
  · intro n hn1 hnl hdvd
    -- the divisibility says that `u ^ n = u`
    have h0 : ((u : ZMod ℓ)) ^ n = (u : ZMod ℓ) := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((g : ℤ) ^ n - g) ℓ).mpr hdvd
      push_cast at h
      rw [hg] at h
      exact sub_eq_zero.mp h
    have hun : u ^ n = u := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h0)
    -- so the order of `u`, which is `ℓ - 1`, divides `n - 1`
    have hpow1 : u ^ (n - 1) = 1 := by
      have hsucc : u ^ (n - 1) * u = u ^ n := by
        rw [← pow_succ]
        congr 1
        omega
      exact mul_right_cancel (by rw [hsucc, hun, one_mul])
    have hdv : ℓ - 1 ∣ n - 1 := hu ▸ orderOf_dvd_of_pow_eq_one hpow1
    rcases Nat.eq_zero_or_pos (n - 1) with h | h
    · omega
    · have := Nat.le_of_dvd h hdv
      omega
  · intro hdvd
    have h0 : (u : ZMod ℓ) = 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((g : ℤ) - 1) ℓ).mpr hdvd
      push_cast at h
      rw [hg] at h
      exact sub_eq_zero.mp h
    have h1 : u = 1 := Units.ext (by rw [h0, Units.val_one])
    rw [h1, orderOf_one] at hu
    omega

/-- **A primitive root modulo an odd prime is invertible modulo that prime.**  A residue divisible
by `ℓ` reproduces itself already at the square, which the defining property forbids. -/
theorem exists_primitiveRoot_natCast_isUnit {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ∃ g : ℕ, IsUnit ((g : ZMod ℓ)) ∧
      (∀ n : ℕ, 1 ≤ n → n + 1 ≤ ℓ → ((ℓ : ℤ) ∣ (g : ℤ) ^ n - g) → n = 1) ∧
      ¬ ((ℓ : ℤ) ∣ (g : ℤ) - 1) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg, hg1⟩ := exists_primitiveRoot_natCast hℓ hℓ2
  refine ⟨g, ?_, hg, hg1⟩
  have hl3 : 3 ≤ ℓ := by
    rcases hℓ.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · have := hℓ.two_le
      rcases h with ⟨m, hm⟩
      omega
  rw [isUnit_iff_ne_zero]
  intro h0
  have hdvd : (ℓ : ℤ) ∣ (g : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h0
  exact absurd (hg 2 (by omega) (by omega) (dvd_sub (dvd_pow hdvd two_ne_zero) hdvd))
    (by norm_num)

/-! ### The valuation of the residue characteristic -/

variable {K : Type*} [Field K] [NumberField K] {ℓ : ℕ}

/-- **The valuation of `ℓ` is the `ℓ - 1`-st power of the valuation of `ζ - 1`.**  The product of
the differences `ζ ^ k - 1`, for `k` running over the nonzero residues modulo `ℓ`, is `ℓ` up to
sign, and all those differences are associated as algebraic integers. -/
theorem valuation_natCast_eq_pow (hℓ : ℓ.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (ℓ : K) = v.valuation K (ζ - 1) ^ (ℓ - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by have := hℓ.two_le; omega⟩
  have hprod := hζ.prod_pow_sub_one_eq_order
  have hsign : v.valuation K ((-1 : K) ^ n) = 1 := by
    rw [map_pow, Valuation.map_neg, map_one, one_pow]
  have hfac : ∀ k ∈ Finset.range n,
      v.valuation K (ζ ^ (k + 1) - 1) = v.valuation K (ζ - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact valuation_pow_sub_one_eq hℓ hζ v (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hval : v.valuation K ((n : K) + 1)
      = ∏ k ∈ Finset.range n, v.valuation K (ζ ^ (k + 1) - 1) := by
    rw [← hprod, map_mul, map_prod, hsign, one_mul]
  rw [show ((n + 1 : ℕ) : K) = (n : K) + 1 by push_cast; ring, hval,
    Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_range]
  congr 1

/-! ### Residues at a place of degree one -/

/-- **At a place of residue degree one every integral element is congruent to a rational
integer.**  An integral element of the number field is congruent to an element of the ring of
integers modulo the place, and residue degree one makes that element congruent to a rational
integer. -/
theorem exists_intCast_sub_lt_one (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (hf : (Ideal.span {(ℓ : ℤ)}).inertiaDeg v.asIdeal = 1) {x : K}
    (hx : v.valuation K x ≤ 1) : ∃ b : ℤ, v.valuation K (x - (b : K)) < 1 := by
  obtain ⟨b, hb⟩ := exists_valuation_sub_algebraMap_le v hx
  obtain ⟨c, hc⟩ := surjective_intCast_quotient_of_inertiaDeg_eq_one hℓ v.asIdeal hf
    (Ideal.Quotient.mk _ b)
  refine ⟨c, ?_⟩
  have hmem : b - (c : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
      map_intCast (Ideal.Quotient.mk v.asIdeal) c]
    exact hc.symm
  have hlt : v.valuation K (algebraMap (𝓞 K) K (b - (c : 𝓞 K))) < 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem _).mpr hmem
  have hsplit : x - (c : K)
      = (x - algebraMap (𝓞 K) K b) + algebraMap (𝓞 K) K (b - (c : 𝓞 K)) := by
    rw [map_sub, map_intCast]
    ring
  have hexp : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    simpa using WithZero.exp_lt_exp.mpr (by omega : (-1 : ℤ) < 0)
  rw [hsplit]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt hb hexp) hlt)

/-- **At a place of residue degree one every integral element is congruent to a natural number.**
Reducing the rational integer of the previous result modulo `ℓ`, which lies in the place, replaces
it by a natural number. -/
theorem exists_natCast_sub_lt_one (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (hf : (Ideal.span {(ℓ : ℤ)}).inertiaDeg v.asIdeal = 1)
    (hlv : v.valuation K (ℓ : K) < 1) {x : K} (hx : v.valuation K x ≤ 1) :
    ∃ m : ℕ, v.valuation K (x - (m : K)) < 1 := by
  obtain ⟨b, hb⟩ := exists_intCast_sub_lt_one hℓ v hf hx
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  refine ⟨(b % (ℓ : ℤ)).toNat, ?_⟩
  have hm : (((b % (ℓ : ℤ)).toNat : ℕ) : ℤ) = b % (ℓ : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg b hℓ0)
  have hmK : (((b % (ℓ : ℤ)).toNat : ℕ) : K) = ((b % (ℓ : ℤ) : ℤ) : K) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) hm
  have hbK : (b : K) = (ℓ : K) * ((b / (ℓ : ℤ) : ℤ) : K) + ((b % (ℓ : ℤ) : ℤ) : K) := by
    have h := congrArg (fun z : ℤ => (z : K)) (Int.mul_ediv_add_emod b (ℓ : ℤ))
    push_cast at h
    linear_combination -h
  have hsplit : x - (((b % (ℓ : ℤ)).toNat : ℕ) : K)
      = (x - (b : K)) + (ℓ : K) * ((b / (ℓ : ℤ) : ℤ) : K) := by
    rw [hmK, hbK]
    ring
  rw [hsplit]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hb ?_)
  rw [Valuation.map_mul]
  calc v.valuation K (ℓ : K) * v.valuation K ((b / (ℓ : ℤ) : ℤ) : K)
      ≤ v.valuation K (ℓ : K) * 1 :=
        mul_le_mul_right (valuation_intCast_le_one (v.valuation K) _) _
    _ = v.valuation K (ℓ : K) := mul_one _
    _ < 1 := hlv

/-! ### `ζ - 1` as a uniformizer -/

/-- **The difference `ζ - 1` is a uniformizer at a place above `ℓ` of ramification index at most
`ℓ - 1`.**  Its valuation is the `ℓ - 1`-st root of the valuation of `ℓ`, so the bound on the
ramification index forces it to be exactly one step below one. -/
theorem valuation_sub_one_eq_exp_neg_one (hℓ : ℓ.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (v : HeightOneSpectrum (𝓞 K)) (hlt : v.valuation K (ζ - 1) < 1)
    (hle : (WithZero.exp (-((ℓ : ℤ) - 1)) : ℤᵐ⁰) ≤ v.valuation K (ℓ : K)) :
    v.valuation K (ζ - 1) = WithZero.exp (-1 : ℤ) := by
  have hl2 : 2 ≤ ℓ := hℓ.two_le
  have hζ0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hℓ.one_lt)
  set a : ℤ := Rigidity.RET.ord K v (ζ - 1) with hadef
  have hva : v.valuation K (ζ - 1) = WithZero.exp (-a) :=
    Rigidity.RET.valuation_eq_exp_neg_ord K v hζ0
  -- the valuation being less than one means that `a` is positive
  have hapos : 0 < a := by
    rw [hva, ← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp] at hlt
    omega
  -- the valuation of `ℓ` is the `ℓ - 1`-st power of that of `ζ - 1`
  have hvl : v.valuation K (ℓ : K) = WithZero.exp (-(a * ((ℓ : ℤ) - 1))) := by
    rw [valuation_natCast_eq_pow hℓ hζ v, hva, ← WithZero.exp_nsmul]
    congr 1
    have : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by omega
    rw [nsmul_eq_mul, ← this]
    ring
  rw [hvl, WithZero.exp_le_exp] at hle
  have hone : a = 1 := by nlinarith [hle, hapos, (by omega : (1 : ℤ) ≤ (ℓ : ℤ) - 1)]
  rw [hva, hone]

/-! ### Automorphisms fixing a place -/

variable {k : Type*} [Field k] [Algebra k K]

/-- **An automorphism fixing a place preserves its valuation.** -/
theorem valuation_map_eq_of_smul_eq {v : HeightOneSpectrum (𝓞 K)} {σ : Gal(K/k)}
    (hσ : σ • v = v) (x : K) : v.valuation K (σ x) = v.valuation K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hσx : σ x ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hx
    rw [Rigidity.RET.valuation_eq_exp_neg_ord K v hσx,
      Rigidity.RET.valuation_eq_exp_neg_ord K v hx]
    congr 2
    have h := ord_galSmul σ v x
    rwa [hσ] at h

/-! ### The local data -/

/-- **The local data at a place above `ℓ` of residue degree one at which `ζ - 1` is a
uniformizer.**  The identity is a Frobenius because the residue field is the prime field, the
valuation of `ℓ` is computed from the product of the differences of the `ℓ`-th roots of unity, and
the action of `δ` on the uniformizer is read off the binomial expansion of `ζ ^ g = (1 + π) ^ g`.
-/
theorem isCyclotomicPlace_of_ringHom {g : ℕ} (hℓ : ℓ.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (v : HeightOneSpectrum (𝓞 K)) [v.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (hf : (Ideal.span {(ℓ : ℤ)}).inertiaDeg v.asIdeal = 1)
    (hunif : v.valuation K (ζ - 1) = WithZero.exp (-1 : ℤ)) (δ : K →+* K)
    (hδv : ∀ x : K, v.valuation K (δ x) = v.valuation K x) (hδζ : δ ζ = ζ ^ g)
    (hg : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ ℓ → ((ℓ : ℤ) ∣ (g : ℤ) ^ n - g) → n = 1)
    (hg1 : ¬ ((ℓ : ℤ) ∣ (g : ℤ) - 1)) :
    IsCyclotomicPlace ℓ g (v.valuation K) (ζ - 1) δ (RingHom.id K) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hl2 : 2 ≤ ℓ := hℓ.two_le
  have hexp1 : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    simpa using WithZero.exp_lt_exp.mpr (by omega : (-1 : ℤ) < 0)
  have hπ1 : v.valuation K (ζ - 1) < 1 := by rw [hunif]; exact hexp1
  have hπle : v.valuation K (ζ - 1) ≤ 1 := hπ1.le
  have hvℓ : v.valuation K (ℓ : K) = v.valuation K (ζ - 1) ^ (ℓ - 1) :=
    valuation_natCast_eq_pow hℓ hζ v
  have hlv : v.valuation K (ℓ : K) < 1 := by
    rw [hvℓ]
    exact pow_lt_one₀ zero_le' hπ1 (by omega)
  have hres : ∀ x : K, v.valuation K x ≤ 1 → ∃ m : ℕ, v.valuation K (x - (m : K)) < 1 :=
    fun x hx => exists_natCast_sub_lt_one hℓ v hf hlv hx
  refine
    { prime := hℓ
      ne_zero := by rw [hunif]; exact WithZero.exp_ne_zero
      lt_one := hπ1
      exists_zpow := ?_
      val_natCast := hvℓ
      exists_natCast := fun x hx _ => hres x hx
      map_val := hδv
      val_sub_lt := ?_
      val_map_sub := ?_
      eq_one_of_dvd := hg
      not_dvd_sub_one := hg1
      map_val_frob := fun x => rfl
      frob_res := ?_
      frob_pi := rfl }
  · -- every valuation is a power of that of the uniformizer
    intro x hx
    refine ⟨Rigidity.RET.ord K v x, ?_⟩
    rw [hunif, ← WithZero.exp_zsmul, Rigidity.RET.valuation_eq_exp_neg_ord K v hx]
    congr 1
    simp
  · -- the automorphism acts trivially on the residues
    intro x hx
    obtain ⟨m, hm⟩ := hres x hx
    have hsplit : δ x - x = δ (x - (m : K)) - (x - (m : K)) := by
      rw [map_sub, map_natCast]
      ring
    rw [hsplit]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hm)
    rw [hδv]
    exact hm
  · -- the automorphism multiplies the uniformizer by `g`
    obtain ⟨B, hB, hBeq⟩ := exists_valuation_one_add_pow (v.valuation K) hπle g
    have hδπ : δ (ζ - 1) = ζ ^ g - 1 := by rw [map_sub, map_one, hδζ]
    have hζeq : (1 : K) + (ζ - 1) = ζ := by ring
    rw [hζeq] at hBeq
    have hkey : δ (ζ - 1) - (g : K) * (ζ - 1) = (ζ - 1) ^ 2 * B := by
      rw [hδπ]
      linear_combination hBeq
    rw [hkey, Valuation.map_mul, map_pow]
    exact mul_le_of_le_one_right' hB
  · -- the identity is a Frobenius
    intro x hx
    show v.valuation K (x - x ^ ℓ) < 1
    obtain ⟨m, hm⟩ := hres x hx
    have hmle : v.valuation K ((m : ℕ) : K) ≤ 1 := valuation_natCast_le_one (v.valuation K) m
    obtain ⟨c, hc⟩ : ((ℓ : ℤ) ∣ ((m : ℤ) ^ ℓ - (m : ℤ))) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.pow_card]
      ring
    have hfermat : ((m : ℕ) : K) ^ ℓ - ((m : ℕ) : K) = (ℓ : K) * ((c : ℤ) : K) := by
      have h := congrArg (fun z : ℤ => (z : K)) hc
      push_cast at h
      linear_combination h
    have h1 : v.valuation K (((m : ℕ) : K) ^ ℓ - ((m : ℕ) : K)) < 1 := by
      rw [hfermat, Valuation.map_mul]
      calc v.valuation K (ℓ : K) * v.valuation K ((c : ℤ) : K)
          ≤ v.valuation K (ℓ : K) * 1 :=
            mul_le_mul_right (valuation_intCast_le_one (v.valuation K) _) _
        _ = v.valuation K (ℓ : K) := mul_one _
        _ < 1 := hlv
    have h2 : v.valuation K (x ^ ℓ - ((m : ℕ) : K) ^ ℓ) < 1 := by
      refine lt_of_le_of_lt (valuation_pow_sub_pow_le (v.valuation K) hx hmle ℓ) ?_
      rw [one_pow, mul_one]
      exact hm
    have hsplit : x - x ^ ℓ
        = (x - ((m : ℕ) : K)) - (((m : ℕ) : K) ^ ℓ - ((m : ℕ) : K)) - (x ^ ℓ - ((m : ℕ) : K) ^ ℓ) :=
      by ring
    rw [hsplit]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ h2)
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)

end InverseGalois.CFT
