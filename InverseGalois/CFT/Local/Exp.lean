/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.NatValuation
import InverseGalois.CFT.Local.ValuedTopology

/-!
# The exponential of a complete valued field of residue characteristic `p`

Let `A` be a complete field with a discrete valuation whose value on the prime `p` is `exp (-e)`.
Legendre's bound on the valuation of a factorial says that the denominators of the exponential
series grow more slowly than the numerators as soon as the argument has valuation at most
`exp (-j)` with `e < j (p - 1)`; on that range the series converges, and the resulting map is a
homomorphism from the additive group to the multiplicative group which changes no valuation.

## Main definitions

* `InverseGalois.CFT.HasResidueChar`: the hypothesis that `p` is prime with valuation `exp (-e)`.
* `InverseGalois.CFT.expTerm`: the terms `x ^ k / k !` of the exponential series.
* `InverseGalois.CFT.padicExp`: the sum of the exponential series.

## Main results

* `InverseGalois.CFT.hasSum_expTerm`: **the exponential series converges** on the elements of
  valuation at most `exp (-j)`, provided `e < j (p - 1)`.
* `InverseGalois.CFT.padicExp_add`: **the exponential turns sums into products.**
* `InverseGalois.CFT.valued_padicExp_sub_one`: **the exponential changes no valuation**, in the
  sense that `exp x - 1` has the valuation of `x`.
* `InverseGalois.CFT.valued_padicExp`: an exponential is a unit of the valuation ring.
* `InverseGalois.CFT.valued_padicExp_sub_padicExp`: **the exponential is an isometry**, hence
  injective.

## Tags

valued field, exponential, Legendre's theorem, nonarchimedean convergence
-/

namespace InverseGalois.CFT

open Filter Topology

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {p e : ℕ}

/-! ### The residue characteristic -/

/-- **A valued field of residue characteristic `p`**, in which `p` itself has valuation
`exp (-e)`. -/
structure HasResidueChar (A : Type*) [Field A] [Valued A ℤᵐ⁰] (p e : ℕ) : Prop where
  /-- The residue characteristic is a prime. -/
  prime : p.Prime
  /-- The prime has valuation less than one. -/
  pos : 0 < e
  /-- The valuation of the prime. -/
  val_p : Valued.v (p : A) = WithZero.exp (-(e : ℤ))

namespace HasResidueChar

variable (h : HasResidueChar A p e)

include h

theorem valued_natCast {n : ℕ} (hn : n ≠ 0) :
    Valued.v (n : A) = WithZero.exp (-((e : ℤ) * padicValNat p n)) :=
  valued_natCast_eq_exp h.prime h.pos h.val_p hn

theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : A) ≠ 0 := fun hz => by
  have := h.valued_natCast hn
  rw [hz, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem factorial_ne_zero (k : ℕ) : ((k.factorial : ℕ) : A) ≠ 0 :=
  h.natCast_ne_zero (Nat.factorial_ne_zero k)

theorem one_lt_p : 1 < (p : ℤ) := by exact_mod_cast h.prime.one_lt

end HasResidueChar

/-! ### The exponential series -/

/-- **The terms of the exponential series.** -/
noncomputable def expTerm (x : A) (k : ℕ) : A := x ^ k / (k.factorial : A)

omit [Valued A ℤᵐ⁰] in
@[simp]
theorem expTerm_zero (x : A) : expTerm x 0 = 1 := by simp [expTerm]

omit [Valued A ℤᵐ⁰] in
@[simp]
theorem expTerm_one (x : A) : expTerm x 1 = x := by simp [expTerm]

/-- **The valuation of a term of the exponential series.** -/
theorem valued_expTerm_le (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (k : ℕ) :
    Valued.v (expTerm x k)
      ≤ WithZero.exp (-(j * k) + (e : ℤ) * padicValNat p k.factorial) := by
  rw [expTerm, map_div₀, map_pow, h.valued_natCast (Nat.factorial_ne_zero k), div_eq_mul_inv,
    ← WithZero.exp_neg, neg_neg]
  calc Valued.v x ^ k * WithZero.exp ((e : ℤ) * padicValNat p k.factorial)
      ≤ WithZero.exp (-j) ^ k * WithZero.exp ((e : ℤ) * padicValNat p k.factorial) :=
        mul_le_mul_left (pow_le_pow_left' hx k) _
    _ = WithZero.exp (-(j * k) + (e : ℤ) * padicValNat p k.factorial) := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
        rw [nsmul_eq_mul]
        ring

/-- **Legendre's bound makes the exponents of the terms grow at least linearly.** -/
theorem le_expTerm_exponent (hp : p.Prime) {j : ℤ} (hj : (e : ℤ) < j * ((p : ℤ) - 1)) (k : ℕ) :
    (k : ℤ) ≤ ((p : ℤ) - 1) * (j * k - (e : ℤ) * padicValNat p k.factorial) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have h1 := sub_one_mul_valFactorial_le hp hk
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by
      have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      exact_mod_cast this
    have he0 : (0 : ℤ) ≤ (e : ℤ) := Int.natCast_nonneg e
    have hm0 : (0 : ℤ) ≤ (padicValNat p k.factorial : ℤ) := Int.natCast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 he0,
      mul_le_mul_of_nonneg_left hj.le (le_trans zero_le_one hk1)]

/-- **The terms of the exponential series tend to zero.** -/
theorem tendsto_expTerm (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Tendsto (expTerm x) cofinite (𝓝 0) := by
  refine tendsto_zero_of_valued fun N => ?_
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨(N * ((p : ℤ) - 1)).toNat, fun k hk => ?_⟩
  refine le_trans (valued_expTerm_le h hx k) (WithZero.exp_le_exp.mpr ?_)
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by have := h.one_lt_p; omega
  have hkN : N * ((p : ℤ) - 1) ≤ (k : ℤ) :=
    le_trans (Int.self_le_toNat _) (by exact_mod_cast hk)
  have hkey := le_expTerm_exponent h.prime hj k
  have h2 : ((p : ℤ) - 1) * N
      ≤ ((p : ℤ) - 1) * (j * k - (e : ℤ) * padicValNat p k.factorial) := by linarith
  have := le_of_mul_le_mul_left h2 hp1
  linarith

/-- **The exponential of an element of a complete valued field.** -/
noncomputable def padicExp (x : A) : A := ∑' k : ℕ, expTerm x k

variable [CompleteSpace A]

/-- **The exponential series converges.** -/
theorem summable_expTerm (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Summable (expTerm x) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_expTerm h hx hj)

/-- **The exponential series converges to the exponential.** -/
theorem hasSum_expTerm (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    HasSum (expTerm x) (padicExp x) :=
  (summable_expTerm h hx hj).hasSum

/-! ### The exponential turns sums into products -/

omit [CompleteSpace A] in
/-- The binomial theorem, divided by a factorial. -/
theorem sum_antidiagonal_expTerm (h : HasResidueChar A p e) (x y : A) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n, expTerm x kl.1 * expTerm y kl.2 = expTerm (x + y) n := by
  rw [expTerm, eq_div_iff (h.factorial_ne_zero n), Finset.sum_mul,
    Commute.add_pow' (Commute.all x y) n]
  refine Finset.sum_congr rfl ?_
  rintro ⟨k, l⟩ hkl
  rw [Finset.mem_antidiagonal] at hkl
  have hk : ((k.factorial : ℕ) : A) ≠ 0 := h.factorial_ne_zero k
  have hl : ((l.factorial : ℕ) : A) ≠ 0 := h.factorial_ne_zero l
  have hfac : (n.factorial : A) = (n.choose k : A) * (k.factorial : A) * (l.factorial : A) := by
    have hkn : k ≤ n := by omega
    have : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
      Nat.choose_mul_factorial_mul_factorial hkn
    have hl' : n - k = l := by omega
    rw [hl'] at this
    have hcast := congrArg (fun m : ℕ => (m : A)) this
    push_cast at hcast
    exact hcast.symm
  rw [expTerm, expTerm, nsmul_eq_mul, hfac]
  field_simp

/-- **The exponential turns sums into products.** -/
theorem padicExp_add (h : HasResidueChar A p e) {x y : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hy : Valued.v y ≤ WithZero.exp (-j))
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    padicExp (x + y) = padicExp x * padicExp y := by
  have hsx := summable_expTerm h hx hj
  have hsy := summable_expTerm h hy hj
  have hxy : Valued.v (x + y) ≤ WithZero.exp (-j) :=
    le_trans (Valuation.map_add Valued.v x y) (max_le hx hy)
  have hprod : Summable fun z : ℕ × ℕ => expTerm x z.1 * expTerm y z.2 :=
    hsx.mul_of_nonarchimedean hsy
  have := hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hprod
  rw [padicExp, padicExp, padicExp, this]
  exact tsum_congr fun n => (sum_antidiagonal_expTerm h x y n).symm

omit [CompleteSpace A] in
/-- The exponential of zero is one. -/
@[simp]
theorem padicExp_zero : padicExp (0 : A) = 1 := by
  have hterm : ∀ k : ℕ, expTerm (0 : A) k = if k = 0 then 1 else 0 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [expTerm, zero_pow hk, hk]
  rw [padicExp, tsum_congr hterm, tsum_ite_eq]

/-! ### The exponential is an isometry -/

/-- **The exponential agrees with `1 + x` to one further digit.** -/
theorem valued_padicExp_sub_one_add (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Valued.v (padicExp x - (1 + x)) ≤ WithZero.exp (-(j + 1)) := by
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by have := h.one_lt_p; omega
  have hsum := hasSum_expTerm h hx hj
  have hshift : HasSum (fun k : ℕ => expTerm x (k + 2))
      (padicExp x - ∑ i ∈ Finset.range 2, expTerm x i) := (hasSum_nat_add_iff' 2).mpr hsum
  have hrange : ∑ i ∈ Finset.range 2, expTerm x i = 1 + x := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, expTerm_zero, expTerm_one]
  rw [hrange] at hshift
  refine valued_le_of_hasSum hshift fun k => ?_
  refine le_trans (valued_expTerm_le h hx (k + 2)) (WithZero.exp_le_exp.mpr ?_)
  have hleg := sub_one_mul_valFactorial_le h.prime (n := k + 2) (by omega)
  have he0 : (0 : ℤ) ≤ (e : ℤ) := Int.natCast_nonneg e
  have hk1 : (0 : ℤ) < (k : ℤ) + 1 := by positivity
  have hcast : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  rw [hcast] at hleg
  set m : ℤ := (padicValNat p (k + 2).factorial : ℤ) with hm
  -- `e * m < j * (k + 1)`, so `j * (k + 2) - e * m ≥ j + 1`
  have h1 := mul_le_mul_of_nonneg_left hleg he0
  have h2 := mul_lt_mul_of_pos_right hj hk1
  have h3 : ((p : ℤ) - 1) * ((e : ℤ) * m) < ((p : ℤ) - 1) * (j * ((k : ℤ) + 1)) := by linarith
  have h4 := Int.lt_iff_add_one_le.mp (lt_of_mul_lt_mul_left h3 hp1.le)
  rw [hcast]
  linarith

/-- **The exponential is congruent to one as closely as its argument is to zero.** -/
theorem valued_padicExp_sub_one_le (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Valued.v (padicExp x - 1) ≤ WithZero.exp (-j) := by
  rw [show padicExp x - 1 = x + (padicExp x - (1 + x)) by ring]
  refine le_trans (Valuation.map_add Valued.v _ _) (max_le hx ?_)
  exact le_trans (valued_padicExp_sub_one_add h hx hj) (WithZero.exp_le_exp.mpr (by omega))

/-- **The exponential changes no valuation.** -/
theorem valued_padicExp_sub_one (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x = WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Valued.v (padicExp x - 1) = WithZero.exp (-j) := by
  have htail := valued_padicExp_sub_one_add h hx.le hj
  have hlt : Valued.v (padicExp x - (1 + x)) < Valued.v x := by
    rw [hx]
    exact lt_of_le_of_lt htail (WithZero.exp_lt_exp.mpr (by omega))
  have hsplit : padicExp x - 1 = x + (padicExp x - (1 + x)) := by ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left _ hlt, hx]

/-- **An exponential is a unit of the valuation ring.** -/
theorem valued_padicExp (h : HasResidueChar A p e) {x : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Valued.v (padicExp x) = 1 := by
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by have := h.one_lt_p; omega
  have hj0 : (0 : ℤ) < j := by nlinarith [Int.natCast_nonneg e]
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · have hx0 : x = 0 := by simpa using h0
    rw [hx0, padicExp_zero, map_one]
  · obtain ⟨i, hi⟩ : ∃ i : ℤ, Valued.v x = WithZero.exp (-i) :=
      ⟨-WithZero.log (Valued.v x), by rw [neg_neg, WithZero.exp_log h0]⟩
    have hij : j ≤ i := by
      rw [hi] at hx
      have := WithZero.exp_le_exp.mp hx
      omega
    have hji : (e : ℤ) < i * ((p : ℤ) - 1) := by nlinarith
    have hone : Valued.v (padicExp x - 1) < 1 := by
      rw [valued_padicExp_sub_one h hi hji]
      calc WithZero.exp (-i) ≤ WithZero.exp (-j) := WithZero.exp_le_exp.mpr (by omega)
        _ < 1 := by simpa using WithZero.exp_lt_exp.mpr (show -j < (0 : ℤ) by omega)
    have := Valuation.map_one_add_of_lt Valued.v hone
    rw [show (1 : A) + (padicExp x - 1) = padicExp x by ring] at this
    exact this

/-- **The exponential is an isometry.** -/
theorem valued_padicExp_sub_padicExp (h : HasResidueChar A p e) {x y : A} {j : ℤ}
    (hx : Valued.v x ≤ WithZero.exp (-j)) (hy : Valued.v y ≤ WithZero.exp (-j))
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) :
    Valued.v (padicExp x - padicExp y) = Valued.v (x - y) := by
  have hsub : Valued.v (x - y) ≤ WithZero.exp (-j) := by
    rw [sub_eq_add_neg]
    exact le_trans (Valuation.map_add Valued.v _ _) (max_le hx (by rwa [Valuation.map_neg]))
  have hfac : padicExp x = padicExp y * padicExp (x - y) := by
    rw [← padicExp_add h hy hsub hj]
    ring_nf
  rcases eq_or_ne x y with rfl | hne
  · simp
  · have h0 : Valued.v (x - y) ≠ 0 := by simpa using sub_ne_zero.mpr hne
    obtain ⟨i, hi⟩ : ∃ i : ℤ, Valued.v (x - y) = WithZero.exp (-i) :=
      ⟨-WithZero.log (Valued.v (x - y)), by rw [neg_neg, WithZero.exp_log h0]⟩
    have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by have := h.one_lt_p; omega
    have hij : j ≤ i := by
      rw [hi] at hsub
      have := WithZero.exp_le_exp.mp hsub
      omega
    have hji : (e : ℤ) < i * ((p : ℤ) - 1) := by nlinarith
    calc Valued.v (padicExp x - padicExp y)
        = Valued.v (padicExp y * (padicExp (x - y) - 1)) := by rw [hfac]; ring_nf
      _ = Valued.v (padicExp y) * Valued.v (padicExp (x - y) - 1) := map_mul _ _ _
      _ = Valued.v (x - y) := by
          rw [valued_padicExp h hy hj, one_mul, valued_padicExp_sub_one h hi hji, hi]

/-- **The exponential is injective.** -/
theorem padicExp_injOn (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {x y : A} (hx : Valued.v x ≤ WithZero.exp (-j))
    (hy : Valued.v y ≤ WithZero.exp (-j)) (hxy : padicExp x = padicExp y) : x = y := by
  have := valued_padicExp_sub_padicExp h hx hy hj
  rw [hxy, sub_self, map_zero] at this
  have : x - y = 0 := by simpa using this.symm
  linear_combination this

end InverseGalois.CFT
