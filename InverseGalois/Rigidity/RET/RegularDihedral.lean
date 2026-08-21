/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.BaseTransfer
import InverseGalois.Rigidity.RET.DihedralLift
import InverseGalois.Rigidity.RET.FixedField
import InverseGalois.Rigidity.RET.RatFuncSubst
import InverseGalois.Rigidity.RET.RegularCyclic

/-!
# Regular dihedral extensions of `ℚ(T)` of odd degree

The dihedral group of order `2n` is a **regular** inverse Galois group over `ℚ` for every odd
`n > 1`.

The construction adds an involution to the twisted Kummer tower of `RegularCyclic`.  Write
`K = ℚ(ζ)` for the `n`-th cyclotomic field and index the linear factors by pairs `(ε, x)` with
`ε ∈ ℤ/2` and `x` a unit of `ℤ/n`, the pair naming the root `(-1) ^ ε · ζ ^ x`.  These `2 φ(n)`
roots are distinct exactly because `n` is odd, and the two involutions in play act on the index
set separately: the coefficient action of the unit `c` multiplies `x` by `c`, and the substitution
`u ↦ -u` adds `1` to `ε`.

The Kummer datum is again a weighted product, with the weight of `(ε, x)` the representative of
`± x⁻¹`, the sign being `+` for `ε = 1` and `-` for `ε = 0`.  Weighting by inverses makes the
coefficient action multiply the datum by an exact `n`-th power, so the cyclotomic character lifts
to the Kummer extension exactly as in the cyclic case; the flip in `ε` sends the weight `a` to
`n - a`, so the substitution `u ↦ -u` sends the datum `g` to `m ^ n / g` for the unweighted
product `m`, and therefore lifts to the involution `w ↦ m / w` of the Kummer extension.

That involution inverts the Kummer automorphism `w ↦ ζ w` and commutes with the lifted cyclotomic
character, so it descends to the degree-`n` layer `L` — the fixed field of the character — where it
inverts a generator of `Gal(L / ℚ(u))`.  The fixed field of `u ↦ -u` inside `ℚ(u)` is a rational
function field by Lüroth, and `L` is a degree-`2n` Galois extension of it with dihedral group.
Regularity is inherited from the cyclic layer: a constant of `L` is fixed by the whole cyclotomic
character, hence rational.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Rigidity.RET.Dihedral

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

open Rigidity.RET (rootMultiplicity_prod_pow prod_pow_ne_zero irreducible_X_pow_sub_C_ratFunc)

open Rigidity.RET.Cyclic

variable (n : ℕ) [hn : Fact (1 < n)] [hodd : Fact (Odd n)]

theorem two_lt : 2 < n := by
  rcases hodd.out with ⟨k, hk⟩
  have := hn.out
  omega

/-! ### The index set -/

/-- The index set of the linear factors: a sign and a unit modulo `n`. -/
abbrev JJ : Type := ZMod 2 × (ZMod n)ˣ

/-- The sign attached to the first coordinate of an index. -/
def sgn (ε : ZMod 2) : KK n := (-1 : KK n) ^ ε.val

theorem zmod_two_cases (ε : ZMod 2) : ε = 0 ∨ ε = 1 := by revert ε; decide

@[simp] theorem sgn_zero : sgn n 0 = 1 := by
  rw [sgn, show (0 : ZMod 2).val = 0 by decide, pow_zero]

@[simp] theorem sgn_one : sgn n 1 = -1 := by
  rw [sgn, show (1 : ZMod 2).val = 1 by decide, pow_one]

theorem sgn_flip (ε : ZMod 2) : sgn n (ε + 1) = -sgn n ε := by
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zero_add, sgn_one, sgn_zero]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, sgn_zero, sgn_one, neg_neg]

theorem sgn_pow_n (ε : ZMod 2) : sgn n ε ^ n = sgn n ε := by
  rw [sgn, ← pow_mul, Nat.mul_comm, pow_mul, hodd.out.neg_one_pow]

/-- Flipping the sign of an index. -/
def jflip (j : JJ n) : JJ n := (j.1 + 1, j.2)

@[simp] theorem jflip_jflip (j : JJ n) : jflip n (jflip n j) = j := by
  rw [jflip, jflip, add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]

/-- Flipping the sign, as an involutive permutation of the index set. -/
def jflipEquiv : JJ n ≃ JJ n :=
  ⟨jflip n, jflip n, jflip_jflip n, jflip_jflip n⟩

@[simp] theorem jflipEquiv_apply (j : JJ n) : jflipEquiv n j = jflip n j := rfl

/-- The coefficient action of a unit on the index set. -/
def jmul (c : (ZMod n)ˣ) (j : JJ n) : JJ n := (j.1, c * j.2)

/-- The coefficient action of a unit, as a permutation of the index set. -/
def jmulEquiv (c : (ZMod n)ˣ) : JJ n ≃ JJ n :=
  (Equiv.refl (ZMod 2)).prodCongr (Equiv.mulLeft c)

@[simp] theorem jmulEquiv_apply (c : (ZMod n)ˣ) (j : JJ n) : jmulEquiv n c j = jmul n c j := rfl

theorem jmul_inv_left (c : (ZMod n)ˣ) (j : JJ n) : jmul n c⁻¹ (jmul n c j) = j := by
  rw [jmul, jmul, inv_mul_cancel_left]

theorem card_JJ : Fintype.card (JJ n) = 2 * n.totient := by
  rw [Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient]

/-! ### The roots -/

/-- The root attached to an index: a `2n`-th root of unity, of order divisible by the odd part. -/
def rt (j : JJ n) : KK n := sgn n j.1 * zetaPow n (j.2 : ZMod n)

theorem zetaPow_pow_n (x : ZMod n) : zetaPow n x ^ n = 1 := by
  rw [zetaPow, ← pow_mul, Nat.mul_comm, pow_mul, (zeta_spec n).pow_eq_one, one_pow]

theorem rt_pow_n (j : JJ n) : rt n j ^ n = sgn n j.1 := by
  rw [rt, mul_pow, zetaPow_pow_n, mul_one, sgn_pow_n]

theorem rt_flip (j : JJ n) : rt n (jflip n j) = -rt n j := by
  rw [rt, rt, jflip, sgn_flip, neg_mul]

theorem rt_injective : Function.Injective (rt n) := by
  rintro ⟨ε, x⟩ ⟨δ, y⟩ h
  have hpow : sgn n ε = sgn n δ := by
    have h2 : rt n (ε, x) ^ n = rt n (δ, y) ^ n := by rw [h]
    rwa [rt_pow_n, rt_pow_n] at h2
  have hεδ : ε = δ := by
    rcases zmod_two_cases ε with rfl | rfl <;> rcases zmod_two_cases δ with rfl | rfl
    · rfl
    · rw [sgn_zero, sgn_one] at hpow
      exact absurd hpow.symm (by norm_num)
    · rw [sgn_zero, sgn_one] at hpow
      exact absurd hpow (by norm_num)
    · rfl
  subst hεδ
  have hz : zetaPow n (x : ZMod n) = zetaPow n (y : ZMod n) := by
    have hs : sgn n ε ≠ 0 := by
      rcases zmod_two_cases ε with rfl | rfl <;> simp
    refine mul_left_cancel₀ hs ?_
    simpa [rt] using h
  exact Prod.ext rfl (Units.ext (zetaPow_injective n hz))

theorem sigmaK_rt (c : (ZMod n)ˣ) (j : JJ n) : sigmaK n c (rt n j) = rt n (jmul n c j) := by
  rw [rt, rt, jmul, map_mul, sigmaK_zetaPow, Units.val_mul]
  congr 1
  simp only [sgn, map_pow, map_neg, map_one]

/-! ### Exponent vectors -/

/-- A linear factor of the Kummer datum, as an element of `K(u)`. -/
def linE (j : JJ n) : EE n := algebraMap (KK n)[X] (EE n) (X - C (rt n j))

theorem linE_ne_zero (j : JJ n) : linE n j ≠ 0 := fun h =>
  X_sub_C_ne_zero (rt n j)
    ((IsFractionRing.injective (KK n)[X] (EE n)) (by rw [map_zero]; exact h))

/-- **The exponent-vector homomorphism** `Φ e = ∏ (u - r j) ^ e j`. -/
def phi (e : JJ n → ℤ) : EE n := ∏ j : JJ n, linE n j ^ e j

theorem phi_ne_zero (e : JJ n → ℤ) : phi n e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (linE_ne_zero n j)

theorem phi_congr {e₁ e₂ : JJ n → ℤ} (h : ∀ j, e₁ j = e₂ j) : phi n e₁ = phi n e₂ :=
  Finset.prod_congr rfl fun j _ => by rw [h j]

theorem phi_zero : phi n (fun _ => 0) = 1 := by
  rw [phi]
  exact Finset.prod_eq_one fun j _ => zpow_zero _

theorem phi_add (e₁ e₂ : JJ n → ℤ) :
    phi n (fun j => e₁ j + e₂ j) = phi n e₁ * phi n e₂ := by
  rw [phi, phi, phi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (linE_ne_zero n j) _ _

theorem phi_zpow (e : JJ n → ℤ) (m : ℤ) : phi n e ^ m = phi n (fun j => m * e j) := by
  rw [phi, phi, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by rw [← zpow_mul, mul_comm]

/-- `Φ` of a vector of natural numbers is the image of an honest polynomial. -/
theorem phi_natCast (A : JJ n → ℕ) :
    phi n (fun j => (A j : ℤ))
      = algebraMap (KK n)[X] (EE n) (∏ j : JJ n, (X - C (rt n j)) ^ A j) := by
  rw [phi, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow, zpow_natCast]; rfl

/-- **`Φ` is injective**: the exponents are recovered as root multiplicities. -/
theorem exponent_eq_zero_of_phi_eq_one {e : JJ n → ℤ} (he : phi n e = 1) (w : JJ n) : e w = 0 := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : JJ n → ℕ, ∀ j, (A j : ℤ) - (B j : ℤ) = e j :=
    ⟨fun j => (e j).toNat, fun j => (-(e j)).toNat, fun j => by
      show ((e j).toNat : ℤ) - ((-(e j)).toNat : ℤ) = e j
      omega⟩
  have hphi : phi n (fun j => (A j : ℤ)) = phi n (fun j => (B j : ℤ)) := by
    have hfun : (fun j => (A j : ℤ)) = fun j => e j + (B j : ℤ) :=
      funext fun j => by have := hAB j; omega
    rw [hfun, phi_add, he, one_mul]
  have hpoly : (∏ j : JJ n, (X - C (rt n j)) ^ A j) = ∏ j : JJ n, (X - C (rt n j)) ^ B j :=
    IsFractionRing.injective (KK n)[X] (EE n) (by rw [← phi_natCast, ← phi_natCast]; exact hphi)
  have hmul : (∏ j : JJ n, (X - C (rt n j)) ^ A j).rootMultiplicity (rt n w)
      = (∏ j : JJ n, (X - C (rt n j)) ^ B j).rootMultiplicity (rt n w) := by rw [hpoly]
  rw [rootMultiplicity_prod_pow _ (rt_injective n), rootMultiplicity_prod_pow _ (rt_injective n)]
    at hmul
  have := hAB w
  omega

/-! ### The two actions on exponent vectors -/

theorem sigmaE_linE (c : (ZMod n)ˣ) (j : JJ n) : sigmaE n c (linE n j) = linE n (jmul n c j) := by
  rw [linE, Rigidity.RET.Cyclic.sigmaE_algebraMap_poly, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, linE, RingHom.coe_coe, sigmaK_rt]

/-- **The coefficient action permutes the exponents.** -/
theorem sigmaE_phi (c : (ZMod n)ˣ) (e : JJ n → ℤ) :
    sigmaE n c (phi n e) = phi n (fun j => e (jmul n c⁻¹ j)) := by
  have h1 : sigmaE n c (phi n e) = ∏ j : JJ n, linE n (jmul n c j) ^ e j := by
    rw [phi, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [map_zpow₀, sigmaE_linE]
  have h2 : phi n (fun j => e (jmul n c⁻¹ j))
      = ∏ j : JJ n, linE n (jmul n c j) ^ e j := by
    rw [phi, ← Equiv.prod_comp (jmulEquiv n c) (fun w => linE n w ^ e (jmul n c⁻¹ w))]
    exact Finset.prod_congr rfl fun j _ => by rw [jmulEquiv_apply, jmul_inv_left]
  rw [h1, h2]

/-- A constant raised to a sum of integer exponents. -/
theorem prod_zpow_const {L : Type*} [Field L] {a : L} (ha : a ≠ 0) {ι : Type*} (s : Finset ι)
    (e : ι → ℤ) : (∏ i ∈ s, a ^ e i) = a ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ha]

/-! ### The substitution `u ↦ -u` -/

section Neg

variable (K : Type*) [Field K]

open Rigidity.RET (ratFuncSubst ratFuncSubstEquiv ratFunc_algHom_ext transcendental_const_mul_X)

theorem transcendental_neg_X : Transcendental K (-RatFunc.X : RatFunc K) := by
  have h := transcendental_const_mul_X (K := K) (c := -1) (by norm_num)
  rwa [map_neg, map_one, neg_one_mul] at h

theorem ratFuncSubst_neg_neg :
    ratFuncSubst (-RatFunc.X : RatFunc K) (transcendental_neg_X K) (-RatFunc.X) = RatFunc.X := by
  rw [map_neg, Rigidity.RET.ratFuncSubst_X, neg_neg]

/-- **The substitution `u ↦ -u`** of the rational function field. -/
def ratFuncNeg : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncSubstEquiv (transcendental_neg_X K) (transcendental_neg_X K) (ratFuncSubst_neg_neg K)
    (ratFuncSubst_neg_neg K)

@[simp] theorem ratFuncNeg_X : ratFuncNeg K (RatFunc.X : RatFunc K) = -RatFunc.X := by
  rw [ratFuncNeg, Rigidity.RET.ratFuncSubstEquiv_apply, Rigidity.RET.ratFuncSubst_X]

theorem ratFuncNeg_ratFuncNeg (x : RatFunc K) : ratFuncNeg K (ratFuncNeg K x) = x := by
  have h : (ratFuncNeg K).toAlgHom.comp (ratFuncNeg K).toAlgHom = AlgHom.id K (RatFunc K) := by
    refine ratFunc_algHom_ext ?_
    rw [AlgHom.comp_apply]
    show ratFuncNeg K (ratFuncNeg K RatFunc.X) = RatFunc.X
    rw [ratFuncNeg_X, map_neg, ratFuncNeg_X, neg_neg]
  exact congrArg (fun φ : RatFunc K →ₐ[K] RatFunc K => φ x) h

/-- **The substitution `u ↦ -u`**, packaged as a ring automorphism.  Building it inside this
section keeps the rational structure of the coefficient field out of the elaboration. -/
def ratFuncNegAut : RingAut (RatFunc K) := (ratFuncNeg K).toRingEquiv

@[simp] theorem ratFuncNegAut_X : ratFuncNegAut K (RatFunc.X : RatFunc K) = -RatFunc.X :=
  ratFuncNeg_X K

theorem ratFuncNegAut_ratFuncNegAut (x : RatFunc K) :
    ratFuncNegAut K (ratFuncNegAut K x) = x := ratFuncNeg_ratFuncNeg K x

theorem ratFuncNeg_ne_id [CharZero K] : ∃ x : RatFunc K, ratFuncNeg K x ≠ x := by
  refine ⟨RatFunc.X, ?_⟩
  rw [ratFuncNeg_X]
  intro hX
  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  have h2 : (2 : RatFunc K) * RatFunc.X = 0 := by linear_combination -hX
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact absurd h2 (by norm_num)
  · exact RatFunc.X_ne_zero h2

end Neg

/-- The substitution `u ↦ -u` of `K(u)`. -/
def rhoE : EE n ≃ₐ[KK n] EE n := ratFuncNeg (KK n)

/-- The substitution `u ↦ -u` of `ℚ(u)`, as a ring automorphism. -/
def rhoF : RingAut FF := ratFuncNegAut ℚ

theorem rhoF_X : rhoF (RatFunc.X : FF) = -RatFunc.X := ratFuncNegAut_X ℚ

theorem rhoF_rhoF (x : FF) : rhoF (rhoF x) = x := ratFuncNegAut_ratFuncNegAut ℚ x

theorem rhoF_ne_id : ∃ x : FF, rhoF x ≠ x := ratFuncNeg_ne_id ℚ

theorem algebraMap_X_EE : algebraMap FF (EE n) (RatFunc.X : FF) = (RatFunc.X : EE n) := by
  rw [← RatFunc.algebraMap_X, Rigidity.RET.algebraMap_ratFunc_ratFunc, Polynomial.map_X,
    RatFunc.algebraMap_X]

theorem algebraMap_KK_EE (a : KK n) :
    algebraMap (KK n) (EE n) a = algebraMap (KK n)[X] (EE n) (C a) := by
  rw [IsScalarTower.algebraMap_apply (KK n) (KK n)[X] (EE n)]
  rfl

theorem linE_eq (j : JJ n) : linE n j = RatFunc.X - algebraMap (KK n) (EE n) (rt n j) := by
  rw [linE, map_sub, RatFunc.algebraMap_X, algebraMap_KK_EE]

theorem rhoE_linE (j : JJ n) : rhoE n (linE n j) = -linE n (jflip n j) := by
  rw [linE_eq, linE_eq, map_sub, rhoE, ratFuncNeg_X, (ratFuncNeg (KK n)).commutes, rt_flip,
    map_neg]
  ring

/-- **The substitution `u ↦ -u` flips the exponents.** -/
theorem rhoE_phi (e : JJ n → ℤ) :
    rhoE n (phi n e) = (-1 : EE n) ^ (∑ j : JJ n, e j) * phi n (fun j => e (jflip n j)) := by
  have h1 : rhoE n (phi n e) = ∏ j : JJ n, ((-1 : EE n) ^ e j * linE n (jflip n j) ^ e j) := by
    rw [phi, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow₀, rhoE_linE, neg_eq_neg_one_mul, mul_zpow]
  have h2 : (∏ j : JJ n, ((-1 : EE n) ^ e j * linE n (jflip n j) ^ e j))
      = (∏ j : JJ n, (-1 : EE n) ^ e j) * ∏ j : JJ n, linE n (jflip n j) ^ e j :=
    Finset.prod_mul_distrib
  have h3 : (∏ j : JJ n, (-1 : EE n) ^ e j) = (-1 : EE n) ^ (∑ j : JJ n, e j) :=
    prod_zpow_const (by norm_num) _ _
  have h4 : (∏ j : JJ n, linE n (jflip n j) ^ e j) = phi n (fun j => e (jflip n j)) := by
    rw [phi, ← Equiv.prod_comp (jflipEquiv n) (fun w => linE n w ^ e (jflip n w))]
    exact Finset.prod_congr rfl fun j _ => by rw [jflipEquiv_apply, jflip_jflip]
  rw [h1, h2, h3, h4]

/-- A ring map out of `ℚ(u)` is determined by its value at the parameter. -/
theorem ringHom_ext_FF {L : Type*} [Field L] {φ ψ : FF →+* L} (hX : φ RatFunc.X = ψ RatFunc.X) :
    φ = ψ := by
  refine IsFractionRing.ringHom_ext (A := ℚ[X]) fun p => ?_
  have h : φ.comp (algebraMap ℚ[X] FF) = ψ.comp (algebraMap ℚ[X] FF) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_X, hX]
  exact congrArg (fun f : ℚ[X] →+* L => f p) h

/-- **The two substitutions `u ↦ -u` agree**: the one of `K(u)` restricts to the one of `ℚ(u)`. -/
theorem rhoE_algebraMap_FF (x : FF) :
    rhoE n (algebraMap FF (EE n) x) = algebraMap FF (EE n) (rhoF x) := by
  have h : ((rhoE n : EE n ≃+* EE n).toRingHom.comp (algebraMap FF (EE n)))
      = (algebraMap FF (EE n)).comp (rhoF : FF ≃+* FF).toRingHom := by
    refine ringHom_ext_FF ?_
    show rhoE n (algebraMap FF (EE n) RatFunc.X) = algebraMap FF (EE n) (rhoF RatFunc.X)
    rw [algebraMap_X_EE, rhoE, ratFuncNeg_X, rhoF_X, map_neg, algebraMap_X_EE]
  exact congrArg (fun f : FF →+* EE n => f x) h

/-- A power of `-1` with an even integer exponent. -/
theorem neg_one_zpow_even {m : ℤ} (hm : Even m) : (-1 : EE n) ^ m = 1 := by
  obtain ⟨t, rfl⟩ := hm
  rw [show t + t = 2 * t by ring, zpow_mul, show ((-1 : EE n) ^ (2 : ℤ)) = 1 by norm_num, one_zpow]

/-- The unweighted product of all the linear factors. -/
def mmE : EE n := phi n (fun _ => 1)

theorem mmE_ne_zero : mmE n ≠ 0 := phi_ne_zero n _

theorem sigmaE_mmE (c : (ZMod n)ˣ) : sigmaE n c (mmE n) = mmE n := by
  rw [mmE, sigmaE_phi]

theorem rhoE_mmE : rhoE n (mmE n) = mmE n := by
  rw [mmE, rhoE_phi]
  have hcard : (∑ _j : JJ n, (1 : ℤ)) = 2 * (n.totient : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, card_JJ, nsmul_eq_mul, Nat.cast_mul]
    norm_num
  rw [hcard, zpow_mul, show ((-1 : EE n) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, one_mul]

/-! ### The twisted Kummer datum -/

/-- The sign of the weight attached to an index. -/
def sgu (ε : ZMod 2) : (ZMod n)ˣ := if ε = 0 then -1 else 1

theorem sgu_flip (ε : ZMod 2) : sgu n (ε + 1) = -sgu n ε := by
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zero_add, sgu, sgu, if_neg (by decide : ¬((1 : ZMod 2) = 0)), if_pos rfl, neg_neg]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, sgu, sgu, if_pos rfl,
      if_neg (by decide : ¬((1 : ZMod 2) = 0))]

/-- The weight attached to an index, as a unit modulo `n`. -/
def aunit (j : JJ n) : (ZMod n)ˣ := sgu n j.1 * j.2⁻¹

theorem aunit_flip (j : JJ n) : aunit n (jflip n j) = -aunit n j := by
  rw [aunit, aunit, jflip, sgu_flip, neg_mul]

theorem aunit_jmul (c : (ZMod n)ˣ) (j : JJ n) : aunit n (jmul n c⁻¹ j) = c * aunit n j := by
  rw [aunit, aunit, jmul, mul_inv_rev, inv_inv, ← mul_assoc]
  exact mul_comm _ _

/-- The weight attached to an index: the representative of `± x⁻¹`. -/
def anat (j : JJ n) : ℕ := ((aunit n j : ZMod n)).val

theorem anat_cast (j : JJ n) : ((anat n j : ℕ) : ZMod n) = (aunit n j : ZMod n) := by
  rw [anat, ZMod.natCast_val, ZMod.cast_id]

theorem anat_lt (j : JJ n) : anat n j < n := ZMod.val_lt _

/-- **The weights of an index and of its flip are complementary.**  This is what makes the
substitution `u ↦ -u` send the Kummer datum to a power of the unweighted product divided by it. -/
theorem anat_flip (j : JJ n) : anat n j + anat n (jflip n j) = n := by
  have hne : (aunit n j : ZMod n) ≠ 0 := Units.ne_zero _
  have h : anat n (jflip n j) = n - anat n j := by
    rw [anat, anat, aunit_flip, Units.val_neg, ZMod.neg_val, if_neg hne]
  have := anat_lt n j
  omega

theorem anat_one : anat n ((1 : ZMod 2), (1 : (ZMod n)ˣ)) = 1 := by
  rw [anat, aunit, sgu, if_neg (by decide : ¬((1 : ZMod 2) = 0)), inv_one, mul_one, Units.val_one,
    ZMod.val_one]

theorem rt_one_one : rt n ((1 : ZMod 2), (1 : (ZMod n)ˣ)) = -zeta n := by
  rw [rt, sgn_one, Units.val_one, zetaPow_one, neg_one_mul]

/-- The weighted product `g = ∏ (u - r j) ^ a j`. -/
def gpoly : (KK n)[X] := ∏ j : JJ n, (X - C (rt n j)) ^ anat n j

theorem gpoly_ne_zero : gpoly n ≠ 0 := prod_pow_ne_zero _ _

/-- `g` has a **simple** root at `-ζ`: this single fact drives both the irreducibility of the
Kummer extension and its regularity. -/
theorem rootMultiplicity_gpoly : (gpoly n).rootMultiplicity (-zeta n) = 1 := by
  rw [gpoly, ← rt_one_one n, rootMultiplicity_prod_pow _ (rt_injective n), anat_one]

/-- The twisted Kummer datum `g`, as an element of `K(u)`. -/
def gE : EE n := algebraMap (KK n)[X] (EE n) (gpoly n)

theorem gE_eq_phi : gE n = phi n (fun j => (anat n j : ℤ)) := (phi_natCast n (anat n)).symm

theorem gE_ne_zero : gE n ≠ 0 := by rw [gE_eq_phi]; exact phi_ne_zero n _

theorem gE_pow_nat (m : ℕ) : gE n ^ m = phi n (fun j => (m : ℤ) * (anat n j : ℤ)) := by
  rw [gE_eq_phi, ← zpow_natCast _ m, phi_zpow]

/-- The correction exponents: the exact amount by which `c · g` and `g ^ c` differ by an `n`-th
power. -/
def hexp (c : (ZMod n)ˣ) (j : JJ n) : ℤ :=
  ((anat n (jmul n c⁻¹ j) : ℤ) - (cnat n c : ℤ) * (anat n j : ℤ)) / (n : ℤ)

theorem dvd_anat_sub (c : (ZMod n)ˣ) (j : JJ n) :
    (n : ℤ) ∣ (anat n (jmul n c⁻¹ j) : ℤ) - (cnat n c : ℤ) * (anat n j : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [anat_cast, anat_cast, cnat_cast, aunit_jmul, Units.val_mul]
  ring

theorem n_mul_hexp (c : (ZMod n)ˣ) (j : JJ n) :
    (n : ℤ) * hexp n c j = (anat n (jmul n c⁻¹ j) : ℤ) - (cnat n c : ℤ) * (anat n j : ℤ) :=
  Int.mul_ediv_cancel' (dvd_anat_sub n c j)

theorem hexp_one (j : JJ n) : hexp n 1 j = 0 := by
  rw [hexp, inv_one, show jmul n 1 j = j from by rw [jmul, one_mul], cnat_one, Nat.cast_one,
    one_mul, sub_self, Int.zero_ediv]

/-- The twisting factor attached to a unit. -/
def hE (c : (ZMod n)ˣ) : EE n := phi n (hexp n c)

theorem hE_ne_zero (c : (ZMod n)ˣ) : hE n c ≠ 0 := phi_ne_zero n _

theorem hE_one : hE n 1 = 1 := by
  rw [hE, phi_congr n (e₂ := fun _ => (0 : ℤ)) (hexp_one n), phi_zero]

theorem hE_pow_nat (c : (ZMod n)ˣ) (m : ℕ) :
    hE n c ^ m = phi n (fun j => (m : ℤ) * hexp n c j) := by
  rw [hE, ← zpow_natCast _ m, phi_zpow]

/-- **The twisting identity** in `K(u)`: `c · g = g ^ c * h c ^ n`. -/
theorem sigmaE_gE (c : (ZMod n)ˣ) : sigmaE n c (gE n) = gE n ^ cnat n c * hE n c ^ n := by
  rw [gE_pow_nat, hE_pow_nat, ← phi_add, gE_eq_phi, sigmaE_phi]
  refine phi_congr n fun j => ?_
  have h := n_mul_hexp n c j
  linarith

/-- **The cocycle identity** satisfied by the twisting factors. -/
theorem hE_cocycle (c d : (ZMod n)ˣ) :
    gE n ^ kk n c d * hE n c ^ cnat n d * sigmaE n c (hE n d) = hE n (c * d) := by
  rw [gE_eq_phi, phi_zpow, hE_pow_nat, hE, sigmaE_phi, hE, ← phi_add, ← phi_add]
  refine phi_congr n fun j => ?_
  have hn0 : (n : ℤ) ≠ 0 := by have := hn.out; positivity
  refine mul_left_cancel₀ hn0 ?_
  have h1 := n_mul_kk n c d
  have h2 := n_mul_hexp n c j
  have h3 := n_mul_hexp n d (jmul n c⁻¹ j)
  have h4 := n_mul_hexp n (c * d) j
  rw [show jmul n (c * d)⁻¹ j = jmul n d⁻¹ (jmul n c⁻¹ j) by
    rw [jmul, jmul, jmul, mul_inv_rev, mul_assoc]] at h4
  linear_combination (anat n j : ℤ) * h1 + (cnat n d : ℤ) * h2 + h3 - h4

/-! ### The flip identities -/

/-- The sum of an exponent vector that pairs up under the flip. -/
theorem sum_flip (F : JJ n → ℤ) (k : ℤ) (h : ∀ j, F j + F (jflip n j) = k) :
    ∑ j : JJ n, F j = k * n.totient := by
  have h1 : ∑ j : JJ n, F (jflip n j) = ∑ j : JJ n, F j := Equiv.sum_comp (jflipEquiv n) F
  have h2 : ∑ j : JJ n, (F j + F (jflip n j)) = (2 * n.totient : ℕ) • k := by
    rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_const, Finset.card_univ, card_JJ]
  rw [Finset.sum_add_distrib, h1, nsmul_eq_mul] at h2
  refine mul_left_cancel₀ (two_ne_zero) ?_
  push_cast at h2 ⊢
  linarith

theorem sum_anat : ∑ j : JJ n, (anat n j : ℤ) = n * n.totient :=
  sum_flip n _ n fun j => by
    have := anat_flip n j
    push_cast [← this]
    ring

theorem even_sum_anat : Even (∑ j : JJ n, (anat n j : ℤ)) := by
  rw [sum_anat]
  obtain ⟨t, ht⟩ := Nat.totient_even (two_lt n)
  exact ⟨n * t, by rw [ht]; push_cast; ring⟩

theorem hexp_flip (c : (ZMod n)ˣ) (j : JJ n) :
    hexp n c j + hexp n c (jflip n j) = 1 - (cnat n c : ℤ) := by
  have hn0 : (n : ℤ) ≠ 0 := by have := hn.out; positivity
  refine mul_left_cancel₀ hn0 ?_
  have h2 := n_mul_hexp n c j
  have h3 := n_mul_hexp n c (jflip n j)
  rw [show jmul n c⁻¹ (jflip n j) = jflip n (jmul n c⁻¹ j) from rfl] at h3
  have h4 : (anat n (jmul n c⁻¹ j) : ℤ) + (anat n (jflip n (jmul n c⁻¹ j)) : ℤ) = n := by
    have := anat_flip n (jmul n c⁻¹ j)
    push_cast [← this]
    ring
  have h5 : (anat n j : ℤ) + (anat n (jflip n j) : ℤ) = n := by
    have := anat_flip n j
    push_cast [← this]
    ring
  rw [mul_add, h2, h3]
  linear_combination h4 - (cnat n c : ℤ) * h5

theorem even_sum_hexp (c : (ZMod n)ˣ) : Even (∑ j : JJ n, hexp n c j) := by
  rw [sum_flip n _ (1 - (cnat n c : ℤ)) (hexp_flip n c)]
  obtain ⟨t, ht⟩ := Nat.totient_even (two_lt n)
  exact ⟨(1 - (cnat n c : ℤ)) * t, by rw [ht]; push_cast; ring⟩

/-- **The substitution `u ↦ -u` inverts the Kummer datum**, up to the `n`-th power of the
unweighted product. -/
theorem rhoE_gE : rhoE n (gE n) * gE n = mmE n ^ n := by
  rw [gE_eq_phi, rhoE_phi, neg_one_zpow_even n (even_sum_anat n), one_mul, ← phi_add, mmE,
    ← zpow_natCast (phi n fun _ => (1 : ℤ)) n, phi_zpow]
  refine phi_congr n fun j => ?_
  have := anat_flip n j
  push_cast [← this]
  ring

/-- **The substitution `u ↦ -u` inverts the twisting factors**, up to a power of the unweighted
product. -/
theorem rhoE_hE (c : (ZMod n)ˣ) :
    rhoE n (hE n c) * hE n c = mmE n ^ (1 - (cnat n c : ℤ)) := by
  rw [hE, rhoE_phi, neg_one_zpow_even n (even_sum_hexp n c), one_mul, ← phi_add, mmE, phi_zpow]
  refine phi_congr n fun j => ?_
  have := hexp_flip n c j
  linarith

/-! ### The Kummer extension -/

/-- The Kummer polynomial `X ^ n - g` is irreducible over `K(u)`: `g` has a simple root, so the
polynomial is Eisenstein at `u + ζ`. -/
theorem kummer_irreducible : Irreducible ((X : (EE n)[X]) ^ n - C (gE n)) :=
  irreducible_X_pow_sub_C_ratFunc (rootMultiplicity_gpoly n) (by have := hn.out; omega)

instance factKummer : Fact (Irreducible ((X : (EE n)[X]) ^ n - C (gE n))) := ⟨kummer_irreducible n⟩

/-- The Kummer extension `M = K(u)(g ^ (1/n))`. -/
abbrev MM : Type := AdjoinRoot ((X : (EE n)[X]) ^ n - C (gE n))

/-- Shortcut for the `ℚ(u)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algFFMM : Algebra FF (MM n) := AdjoinRoot.instAlgebra _

/-- Shortcut for the `K(u)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algEEMM : Algebra (EE n) (MM n) := AdjoinRoot.instAlgebra _

/-- The chosen `n`-th root of `g`. -/
def wr : MM n := AdjoinRoot.root _

theorem wr_pow : wr n ^ n = algebraMap (EE n) (MM n) (gE n) := by
  rw [wr, AdjoinRoot.algebraMap_eq]
  exact root_X_pow_sub_C_pow n (gE n)

theorem kummer_ne_zero : ((X : (EE n)[X]) ^ n - C (gE n)) ≠ 0 := (kummer_irreducible n).ne_zero

instance : FiniteDimensional (EE n) (MM n) := (AdjoinRoot.powerBasis (kummer_ne_zero n)).finite

theorem finrank_EE_MM : Module.finrank (EE n) (MM n) = n := by
  rw [(AdjoinRoot.powerBasis (kummer_ne_zero n)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

instance : FiniteDimensional FF (MM n) := .trans FF (EE n) (MM n)

theorem finrank_FF_MM : Module.finrank FF (MM n) = n.totient * n := by
  rw [← Module.finrank_mul_finrank FF (EE n) (MM n), finrank_FF_EE, finrank_EE_MM]

/-- The defining relation of `M`, in the form required to lift a homomorphism out of it. -/
private theorem eval₂_kummer {i : EE n →+* MM n} {x : MM n} (h : x ^ n = i (gE n)) :
    ((X : (EE n)[X]) ^ n - C (gE n)).eval₂ i x = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h, sub_self]

/-- `ζ`, viewed in `M`. -/
def zetaM : MM n := algebraMap (KK n) (MM n) (zeta n)

theorem zetaM_pow_eq_one_iff (m : ℕ) : zetaM n ^ m = 1 ↔ n ∣ m := by
  rw [zetaM, ← map_pow, ← (zeta_spec n).pow_eq_one_iff_dvd m]
  constructor
  · intro h
    exact (algebraMap (KK n) (MM n)).injective (by rw [h, map_one])
  · intro h; rw [h, map_one]

theorem zetaM_pow : zetaM n ^ n = 1 := (zetaM_pow_eq_one_iff n n).mpr dvd_rfl

theorem wr_ne_zero : wr n ≠ 0 := root_X_pow_sub_C_ne_zero hn.out (gE n)

/-- The Kummer automorphism `w ↦ ζ w`, as an algebra map. -/
def tauHom : MM n →ₐ[EE n] MM n :=
  AdjoinRoot.liftAlgHom ((X : (EE n)[X]) ^ n - C (gE n)) (Algebra.ofId (EE n) (MM n))
    (zetaM n * wr n)
    (eval₂_kummer n (by rw [mul_pow, zetaM_pow, one_mul, wr_pow]; rfl))

/-- **The Kummer automorphism** `w ↦ ζ w` of `M / K(u)`. -/
def tau : MM n ≃ₐ[EE n] MM n := AlgEquiv.ofBijective (tauHom n) (tauHom n).bijective

@[simp] theorem tau_wr : tau n (wr n) = zetaM n * wr n := by
  simp only [tau, AlgEquiv.coe_ofBijective, tauHom, wr, AdjoinRoot.liftAlgHom_root]

/-- The twisting factor, viewed in `M`. -/
def hM (c : (ZMod n)ˣ) : MM n := algebraMap (EE n) (MM n) (hE n c)

theorem hM_ne_zero (c : (ZMod n)ˣ) : hM n c ≠ 0 := fun h =>
  hE_ne_zero n c ((algebraMap (EE n) (MM n)).injective (by rw [map_zero, ← hM, h]))

/-- The unweighted product, viewed in `M`. -/
def mmM : MM n := algebraMap (EE n) (MM n) (mmE n)

theorem mmM_ne_zero : mmM n ≠ 0 := fun h =>
  mmE_ne_zero n ((algebraMap (EE n) (MM n)).injective (by rw [map_zero, ← mmM, h]))

/-- The lift of the unit `c` to `M`, sending `w` to `w ^ c * h c`. -/
def sigmaHomM (c : (ZMod n)ˣ) : MM n →ₐ[FF] MM n :=
  AdjoinRoot.liftAlgHom ((X : (EE n)[X]) ^ n - C (gE n))
    ((IsScalarTower.toAlgHom FF (EE n) (MM n)).comp (sigmaE n c).toAlgHom)
    (wr n ^ cnat n c * hM n c)
    (eval₂_kummer n (by
      show (wr n ^ cnat n c * hM n c) ^ n = algebraMap (EE n) (MM n) (sigmaE n c (gE n))
      rw [sigmaE_gE, map_mul, map_pow, map_pow, mul_pow, ← pow_mul,
        Nat.mul_comm (cnat n c) n, pow_mul, wr_pow, hM]))

/-- The lift of the unit `c` to an automorphism of `M / ℚ(u)`. -/
def sigmaMe (c : (ZMod n)ˣ) : MM n ≃ₐ[FF] MM n :=
  AlgEquiv.ofBijective (sigmaHomM n c) (sigmaHomM n c).bijective

@[simp] theorem sigmaMe_wr (c : (ZMod n)ˣ) :
    sigmaMe n c (wr n) = wr n ^ cnat n c * hM n c := by
  simp only [sigmaMe, AlgEquiv.coe_ofBijective, sigmaHomM, wr, AdjoinRoot.liftAlgHom_root]

@[simp] theorem sigmaMe_algebraMap (c : (ZMod n)ˣ) (x : EE n) :
    sigmaMe n c (algebraMap (EE n) (MM n) x) = algebraMap (EE n) (MM n) (sigmaE n c x) := by
  rw [sigmaMe, AlgEquiv.coe_ofBijective, sigmaHomM, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]
  rfl

/-- Two ring maps out of `M` agreeing on `K(u)` and on `w` agree. -/
theorem ringHom_ext_M {φ ψ : MM n →+* MM n}
    (hbase : ∀ x : EE n, φ (algebraMap (EE n) (MM n) x) = ψ (algebraMap (EE n) (MM n) x))
    (hw : φ (wr n) = ψ (wr n)) (y : MM n) : φ y = ψ y := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  induction q using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | monomial i c =>
      have hmk : AdjoinRoot.mk ((X : (EE n)[X]) ^ n - C (gE n)) (Polynomial.monomial i c)
          = algebraMap (EE n) (MM n) c * wr n ^ i := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
        rfl
      rw [hmk, map_mul, map_mul, map_pow, map_pow, hbase, hw]

/-- An automorphism of `M` over `ℚ(u)` is determined by its restriction to `K(u)` and its value
on `w`. -/
theorem algEquiv_ext_M {f g : MM n ≃ₐ[FF] MM n}
    (hbase : ∀ x : EE n, f (algebraMap (EE n) (MM n) x) = g (algebraMap (EE n) (MM n) x))
    (hw : f (wr n) = g (wr n)) : f = g :=
  AlgEquiv.ext fun y =>
    ringHom_ext_M n (φ := (f : MM n →+* MM n)) (ψ := (g : MM n →+* MM n)) hbase hw y

theorem sigmaMe_one : sigmaMe n 1 = 1 := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [sigmaMe_algebraMap, map_one, AlgEquiv.one_apply, AlgEquiv.one_apply]
  · rw [sigmaMe_wr, cnat_one, pow_one, hM, hE_one, map_one, mul_one, AlgEquiv.one_apply]

theorem sigmaMe_mul (c d : (ZMod n)ˣ) : sigmaMe n (c * d) = sigmaMe n c * sigmaMe n d := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, sigmaMe_algebraMap, sigmaMe_algebraMap, sigmaMe_algebraMap, map_mul,
      AlgEquiv.mul_apply]
  · have hcoc := congrArg (algebraMap (EE n) (MM n)) (hE_cocycle n c d)
    rw [map_mul, map_mul, map_zpow₀, map_pow, ← wr_pow] at hcoc
    have hpow : wr n ^ (cnat n c * cnat n d)
        = wr n ^ cnat n (c * d) * (wr n ^ n) ^ kk n c d := by
      rw [← zpow_natCast (wr n) (cnat n c * cnat n d), ← zpow_natCast (wr n) (cnat n (c * d)),
        ← zpow_natCast (wr n) n, ← zpow_mul, ← zpow_add₀ (wr_ne_zero n)]
      congr 1
      have h := n_mul_kk n c d
      push_cast
      linarith
    simp only [AlgEquiv.mul_apply, sigmaMe_wr, hM, map_mul, map_pow, sigmaMe_algebraMap]
    rw [mul_pow, ← pow_mul, hpow, ← hcoc]
    ring

/-- **The lifted cyclotomic character**: a homomorphism from the units of `ℤ/n` to the
automorphism group of `M / ℚ(u)`. -/
def sigmaM : (ZMod n)ˣ →* (MM n ≃ₐ[FF] MM n) where
  toFun := sigmaMe n
  map_one' := sigmaMe_one n
  map_mul' := sigmaMe_mul n

@[simp] theorem sigmaM_apply (c : (ZMod n)ˣ) : sigmaM n c = sigmaMe n c := rfl

theorem sigmaM_injective : Function.Injective (sigmaM n) := by
  intro c d h
  refine sigmaE_injective n (AlgEquiv.ext fun x => ?_)
  refine (algebraMap (EE n) (MM n)).injective ?_
  rw [← sigmaMe_algebraMap, ← sigmaMe_algebraMap, ← sigmaM_apply, ← sigmaM_apply, h]

instance finite_range_sigmaM : Finite ↥(MonoidHom.range (sigmaM n)) :=
  Finite.of_equiv _ (MonoidHom.ofInjective (sigmaM_injective n)).toEquiv

theorem card_range_sigmaM : Nat.card ↥(MonoidHom.range (sigmaM n)) = n.totient := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (sigmaM_injective n)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### The fixed fields -/

/-- A subfield over which the whole extension has the same degree is the base field. -/
private theorem eq_bot_of_finrank_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (S : IntermediateField F E)
    (h : Module.finrank S E = Module.finrank F E) : S = ⊥ := by
  have hmul := Module.finrank_mul_finrank F S E
  rw [h] at hmul
  refine IntermediateField.finrank_eq_one_iff.mp
    (Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := F) (M := E)) ?_)
  rw [one_mul]
  exact hmul

/-- `ζ` comes from `K(u)`. -/
theorem zetaM_eq : zetaM n = algebraMap (EE n) (MM n) (algebraMap (KK n) (EE n) (zeta n)) := by
  rw [zetaM, ← IsScalarTower.algebraMap_apply]

@[simp] theorem tau_zetaM : tau n (zetaM n) = zetaM n := by
  rw [zetaM_eq]; exact (tau n).commutes _

theorem tau_pow_wr (m : ℕ) : (tau n ^ m) (wr n) = zetaM n ^ m * wr n := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' (tau n) k, AlgEquiv.mul_apply, ih, map_mul, map_pow, tau_zetaM, tau_wr,
        pow_succ (zetaM n) k]
      ring

theorem tau_pow_eq_one_iff (m : ℕ) : tau n ^ m = 1 ↔ n ∣ m := by
  constructor
  · intro h
    have hz : zetaM n ^ m * wr n = wr n := by
      rw [← tau_pow_wr, h, AlgEquiv.one_apply]
    have hz1 : zetaM n ^ m = 1 :=
      mul_right_cancel₀ (wr_ne_zero n) (by rw [hz, one_mul])
    exact (zetaM_pow_eq_one_iff n m).mp hz1
  · intro h
    refine AlgEquiv.coe_algHom_injective (AdjoinRoot.algHom_ext ?_)
    show (tau n ^ m) (wr n) = (1 : MM n ≃ₐ[EE n] MM n) (wr n)
    rw [tau_pow_wr, (zetaM_pow_eq_one_iff n m).mpr h, one_mul, AlgEquiv.one_apply]

theorem orderOf_tau : orderOf (tau n) = n :=
  Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((tau_pow_eq_one_iff n n).mpr dvd_rfl))
    ((tau_pow_eq_one_iff n (orderOf (tau n))).mp (pow_orderOf_eq_one _))

theorem fixedField_tau : IntermediateField.fixedField (Subgroup.zpowers (tau n)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tau, finrank_EE_MM]

/-- **An element of `M` fixed by the Kummer automorphism lies in `K(u)`.** -/
theorem exists_of_tau_fixed {x : MM n} (hx : tau n x = x) :
    ∃ y : EE n, algebraMap (EE n) (MM n) y = x := by
  have hle : Subgroup.zpowers (tau n) ≤ MulAction.stabilizer (MM n ≃ₐ[EE n] MM n) x :=
    Subgroup.zpowers_le.mpr hx
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tau n)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_tau, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### The Galois group of `M / ℚ(u)` -/

/-- `τ`, as an automorphism of `M` over `ℚ(u)`. -/
def tauF : MM n ≃ₐ[FF] MM n := AlgEquiv.restrictScalars FF (tau n)

@[simp] theorem tauF_apply (x : MM n) : tauF n x = tau n x := rfl

@[simp] theorem tau_hM (c : (ZMod n)ˣ) : tau n (hM n c) = hM n c := by
  rw [hM]; exact (tau n).commutes _

@[simp] theorem sigmaMe_zetaM (c : (ZMod n)ˣ) :
    sigmaMe n c (zetaM n) = zetaM n ^ cnat n c := by
  rw [zetaM_eq, sigmaMe_algebraMap, sigmaE_algebraMap, sigmaK_zeta, map_pow, map_pow]

/-- **The two families of automorphisms commute**: the exponent in the lift of `c` is the
cyclotomic character of `c`. -/
theorem commute_tauF_sigmaM (c : (ZMod n)ˣ) : tauF n * sigmaMe n c = sigmaMe n c * tauF n := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaMe_algebraMap, tauF_apply, (tau n).commutes,
      tauF_apply, (tau n).commutes, sigmaMe_algebraMap]
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaMe_wr, tauF_apply, map_mul, map_pow, tau_wr,
      tau_hM, tauF_apply, tau_wr, map_mul, sigmaMe_zetaM, sigmaMe_wr, mul_pow]
    ring

/-! ### The degree-`n` layer -/

/-- **The degree-`n` layer**: the fixed field of the lifted cyclotomic character. -/
def LL : IntermediateField FF (MM n) :=
  IntermediateField.fixedField (MonoidHom.range (sigmaM n))

instance (priority := high) smulFFFF : SMul FF FF := instSMulOfMul

instance (priority := high) isScalarTowerFFFFMM : IsScalarTower FF FF (MM n) :=
  ⟨fun a b c => by rw [smul_eq_mul, mul_smul]⟩

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) algFFLL : Algebra FF (LL n) := IntermediateField.algebra' (LL n)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) isScalarTowerFFLLMM : IsScalarTower FF (LL n) (MM n) :=
  IntermediateField.isScalarTower_mid' (LL n)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) finiteDimensionalFFLL : FiniteDimensional FF (LL n) :=
  IntermediateField.finiteDimensional_left (LL n)

theorem mem_LL_iff {x : MM n} : x ∈ LL n ↔ ∀ c, sigmaMe n c x = x := by
  rw [LL, IntermediateField.mem_fixedField_iff]
  refine ⟨fun hx c => hx (sigmaM n c) ⟨c, rfl⟩, fun hx f hf => ?_⟩
  obtain ⟨c, rfl⟩ := hf
  exact hx c

theorem finrank_LL_MM : Module.finrank (LL n) (MM n) = n.totient := by
  rw [LL, IntermediateField.finrank_fixedField_eq_card, card_range_sigmaM]

theorem finrank_FF_LL : Module.finrank FF (LL n) = n := by
  have h := Module.finrank_mul_finrank FF (LL n) (MM n)
  rw [finrank_LL_MM, finrank_FF_MM, Nat.mul_comm n.totient n] at h
  exact Nat.eq_of_mul_eq_mul_right (totient_pos n) h

theorem tauF_mem_LL {x : MM n} (hx : x ∈ LL n) : tauF n x ∈ LL n := by
  rw [mem_LL_iff] at hx ⊢
  intro c
  have h := congrArg (fun e : MM n ≃ₐ[FF] MM n => e x) (commute_tauF_sigmaM n c)
  simp only [AlgEquiv.mul_apply] at h
  rw [← h, hx]

/-- `τ`, viewed as an endomorphism of the degree-`n` layer. -/
def tauLHom : LL n →ₐ[FF] LL n where
  toFun x := ⟨tauF n (x : MM n), tauF_mem_LL n x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (by
    show tauF n ((algebraMap FF (LL n) r : LL n) : MM n)
      = ((algebraMap FF (LL n) r : LL n) : MM n)
    rw [IntermediateField.coe_algebraMap_apply]
    exact (tauF n).commutes r)

/-- `τ`, as an automorphism of the degree-`n` layer over `ℚ(u)`. -/
def tauL : LL n ≃ₐ[FF] LL n := AlgEquiv.ofBijective (tauLHom n) (tauLHom n).bijective

@[simp] theorem tauL_apply (x : LL n) : (tauL n x : MM n) = tauF n (x : MM n) := rfl

theorem fixedField_tauL : IntermediateField.fixedField (Subgroup.zpowers (tauL n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hfix : tauF n (x : MM n) = (x : MM n) := by
    have h := hx (tauL n) (Subgroup.mem_zpowers _)
    exact congrArg (Subtype.val) h
  obtain ⟨y, hy⟩ := exists_of_tau_fixed n hfix
  have hyfix : ∀ c, sigmaE n c y = y := by
    intro c
    refine (algebraMap (EE n) (MM n)).injective ?_
    rw [← sigmaMe_algebraMap, hy]
    exact (mem_LL_iff n).mp x.2 c
  obtain ⟨z, hz⟩ := exists_of_sigmaE_fixed n hyfix
  refine IntermediateField.mem_bot.mpr ⟨z, Subtype.ext ?_⟩
  rw [IntermediateField.coe_algebraMap_apply, ← hy, ← hz, ← IsScalarTower.algebraMap_apply]

theorem fixedField_top_LL :
    IntermediateField.fixedField (⊤ : Subgroup (LL n ≃ₐ[FF] LL n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tauL n)) := by
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun f _ => hx f (Subgroup.mem_top f)
  rwa [fixedField_tauL] at hmem

instance isGalois_FF_LL : IsGalois FF (LL n) :=
  IsGalois.of_fixedField_eq_bot FF (LL n) (fixedField_top_LL n)

/-- **The layer is a degree-`n` Galois extension of `ℚ(u)`.** -/
theorem card_aut_LL : Nat.card (LL n ≃ₐ[FF] LL n) = n := by
  rw [IsGalois.card_aut_eq_finrank, finrank_FF_LL]

theorem zpowers_tauL_top : Subgroup.zpowers (tauL n) = ⊤ := by
  have h := IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (tauL n))
  rw [fixedField_tauL, IntermediateField.fixingSubgroup_bot] at h
  exact h.symm

theorem orderOf_tauL : orderOf (tauL n) = n := by
  have h : Nat.card ↥(Subgroup.zpowers (tauL n)) = Nat.card (LL n ≃ₐ[FF] LL n) := by
    rw [zpowers_tauL_top]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [Nat.card_zpowers] at h
  rw [h, card_aut_LL]

/-! ### The involution -/

/-- A ring map out of `K(u)` is determined by its restriction to `K` and its value at the
parameter. -/
theorem ringHom_ext_EE {L : Type*} [Field L] {φ ψ : EE n →+* L}
    (hC : ∀ a : KK n, φ (algebraMap (KK n) (EE n) a) = ψ (algebraMap (KK n) (EE n) a))
    (hX : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  refine IsFractionRing.ringHom_ext (A := (KK n)[X]) fun p => ?_
  have h : φ.comp (algebraMap (KK n)[X] (EE n)) = ψ.comp (algebraMap (KK n)[X] (EE n)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← algebraMap_KK_EE, hC]
    · rw [RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_X, hX]
  exact congrArg (fun f : (KK n)[X] →+* L => f p) h

theorem sigmaE_X (c : (ZMod n)ˣ) : sigmaE n c (RatFunc.X : EE n) = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, Rigidity.RET.Cyclic.sigmaE_algebraMap_poly, Polynomial.map_X]

/-- **The coefficient action and the substitution `u ↦ -u` commute**: one moves the constants,
the other moves the parameter. -/
theorem rhoE_sigmaE (c : (ZMod n)ˣ) (x : EE n) :
    rhoE n (sigmaE n c x) = sigmaE n c (rhoE n x) := by
  have h : ((rhoE n : EE n ≃+* EE n).toRingHom.comp (sigmaE n c : EE n ≃+* EE n).toRingHom)
      = ((sigmaE n c : EE n ≃+* EE n).toRingHom.comp (rhoE n : EE n ≃+* EE n).toRingHom) := by
    refine ringHom_ext_EE n (fun a => ?_) ?_
    · show rhoE n (sigmaE n c (algebraMap (KK n) (EE n) a))
        = sigmaE n c (rhoE n (algebraMap (KK n) (EE n) a))
      rw [Rigidity.RET.Cyclic.sigmaE_algebraMap, (rhoE n).commutes, (rhoE n).commutes,
        Rigidity.RET.Cyclic.sigmaE_algebraMap]
    · show rhoE n (sigmaE n c RatFunc.X) = sigmaE n c (rhoE n RatFunc.X)
      rw [sigmaE_X, rhoE, ratFuncNeg_X, map_neg, sigmaE_X]
  exact congrArg (fun f : EE n →+* EE n => f x) h

/-- The flip identity for the twisting factors, cleared of denominators. -/
theorem rhoE_hE_nat (c : (ZMod n)ˣ) :
    rhoE n (hE n c) * hE n c * mmE n ^ cnat n c = mmE n := by
  rw [rhoE_hE, ← zpow_natCast (mmE n) (cnat n c), ← zpow_add₀ (mmE_ne_zero n),
    show (1 - (cnat n c : ℤ)) + (cnat n c : ℤ) = 1 by ring, zpow_one]

theorem zetaM_ne_zero : zetaM n ≠ 0 := by
  intro h
  have h1 := zetaM_pow n
  rw [h, zero_pow (by have := hn.out; omega)] at h1
  exact zero_ne_one h1

@[simp] theorem tau_mmM : tau n (mmM n) = mmM n := by rw [mmM]; exact (tau n).commutes _

@[simp] theorem sigmaMe_mmM (c : (ZMod n)ˣ) : sigmaMe n c (mmM n) = mmM n := by
  rw [mmM, sigmaMe_algebraMap, sigmaE_mmE]

/-- The involution `w ↦ m / w`, `u ↦ -u`, as an algebra map over the constants. -/
def iotaHom : MM n →ₐ[KK n] MM n :=
  AdjoinRoot.liftAlgHom ((X : (EE n)[X]) ^ n - C (gE n))
    ((IsScalarTower.toAlgHom (KK n) (EE n) (MM n)).comp (rhoE n).toAlgHom)
    (mmM n * (wr n)⁻¹)
    (eval₂_kummer n (by
      show (mmM n * (wr n)⁻¹) ^ n = algebraMap (EE n) (MM n) (rhoE n (gE n))
      have hwn : wr n ^ n ≠ 0 := pow_ne_zero _ (wr_ne_zero n)
      have hg : algebraMap (EE n) (MM n) (rhoE n (gE n)) * wr n ^ n = mmM n ^ n := by
        have h := congrArg (algebraMap (EE n) (MM n)) (rhoE_gE n)
        rw [map_mul, map_pow, ← wr_pow] at h
        exact h
      rw [mul_pow, inv_pow, ← hg, mul_assoc, mul_inv_cancel₀ hwn, mul_one]))

@[simp] theorem iotaHom_algebraMap (x : EE n) :
    iotaHom n (algebraMap (EE n) (MM n) x) = algebraMap (EE n) (MM n) (rhoE n x) := by
  rw [iotaHom, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]
  rfl

@[simp] theorem iotaHom_wr : iotaHom n (wr n) = mmM n * (wr n)⁻¹ := by
  simp only [iotaHom, wr, AdjoinRoot.liftAlgHom_root]

@[simp] theorem iotaHom_mmM : iotaHom n (mmM n) = mmM n := by
  rw [mmM, iotaHom_algebraMap, rhoE_mmE]

@[simp] theorem iotaHom_zetaM : iotaHom n (zetaM n) = zetaM n := by
  rw [zetaM]; exact (iotaHom n).commutes _

/-- **The involution squares to the identity.** -/
theorem iotaHom_iotaHom (y : MM n) : iotaHom n (iotaHom n y) = y := by
  refine ringHom_ext_M n (φ := ((iotaHom n).comp (iotaHom n)).toRingHom)
    (ψ := RingHom.id (MM n)) (fun x => ?_) ?_ y
  · show iotaHom n (iotaHom n (algebraMap (EE n) (MM n) x)) = algebraMap (EE n) (MM n) x
    rw [iotaHom_algebraMap, iotaHom_algebraMap, rhoE, ratFuncNeg_ratFuncNeg]
  · show iotaHom n (iotaHom n (wr n)) = wr n
    rw [iotaHom_wr, map_mul, map_inv₀, iotaHom_wr, iotaHom_mmM, mul_inv, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ (mmM_ne_zero n), one_mul]

/-- **The involution commutes with the lifted cyclotomic character**, so it preserves the
degree-`n` layer. -/
theorem iotaHom_sigmaMe (c : (ZMod n)ˣ) (y : MM n) :
    iotaHom n (sigmaMe n c y) = sigmaMe n c (iotaHom n y) := by
  refine ringHom_ext_M n
    (φ := (iotaHom n).toRingHom.comp (sigmaMe n c : MM n ≃+* MM n).toRingHom)
    (ψ := (sigmaMe n c : MM n ≃+* MM n).toRingHom.comp (iotaHom n).toRingHom) (fun x => ?_) ?_ y
  · show iotaHom n (sigmaMe n c (algebraMap (EE n) (MM n) x))
      = sigmaMe n c (iotaHom n (algebraMap (EE n) (MM n) x))
    rw [sigmaMe_algebraMap, iotaHom_algebraMap, iotaHom_algebraMap, sigmaMe_algebraMap,
      rhoE_sigmaE]
  · show iotaHom n (sigmaMe n c (wr n)) = sigmaMe n c (iotaHom n (wr n))
    have key : iotaHom n (hM n c) * hM n c * mmM n ^ cnat n c = mmM n := by
      have h := congrArg (algebraMap (EE n) (MM n)) (rhoE_hE_nat n c)
      rw [map_mul, map_mul, map_pow] at h
      rw [hM, iotaHom_algebraMap, mmM]
      exact h
    have hwk : wr n ^ cnat n c ≠ 0 := pow_ne_zero _ (wr_ne_zero n)
    have hh0 : hM n c ≠ 0 := hM_ne_zero n c
    simp only [sigmaMe_wr, iotaHom_wr, map_mul, map_pow, map_inv₀, sigmaMe_mmM]
    refine mul_right_cancel₀ (mul_ne_zero hwk hh0) ?_
    calc (mmM n * (wr n)⁻¹) ^ cnat n c * iotaHom n (hM n c) * (wr n ^ cnat n c * hM n c)
        = mmM n ^ cnat n c * ((wr n ^ cnat n c)⁻¹ * wr n ^ cnat n c)
            * (iotaHom n (hM n c) * hM n c) := by
          rw [mul_pow, inv_pow]; ring
      _ = mmM n ^ cnat n c * (iotaHom n (hM n c) * hM n c) := by
          rw [inv_mul_cancel₀ hwk, mul_one]
      _ = mmM n := by
          conv_rhs => rw [← key]
          ring
      _ = mmM n * ((wr n ^ cnat n c * hM n c)⁻¹ * (wr n ^ cnat n c * hM n c)) := by
          rw [inv_mul_cancel₀ (mul_ne_zero hwk hh0), mul_one]
      _ = mmM n * (wr n ^ cnat n c * hM n c)⁻¹ * (wr n ^ cnat n c * hM n c) := by ring

/-- **The involution inverts the Kummer automorphism.** -/
theorem iotaHom_tau (y : MM n) : iotaHom n (tau n (iotaHom n y)) = (tau n).symm y := by
  have hz : zetaM n ≠ 0 := zetaM_ne_zero n
  have hm : mmM n ≠ 0 := mmM_ne_zero n
  have hw : wr n ≠ 0 := wr_ne_zero n
  refine ringHom_ext_M n
    (φ := (iotaHom n).toRingHom.comp
      (((tau n : MM n ≃+* MM n).toRingHom).comp (iotaHom n).toRingHom))
    (ψ := ((tau n).symm : MM n ≃+* MM n).toRingHom) (fun x => ?_) ?_ y
  · show iotaHom n (tau n (iotaHom n (algebraMap (EE n) (MM n) x)))
      = (tau n).symm (algebraMap (EE n) (MM n) x)
    rw [iotaHom_algebraMap, (tau n).commutes, iotaHom_algebraMap, rhoE, ratFuncNeg_ratFuncNeg,
      AlgEquiv.commutes]
  · show iotaHom n (tau n (iotaHom n (wr n))) = (tau n).symm (wr n)
    have hsym : (tau n).symm (wr n) = (zetaM n)⁻¹ * wr n := by
      refine ((tau n).symm_apply_eq).mpr ?_
      rw [map_mul, map_inv₀, tau_zetaM, tau_wr, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    rw [hsym, iotaHom_wr]
    simp only [map_mul, map_inv₀, tau_mmM, tau_wr, iotaHom_zetaM, iotaHom_wr, iotaHom_mmM]
    field_simp

/-! ### The involution on the degree-`n` layer -/

theorem iotaHom_mem_LL {x : MM n} (hx : x ∈ LL n) : iotaHom n x ∈ LL n := by
  rw [mem_LL_iff] at hx ⊢
  intro c
  rw [← iotaHom_sigmaMe, hx]

/-- The involution, viewed as an endomorphism of the degree-`n` layer. -/
def iotaLHom : LL n →+* LL n where
  toFun x := ⟨iotaHom n (x : MM n), iotaHom_mem_LL n x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (iotaHom n) (x : MM n) (y : MM n))
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add (iotaHom n) (x : MM n) (y : MM n))

@[simp] theorem iotaLHom_coe (x : LL n) : (iotaLHom n x : MM n) = iotaHom n (x : MM n) := rfl

theorem iotaLHom_iotaLHom (x : LL n) : iotaLHom n (iotaLHom n x) = x :=
  Subtype.ext (iotaHom_iotaHom n (x : MM n))

/-- **The involution of the degree-`n` layer.** -/
def iotaL : LL n ≃+* LL n :=
  RingEquiv.ofBijective (iotaLHom n)
    ⟨fun a b h => by
      have h2 := congrArg (iotaLHom n) h
      rwa [iotaLHom_iotaLHom, iotaLHom_iotaLHom] at h2,
     fun b => ⟨iotaLHom n b, iotaLHom_iotaLHom n b⟩⟩

@[simp] theorem iotaL_coe (x : LL n) : (iotaL n x : MM n) = iotaHom n (x : MM n) := rfl

theorem iotaL_iotaL (x : LL n) : iotaL n (iotaL n x) = x := iotaLHom_iotaLHom n x

/-- **The involution acts on the base by the substitution `u ↦ -u`.** -/
theorem iotaL_algebraMap (z : FF) :
    iotaL n (algebraMap FF (LL n) z) = algebraMap FF (LL n) (rhoF z) := by
  refine Subtype.ext ?_
  rw [iotaL_coe, IntermediateField.coe_algebraMap_apply, IntermediateField.coe_algebraMap_apply,
    IsScalarTower.algebraMap_apply FF (EE n) (MM n),
    IsScalarTower.algebraMap_apply FF (EE n) (MM n), iotaHom_algebraMap, rhoE_algebraMap_FF]

theorem coe_tauL_symm (x : LL n) : ((tauL n).symm x : MM n) = (tau n).symm (x : MM n) := by
  have h := congrArg (Subtype.val) ((tauL n).apply_symm_apply x)
  rw [tauL_apply, tauF_apply] at h
  exact ((tau n).eq_symm_apply).mpr h

/-- **The involution inverts the Kummer automorphism of the layer.** -/
theorem iotaL_tauL (x : LL n) : iotaL n (tauL n (iotaL n x)) = (tauL n).symm x := by
  refine Subtype.ext ?_
  rw [iotaL_coe, tauL_apply, tauF_apply, iotaL_coe, iotaHom_tau, coe_tauL_symm]

/-! ### The constants of the Kummer extension -/

/-- `g`, read over the algebraic closure of `K`. -/
def gbar : (Kbar n)[X] := (gpoly n).map (algebraMap (KK n) (Kbar n))

theorem gbar_eq : gbar n
    = ∏ j : JJ n, (X - C (algebraMap (KK n) (Kbar n) (rt n j))) ^ anat n j := by
  rw [gbar, gpoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun j _ => by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- The simple root of `g` survives the passage to the algebraic closure. -/
theorem rootMultiplicity_gbar :
    (gbar n).rootMultiplicity (algebraMap (KK n) (Kbar n) (-zeta n)) = 1 := by
  have hinj : Function.Injective (fun j => algebraMap (KK n) (Kbar n) (rt n j)) :=
    fun _ _ h => rt_injective n ((algebraMap (KK n) (Kbar n)).injective h)
  rw [gbar_eq, ← rt_one_one n]
  exact (rootMultiplicity_prod_pow (fun j => algebraMap (KK n) (Kbar n) (rt n j)) hinj
    (anat n) ((1 : ZMod 2), (1 : (ZMod n)ˣ))).trans (anat_one n)

theorem algebraMap_gE_geom :
    algebraMap (EE n) (GG n) (gE n) = algebraMap (Kbar n)[X] (GG n) (gbar n) :=
  Rigidity.RET.algebraMap_ratFunc_ratFunc (k := KK n) (K := Kbar n) (gpoly n)

/-- The Kummer polynomial stays irreducible over `K̄(u)`: the extension is geometric. -/
theorem kummer_irreducible_geom :
    Irreducible (((X : (EE n)[X]) ^ n - C (gE n)).map (algebraMap (EE n) (GG n))) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    algebraMap_gE_geom]
  exact irreducible_X_pow_sub_C_ratFunc (rootMultiplicity_gbar n) (by have := hn.out; omega)

theorem minpoly_wr : minpoly (EE n) (wr n) = (X : (EE n)[X]) ^ n - C (gE n) := by
  have hm : ((X : (EE n)[X]) ^ n - C (gE n)).Monic :=
    monic_X_pow_sub_C (gE n) (by have := hn.out; omega)
  rw [wr, AdjoinRoot.minpoly_root (kummer_ne_zero n), hm.leadingCoeff, inv_one, map_one, mul_one]

theorem adjoin_wr_top : IntermediateField.adjoin (EE n) ({wr n} : Set (MM n)) = ⊤ := by
  refine top_unique fun x _ => ?_
  have h : x ∈ Algebra.adjoin (EE n) ({wr n} : Set (MM n)) := by
    rw [wr, AdjoinRoot.adjoinRoot_eq_top]
    trivial
  exact IntermediateField.algebra_adjoin_le_adjoin (EE n) _ h

/-- **The constants of `M` are exactly `K`**: the Kummer extension is geometric over `K`. -/
theorem algebraicClosure_KK_MM : algebraicClosure (KK n) (MM n) = ⊥ :=
  Rigidity.RET.algebraicClosure_eq_bot_of_isField_tensor (F := KK n) (K := EE n) (K' := GG n)
    (L := MM n) (splits_geom n) (Rigidity.RET.algebraicClosure_ratFunc (KK n))
    (Rigidity.RET.isField_tensor_of_primitive_irreducible (MM n) (wr n) (adjoin_wr_top n)
      (by rw [minpoly_wr]; exact kummer_irreducible_geom n))

theorem exists_const_of_isIntegral {y : MM n} (hy : IsIntegral (KK n) y) :
    ∃ a : KK n, algebraMap (KK n) (MM n) a = y := by
  have hmem : y ∈ algebraicClosure (KK n) (MM n) := mem_algebraicClosure_iff'.mpr hy
  rw [algebraicClosure_KK_MM, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### Regularity of the layer -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The layer sits over `ℚ` through `ℚ(u)`; a shortcut for a slow instance search. -/
instance (priority := high) isScalarTowerQFFLL : IsScalarTower ℚ FF ↥(LL n) := inferInstance

/-- The two routes from `ℚ` into `M`, through the constants and through `ℚ(u)`, agree. -/
theorem rationalMaps_eq :
    (algebraMap (KK n) (MM n)).comp (algebraMap ℚ (KK n))
      = (algebraMap FF (MM n)).comp (algebraMap ℚ FF) :=
  Subsingleton.elim _ _

set_option synthInstance.maxHeartbeats 400000 in
/-- The two routes from `ℚ` into `M`, through the layer and through the constants, agree. -/
theorem rationalMaps_LL :
    (algebraMap ↥(LL n) (MM n)).comp (algebraMap ℚ ↥(LL n))
      = (algebraMap (KK n) (MM n)).comp (algebraMap ℚ (KK n)) :=
  Subsingleton.elim _ _

theorem sigmaMe_algebraMap_KK (c : (ZMod n)ˣ) (a : KK n) :
    sigmaMe n c (algebraMap (KK n) (MM n) a) = algebraMap (KK n) (MM n) (sigmaK n c a) := by
  rw [IsScalarTower.algebraMap_apply (KK n) (EE n) (MM n),
    IsScalarTower.algebraMap_apply (KK n) (EE n) (MM n), sigmaMe_algebraMap,
    Rigidity.RET.Cyclic.sigmaE_algebraMap]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The layer is regular**: it gains no constants over `ℚ`. -/
theorem regular_LL : algebraicClosure ℚ ↥(LL n) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.mp hx
  have hpm : (minpoly ℚ x).Monic := minpoly.monic hxint
  have hpx : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  have hPx : aeval x ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hpx
  have hPy : aeval (x : MM n) ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    have hval := Polynomial.aeval_algHom_apply (LL n).val x ((minpoly ℚ x).map (algebraMap ℚ FF))
    rw [hPx, map_zero] at hval
    exact hval
  have hyint : IsIntegral (KK n) (x : MM n) := by
    refine ⟨(minpoly ℚ x).map (algebraMap ℚ (KK n)), hpm.map _, ?_⟩
    rw [eval₂_map, rationalMaps_eq, ← eval₂_map]
    exact hPy
  obtain ⟨a, ha⟩ := exists_const_of_isIntegral n hyint
  have hfix : ∀ f : KK n ≃ₐ[ℚ] KK n, f a = a := by
    intro f
    obtain ⟨c, rfl⟩ := sigmaK_surjective n f
    refine (algebraMap (KK n) (MM n)).injective ?_
    rw [← sigmaMe_algebraMap_KK, ha]
    exact (mem_LL_iff n).mp x.2 c
  have hmem : a ∈ (⊥ : IntermediateField ℚ (KK n)) := (IsGalois.mem_bot_iff_fixed a).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  refine IntermediateField.mem_bot.mpr ⟨q, Subtype.ext ?_⟩
  have h1 : ((algebraMap ℚ ↥(LL n) q : ↥(LL n)) : MM n)
      = (algebraMap ↥(LL n) (MM n)).comp (algebraMap ℚ ↥(LL n)) q := rfl
  rw [h1, rationalMaps_LL, RingHom.comp_apply, hq, ha]

/-! ### The base field `ℚ(u²)` -/

theorem rhoF_mul_rhoF : rhoF * rhoF = 1 :=
  RingEquiv.ext fun x => rhoF_rhoF x

theorem rhoF_ne_one : rhoF ≠ 1 := by
  obtain ⟨x, hx⟩ := rhoF_ne_id
  intro h
  exact hx (congrArg (fun f : RingAut FF => f x) h)

theorem orderOf_rhoF : orderOf rhoF = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact rhoF_mul_rhoF) rhoF_ne_one

/-- The two-element group of substitutions `u ↦ ± u`. -/
def rhoSub : Subgroup (RingAut FF) := Subgroup.zpowers rhoF

instance mulSemiringActionRhoSub : MulSemiringAction ↥rhoSub FF :=
  MulSemiringAction.compHom _ rhoSub.subtype

instance : Finite ↥rhoSub :=
  Nat.finite_of_card_ne_zero (by rw [rhoSub, Nat.card_zpowers, orderOf_rhoF]; norm_num)

instance : FaithfulSMul ↥rhoSub FF :=
  ⟨fun {_ _} h => Subtype.ext (RingEquiv.ext fun x => h x)⟩

theorem rhoSub_fix : ∀ (g : ↥rhoSub) (c : ℚ), g • (RatFunc.C c : FF) = RatFunc.C c := by
  intro g c
  rw [eq_ratCast (RatFunc.C : ℚ →+* FF) c]
  exact map_ratCast (MulSemiringAction.toRingEquiv _ _ g) c

/-- **The base field** `ℚ(u²)`: the invariants of the substitution `u ↦ -u`. -/
abbrev B0 := Rigidity.RET.fixedField rhoSub_fix

theorem mem_B0 {x : FF} : x ∈ B0 ↔ rhoF x = x := by
  constructor
  · intro hx
    exact hx ⟨rhoF, Subgroup.mem_zpowers rhoF⟩
  · intro hx g
    have hle : rhoSub ≤ MulAction.stabilizer (RingAut FF) x := Subgroup.zpowers_le.mpr hx
    exact hle g.2

instance : Fintype ↥rhoSub := Fintype.ofFinite _

theorem card_rhoSub : Fintype.card ↥rhoSub = 2 := by
  rw [← Nat.card_eq_fintype_card, rhoSub, Nat.card_zpowers, orderOf_rhoF]

theorem finrank_B0_FF : Module.finrank ↥B0 FF = 2 :=
  (Rigidity.RET.finrank_fixedField rhoSub_fix).trans card_rhoSub

/-- The degree-`n` layer is finite over the base field. -/
instance finiteDimensionalB0LL : FiniteDimensional ↥B0 ↥(LL n) :=
  Module.Finite.trans (R := ↥B0) FF ↥(LL n)

theorem finrank_B0_LL : Module.finrank ↥B0 ↥(LL n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ↥B0 FF ↥(LL n), finrank_B0_FF, finrank_FF_LL]

/-- The Kummer automorphism of the layer, over the base field. -/
def tauB : LL n ≃ₐ[↥B0] LL n := AlgEquiv.restrictScalars ↥B0 (tauL n)

@[simp] theorem tauB_apply (x : LL n) : tauB n x = tauL n x := rfl

/-- The involution of the layer, over the base field. -/
def iotaB : LL n ≃ₐ[↥B0] LL n :=
  AlgEquiv.ofRingEquiv (f := iotaL n) (fun z => by
    have h : algebraMap ↥B0 ↥(LL n) z = algebraMap FF ↥(LL n) (z : FF) :=
      IsScalarTower.algebraMap_apply ↥B0 FF ↥(LL n) z
    rw [h, iotaL_algebraMap, mem_B0.mp z.2])

@[simp] theorem iotaB_apply (x : LL n) : iotaB n x = iotaL n x := rfl

theorem tauB_pow_apply (m : ℕ) : ∀ x : LL n, (tauB n ^ m) x = (tauL n ^ m) x := by
  induction m with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, tauB_apply, ih]

theorem tauB_pow_eq_one_iff (m : ℕ) : tauB n ^ m = 1 ↔ tauL n ^ m = 1 := by
  constructor
  · intro h
    refine AlgEquiv.ext fun x => ?_
    rw [← tauB_pow_apply, h, AlgEquiv.one_apply, AlgEquiv.one_apply]
  · intro h
    refine AlgEquiv.ext fun x => ?_
    rw [tauB_pow_apply, h, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem tauB_pow_n : tauB n ^ n = 1 :=
  (tauB_pow_eq_one_iff n n).mpr
    (orderOf_dvd_iff_pow_eq_one.mp (by rw [orderOf_tauL]))

theorem orderOf_tauB : orderOf (tauB n) = n := by
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (tauB_pow_n n)) ?_
  have h : tauL n ^ orderOf (tauB n) = 1 := (tauB_pow_eq_one_iff n _).mp (pow_orderOf_eq_one _)
  have h2 := orderOf_dvd_of_pow_eq_one h
  rwa [orderOf_tauL] at h2

theorem iotaB_mul_iotaB : iotaB n * iotaB n = 1 :=
  AlgEquiv.ext fun x => by
    rw [AlgEquiv.mul_apply, iotaB_apply, iotaB_apply, iotaL_iotaL, AlgEquiv.one_apply]

/-- **The involution inverts the rotation.** -/
theorem iotaB_conj : iotaB n * tauB n * (iotaB n)⁻¹ = (tauB n)⁻¹ := by
  have hinv : (iotaB n)⁻¹ = iotaB n := inv_eq_of_mul_eq_one_right (iotaB_mul_iotaB n)
  rw [hinv]
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, iotaB_apply, tauB_apply, iotaB_apply, iotaL_tauL]
  rfl

theorem iotaB_ne_tauB_pow (m : ℕ) : iotaB n ≠ tauB n ^ m := by
  obtain ⟨z, hz⟩ := rhoF_ne_id
  intro h
  have h1 : iotaB n (algebraMap FF ↥(LL n) z) = (tauB n ^ m) (algebraMap FF ↥(LL n) z) := by
    rw [h]
  rw [iotaB_apply, iotaL_algebraMap, tauB_pow_apply, (tauL n ^ m).commutes] at h1
  exact hz ((algebraMap FF ↥(LL n)).injective h1)

/-- **The dihedral group, realized inside the automorphisms of the layer.** -/
def dihedralHom : DihedralGroup n →* (LL n ≃ₐ[↥B0] LL n) :=
  Rigidity.RET.dihedralLift (tauB_pow_n n) (iotaB_mul_iotaB n) (iotaB_conj n)

theorem dihedralHom_injective : Function.Injective (dihedralHom n) :=
  Rigidity.RET.dihedralLift_injective _ _ _ (orderOf_tauB n) fun m _ => iotaB_ne_tauB_pow n m

/-! ### The Galois group of the layer over the base -/

theorem fixedField_top_B0 :
    IntermediateField.fixedField (⊤ : Subgroup (LL n ≃ₐ[↥B0] LL n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hfix : tauL n x = x := by
    have h := hx (tauB n) (Subgroup.mem_top _)
    rwa [tauB_apply] at h
  have hle : Subgroup.zpowers (tauL n) ≤ MulAction.stabilizer (LL n ≃ₐ[FF] LL n) x :=
    Subgroup.zpowers_le.mpr hfix
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tauL n)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_tauL, IntermediateField.mem_bot] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hi : iotaL n x = x := by
    have h := hx (iotaB n) (Subgroup.mem_top _)
    rwa [iotaB_apply] at h
  rw [← hz, iotaL_algebraMap] at hi
  have hz2 : rhoF z = z := (algebraMap FF ↥(LL n)).injective hi
  exact IntermediateField.mem_bot.mpr ⟨⟨z, mem_B0.mpr hz2⟩, hz⟩

instance isGalois_B0_LL : IsGalois ↥B0 ↥(LL n) :=
  IsGalois.of_fixedField_eq_bot ↥B0 ↥(LL n) (fixedField_top_B0 n)

theorem card_aut_B0_LL : Nat.card (LL n ≃ₐ[↥B0] LL n) = 2 * n := by
  rw [IsGalois.card_aut_eq_finrank, finrank_B0_LL]

theorem dihedralHom_bijective : Function.Bijective (dihedralHom n) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨dihedralHom_injective n, ?_⟩
  rw [card_aut_B0_LL, Nat.card_eq_fintype_card, DihedralGroup.card]

/-- **The Galois group of the layer over `ℚ(u²)` is the dihedral group of order `2n`.** -/
def dihedralEquiv : DihedralGroup n ≃* (LL n ≃ₐ[↥B0] LL n) :=
  MulEquiv.ofBijective (dihedralHom n) (dihedralHom_bijective n)

/-! ### The regular realization -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **The dihedral group of order `2n` is a regular Galois group over the base `ℚ(u²)`.** -/
theorem isRegularGaloisGroupOverBase_B0 :
    IsRegularGaloisGroupOverBase ℚ ↥B0 (DihedralGroup n) :=
  ⟨↥(LL n), inferInstance, inferInstance, inferInstance, isGalois_B0_LL n, inferInstance,
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _), regular_LL n,
    ⟨(dihedralEquiv n).symm⟩⟩

/-- **The dihedral group of order `2n` is a regular inverse Galois group** for every odd `n > 1`. -/
theorem isRegularInverseGalois_dihedral_odd : IsRegularInverseGalois (DihedralGroup n) := by
  obtain ⟨e⟩ := Rigidity.RET.exists_ringEquiv_fixedField rhoSub_fix
  have ealg : ↥B0 ≃ₐ[ℚ] FF :=
    AlgEquiv.ofRingEquiv (f := e.symm) fun q =>
      congrArg (fun f : ℚ →+* FF => f q)
        (Subsingleton.elim ((e.symm : ↥B0 →+* FF).comp (algebraMap ℚ ↥B0)) (algebraMap ℚ FF))
  exact isRegularInverseGalois_of_overBase _
    (IsRegularGaloisGroupOverBase.of_algEquiv (isRegularGaloisGroupOverBase_B0 n) ealg)

end

end Rigidity.RET.Dihedral

namespace Rigidity.RET

/-- **The dihedral group of order `2n` is a regular inverse Galois group for every odd `n > 1`.**

In particular `DihedralGroup 5`, the symmetry group of the regular pentagon, is the Galois group
of a regular extension of `ℚ(T)`. -/
theorem isRegularInverseGalois_dihedral_of_odd {n : ℕ} (h1 : 1 < n) (hodd : Odd n) :
    IsRegularInverseGalois (DihedralGroup n) :=
  haveI : Fact (1 < n) := ⟨h1⟩
  haveI : Fact (Odd n) := ⟨hodd⟩
  Rigidity.RET.Dihedral.isRegularInverseGalois_dihedral_odd n

/-- **The symmetry group of the regular pentagon is a regular inverse Galois group.** -/
theorem isRegularInverseGalois_dihedral_five : IsRegularInverseGalois (DihedralGroup 5) :=
  isRegularInverseGalois_dihedral_of_odd (by norm_num) (by decide)

end Rigidity.RET
