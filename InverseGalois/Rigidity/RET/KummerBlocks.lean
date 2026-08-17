/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RadicalIndep
import InverseGalois.Rigidity.RET.RegularCyclic

/-!
# Blocks of independent twisted Kummer data over `K(T)`

The cyclic construction of `Rigidity.RET.Cyclic` attaches to the `n`-th cyclotomic field
`K = ℚ(ζ)` a single Kummer datum

`g = ∏_{v : (ℤ/n)ˣ} (T - ζ ^ v) ^ a v`,   `a v = ` the representative of `v⁻¹`,

whose defining property is the twisting identity `c · g = g ^ c * h c ^ n`.  That identity is
what makes the cyclotomic character lift to the Kummer extension, and the exponent vector
`a` is *forced* by it: the coefficient action permutes the linear factors transitively, so the
admissible exponent vectors form a cyclic group.  Producing several **independent** Kummer data
therefore requires several orbits of linear factors.

This file supplies them.  The linear factors are indexed by `k` blocks of units,

`rt (i, v) = (i + 1) · ζ ^ v`,   `(i, v) : Fin k × (ℤ/n)ˣ`,

the positive integer scalars being fixed by the coefficient action and keeping the roots
distinct.  Everything from the cyclic file is then carried over blockwise: the exponent-vector
homomorphism `Φ`, its injectivity, the equivariance `c · Φ e = Φ (e ∘ (·, c⁻¹ * ·))`, the data
`g i` supported on the `i`-th block, the twisting identity and the cocycle identity.

The new ingredient is **multiplicative independence**: a product `∏ g i ^ m i` is an `n`-th power
in `K(T)` only if every `m i` is divisible by `n`.  This is read off from root multiplicities at
the roots `rt (i, 1)`, which lie in a single block each.
-/

open Polynomial

namespace Rigidity.RET.Abel

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

open Rigidity.RET (rootMultiplicity_prod_pow prod_pow_ne_zero)
open Rigidity.RET.Cyclic

variable (n : ℕ) [hn : Fact (1 < n)] (k : ℕ)

/-! ### The blocked set of roots -/

/-- The index set of the linear factors: `k` blocks, each a copy of the units modulo `n`. -/
abbrev JJ : Type := Fin k × (ZMod n)ˣ

/-- The positive integer scalar attached to a block. -/
def bnat (i : Fin k) : ℕ := (i : ℕ) + 1

theorem bnat_ne_zero (i : Fin k) : bnat k i ≠ 0 := Nat.succ_ne_zero _

/-- The root attached to an index: the block scalar times a root of unity. -/
def rtA (j : JJ n k) : KK n := (bnat k j.1 : KK n) * zetaPow n (j.2 : ZMod n)

theorem rtA_pow (j : JJ n k) : rtA n k j ^ n = ((bnat k j.1 : ℕ) : KK n) ^ n := by
  rw [rtA, mul_pow, zetaPow, ← pow_mul, mul_comm ((j.2 : ZMod n)).val n, pow_mul,
    (zeta_spec n).pow_eq_one, one_pow, mul_one]

theorem rtA_injective : Function.Injective (rtA n k) := by
  rintro ⟨i, v⟩ ⟨i', v'⟩ h
  have hp : ((bnat k i : ℕ) : KK n) ^ n = ((bnat k i' : ℕ) : KK n) ^ n := by
    rw [← rtA_pow n k (i, v), ← rtA_pow n k (i', v'), h]
  have hq : bnat k i ^ n = bnat k i' ^ n := by
    have : ((bnat k i ^ n : ℕ) : KK n) = ((bnat k i' ^ n : ℕ) : KK n) := by push_cast; exact hp
    exact Nat.cast_injective this
  have hb : bnat k i = bnat k i' := Nat.pow_left_injective (by have := hn.out; omega) hq
  have hi : i = i' := Fin.ext (by have : (i : ℕ) + 1 = (i' : ℕ) + 1 := hb; omega)
  subst hi
  have hbne : ((bnat k i : ℕ) : KK n) ≠ 0 := Nat.cast_ne_zero.mpr (bnat_ne_zero k i)
  exact Prod.ext rfl (Units.ext (zetaPow_injective n (mul_left_cancel₀ hbne h)))

theorem sigmaK_rtA (c : (ZMod n)ˣ) (j : JJ n k) :
    sigmaK n c (rtA n k j) = rtA n k (j.1, c * j.2) := by
  rw [rtA, rtA, map_mul, map_natCast, sigmaK_zetaPow, Units.val_mul]

/-! ### The exponent-vector homomorphism -/

/-- A linear factor of the blocked Kummer datum, as an element of `K(T)`. -/
def linA (j : JJ n k) : EE n := linF (rtA n k j)

theorem linA_ne_zero (j : JJ n k) : linA n k j ≠ 0 := linF_ne_zero (rtA n k j)

/-- **The exponent-vector homomorphism** `Φ e = ∏ (T - rt j) ^ e j`. -/
def phiA (e : JJ n k → ℤ) : EE n := ∏ j : JJ n k, linA n k j ^ e j

theorem phiA_eq_phiF (e : JJ n k → ℤ) : phiA n k e = phiF (rtA n k) e := rfl

theorem phiA_ne_zero (e : JJ n k → ℤ) : phiA n k e ≠ 0 := phiF_ne_zero _ e

theorem phiA_congr {e₁ e₂ : JJ n k → ℤ} (h : ∀ j, e₁ j = e₂ j) : phiA n k e₁ = phiA n k e₂ :=
  phiF_congr _ h

theorem phiA_zero : phiA n k (fun _ => 0) = 1 := phiF_zero _

theorem phiA_add (e₁ e₂ : JJ n k → ℤ) :
    phiA n k (fun j => e₁ j + e₂ j) = phiA n k e₁ * phiA n k e₂ := phiF_add _ e₁ e₂

theorem phiA_zpow (e : JJ n k → ℤ) (m : ℤ) :
    phiA n k e ^ m = phiA n k (fun j => m * e j) := phiF_zpow _ e m

theorem phiA_prod {ι : Type*} (s : Finset ι) (e : ι → JJ n k → ℤ) :
    ∏ i ∈ s, phiA n k (e i) = phiA n k (fun j => ∑ i ∈ s, e i j) := phiF_prod _ s e

/-- `Φ` of a vector of natural numbers is the image of an honest polynomial. -/
theorem phiA_natCast (A : JJ n k → ℕ) :
    phiA n k (fun j => (A j : ℤ))
      = algebraMap (KK n)[X] (EE n) (∏ j : JJ n k, (X - C (rtA n k j)) ^ A j) :=
  phiF_natCast _ A

/-- **`Φ` is injective**: the exponents are recovered as root multiplicities. -/
theorem exponent_eq_zero_of_phiA_eq_one {e : JJ n k → ℤ} (he : phiA n k e = 1) (j : JJ n k) :
    e j = 0 :=
  eq_zero_of_phiF_eq_one _ (rtA_injective n k) he j

/-! ### The coefficient action on blocked exponent vectors -/

theorem sigmaE_linA (c : (ZMod n)ˣ) (j : JJ n k) :
    sigmaE n c (linA n k j) = linA n k (j.1, c * j.2) := by
  rw [linA, linF, sigmaE_algebraMap_poly, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    linA, linF, RingHom.coe_coe, sigmaK_rtA]

/-- **The coefficient action permutes the exponents**, blockwise. -/
theorem sigmaE_phiA (c : (ZMod n)ˣ) (e : JJ n k → ℤ) :
    sigmaE n c (phiA n k e) = phiA n k (fun j => e (j.1, c⁻¹ * j.2)) := by
  have h1 : sigmaE n c (phiA n k e) = ∏ j : JJ n k, linA n k (j.1, c * j.2) ^ e j := by
    rw [phiA, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [map_zpow₀, sigmaE_linA]
  have h2 : phiA n k (fun j => e (j.1, c⁻¹ * j.2))
      = ∏ j : JJ n k, linA n k (j.1, c * j.2) ^ e j := by
    rw [phiA, ← Equiv.prod_comp ((Equiv.refl (Fin k)).prodCongr (Equiv.mulLeft c))
      (fun j : JJ n k => linA n k j ^ e (j.1, c⁻¹ * j.2))]
    refine Finset.prod_congr rfl fun j _ => ?_
    show linA n k (j.1, c * j.2) ^ e (j.1, c⁻¹ * (c * j.2)) = linA n k (j.1, c * j.2) ^ e j
    rw [inv_mul_cancel_left]
  rw [h1, h2]

/-! ### The blocked Kummer data -/

/-- The exponent vector of the `i`-th datum: the cyclic weights on the `i`-th block, zero
elsewhere. -/
def anatA (i : Fin k) (j : JJ n k) : ℕ := if j.1 = i then anat n j.2 else 0

theorem anatA_self (i : Fin k) : anatA n k i (i, 1) = 1 := by
  rw [anatA, if_pos rfl, anat_one]

/-- The `i`-th Kummer datum, as a polynomial. -/
def gApoly (i : Fin k) : (KK n)[X] := ∏ j : JJ n k, (X - C (rtA n k j)) ^ anatA n k i j

theorem gApoly_ne_zero (i : Fin k) : gApoly n k i ≠ 0 := prod_pow_ne_zero _ _

/-- The `i`-th datum has a **simple** root at `rt (i, 1)`. -/
theorem rootMultiplicity_gApoly (i : Fin k) :
    (gApoly n k i).rootMultiplicity (rtA n k (i, 1)) = 1 := by
  rw [gApoly, rootMultiplicity_prod_pow _ (rtA_injective n k), anatA_self]

/-- The `i`-th Kummer datum, as an element of `K(T)`. -/
def gA (i : Fin k) : EE n := phiA n k (fun j => (anatA n k i j : ℤ))

theorem gA_eq_algebraMap (i : Fin k) :
    gA n k i = algebraMap (KK n)[X] (EE n) (gApoly n k i) := phiA_natCast n k _

theorem gA_eq_phiF (i : Fin k) :
    gA n k i = phiF (rtA n k) (fun j => (anatA n k i j : ℤ)) := rfl

theorem gA_ne_zero (i : Fin k) : gA n k i ≠ 0 := phiA_ne_zero n k _

theorem gA_zpow (i : Fin k) (m : ℤ) :
    gA n k i ^ m = phiA n k (fun j => m * (anatA n k i j : ℤ)) := by
  rw [gA, phiA_zpow]

/-- The twisting factor of the `i`-th datum attached to a unit. -/
def hA (i : Fin k) (c : (ZMod n)ˣ) : EE n :=
  phiA n k (fun j => if j.1 = i then hexp n c j.2 else 0)

theorem hA_ne_zero (i : Fin k) (c : (ZMod n)ˣ) : hA n k i c ≠ 0 := phiA_ne_zero n k _

theorem hA_one (i : Fin k) : hA n k i 1 = 1 := by
  rw [hA, phiA_congr n k (e₂ := fun _ => (0 : ℤ)) (fun j => by
    by_cases hj : j.1 = i <;> simp [hj, hexp_one]), phiA_zero]

theorem hA_zpow (i : Fin k) (c : (ZMod n)ˣ) (m : ℤ) :
    hA n k i c ^ m = phiA n k (fun j => m * (if j.1 = i then hexp n c j.2 else 0)) := by
  rw [hA, phiA_zpow]

/-- **The twisting identity** in `K(T)`, blockwise: `c · g i = g i ^ c * h i c ^ n`. -/
theorem sigmaE_gA (c : (ZMod n)ˣ) (i : Fin k) :
    sigmaE n c (gA n k i) = gA n k i ^ cnat n c * hA n k i c ^ n := by
  rw [← zpow_natCast (gA n k i) (cnat n c), ← zpow_natCast (hA n k i c) n, gA_zpow, hA_zpow,
    ← phiA_add, gA, sigmaE_phiA]
  refine phiA_congr n k fun j => ?_
  by_cases hj : j.1 = i
  · simp only [anatA, hj]
    have h := n_mul_hexp n c j.2
    push_cast
    linarith
  · simp [anatA, hj]

/-- **The cocycle identity** satisfied by the blocked twisting factors. -/
theorem hA_cocycle (i : Fin k) (c d : (ZMod n)ˣ) :
    gA n k i ^ kk n c d * hA n k i c ^ cnat n d * sigmaE n c (hA n k i d) = hA n k i (c * d) := by
  rw [gA_zpow, ← zpow_natCast (hA n k i c) (cnat n d), hA_zpow, hA, sigmaE_phiA, hA,
    ← phiA_add, ← phiA_add]
  refine phiA_congr n k fun j => ?_
  by_cases hj : j.1 = i
  · simp only [anatA, hj]
    have hn0 : (n : ℤ) ≠ 0 := by have := hn.out; positivity
    refine mul_left_cancel₀ hn0 ?_
    have h1 := n_mul_kk n c d
    have h2 := n_mul_hexp n c j.2
    have h3 := n_mul_hexp n d (c⁻¹ * j.2)
    have h4 := n_mul_hexp n (c * d) j.2
    rw [show (c * d)⁻¹ * j.2 = d⁻¹ * (c⁻¹ * j.2) by rw [mul_inv_rev, mul_assoc]] at h4
    push_cast
    linear_combination (anat n j.2 : ℤ) * h1 + (cnat n d : ℤ) * h2 + h3 - h4
  · simp [anatA, hj]

/-! ### Multiplicative independence of the blocked data -/

/-- **An `n`-th power pins the exponents down modulo `n`.** -/
theorem n_dvd_of_pow_eq_phiA (E : JJ n k → ℤ) (y : EE n) (hy : y ≠ 0)
    (h : y ^ n = phiA n k E) (j : JJ n k) : (n : ℤ) ∣ E j :=
  dvd_of_pow_eq_phiF _ (rtA_injective n k) E hy h j

/-- The product of the blocked data with integer exponents is again a product of linear
factors, whose exponent on the `i`-th block is the `i`-th exponent times the cyclic weight. -/
theorem prod_zpow_phiF {F : Type*} [Field F] (rt : JJ n k → F) (m : Fin k → ℤ) :
    ∏ i : Fin k, phiF rt (fun j => (anatA n k i j : ℤ)) ^ m i
      = phiF rt (fun j => m j.1 * (anat n j.2 : ℤ)) := by
  rw [show (∏ i : Fin k, phiF rt (fun j => (anatA n k i j : ℤ)) ^ m i)
      = ∏ i : Fin k, phiF rt (fun j => m i * (anatA n k i j : ℤ)) from
    Finset.prod_congr rfl fun i _ => phiF_zpow rt _ (m i), phiF_prod]
  refine phiF_congr rt fun j => ?_
  simp only [anatA, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- **Independence modulo `n`-th powers, over any base carrying the roots.** -/
theorem dvd_of_pow_eq_prod_zpow {F : Type*} [Field F] (rt : JJ n k → F)
    (hrt : Function.Injective rt) (m : Fin k → ℤ) {y : RatFunc F} (hy : y ≠ 0)
    (h : y ^ n = ∏ i : Fin k, phiF rt (fun j => (anatA n k i j : ℤ)) ^ m i) (i : Fin k) :
    (n : ℤ) ∣ m i := by
  rw [prod_zpow_phiF n k rt m] at h
  have := dvd_of_pow_eq_phiF rt hrt _ hy h (i, 1)
  simpa [anat_one] using this

/-- **The blocked data are independent modulo `n`-th powers.** -/
theorem gA_indep (m : Fin k → ℤ) (y : EE n) (hy : y ≠ 0)
    (h : y ^ n = ∏ i : Fin k, gA n k i ^ m i) (i : Fin k) : (n : ℤ) ∣ m i := by
  simp only [gA_eq_phiF] at h
  exact dvd_of_pow_eq_prod_zpow n k (rtA n k) (rtA_injective n k) m hy h i

/-! ### The blocked data over the geometric base field -/

/-- The roots of the blocked data, read in an algebraic closure of `K`. -/
def rtBar (j : JJ n k) : Kbar n := algebraMap (KK n) (Kbar n) (rtA n k j)

theorem rtBar_injective : Function.Injective (rtBar n k) := fun _ _ h =>
  rtA_injective n k ((algebraMap (KK n) (Kbar n)).injective h)

/-- The `i`-th blocked datum, read over the geometric base field `K̄(T)`. -/
def gABar (i : Fin k) : GG n := algebraMap (EE n) (GG n) (gA n k i)

theorem gABar_eq_phiF (i : Fin k) :
    gABar n k i = phiF (rtBar n k) (fun j => (anatA n k i j : ℤ)) := by
  rw [gABar, gA_eq_phiF, algebraMap_phiF]
  rfl

theorem gABar_ne_zero (i : Fin k) : gABar n k i ≠ 0 := by
  rw [gABar_eq_phiF]
  exact phiF_ne_zero _ _

/-- **The blocked data stay independent modulo `n`-th powers over `K̄(T)`.** -/
theorem gABar_indep (m : Fin k → ℤ) (y : GG n) (hy : y ≠ 0)
    (h : y ^ n = ∏ i : Fin k, gABar n k i ^ m i) (i : Fin k) : (n : ℤ) ∣ m i := by
  simp only [gABar_eq_phiF] at h
  exact dvd_of_pow_eq_prod_zpow n k (rtBar n k) (rtBar_injective n k) m hy h i

end

end Rigidity.RET.Abel
