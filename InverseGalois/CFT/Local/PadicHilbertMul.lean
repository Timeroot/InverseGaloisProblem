import Mathlib
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Local.UnramifiedNormForm
import InverseGalois.CFT.Local.RamifiedNormForm
import InverseGalois.CFT.Local.HilbertMul

/-!
# Bimultiplicativity of the Hilbert symbol over `ℚ_[p]`, and the local Brauer group

Fix an odd prime `p`.  The two files `InverseGalois.CFT.Local.UnramifiedNormForm` and
`InverseGalois.CFT.Local.RamifiedNormForm` compute the Hilbert symbol `⟨a, b⟩` over `ℚ_[p]` for
`b` of the two shapes `w` and `p * w`, with `w` a unit of `ℤ_[p]`, and in each case exhibit the
symbol as multiplicative in `a`.  The observation that completes the local theory is that these
two shapes exhaust the square classes: every nonzero `b : ℚ_[p]` is `c ^ 2 * w` or
`c ^ 2 * (p * w)`, and the Hilbert symbol does not see the factor `c ^ 2`.  Multiplicativity of
`⟨-, b⟩` therefore holds for *every* nonzero `b`, and by symmetry the symbol is bimultiplicative.

Two consequences are drawn.  The first is that for a nonsquare `b` the character `⟨-, b⟩` is
onto `{1, -1}`: against a unit `w` with nonsquare residue the uniformiser has symbol `-1`, and
against a ramified `p * w` any unit with nonsquare residue does.  The second is arithmetic: the
Hilbert symbol is a surjective homomorphism `ℚ_[p]ˣ →* ℤˣ` whose kernel is the group of norms
from `ℚ_[p](√b)`, so that norm group has index two and the relative Brauer group
`Br(ℚ_[p](√b) / ℚ_[p])`, which is the corresponding quotient, has order two.

The file closes with the classical closed formula for the symbol of `p ^ α * u` against
`p ^ β * v`, a product of quadratic characters of the residue field.

## Main results

* `InverseGalois.CFT.Local.exists_sq_mul_normal_form`: **the square-class normal form**, every
  nonzero `p`-adic number is a square times a unit or a square times a uniformiser times a unit.
* `InverseGalois.CFT.Local.hilbertSymbol_padic_mul_left`,
  `InverseGalois.CFT.Local.hilbertSymbol_padic_mul_right`: **the Hilbert symbol over `ℚ_[p]` is
  bimultiplicative**, for `p` odd.
* `InverseGalois.CFT.Local.exists_hilbertSymbol_eq_neg_one`: against a nonsquare the symbol takes
  the value `-1`.
* `InverseGalois.CFT.Local.padicHilbertHom`, `InverseGalois.CFT.Local.coe_padicHilbertHom`,
  `InverseGalois.CFT.Local.surjective_padicHilbertHom`: the symbol against a fixed nonzero `b` as
  a surjective character `ℚ_[p]ˣ →* ℤˣ`.
* `InverseGalois.CFT.Local.normSubgroup_index_eq_two`: **the norm group of a quadratic extension
  of `ℚ_[p]` has index two.**
* `InverseGalois.CFT.Local.card_relative_sqrtExt_padic`: **the relative Brauer group of a
  quadratic extension of `ℚ_[p]` has order two.**
* `InverseGalois.CFT.Local.hilbertSymbol_padic_eq`: **the explicit formula** for the symbol of
  `p ^ α * u` against `p ^ β * v`.
* `InverseGalois.CFT.Local.hilbertSymbol_sq_mul_right`,
  `InverseGalois.CFT.Local.sign_pow_eq_ite`,
  `InverseGalois.CFT.Local.sign_pow_natAbs_eq_ite`: the bookkeeping lemmas used throughout.

## Tags

Hilbert symbol, p-adic field, norm group, Brauer group, quadratic character
-/

open Polynomial

namespace InverseGalois.CFT.Local

variable {p : ℕ} [Fact p.Prime]

/-! ### Bookkeeping -/

/-- The Hilbert symbol is invariant under multiplying its second argument by a nonzero square,
here written on the left. -/
theorem hilbertSymbol_sq_mul_right {K : Type*} [Field K] (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol a (c ^ 2 * b) = hilbertSymbol a b := by
  rw [mul_comm, hilbertSymbol_mul_sq_right _ _ _ hc]

/-- A power of a sign is `1` for an even exponent and the sign itself for an odd one. -/
theorem sign_pow_eq_ite {s : ℤ} (hs : s = 1 ∨ s = -1) (k : ℕ) :
    s ^ k = if Even k then 1 else s := by
  rcases hs with rfl | rfl
  · simp
  · split_ifs with h
    · exact h.neg_one_pow
    · exact (Nat.not_even_iff_odd.mp h).neg_one_pow

/-- A sign raised to the absolute value of an integer is `1` exactly when that integer is even. -/
theorem sign_pow_natAbs_eq_ite {s : ℤ} (hs : s = 1 ∨ s = -1) (k : ℤ) :
    s ^ k.natAbs = if Even k then 1 else s := by
  rw [sign_pow_eq_ite hs]
  simp only [Int.natAbs_even]

/-! ### The square-class normal form -/

/-- **Every nonzero `p`-adic number is a square times one of two normal forms.**  Writing
`b = p ^ n * u` with `u` a unit of `ℤ_[p]`, the square `c ^ 2` with `c = p ^ ⌊n / 2⌋` absorbs the
even part of the power of the uniformiser, leaving either a unit or a uniformiser times a unit
according to the parity of `n`. -/
theorem exists_sq_mul_normal_form {b : ℚ_[p]} (hb : b ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ((∃ w : ℤ_[p], IsUnit w ∧ b = c ^ 2 * (w : ℚ_[p])) ∨
      (∃ w : ℤ_[p], IsUnit w ∧ b = c ^ 2 * ((p : ℚ_[p]) * (w : ℚ_[p])))) := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_zpow hb
  rcases Int.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hn : n = 2 * k := by omega
    subst hn
    exact ⟨(p : ℚ_[p]) ^ k, zpow_ne_zero _ hp0, Or.inl ⟨u, hu, by rw [zpow_two_mul_eq_sq]⟩⟩
  · obtain ⟨k, hk⟩ := ho
    subst hk
    refine ⟨(p : ℚ_[p]) ^ k, zpow_ne_zero _ hp0, Or.inr ⟨u, hu, ?_⟩⟩
    rw [zpow_add₀ hp0, zpow_one, zpow_two_mul_eq_sq]
    ring

/-! ### Bimultiplicativity -/

/-- **The `p`-adic Hilbert symbol is multiplicative in its first argument**, for `p` odd.  Put
the second argument in square-class normal form and discard the square factor.  Against a unit
whose residue is a square both sides are `1`; against a unit whose residue is not a square this
is the multiplicativity of the unramified character, and against a uniformiser times a unit it is
the multiplicativity of the ramified one. -/
theorem hilbertSymbol_padic_mul_left (hp : p ≠ 2) {a a' b : ℚ_[p]}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol (a * a') b = hilbertSymbol a b * hilbertSymbol a' b := by
  obtain ⟨c, hc, hcase⟩ := exists_sq_mul_normal_form hb
  rcases hcase with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · rw [hilbertSymbol_sq_mul_right _ _ _ hc, hilbertSymbol_sq_mul_right _ _ _ hc,
      hilbertSymbol_sq_mul_right _ _ _ hc]
    by_cases hws : IsSquare (PadicInt.toZMod w)
    · have hsq : IsSquare ((w : ℚ_[p])) :=
        (isSquare_coe_iff hw).mpr (isSquare_of_isSquare_toZMod hp hw hws)
      rw [hilbertSymbol_of_isSquare_right _ _ hsq, hilbertSymbol_of_isSquare_right _ _ hsq,
        hilbertSymbol_of_isSquare_right _ _ hsq]
      norm_num
    · exact hilbertSymbol_unramified_mul hp hw hws ha ha'
  · rw [hilbertSymbol_sq_mul_right _ _ _ hc, hilbertSymbol_sq_mul_right _ _ _ hc,
      hilbertSymbol_sq_mul_right _ _ _ hc]
    exact hilbertSymbol_ramified_mul hp hw ha ha'

/-- **The `p`-adic Hilbert symbol is multiplicative in its second argument**, for `p` odd, by
symmetry of the symbol. -/
theorem hilbertSymbol_padic_mul_right (hp : p ≠ 2) {a b b' : ℚ_[p]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol a (b * b') = hilbertSymbol a b * hilbertSymbol a b' := by
  rw [hilbertSymbol_comm a (b * b'), hilbertSymbol_comm a b, hilbertSymbol_comm a b']
  exact hilbertSymbol_padic_mul_left hp hb hb' ha

/-- **The Hilbert symbol against a nonsquare takes the value `-1`**, for `p` odd.  In the
unramified normal form `b = c ^ 2 * w` the residue of `w` cannot be a square, and the uniformiser,
whose valuation is odd, has symbol `-1` against it.  In the ramified normal form
`b = c ^ 2 * (p * w)` any unit with nonsquare residue does. -/
theorem exists_hilbertSymbol_eq_neg_one (hp : p ≠ 2) {b : ℚ_[p]} (hb : b ≠ 0)
    (hbs : ¬ IsSquare b) : ∃ a : ℚ_[p], a ≠ 0 ∧ hilbertSymbol a b = -1 := by
  obtain ⟨c, hc, hcase⟩ := exists_sq_mul_normal_form hb
  rcases hcase with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · have hws : ¬ IsSquare (PadicInt.toZMod w) := by
      intro h
      obtain ⟨y, hy⟩ := (isSquare_coe_iff hw).mpr (isSquare_of_isSquare_toZMod hp hw h)
      exact hbs ⟨c * y, by rw [hy]; ring⟩
    refine ⟨(p : ℚ_[p]), NeZero.ne _, ?_⟩
    rw [hilbertSymbol_sq_mul_right _ _ _ hc]
    rcases hilbertSymbol_eq_one_or ((p : ℚ_[p])) ((w : ℚ_[p])) with h1 | h1
    · refine absurd ((hilbertSymbol_unramified hp hw hws (NeZero.ne _)).mp h1) ?_
      rw [Padic.valuation_p]
      rintro ⟨r, hr⟩
      omega
    · exact h1
  · obtain ⟨u, hu, hus⟩ := exists_unramified_nonsquare (p := p) hp
    refine ⟨(u : ℚ_[p]), PadicInt.coe_ne_zero.mpr hu.ne_zero, ?_⟩
    rw [hilbertSymbol_sq_mul_right _ _ _ hc]
    rcases hilbertSymbol_eq_one_or ((u : ℚ_[p])) ((p : ℚ_[p]) * (w : ℚ_[p])) with h1 | h1
    · exfalso
      have hz : ((p : ℚ_[p]) ^ (0 : ℤ)) * (u : ℚ_[p]) = (u : ℚ_[p]) := by
        rw [zpow_zero, one_mul]
      rw [← hz] at h1
      rcases (hilbertSymbol_ramified hp hw hu).mp h1 with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact hus h2
      · exact h2 ⟨0, (add_zero 0).symm⟩
    · exact h1

/-! ### The Hilbert character of `ℚ_[p]ˣ` -/

/-- **The Hilbert symbol against a fixed nonzero `b` as a character of `ℚ_[p]ˣ`**, for `p` odd.
Bimultiplicativity of the `p`-adic symbol makes this a group homomorphism. -/
noncomputable def padicHilbertHom (hp : p ≠ 2) {b : ℚ_[p]} (hb : b ≠ 0) : ℚ_[p]ˣ →* ℤˣ where
  toFun a := hilbertUnit (a : ℚ_[p]) b
  map_one' := by
    rw [← Units.val_inj]
    simp only [Units.val_one, coe_hilbertUnit]
    exact hilbertSymbol_one_left b
  map_mul' a a' := by
    rw [← Units.val_inj]
    simp only [Units.val_mul, coe_hilbertUnit]
    exact hilbertSymbol_padic_mul_left hp a.ne_zero a'.ne_zero hb

/-- The `p`-adic Hilbert character is computed by the Hilbert symbol. -/
@[simp] theorem coe_padicHilbertHom (hp : p ≠ 2) {b : ℚ_[p]} (hb : b ≠ 0) (a : ℚ_[p]ˣ) :
    ((padicHilbertHom hp hb a : ℤˣ) : ℤ) = hilbertSymbol (a : ℚ_[p]) b :=
  coe_hilbertUnit _ _

/-- **The Hilbert character attached to a nonsquare is onto `ℤˣ`**, for `p` odd: the value `1` is
taken at `1`, and the value `-1` at an element supplied by
`InverseGalois.CFT.Local.exists_hilbertSymbol_eq_neg_one`. -/
theorem surjective_padicHilbertHom (hp : p ≠ 2) {b : ℚ_[p]} (hb : b ≠ 0) (hbs : ¬ IsSquare b) :
    Function.Surjective (padicHilbertHom hp hb) := by
  intro y
  rcases Int.units_eq_one_or y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · obtain ⟨a, ha, hsym⟩ := exists_hilbertSymbol_eq_neg_one hp hb hbs
    refine ⟨Units.mk0 a ha, ?_⟩
    rw [← Units.val_inj, coe_padicHilbertHom, Units.val_mk0, hsym, Units.val_neg, Units.val_one]

/-! ### The norm group and the relative Brauer group -/

section NormIndex

variable {b : ℚ_[p]} [Fact (Irreducible (X ^ 2 - C b))]

/-- **The norm group of a quadratic extension of `ℚ_[p]` has index two**, for `p` odd.  The
Hilbert character of `ℚ_[p]ˣ` attached to `b` has the norm group as its kernel and is onto `ℤˣ`,
a group of order two. -/
theorem normSubgroup_index_eq_two (hp : p ≠ 2) (hbs : ¬ IsSquare b) :
    (normSubgroup ℚ_[p] (sqrtExt ℚ_[p] b)).index = 2 := by
  have hb : b ≠ 0 := by rintro rfl; exact hbs IsSquare.zero
  have hker : (padicHilbertHom hp hb).ker = normSubgroup ℚ_[p] (sqrtExt ℚ_[p] b) := by
    ext a
    rw [MonoidHom.mem_ker, mem_normSubgroup_sqrtExt_iff_hilbertSymbol hbs]
    exact hilbertUnit_eq_one_iff _ _
  rw [← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (surjective_padicHilbertHom hp hb hbs), Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- **The relative Brauer group of a quadratic extension of `ℚ_[p]` has order two**, for `p` odd:
it is the quotient of `ℚ_[p]ˣ` by the norm group, which has index two. -/
theorem card_relative_sqrtExt_padic (hp : p ≠ 2) (hbs : ¬ IsSquare b) :
    Nat.card ↥(BrauerGroup.relative ℚ_[p] (sqrtExt ℚ_[p] b)) = 2 := by
  rw [← Nat.card_congr (brauerSqrtExtEquiv (K := ℚ_[p]) (b := b)).toEquiv,
    ← Subgroup.index_eq_card]
  exact normSubgroup_index_eq_two hp hbs

end NormIndex

/-! ### The explicit formula -/

/-- **The `p`-adic Hilbert symbol, computed**, for `p` odd: for units `u` and `v` of `ℤ_[p]` and
integers `α` and `β`,
`⟨p ^ α * u, p ^ β * v⟩ = (-1 / p) ^ (α * β) * (u / p) ^ β * (v / p) ^ α`,
where `(- / p)` is the quadratic character of the residue field and the exponents are read modulo
two.  For `β` even the second argument is a square times the unit `v`, and the symbol is the
unramified character of `v` evaluated at the parity of `α`; for `β` odd it is a square times
`p * v`, and the ramified computation applies. -/
theorem hilbertSymbol_padic_eq (hp : p ≠ 2) (α β : ℤ) {u v : ℤ_[p]} (hu : IsUnit u)
    (hv : IsUnit v) :
    hilbertSymbol ((p : ℚ_[p]) ^ α * (u : ℚ_[p])) ((p : ℚ_[p]) ^ β * (v : ℚ_[p]))
      = (if Even (α * β) then 1 else quadraticChar (ZMod p) (-1))
          * quadraticChar (ZMod p) (PadicInt.toZMod u) ^ β.natAbs
          * quadraticChar (ZMod p) (PadicInt.toZMod v) ^ α.natAbs := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have huz : PadicInt.toZMod u ≠ 0 := toZMod_ne_zero_iff_isUnit.mpr hu
  have hvz : PadicInt.toZMod v ≠ 0 := toZMod_ne_zero_iff_isUnit.mpr hv
  have hane : (p : ℚ_[p]) ^ α * (u : ℚ_[p]) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hp0) (PadicInt.coe_ne_zero.mpr hu.ne_zero)
  have hval : ((p : ℚ_[p]) ^ α * (u : ℚ_[p])).valuation = α := valuation_eq_of_eq_zpow_mul hu rfl
  rcases Int.even_or_odd β with he | ho
  · obtain ⟨m, hm⟩ := he
    have hb : β = 2 * m := by omega
    subst hb
    have key : (p : ℚ_[p]) ^ (2 * m) * (v : ℚ_[p]) = ((p : ℚ_[p]) ^ m) ^ 2 * (v : ℚ_[p]) := by
      rw [zpow_two_mul_eq_sq]
    have h2m : Even (2 * m) := ⟨m, by ring⟩
    have ham : Even (α * (2 * m)) := h2m.mul_left α
    rw [key, hilbertSymbol_sq_mul_right _ _ _ (zpow_ne_zero _ hp0),
      sign_pow_natAbs_eq_ite (quadraticChar_dichotomy huz),
      sign_pow_natAbs_eq_ite (quadraticChar_dichotomy hvz), if_pos h2m, if_pos ham,
      one_mul, one_mul]
    by_cases hvs : IsSquare (PadicInt.toZMod v)
    · have hsq : IsSquare ((v : ℚ_[p])) :=
        (isSquare_coe_iff hv).mpr (isSquare_of_isSquare_toZMod hp hv hvs)
      rw [hilbertSymbol_of_isSquare_right _ _ hsq,
        (quadraticChar_one_iff_isSquare hvz).mpr hvs]
      split_ifs <;> rfl
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hvs]
      by_cases ha : Even α
      · rw [if_pos ha, (hilbertSymbol_unramified hp hv hvs hane).mpr (by rw [hval]; exact ha)]
      · rw [if_neg ha, (hilbertSymbol_unramified_eq_neg_one_iff hp hv hvs hane).mpr
          (by rw [hval]; exact ha)]
  · obtain ⟨m, hm⟩ := ho
    subst hm
    have key : (p : ℚ_[p]) ^ (2 * m + 1) * (v : ℚ_[p])
        = ((p : ℚ_[p]) ^ m) ^ 2 * ((p : ℚ_[p]) * (v : ℚ_[p])) := by
      rw [zpow_add₀ hp0, zpow_one, zpow_two_mul_eq_sq]
      ring
    have hodd : ¬ Even (2 * m + 1) := by
      rintro ⟨r, hr⟩
      omega
    rw [key, hilbertSymbol_sq_mul_right _ _ _ (zpow_ne_zero _ hp0),
      hilbertSymbol_ramified_eq hp hv hu,
      sign_pow_natAbs_eq_ite (quadraticChar_dichotomy huz),
      sign_pow_natAbs_eq_ite (quadraticChar_dichotomy hvz), if_neg hodd]
    by_cases ha : Even α
    · have ham : Even (α * (2 * m + 1)) := ha.mul_right (2 * m + 1)
      simp only [if_pos ha, if_pos ham]
      ring
    · have ham : ¬ Even (α * (2 * m + 1)) := Int.not_even_iff_odd.mpr
        ((Int.not_even_iff_odd.mp ha).mul (Int.not_even_iff_odd.mp hodd))
      have hneg : PadicInt.toZMod (-v) = (-1) * PadicInt.toZMod v := by
        rw [map_neg]
        ring
      simp only [if_neg ha, if_neg ham]
      rw [hneg, map_mul]
      ring

end InverseGalois.CFT.Local
