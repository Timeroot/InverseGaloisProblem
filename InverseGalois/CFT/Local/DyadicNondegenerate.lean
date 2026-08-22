import Mathlib
import InverseGalois.CFT.Local.DyadicHilbertMul
import InverseGalois.CFT.Local.PadicSquaresTwo
import InverseGalois.CFT.Local.HilbertMul

/-!
# Nondegeneracy of the Hilbert symbol at the dyadic place

The file `InverseGalois/CFT/Local/DyadicHilbertMul.lean` computes the Hilbert symbol of `ℚ_[2]`
on the four shapes `⟨u, v⟩`, `⟨2 u, v⟩`, `⟨u, 2 v⟩`, `⟨2 u, 2 v⟩` with `u` and `v` units of
`ℤ_[2]`, and deduces that the symbol is bimultiplicative.  This file draws from that table the
statement that the symbol is *nondegenerate*: against a nonsquare `b` the character `⟨-, b⟩`
takes the value `-1`.

The square class of a nonzero `b` is represented by a unit `w` of `ℤ_[2]` or by `2 w`, and the
symbol does not see the square factor.  In the ramified shape the unit `5` always works, its
`ω` sign being `-1` while its `ε` sign is trivial.  In the unramified shape `b` is a nonsquare
exactly when the residue of `w` modulo `8` is one of `3`, `5`, `7`; against `3` and `7` the
partner `-1` has symbol `-1`, since the `ε` signs of both are nontrivial, and against `5` the
uniformiser `2` does, the `ω` sign of `5` being `-1`.

As over `ℚ_[p]` with `p` odd, nondegeneracy turns the symbol against a fixed nonsquare `b` into
a surjective character of `ℚ_[2]ˣ` whose kernel is the group of norms from `ℚ_[2](√b)`.  That
norm group therefore has index two, and the relative Brauer group of `ℚ_[2](√b)`, which is the
corresponding quotient, has order two.

## Main results

* `InverseGalois.CFT.Local.exists_hilbertSymbol_eq_neg_one_two`: **the dyadic Hilbert symbol is
  nondegenerate**, against a nonsquare it takes the value `-1`.
* `InverseGalois.CFT.Local.dyadicHilbertHom`,
  `InverseGalois.CFT.Local.coe_dyadicHilbertHom`,
  `InverseGalois.CFT.Local.surjective_dyadicHilbertHom`: the symbol against a fixed nonzero `b`
  as a character `ℚ_[2]ˣ →* ℤˣ`, surjective when `b` is a nonsquare.
* `InverseGalois.CFT.Local.normSubgroup_index_eq_two_dyadic`: **the norm group of a quadratic
  extension of `ℚ_[2]` has index two.**
* `InverseGalois.CFT.Local.card_relative_sqrtExt_dyadic`: **the relative Brauer group of a
  quadratic extension of `ℚ_[2]` has order two.**

## Tags

Hilbert symbol, dyadic place, norm group, Brauer group
-/

open Polynomial

namespace InverseGalois.CFT.Local

/-! ### Nondegeneracy -/

/-- The unramified representative of a square class is the unit itself. -/
theorem dyadicPart_false (w : ℤ_[2]) : dyadicPart false w = w := rfl

/-- The ramified representative of a square class is twice the unit. -/
theorem dyadicPart_true (w : ℤ_[2]) : dyadicPart true w = 2 * w := rfl

/-- The unit `5` pairs nontrivially with every doubled unit: its `ε` sign is trivial while its
`ω` sign is `-1`. -/
theorem dyadicEpsProd_five_mul_omega_five :
    ∀ s : ZMod 8, dyadicEpsProd 5 s * dyadicOmegaSign 5 = -1 := by decide

/-- **The dyadic Hilbert symbol against a nonsquare takes the value `-1`.**  In the ramified
normal form `b = c ^ 2 * (2 w)` the unit `5` is a partner; in the unramified form
`b = c ^ 2 * w` the residue of `w` modulo `8` is `3`, `5` or `7`, and a partner is `-1` in the
first and third cases and the uniformiser `2` in the second. -/
theorem exists_hilbertSymbol_eq_neg_one_two {b : ℚ_[2]} (hb : b ≠ 0) (hbs : ¬ IsSquare b) :
    ∃ a : ℚ_[2], a ≠ 0 ∧ hilbertSymbol a b = -1 := by
  obtain ⟨c, e, w, hc, hw, rfl⟩ := exists_sq_mul_dyadicPart hb
  have hneg : ((-1 : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr isUnit_one.neg.ne_zero
  cases e
  · rw [dyadicPart_false] at hbs ⊢
    have hne : PadicInt.toZModPow 3 w ≠ 1 := by
      intro h
      obtain ⟨y, hy⟩ := (isSquare_coe_iff_two hw).mpr h
      exact hbs ⟨c * y, by rw [hy]; ring⟩
    rcases (isUnit_zmod_eight _).mp (hw.map (PadicInt.toZModPow 3)) with h | h | h | h
    · exact absurd h hne
    · refine ⟨((-1 : ℤ_[2]) : ℚ_[2]), hneg, ?_⟩
      rw [mul_comm (c ^ 2) ((w : ℤ_[2]) : ℚ_[2]), hilbertSymbol_mul_sq_right _ _ _ hc,
        hilbertSymbol_units_two_eq' isUnit_one.neg hw, map_neg, map_one, h]
      decide
    · refine ⟨(2 : ℚ_[2]), two_ne_zero, ?_⟩
      rw [mul_comm (c ^ 2) ((w : ℤ_[2]) : ℚ_[2]), hilbertSymbol_mul_sq_right _ _ _ hc,
        hilbertSymbol_two_unit hw, h]
      decide
    · refine ⟨((-1 : ℤ_[2]) : ℚ_[2]), hneg, ?_⟩
      rw [mul_comm (c ^ 2) ((w : ℤ_[2]) : ℚ_[2]), hilbertSymbol_mul_sq_right _ _ _ hc,
        hilbertSymbol_units_two_eq' isUnit_one.neg hw, map_neg, map_one, h]
      decide
  · rw [dyadicPart_true]
    refine ⟨((5 : ℤ_[2]) : ℚ_[2]), PadicInt.coe_ne_zero.mpr isUnit_five_two.ne_zero, ?_⟩
    rw [mul_comm (c ^ 2) ((2 * w : ℤ_[2]) : ℚ_[2]), hilbertSymbol_mul_sq_right _ _ _ hc,
      hilbertSymbol_unit_two_mul isUnit_five_two hw, toZModPow_three_five]
    exact dyadicEpsProd_five_mul_omega_five _

/-! ### The Hilbert character of `ℚ_[2]ˣ` -/

/-- **The dyadic Hilbert symbol against a fixed nonzero `b` as a character of `ℚ_[2]ˣ`.**
Bimultiplicativity of the dyadic symbol makes this a group homomorphism. -/
noncomputable def dyadicHilbertHom {b : ℚ_[2]} (hb : b ≠ 0) : ℚ_[2]ˣ →* ℤˣ where
  toFun a := hilbertUnit (a : ℚ_[2]) b
  map_one' := by
    rw [← Units.val_inj]
    simp only [Units.val_one, coe_hilbertUnit]
    exact hilbertSymbol_one_left b
  map_mul' a a' := by
    rw [← Units.val_inj]
    simp only [Units.val_mul, coe_hilbertUnit]
    exact hilbertSymbol_dyadic_mul_left a.ne_zero a'.ne_zero hb

/-- The dyadic Hilbert character is computed by the Hilbert symbol. -/
@[simp] theorem coe_dyadicHilbertHom {b : ℚ_[2]} (hb : b ≠ 0) (a : ℚ_[2]ˣ) :
    ((dyadicHilbertHom hb a : ℤˣ) : ℤ) = hilbertSymbol (a : ℚ_[2]) b :=
  coe_hilbertUnit _ _

/-- **The dyadic Hilbert character attached to a nonsquare is onto `ℤˣ`**: the value `1` is taken
at `1`, and the value `-1` at an element supplied by
`InverseGalois.CFT.Local.exists_hilbertSymbol_eq_neg_one_two`. -/
theorem surjective_dyadicHilbertHom {b : ℚ_[2]} (hb : b ≠ 0) (hbs : ¬ IsSquare b) :
    Function.Surjective (dyadicHilbertHom hb) := by
  intro y
  rcases Int.units_eq_one_or y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · obtain ⟨a, ha, hsym⟩ := exists_hilbertSymbol_eq_neg_one_two hb hbs
    refine ⟨Units.mk0 a ha, ?_⟩
    rw [← Units.val_inj, coe_dyadicHilbertHom, Units.val_mk0, hsym, Units.val_neg, Units.val_one]

/-! ### The norm group and the relative Brauer group -/

section NormIndex

variable {b : ℚ_[2]} [Fact (Irreducible (X ^ 2 - C b))]

/-- **The norm group of a quadratic extension of `ℚ_[2]` has index two.**  The Hilbert character
of `ℚ_[2]ˣ` attached to `b` has the norm group as its kernel and is onto `ℤˣ`, a group of
order two. -/
theorem normSubgroup_index_eq_two_dyadic (hbs : ¬ IsSquare b) :
    (normSubgroup ℚ_[2] (sqrtExt ℚ_[2] b)).index = 2 := by
  have hb : b ≠ 0 := by rintro rfl; exact hbs IsSquare.zero
  have hker : (dyadicHilbertHom hb).ker = normSubgroup ℚ_[2] (sqrtExt ℚ_[2] b) := by
    ext a
    rw [MonoidHom.mem_ker, mem_normSubgroup_sqrtExt_iff_hilbertSymbol hbs]
    exact hilbertUnit_eq_one_iff _ _
  rw [← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (surjective_dyadicHilbertHom hb hbs), Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- **The relative Brauer group of a quadratic extension of `ℚ_[2]` has order two**: it is the
quotient of `ℚ_[2]ˣ` by the norm group, which has index two. -/
theorem card_relative_sqrtExt_dyadic (hbs : ¬ IsSquare b) :
    Nat.card ↥(BrauerGroup.relative ℚ_[2] (sqrtExt ℚ_[2] b)) = 2 := by
  rw [← Nat.card_congr (brauerSqrtExtEquiv (K := ℚ_[2]) (b := b)).toEquiv,
    ← Subgroup.index_eq_card]
  exact normSubgroup_index_eq_two_dyadic hbs

end NormIndex

end InverseGalois.CFT.Local
