import Mathlib
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.PadicSquaresTwo

/-!
# Rational representatives for the square classes of `ℚ_[p]`

The squares of `ℚ_[p]` form an open subgroup of the multiplicative group: a `p`-adic number
sufficiently close to `1` is automatically a square, by Hensel's lemma started at the approximate
root `1`. For an odd prime this is the statement that `1 + p ℤ_[p]` consists of squares, and at
the dyadic place it is the statement that `1 + 8 ℤ_[2]` consists of squares. Consequently each
square class of `ℚ_[p]` is an open subset of `ℚ_[p]`, and since the rational numbers are dense
in `ℚ_[p]` every square class contains a rational number.

The concrete ball used below is `‖y - x‖ < ‖x‖ / (8 * p)`, a radius that is small enough at every
prime, including `p = 2`.

## Main results

* `InverseGalois.CFT.norm_eq_one_of_norm_sub_one_lt`: a `p`-adic number at distance less than `1`
  from `1` has norm `1`.
* `InverseGalois.CFT.isSquare_of_norm_sub_one_lt_one`: for an odd prime, a `p`-adic number at
  distance less than `1` from `1` is a square.
* `InverseGalois.CFT.isSquare_of_norm_sub_one_le_eight`: a dyadic number at distance at most
  `1 / 8` from `1` is a square.
* `InverseGalois.CFT.isSquare_of_norm_sub_one_lt`: a `p`-adic number at distance less than
  `1 / (8 * p)` from `1` is a square, uniformly in `p`.
* `InverseGalois.CFT.isSquare_div_of_dist_lt`: two nonzero `p`-adic numbers at distance less than
  `‖x‖ / (8 * p)` lie in the same square class.
* `InverseGalois.CFT.exists_rat_isSquare_div`: every square class of `ℚ_[p]` contains a nonzero
  rational number.
-/

namespace InverseGalois.CFT

open Local

variable {p : ℕ} [Fact p.Prime]

/-- A `p`-adic number at distance less than `1` from `1` has norm exactly `1`, by the
ultrametric inequality applied in both directions. -/
theorem norm_eq_one_of_norm_sub_one_lt {u : ℚ_[p]} (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have hle : ‖u‖ ≤ 1 := by
    have e : (u - 1) + 1 = u := by ring
    have hna := Padic.nonarchimedean (u - 1) (1 : ℚ_[p])
    rw [e, norm_one] at hna
    exact hna.trans (max_le h.le le_rfl)
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  have e : u + -(u - 1) = 1 := by ring
  have hna := Padic.nonarchimedean u (-(u - 1))
  rw [e, norm_neg, norm_one] at hna
  exact absurd hna (not_le.mpr (max_lt hlt h))

/-- For an odd prime `p`, a `p`-adic number at distance less than `1` from `1` is a square: it is
a unit of `ℤ_[p]` whose residue modulo `p` is the square `1`. -/
theorem isSquare_of_norm_sub_one_lt_one (hp : p ≠ 2) {u : ℚ_[p]} (h : ‖u - 1‖ < 1) :
    IsSquare u := by
  have hu : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt h
  obtain ⟨v, hvc⟩ : ∃ v : ℤ_[p], (v : ℚ_[p]) = u := ⟨⟨u, hu.le⟩, rfl⟩
  have hvn : ‖v‖ = 1 := by rw [PadicInt.norm_def, hvc, hu]
  have hvu : IsUnit v := PadicInt.isUnit_iff.mpr hvn
  have hsub : ‖v - 1‖ = ‖u - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, hvc, PadicInt.coe_one]
  have hmem : v - 1 ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hsub]
    exact h
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hsq : IsSquare v := isSquare_of_isSquare_toZMod hp hvu (by rw [hmem]; exact IsSquare.one)
  rw [← hvc]
  exact (isSquare_coe_iff hvu).mpr hsq

/-- A dyadic number at distance at most `1 / 8` from `1` is a square: it is a unit of `ℤ_[2]`
congruent to `1` modulo `8`. -/
theorem isSquare_of_norm_sub_one_le_eight {u : ℚ_[2]} (h : ‖u - 1‖ ≤ 1 / 8) : IsSquare u := by
  have h1 : ‖u - 1‖ < 1 := by linarith
  have hu : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt h1
  obtain ⟨v, hvc⟩ : ∃ v : ℤ_[2], (v : ℚ_[2]) = u := ⟨⟨u, hu.le⟩, rfl⟩
  have hvn : ‖v‖ = 1 := by rw [PadicInt.norm_def, hvc, hu]
  have hvu : IsUnit v := PadicInt.isUnit_iff.mpr hvn
  have hsub : ‖v - 1‖ = ‖u - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, hvc, PadicInt.coe_one]
  have hmem : v - 1 ∈ RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow, hsub]
    refine h.trans (le_of_eq ?_)
    norm_num
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hsq : IsSquare v := isSquare_of_toZModPow_three_eq_one hmem
  rw [← hvc]
  exact (isSquare_coe_iff hvu).mpr hsq

/-- A `p`-adic number at distance less than `1 / (8 * p)` from `1` is a square, at every prime:
for an odd prime the radius `1 / (8 * p)` is below `1`, and at `p = 2` it equals `1 / 16`, which
is below `1 / 8`. -/
theorem isSquare_of_norm_sub_one_lt {u : ℚ_[p]} (h : ‖u - 1‖ < 1 / (8 * p)) : IsSquare u := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  rcases eq_or_ne p 2 with rfl | hp
  · refine isSquare_of_norm_sub_one_le_eight ?_
    norm_num at h ⊢
    linarith
  · refine isSquare_of_norm_sub_one_lt_one hp (lt_of_lt_of_le h ?_)
    rw [div_le_one (by linarith)]
    linarith

/-- Two nonzero `p`-adic numbers at distance less than `‖x‖ / (8 * p)` lie in the same square
class, since their quotient is within `1 / (8 * p)` of `1`. -/
theorem isSquare_div_of_dist_lt {x y : ℚ_[p]} (hx : x ≠ 0) (h : ‖y - x‖ < ‖x‖ / (8 * p)) :
    IsSquare (y / x) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine isSquare_of_norm_sub_one_lt ?_
  have hq : y / x - 1 = (y - x) / x := by field_simp
  rw [hq, norm_div, div_lt_iff₀ hxpos, show (1 : ℝ) / (8 * p) * ‖x‖ = ‖x‖ / (8 * p) by ring]
  exact h

/-- Every square class of `ℚ_[p]` contains a nonzero rational number, because the square classes
are open and the rational numbers are dense in `ℚ_[p]`. -/
theorem exists_rat_isSquare_div {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧ IsSquare (x / (r : ℚ_[p])) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hden : (0 : ℝ) < 8 * p := by linarith
  obtain ⟨r, hr⟩ := Padic.rat_dense p x (div_pos hxpos hden)
  have hrx : ‖(r : ℚ_[p]) - x‖ < ‖x‖ / (8 * p) := by rwa [← norm_neg, neg_sub]
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero, zero_sub, norm_neg, lt_div_iff₀ hden] at hrx
    nlinarith
  obtain ⟨w, hw⟩ := isSquare_div_of_dist_lt hx hrx
  exact ⟨r, hr0, w⁻¹, by rw [← mul_inv, ← hw, inv_div]⟩

end InverseGalois.CFT
