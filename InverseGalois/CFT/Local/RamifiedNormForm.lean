import Mathlib
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.PadicHilbert

/-!
# The norm form of a ramified quadratic extension of `ℚ_[p]`

Fix an odd prime `p` and a unit `w` of `ℤ_[p]`.  The element `b = p * w` has valuation one, so it
is not a square and `ℚ_[p](√b)` is a *ramified* quadratic extension.  This file decides which
`p`-adic numbers are norms from that extension, that is, of the shape `x ^ 2 - b * y ^ 2`, and
consequently computes the Hilbert symbol `⟨a, p * w⟩` for every nonzero `a`.

Write a nonzero `a` as `p ^ n * u` with `u` a unit of `ℤ_[p]`.  The answer is a clean parity
statement: `a` is a norm exactly when either `n` is even and the residue of `u` is a square mod
`p`, or `n` is odd and the residue of `-w * u` is a square mod `p`.

The proof of the forward direction is a valuation computation.  Factoring `x = p ^ i * x'` and
`y = p ^ j * y'` with `x'` and `y'` units, the two terms `x ^ 2` and `p * w * y ^ 2` have
valuations `2 * i` and `2 * j + 1`, which can never agree.  Pulling the smaller power of `p` out
of the difference leaves a unit whose residue is either the square `x̄' ^ 2` or the element
`-w̄ * ȳ' ^ 2`, and comparing valuations with `a = p ^ n * u` identifies `n` and `u`.  Conversely
Hensel's lemma turns a square residue into an actual square, giving a norm with `y = 0` in the
even case and with `x = 0` in the odd case.

Reading the answer through the quadratic character of the residue field turns it into a product
formula, from which the Hilbert symbol against a fixed ramified `b` is seen to be multiplicative
in its other argument.

## Main results

* `InverseGalois.CFT.Local.not_isSquare_p_mul_unit`: a uniformiser times a unit is not a square,
  so it generates a ramified quadratic extension.
* `InverseGalois.CFT.Local.zpow_mul_unit_inj`: the exponent and the unit in a factorisation
  `p ^ n * u` are determined.
* `InverseGalois.CFT.Local.even_residue_of_eq_zpow_mul`,
  `InverseGalois.CFT.Local.odd_residue_of_eq_zpow_mul`: the two branches of the valuation
  argument, packaged for reuse.
* `InverseGalois.CFT.Local.residue_sq_of_eq_sub_sq`: a norm from the ramified extension has the
  stated parity and residue behaviour.
* `InverseGalois.CFT.Local.exists_sub_sq_of_residue_sq`: the converse, by Hensel's lemma.
* `InverseGalois.CFT.Local.hilbertSymbol_ramified`: the resulting computation of the Hilbert
  symbol `⟨p ^ n * u, p * w⟩`.
* `InverseGalois.CFT.Local.eq_quadraticChar_of_iff`: a sign that is `1` exactly on squares is the
  quadratic character.
* `InverseGalois.CFT.Local.hilbertSymbol_ramified_eq`: the same computation as a product of
  quadratic characters of the residue field.
* `InverseGalois.CFT.Local.hilbertSymbol_ramified_mul`: the Hilbert symbol against a ramified
  second argument is multiplicative in its first argument.
-/

namespace InverseGalois.CFT.Local

variable {p : ℕ} [Fact p.Prime]

/-- The uniformiser reduces to zero in the residue field. -/
theorem toZMod_p_eq_zero : PadicInt.toZMod ((p : ℤ_[p])) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

/-- **A uniformiser times a unit is not a square.**  Its valuation is `1 + 0 = 1`, whereas the
valuation of a square is even; so `p * w` generates a ramified quadratic extension of `ℚ_[p]`. -/
theorem not_isSquare_p_mul_unit {w : ℤ_[p]} (hw : IsUnit w) :
    ¬ IsSquare ((p : ℚ_[p]) * (w : ℚ_[p])) := by
  intro h
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have hwne : ((w : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hw.ne_zero
  have hv := even_valuation_of_isSquare (mul_ne_zero hp0 hwne) h
  rw [Padic.valuation_mul hp0 hwne, Padic.valuation_p, valuation_coe_eq_zero hw] at hv
  obtain ⟨r, hr⟩ := hv
  omega

/-- **A factorisation into a power of the uniformiser and a unit is unique.**  The valuation of
`p ^ n * u` is `n`, which pins down the exponent, and cancelling the power of `p` pins down the
unit. -/
theorem zpow_mul_unit_inj {n m : ℤ} {u c : ℤ_[p]} (hu : IsUnit u) (hc : IsUnit c)
    (h : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) = (p : ℚ_[p]) ^ m * (c : ℚ_[p])) :
    n = m ∧ u = c := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have hune : ((u : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  have hcne : ((c : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hc.ne_zero
  have hval := congrArg Padic.valuation h
  rw [Padic.valuation_mul (zpow_ne_zero _ hp0) hune,
    Padic.valuation_mul (zpow_ne_zero _ hp0) hcne, Padic.valuation_zpow,
    Padic.valuation_zpow, Padic.valuation_p, valuation_coe_eq_zero hu,
    valuation_coe_eq_zero hc] at hval
  have hnm : n = m := by omega
  subst hnm
  exact ⟨rfl, Subtype.coe_injective (mul_left_cancel₀ (zpow_ne_zero n hp0) h)⟩

/-- **The even branch of the valuation argument.**  If `p ^ n * u` equals `p ^ m * c` with `m`
even and the residue of the unit `c` the square of the residue of a unit `x'`, then `n` is even
and the residue of `u` is a square. -/
theorem even_residue_of_eq_zpow_mul {m n : ℤ} {u c x' : ℤ_[p]} (hu : IsUnit u) (hx' : IsUnit x')
    (hm : Even m) (hc : PadicInt.toZMod c = PadicInt.toZMod x' ^ 2)
    (h : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) = (p : ℚ_[p]) ^ m * (c : ℚ_[p])) :
    Even n ∧ IsSquare (PadicInt.toZMod u) := by
  have hcu : IsUnit c := toZMod_ne_zero_iff_isUnit.mp (by
    rw [hc]; exact pow_ne_zero 2 (toZMod_ne_zero_iff_isUnit.mpr hx'))
  obtain ⟨rfl, rfl⟩ := zpow_mul_unit_inj hu hcu h
  exact ⟨hm, PadicInt.toZMod x', by rw [hc]; ring⟩

/-- **The odd branch of the valuation argument.**  If `p ^ n * u` equals `p ^ m * c` with `m` odd
and the residue of `c` equal to `-w̄ * ȳ' ^ 2` for units `w` and `y'`, then `n` is odd and the
residue of `-(w * u)` is the square of `w̄ * ȳ'`. -/
theorem odd_residue_of_eq_zpow_mul {m n : ℤ} {u c w y' : ℤ_[p]} (hu : IsUnit u) (hw : IsUnit w)
    (hy' : IsUnit y') (hm : ¬ Even m)
    (hc : PadicInt.toZMod c = -(PadicInt.toZMod w * PadicInt.toZMod y' ^ 2))
    (h : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) = (p : ℚ_[p]) ^ m * (c : ℚ_[p])) :
    ¬ Even n ∧ IsSquare (PadicInt.toZMod (-(w * u))) := by
  have hcu : IsUnit c := toZMod_ne_zero_iff_isUnit.mp (by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero (toZMod_ne_zero_iff_isUnit.mpr hw)
      (pow_ne_zero 2 (toZMod_ne_zero_iff_isUnit.mpr hy'))))
  obtain ⟨rfl, rfl⟩ := zpow_mul_unit_inj hu hcu h
  refine ⟨hm, PadicInt.toZMod w * PadicInt.toZMod y', ?_⟩
  rw [map_neg, map_mul, hc]
  ring

/-- **A norm from the ramified quadratic extension has constrained parity and residue.**  If
`p ^ n * u` is of the shape `x ^ 2 - p * w * y ^ 2` for units `u` and `w`, then either `n` is
even and the residue of `u` is a square mod `p`, or `n` is odd and the residue of `-(w * u)` is.

Factor `x = p ^ i * x'` and `y = p ^ j * y'` with `x'` and `y'` units.  The two terms of the
difference have valuations `2 * i` and `2 * j + 1`, so exactly one of them is the smaller; pulling
that power of the uniformiser out of the difference leaves a unit whose residue is `x̄' ^ 2` in the
first case and `-w̄ * ȳ' ^ 2` in the second, and the factorisation is then unique.  The degenerate
cases `x = 0` and `y = 0` are the two branches with one term absent. -/
theorem residue_sq_of_eq_sub_sq {w : ℤ_[p]} (hw : IsUnit w) {n : ℤ} {u : ℤ_[p]}
    (hu : IsUnit u) {x y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) = x ^ 2 - (p : ℚ_[p]) * (w : ℚ_[p]) * y ^ 2) :
    (Even n ∧ IsSquare (PadicInt.toZMod u)) ∨
      (¬ Even n ∧ IsSquare (PadicInt.toZMod (-(w * u)))) := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have hune : ((u : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  have hane : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hp0) hune
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := by
      rintro rfl
      exact hane (by rw [h]; ring)
    obtain ⟨j, y', hy', rfl⟩ := exists_unit_mul_zpow hy
    refine Or.inr (odd_residue_of_eq_zpow_mul (m := j + j + 1) (c := -(w * y' ^ 2))
      hu hw hy' ?_ ?_ ?_)
    · rw [Int.even_add_one, not_not]
      exact ⟨j, rfl⟩
    · simp [map_neg, map_mul, map_pow]
    · rw [h]
      push_cast
      simp only [zpow_add₀ hp0, zpow_one]
      field_simp
      ring
  · obtain ⟨i, x', hx', rfl⟩ := exists_unit_mul_zpow hx
    by_cases hy : y = 0
    · subst hy
      refine Or.inl (even_residue_of_eq_zpow_mul (m := i + i) (c := x' ^ 2) hu hx'
        ⟨i, rfl⟩ ?_ ?_)
      · simp [map_pow]
      · rw [h]
        push_cast
        simp only [zpow_add₀ hp0]
        field_simp
        ring
    · obtain ⟨j, y', hy', rfl⟩ := exists_unit_mul_zpow hy
      rcases le_or_gt i j with hij | hij
      · set k : ℕ := (j - i).toNat
        have hk : (k : ℤ) = j - i := Int.toNat_of_nonneg (by omega)
        have hzero : PadicInt.toZMod ((p : ℤ_[p]) ^ (2 * k + 1)) = 0 := by
          rw [map_pow, toZMod_p_eq_zero, zero_pow (by omega)]
        refine Or.inl (even_residue_of_eq_zpow_mul (m := i + i)
          (c := x' ^ 2 - (p : ℤ_[p]) ^ (2 * k + 1) * w * y' ^ 2) hu hx' ⟨i, rfl⟩ ?_ ?_)
        · rw [map_sub, map_mul, map_mul, hzero, zero_mul, zero_mul, sub_zero, map_pow]
        · have key : ((p : ℚ_[p])) ^ (j - i + (j - i) + 1) = ((p : ℚ_[p])) ^ (2 * k + 1) := by
            rw [← zpow_natCast ((p : ℚ_[p])) (2 * k + 1)]
            congr 1
            push_cast
            omega
          rw [h]
          push_cast
          rw [← key]
          simp only [zpow_add₀ hp0, zpow_sub₀ hp0, zpow_one]
          field_simp
      · set k : ℕ := (i - j - 1).toNat
        have hk : (k : ℤ) = i - j - 1 := Int.toNat_of_nonneg (by omega)
        have hzero : PadicInt.toZMod ((p : ℤ_[p]) ^ (2 * k + 1)) = 0 := by
          rw [map_pow, toZMod_p_eq_zero, zero_pow (by omega)]
        refine Or.inr (odd_residue_of_eq_zpow_mul (m := j + j + 1)
          (c := (p : ℤ_[p]) ^ (2 * k + 1) * x' ^ 2 - w * y' ^ 2) hu hw hy' ?_ ?_ ?_)
        · rw [Int.even_add_one, not_not]
          exact ⟨j, rfl⟩
        · rw [map_sub, map_mul, map_mul, hzero, zero_mul, map_pow]
          ring
        · have key : ((p : ℚ_[p])) ^ (i - j - 1 + (i - j - 1) + 1) =
              ((p : ℚ_[p])) ^ (2 * k + 1) := by
            rw [← zpow_natCast ((p : ℚ_[p])) (2 * k + 1)]
            congr 1
            push_cast
            omega
          rw [h]
          push_cast
          rw [← key]
          simp only [zpow_add₀ hp0, zpow_sub₀ hp0, zpow_one]
          field_simp

/-- **The parity and residue conditions produce a norm.**  For `p` odd, if `n` is even and the
residue of `u` is a square, then Hensel's lemma makes `u` a square and `p ^ n * u` is itself a
square, a norm with `y = 0`.  If `n` is odd and the residue of `-(w * u)` is a square, then
`-(w * u) = v ^ 2` in `ℤ_[p]`, and `u = -(w * (v * w⁻¹) ^ 2)` exhibits `p ^ n * u` as
`-p * w * (p ^ m * v * w⁻¹) ^ 2`, a norm with `x = 0`. -/
theorem exists_sub_sq_of_residue_sq (hp : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) {n : ℤ} {u : ℤ_[p]}
    (hu : IsUnit u)
    (h : (Even n ∧ IsSquare (PadicInt.toZMod u)) ∨
      (¬ Even n ∧ IsSquare (PadicInt.toZMod (-(w * u))))) :
    ∃ x y : ℚ_[p], (p : ℚ_[p]) ^ n * (u : ℚ_[p]) = x ^ 2 - (p : ℚ_[p]) * (w : ℚ_[p]) * y ^ 2 := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  rcases h with ⟨⟨m, rfl⟩, hsq⟩ | ⟨hodd, hsq⟩
  · obtain ⟨v, hv⟩ := isSquare_of_isSquare_toZMod hp hu hsq
    refine ⟨(p : ℚ_[p]) ^ m * (v : ℚ_[p]), 0, ?_⟩
    rw [hv]
    push_cast
    simp only [zpow_add₀ hp0]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + m + 1 := by
      rcases Int.even_or_odd n with he | ⟨m, hm⟩
      · exact absurd he hodd
      · exact ⟨m, by omega⟩
    have hwu : IsUnit (-(w * u)) := (hw.mul hu).neg
    obtain ⟨v, hv⟩ := isSquare_of_isSquare_toZMod hp hwu hsq
    obtain ⟨e, he⟩ := hw.exists_right_inv
    have hue : u = -(w * (v * e) ^ 2) := by
      calc u = u * (w * e) ^ 2 := by rw [he]; ring
      _ = -(w * (v * e) ^ 2) := by linear_combination (-(w * e ^ 2)) * hv
    refine ⟨0, (p : ℚ_[p]) ^ m * ((v * e : ℤ_[p]) : ℚ_[p]), ?_⟩
    rw [hue]
    push_cast
    simp only [zpow_add₀ hp0, zpow_one]
    ring

/-- **The Hilbert symbol against a ramified second argument**, for `p` odd: for a unit `w` the
symbol `⟨p ^ n * u, p * w⟩` is `1` exactly when `n` is even and the residue of `u` is a square
mod `p`, or `n` is odd and the residue of `-(w * u)` is.  This is the norm description of the
symbol combined with the two previous statements. -/
theorem hilbertSymbol_ramified (hp : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) {n : ℤ} {u : ℤ_[p]}
    (hu : IsUnit u) :
    hilbertSymbol ((p : ℚ_[p]) ^ n * (u : ℚ_[p])) ((p : ℚ_[p]) * (w : ℚ_[p])) = 1 ↔
      (Even n ∧ IsSquare (PadicInt.toZMod u)) ∨
        (¬ Even n ∧ IsSquare (PadicInt.toZMod (-(w * u)))) := by
  rw [hilbertSymbol_eq_one_iff_exists_sub_sq (not_isSquare_p_mul_unit hw)]
  exact ⟨fun ⟨s, t, hst⟩ => residue_sq_of_eq_sub_sq hw hu hst,
    exists_sub_sq_of_residue_sq hp hw hu⟩

/-- A sign taking the value `1` exactly when a nonzero residue is a square is the value of the
quadratic character at that residue. -/
theorem eq_quadraticChar_of_iff {s : ℤ} {z : ZMod p} (hz : z ≠ 0) (hs : s = 1 ∨ s = -1)
    (h : s = 1 ↔ IsSquare z) : s = quadraticChar (ZMod p) z := by
  rcases hs with rfl | rfl
  · exact ((quadraticChar_one_iff_isSquare hz).mpr (h.mp rfl)).symm
  · refine (quadraticChar_neg_one_iff_not_isSquare.mpr ?_).symm
    intro hsq
    have hcon := h.mpr hsq
    omega

/-- **The Hilbert symbol against a ramified second argument, as a character value**, for `p` odd:
the symbol `⟨p ^ n * u, p * w⟩` is the quadratic character of the residue of `u`, corrected by the
quadratic character of the residue of `-w` when `n` is odd. -/
theorem hilbertSymbol_ramified_eq (hp : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) {n : ℤ} {u : ℤ_[p]}
    (hu : IsUnit u) :
    hilbertSymbol ((p : ℚ_[p]) ^ n * (u : ℚ_[p])) ((p : ℚ_[p]) * (w : ℚ_[p]))
      = quadraticChar (ZMod p) (PadicInt.toZMod u)
          * (if Even n then 1 else quadraticChar (ZMod p) (PadicInt.toZMod (-w))) := by
  by_cases hn : Even n
  · rw [if_pos hn, mul_one]
    refine eq_quadraticChar_of_iff (toZMod_ne_zero_iff_isUnit.mpr hu)
      (hilbertSymbol_eq_one_or _ _) ?_
    rw [hilbertSymbol_ramified hp hw hu]
    constructor
    · rintro (⟨-, hs⟩ | ⟨hs, -⟩)
      · exact hs
      · exact absurd hn hs
    · exact fun hs => Or.inl ⟨hn, hs⟩
  · have hzz : PadicInt.toZMod u * PadicInt.toZMod (-w) = PadicInt.toZMod (-(w * u)) := by
      rw [map_neg, map_neg, map_mul]
      ring
    rw [if_neg hn, ← map_mul, hzz]
    refine eq_quadraticChar_of_iff (toZMod_ne_zero_iff_isUnit.mpr (hw.mul hu).neg)
      (hilbertSymbol_eq_one_or _ _) ?_
    rw [hilbertSymbol_ramified hp hw hu]
    constructor
    · rintro (⟨hs, -⟩ | ⟨-, hs⟩)
      · exact absurd hs hn
      · exact hs
    · exact fun hs => Or.inr ⟨hn, hs⟩

/-- **The Hilbert symbol against a ramified second argument is multiplicative**, for `p` odd:
decompose the two nonzero arguments as a power of the uniformiser times a unit, read the symbol as
a character value, and use that the quadratic character is multiplicative while the correction
factor squares to one. -/
theorem hilbertSymbol_ramified_mul (hp : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) {a a' : ℚ_[p]}
    (ha : a ≠ 0) (ha' : a' ≠ 0) :
    hilbertSymbol (a * a') ((p : ℚ_[p]) * (w : ℚ_[p]))
      = hilbertSymbol a ((p : ℚ_[p]) * (w : ℚ_[p]))
        * hilbertSymbol a' ((p : ℚ_[p]) * (w : ℚ_[p])) := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_zpow ha
  obtain ⟨m, u', hu', rfl⟩ := exists_unit_mul_zpow ha'
  have hprod : (p : ℚ_[p]) ^ n * (u : ℚ_[p]) * ((p : ℚ_[p]) ^ m * (u' : ℚ_[p]))
      = (p : ℚ_[p]) ^ (n + m) * ((u * u' : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    rw [zpow_add₀ hp0]
    ring
  have hqc : quadraticChar (ZMod p) (PadicInt.toZMod (u * u'))
      = quadraticChar (ZMod p) (PadicInt.toZMod u)
        * quadraticChar (ZMod p) (PadicInt.toZMod u') := by
    rw [map_mul, map_mul]
  have hX : quadraticChar (ZMod p) (PadicInt.toZMod (-w)) ^ 2 = 1 :=
    quadraticChar_sq_one (toZMod_ne_zero_iff_isUnit.mpr hw.neg)
  rw [hprod, hilbertSymbol_ramified_eq hp hw (hu.mul hu'), hilbertSymbol_ramified_eq hp hw hu,
    hilbertSymbol_ramified_eq hp hw hu', hqc]
  by_cases hn : Even n
  · by_cases hm : Even m
    · rw [if_pos hn, if_pos hm, if_pos (Int.even_add.mpr (iff_of_true hn hm))]
      ring
    · rw [if_pos hn, if_neg hm, if_neg (fun hc => hm ((Int.even_add.mp hc).mp hn))]
      ring
  · by_cases hm : Even m
    · rw [if_neg hn, if_pos hm, if_neg (fun hc => hn ((Int.even_add.mp hc).mpr hm))]
      ring
    · rw [if_neg hn, if_neg hm, if_pos (Int.even_add.mpr (iff_of_false hn hm))]
      linear_combination (-(quadraticChar (ZMod p) (PadicInt.toZMod u)
        * quadraticChar (ZMod p) (PadicInt.toZMod u'))) * hX

end InverseGalois.CFT.Local
