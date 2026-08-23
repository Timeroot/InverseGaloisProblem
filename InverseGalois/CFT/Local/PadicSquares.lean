import Mathlib

/-!
# Squares in the `p`-adic numbers

This file develops the elementary theory of squares in `ℤ_[p]` and `ℚ_[p]` for an odd prime `p`.
The central input is Hensel's lemma: for `p` odd, a `p`-adic unit is a square exactly when its
residue in `ZMod p` is a square, because the derivative of `X ^ 2 - C u` at an approximate root
is a unit. From this one reads off the description of the squares of `ℚ_[p]ˣ`: an element is a
square precisely when it can be written as `p ^ (2 * n)` times a unit with square residue.

These are the basic facts underlying local class field theory at a finite place, and in
particular the computation of the Hilbert symbol over `ℚ_[p]`.

## Main results

* `InverseGalois.CFT.Local.isSquare_of_isSquare_toZMod`: for `p` odd, a unit of `ℤ_[p]` whose
  residue mod `p` is a square is itself a square.
* `InverseGalois.CFT.Local.isSquare_iff_isSquare_toZMod`: the resulting characterisation of the
  squares among the units of `ℤ_[p]`.
* `InverseGalois.CFT.Local.isSquare_coe_iff`: a unit of `ℤ_[p]` is a square in `ℚ_[p]` if and
  only if it is a square in `ℤ_[p]`.
* `InverseGalois.CFT.Local.exists_unit_mul_zpow`: every nonzero element of `ℚ_[p]` is a power of
  `p` times a unit of `ℤ_[p]`.
* `InverseGalois.CFT.Local.isSquare_iff_exists`: for `p` odd, the description of the squares of
  `ℚ_[p]ˣ` in terms of an even power of `p` and a unit with square residue.
* `InverseGalois.CFT.Local.exists_not_isSquare_unit` and
  `InverseGalois.CFT.Local.not_isSquare_p`: two independent nontrivial square classes, `u` with
  nonsquare residue and the uniformiser `p` itself.
* `InverseGalois.CFT.Local.isSquare_real_iff`: the archimedean analogue.
-/

namespace InverseGalois.CFT.Local

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- For an odd prime `p`, the element `2` is a unit of `ℤ_[p]`, that is, it has norm one. -/
theorem norm_two (hp : p ≠ 2) : ‖(2 : ℤ_[p])‖ = 1 := by
  by_contra h
  have h1 : ‖(2 : ℤ_[p])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) h
  have h2 : ((2 : ℤ) : ℤ_[p]) = (2 : ℤ_[p]) := by push_cast; ring
  rw [← h2, PadicInt.norm_int_lt_one_iff_dvd] at h1
  have h3 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h1
  have := (Fact.out : p.Prime).two_le
  omega

/-- Hensel's lemma for squares: for an odd prime `p`, a unit of `ℤ_[p]` whose residue in
`ZMod p` is a square is itself a square in `ℤ_[p]`. -/
theorem isSquare_of_isSquare_toZMod (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u)
    (h : IsSquare (PadicInt.toZMod u)) : IsSquare u := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) b
  have hane : PadicInt.toZMod a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hb
    exact (hu.map PadicInt.toZMod).ne_zero hb
  have hker : ∀ x : ℤ_[p], ‖x‖ < 1 → PadicInt.toZMod x = 0 := by
    intro x hx
    have hmem : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx
    exact hmem
  have hanorm : ‖a‖ = 1 := by
    rw [← PadicInt.isUnit_iff]
    by_contra hna
    exact hane (hker a (PadicInt.not_isUnit_iff.mp hna))
  have hker' : ∀ x : ℤ_[p], PadicInt.toZMod x = 0 → ‖x‖ < 1 := by
    intro x hx
    have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod]; exact hx
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
    exact hm
  have hsmall : ‖a * a - u‖ < 1 := by
    refine hker' _ ?_
    simp [hb]
  set F : Polynomial ℤ_[p] := X ^ 2 - C u with hF
  have hev : F.aeval a = a * a - u := by simp [hF, sq]
  have hder : F.derivative.aeval a = 2 * a := by
    simp [hF]
    norm_num
  have hdnorm : ‖F.derivative.aeval a‖ = 1 := by
    rw [hder, norm_mul, norm_two hp, hanorm, mul_one]
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hdnorm, one_pow, hev]; exact hsmall
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hz2 : z ^ 2 - u = 0 := by simpa [hF] using hz
  linear_combination -hz2

/-- Reduction modulo `p` carries squares of `ℤ_[p]` to squares of `ZMod p`. -/
theorem isSquare_toZMod_of_isSquare {u : ℤ_[p]} (h : IsSquare u) :
    IsSquare (PadicInt.toZMod u) := h.map PadicInt.toZMod

/-- For an odd prime `p`, a unit of `ℤ_[p]` is a square exactly when its residue mod `p` is. -/
theorem isSquare_iff_isSquare_toZMod (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare u ↔ IsSquare (PadicInt.toZMod u) :=
  ⟨isSquare_toZMod_of_isSquare, isSquare_of_isSquare_toZMod hp hu⟩

/-- A unit of `ℤ_[p]` is a square in the field `ℚ_[p]` exactly when it is a square in `ℤ_[p]`:
a square root of a unit automatically has norm one. -/
theorem isSquare_coe_iff {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare ((u : ℚ_[p])) ↔ IsSquare u := by
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h => h.map (algebraMap ℤ_[p] ℚ_[p])⟩
  have hun : ‖(u : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hu
  have hyy : ‖y‖ * ‖y‖ = 1 := by rw [← norm_mul, ← hy, hun]
  have hy1 : ‖y‖ = 1 := by nlinarith [norm_nonneg y]
  refine ⟨⟨y, hy1.le⟩, ?_⟩
  apply Subtype.coe_injective
  exact hy

/-- Every nonzero `p`-adic number is an integral power of `p` times a unit of `ℤ_[p]`. -/
theorem exists_unit_mul_zpow {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : ℤ_[p]), IsUnit u ∧ x = (p : ℚ_[p]) ^ n * (u : ℚ_[p]) := by
  have hpR : ((p : ℝ)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  set n := x.valuation with hn
  have hnorm : ‖x * (p : ℚ_[p]) ^ (-n)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p_zpow, ← hn,
      ← zpow_add₀ hpR]
    simp
  refine ⟨n, ⟨x * (p : ℚ_[p]) ^ (-n), hnorm.le⟩, PadicInt.isUnit_iff.mpr hnorm, ?_⟩
  show x = (p : ℚ_[p]) ^ n * (x * (p : ℚ_[p]) ^ (-n))
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  rw [zpow_neg, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hp0), one_mul]

/-- For an odd prime `p`, a nonzero `p`-adic number is a square exactly when it is an even power
of `p` times a unit of `ℤ_[p]` whose residue mod `p` is a square. -/
theorem isSquare_iff_exists (hp : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0) :
    IsSquare x ↔ ∃ (n : ℤ) (u : ℤ_[p]), IsUnit u ∧ IsSquare (PadicInt.toZMod u) ∧
      x = (p : ℚ_[p]) ^ (2 * n) * (u : ℚ_[p]) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_zpow hy
    refine ⟨n, u * u, hu.mul hu, IsSquare.map (a := u * u) PadicInt.toZMod ⟨u, rfl⟩, ?_⟩
    rw [two_mul, zpow_add₀ (NeZero.ne _)]
    push_cast
    ring
  · rintro ⟨n, u, hu, hsq, rfl⟩
    obtain ⟨w, hw⟩ := isSquare_of_isSquare_toZMod hp hu hsq
    refine ⟨(p : ℚ_[p]) ^ n * (w : ℚ_[p]), ?_⟩
    rw [hw, two_mul, zpow_add₀ (NeZero.ne _)]
    push_cast
    ring

/-- For an odd prime `p` there is a unit of `ℤ_[p]` that is not a square in `ℚ_[p]`, namely any
lift of a nonsquare residue mod `p`. -/
theorem exists_not_isSquare_unit (hp : p ≠ 2) :
    ∃ u : ℤ_[p], IsUnit u ∧ ¬ IsSquare (u : ℚ_[p]) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  obtain ⟨u, hu⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) a
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  have hunit : IsUnit u := by
    by_contra h
    rw [PadicInt.not_isUnit_iff] at h
    have hm : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]; exact h
    rw [← PadicInt.ker_toZMod] at hm
    exact ha0 (hu ▸ hm)
  exact ⟨u, hunit, fun h => ha (hu ▸ ((isSquare_coe_iff hunit).mp h).map PadicInt.toZMod)⟩

/-- The uniformiser `p` is never a square in `ℚ_[p]`, since its valuation is odd. -/
theorem not_isSquare_p : ¬ IsSquare ((p : ℚ_[p])) := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact (NeZero.ne ((p : ℚ_[p]))) hy
  have hval := Padic.valuation_mul hy0 hy0
  rw [← hy, Padic.valuation_p] at hval
  omega

/-- The valuation of a nonzero square in `ℚ_[p]` is even. -/
theorem even_valuation_of_isSquare {x : ℚ_[p]} (hx : x ≠ 0) (h : IsSquare x) :
    Even x.valuation := by
  obtain ⟨y, rfl⟩ := h
  have hy : y ≠ 0 := by rintro rfl; simp at hx
  rw [Padic.valuation_mul hy hy]
  exact ⟨y.valuation, rfl⟩

/-- The archimedean analogue: a real number is a square exactly when it is nonnegative. -/
theorem isSquare_real_iff (x : ℝ) : IsSquare x ↔ 0 ≤ x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ mul_self_nonneg y,
    fun h => ⟨Real.sqrt x, (Real.mul_self_sqrt h).symm⟩⟩

end InverseGalois.CFT.Local
