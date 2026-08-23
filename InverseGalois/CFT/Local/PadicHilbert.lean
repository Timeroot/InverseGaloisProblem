import Mathlib
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Local.PadicSquares

/-!
# The Hilbert symbol over `ℚ_[p]` for an odd prime `p`

Following Serre, *A Course in Arithmetic*, Chapter III §1, this file computes the Hilbert symbol
of two `p`-adic numbers at an odd finite place in the two configurations that matter: a pair of
units, and the uniformiser against a unit.

The first computation is a counting argument in the residue field followed by Hensel's lemma.
Over the finite field `ZMod p` with `p` odd the two sets `{ū x ^ 2}` and `{1 - v̄ y ^ 2}` are too
large to be disjoint, so the equation `ū x ^ 2 + v̄ y ^ 2 = 1` is solvable; lifting `x` and `y`
arbitrarily to `ℤ_[p]` makes `u x₀ ^ 2 + v y₀ ^ 2` a unit congruent to `1` mod `p`, hence a
square, and the resulting triple is a point of the conic.  So the form `⟨u, v⟩` is isotropic and
the symbol of two units is `1`.

The second computation is a valuation argument.  If `p = s ^ 2 - u t ^ 2` with `u` a unit, then
dividing by `t ^ 2` writes the element `c = p / t ^ 2`, whose valuation `1 - 2 v(t)` is odd, as
`r ^ 2 - u`.  A negative valuation for `c` would force `2 v(r) = v(c)`, an impossible parity, so
`c` lies in the maximal ideal; then `r` is a unit of `ℤ_[p]` and reduction mod `p` exhibits the
residue of `u` as the square of the residue of `r`.  Hence `⟨p, u⟩ = 1` exactly when `u` is a
square modulo `p`.

Together with the invariance of the symbol under squares these give the value of `⟨a, b⟩` for
any two `p`-adic numbers of even valuation.

## Main results

* `InverseGalois.CFT.Local.exists_add_sq_eq_one`: over `ZMod p` with `p` odd, the equation
  `a * x ^ 2 + b * y ^ 2 = 1` is solvable for any two nonzero coefficients.
* `InverseGalois.CFT.Local.isHilbertIsotropic_of_isUnit`: for `p` odd, the binary form attached
  to two units of `ℤ_[p]` is isotropic over `ℚ_[p]`.
* `InverseGalois.CFT.Local.hilbertSymbol_unit_unit`,
  `InverseGalois.CFT.Local.hilbertSymbol_eq_one_of_norm_eq_one`: consequently the Hilbert symbol
  of two `p`-adic units is `1`.
* `InverseGalois.CFT.Local.isSquare_toZMod_of_eq_sub_sq`: if the uniformiser is a norm from the
  quadratic extension attached to a unit `u`, then the residue of `u` is a square.
* `InverseGalois.CFT.Local.hilbertSymbol_p_unit`: the symbol of the uniformiser against a unit
  is `1` exactly when the residue of the unit is a square mod `p`.
* `InverseGalois.CFT.Local.hilbertSymbol_of_even_valuations`: two nonzero `p`-adic numbers of
  even valuation have Hilbert symbol `1`.
* `InverseGalois.CFT.Local.toZMod_eq_zero_iff`,
  `InverseGalois.CFT.Local.toZMod_ne_zero_iff_isUnit`: the residue map detects units.
* `InverseGalois.CFT.Local.valuation_eq_of_norm_eq`,
  `InverseGalois.CFT.Local.valuation_coe_eq_zero`: valuation bookkeeping used throughout.
-/

namespace InverseGalois.CFT.Local

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- A `p`-adic integer has residue zero mod `p` exactly when its norm is less than one: the
kernel of the residue map is the maximal ideal, which consists of the nonunits. -/
theorem toZMod_eq_zero_iff {x : ℤ_[p]} : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

/-- A `p`-adic integer is a unit exactly when its residue mod `p` is nonzero. -/
theorem toZMod_ne_zero_iff_isUnit {x : ℤ_[p]} : PadicInt.toZMod x ≠ 0 ↔ IsUnit x := by
  rw [ne_eq, toZMod_eq_zero_iff, ← PadicInt.not_isUnit_iff, not_not]

/-- **Every binary quadratic form over an odd residue field represents one.**  For `p` an odd
prime and `a`, `b` nonzero in `ZMod p`, the equation `a * x ^ 2 + b * y ^ 2 = 1` has a solution:
the two quadratic polynomials `a * X ^ 2` and `b * X ^ 2 - 1` take a common negated value, since
each of their value sets covers more than half the field. -/
theorem exists_add_sq_eq_one (hp : p ≠ 2) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : ZMod p, a * x ^ 2 + b * y ^ 2 = 1 := by
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hf : (C a * X ^ 2 : (ZMod p)[X]).degree = 2 := by
    simpa using degree_C_mul_X_pow 2 ha
  have h1 : (C b * X ^ 2 : (ZMod p)[X]).degree = 2 := by
    simpa using degree_C_mul_X_pow 2 hb
  have hg : (C b * X ^ 2 - 1 : (ZMod p)[X]).degree = 2 := by
    rw [← C_1, degree_sub_C (by rw [h1]; norm_num), h1]
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one] at hxy
  linear_combination hxy

/-- **The form attached to two `p`-adic units is isotropic**, for `p` odd.  Solve
`ū x ^ 2 + v̄ y ^ 2 = 1` in the residue field and lift the solution arbitrarily: the value
`w = u x₀ ^ 2 + v y₀ ^ 2` is then a unit whose residue is `1`, hence a square by Hensel's lemma,
and a square root of `w` completes `(x₀, y₀)` to a point of the conic. -/
theorem isHilbertIsotropic_of_isUnit (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u) (hv : IsUnit v) :
    IsHilbertIsotropic ((u : ℚ_[p])) ((v : ℚ_[p])) := by
  obtain ⟨x, y, hxy⟩ := exists_add_sq_eq_one hp
    (toZMod_ne_zero_iff_isUnit.mpr hu) (toZMod_ne_zero_iff_isUnit.mpr hv)
  obtain ⟨x₀, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) x
  obtain ⟨y₀, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) y
  set w : ℤ_[p] := u * x₀ ^ 2 + v * y₀ ^ 2 with hw
  have hwZ : PadicInt.toZMod w = 1 := by
    rw [hw]
    push_cast [map_add, map_mul, map_pow]
    exact hxy
  have hwu : IsUnit w := toZMod_ne_zero_iff_isUnit.mp (by rw [hwZ]; exact one_ne_zero)
  obtain ⟨z₀, hz₀⟩ :=
    isSquare_of_isSquare_toZMod hp hwu (by rw [hwZ]; exact ⟨1, (one_mul 1).symm⟩)
  have hz0ne : (z₀ : ℚ_[p]) ≠ 0 := by
    refine PadicInt.coe_ne_zero.mpr ?_
    rintro rfl
    rw [mul_zero] at hz₀
    exact hwu.ne_zero hz₀
  refine ⟨(x₀ : ℚ_[p]), (y₀ : ℚ_[p]), (z₀ : ℚ_[p]), fun h => hz0ne h.2.2, ?_⟩
  have hcast : ((w : ℤ_[p]) : ℚ_[p]) = ((z₀ * z₀ : ℤ_[p]) : ℚ_[p]) := by rw [hz₀]
  rw [hw] at hcast
  push_cast at hcast
  linear_combination -hcast

/-- Two nonzero `p`-adic numbers of the same absolute value have the same valuation, the norm
being a strictly decreasing power of `p`. -/
theorem valuation_eq_of_norm_eq {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) (h : ‖x‖ = ‖y‖) :
    x.valuation = y.valuation := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy] at h
  have h2 := (zpow_right_inj₀ (lt_trans zero_lt_one hp1) hp1.ne').mp h
  omega

/-- A unit of `ℤ_[p]` has valuation zero in `ℚ_[p]`. -/
theorem valuation_coe_eq_zero {u : ℤ_[p]} (hu : IsUnit u) : ((u : ℚ_[p])).valuation = 0 := by
  have h1 : ‖(u : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hu
  have hne : (u : ℚ_[p]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have h2 := valuation_eq_of_norm_eq hne (one_ne_zero (α := ℚ_[p])) (by rw [h1, norm_one])
  rwa [Padic.valuation_one] at h2

/-- **The uniformiser is a norm only from the unramified quadratic extension.**  If the
uniformiser `p` is of the shape `s ^ 2 - u t ^ 2` for a unit `u` of `ℤ_[p]`, then the residue of
`u` mod `p` is a square.  Indeed `t` cannot vanish, and `c = p / t ^ 2` has odd valuation while
satisfying `r ^ 2 = u + c` for `r = s / t`; a negative valuation for `c` would make it the
valuation of the square `r ^ 2`, which is even, so `c` lies in the maximal ideal, `r` is a unit
of `ℤ_[p]`, and reducing `r ^ 2 - u` mod `p` gives the assertion. -/
theorem isSquare_toZMod_of_eq_sub_sq {u : ℤ_[p]} (hu : IsUnit u) {s t : ℚ_[p]}
    (h : (p : ℚ_[p]) = s ^ 2 - (u : ℚ_[p]) * t ^ 2) : IsSquare (PadicInt.toZMod u) := by
  have hunorm : ‖(u : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hu
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have ht : t ≠ 0 := by
    rintro rfl
    refine not_isSquare_p (p := p) ⟨s, ?_⟩
    rw [h]; ring
  set c : ℚ_[p] := (p : ℚ_[p]) / t ^ 2 with hcdef
  set r : ℚ_[p] := s / t with hrdef
  have hc : r ^ 2 = (u : ℚ_[p]) + c := by
    rw [hrdef, hcdef, div_pow]
    field_simp
    linear_combination -h
  have hcne : c ≠ 0 := div_ne_zero hp0 (pow_ne_zero 2 ht)
  have hcval : c.valuation = 1 - 2 * t.valuation := by
    rw [hcdef, div_eq_mul_inv, Padic.valuation_mul hp0 (inv_ne_zero (pow_ne_zero 2 ht)),
      Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]
    ring
  have hcne1 : ‖c‖ ≠ 1 := by
    intro h1
    have h2 := valuation_eq_of_norm_eq hcne (one_ne_zero (α := ℚ_[p])) (by rw [h1, norm_one])
    rw [Padic.valuation_one, hcval] at h2
    omega
  rcases lt_or_gt_of_ne hcne1 with hlt | hgt
  · have hne : ‖(u : ℚ_[p])‖ ≠ ‖c‖ := by rw [hunorm]; exact fun h' => hcne1 h'.symm
    have hr2 : ‖r ^ 2‖ = 1 := by
      rw [hc, Padic.add_eq_max_of_ne hne, hunorm, max_eq_left hlt.le]
    have hrn : ‖r‖ = 1 := by
      rw [norm_pow] at hr2
      nlinarith [norm_nonneg r]
    set R : ℤ_[p] := ⟨r, hrn.le⟩ with hR
    have hRc : ((R : ℤ_[p]) : ℚ_[p]) = r := rfl
    have hdiff : ‖R ^ 2 - u‖ < 1 := by
      have hval : ((R ^ 2 - u : ℤ_[p]) : ℚ_[p]) = c := by
        push_cast [hRc]
        linear_combination hc
      rw [PadicInt.norm_def, hval]
      exact hlt
    have hz : PadicInt.toZMod (R ^ 2 - u) = 0 := toZMod_eq_zero_iff.mpr hdiff
    refine ⟨PadicInt.toZMod R, ?_⟩
    rw [map_sub, map_pow, sub_eq_zero] at hz
    rw [← hz]; ring
  · have hne : ‖(u : ℚ_[p])‖ ≠ ‖c‖ := by rw [hunorm]; exact fun h' => hcne1 h'.symm
    have hr2 : ‖r ^ 2‖ = ‖c‖ := by
      rw [hc, Padic.add_eq_max_of_ne hne, hunorm, max_eq_right hgt.le]
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hr2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero] at hr2
      exact hcne (norm_eq_zero.mp hr2.symm)
    have hval := valuation_eq_of_norm_eq (pow_ne_zero 2 hrne) hcne hr2
    rw [Padic.valuation_pow, hcval] at hval
    omega

/-- **The Hilbert symbol of two `p`-adic units is `1`**, for `p` odd. -/
theorem hilbertSymbol_unit_unit (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ((u : ℚ_[p])) ((v : ℚ_[p])) = 1 :=
  hilbertSymbol_eq_one_iff.mpr (isHilbertIsotropic_of_isUnit hp hu hv)

/-- The Hilbert symbol of two `p`-adic numbers of absolute value one is `1`, for `p` odd: this is
the previous statement phrased inside `ℚ_[p]`. -/
theorem hilbertSymbol_eq_one_of_norm_eq_one (hp : p ≠ 2) {a b : ℚ_[p]} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) : hilbertSymbol a b = 1 :=
  hilbertSymbol_unit_unit (u := ⟨a, ha.le⟩) (v := ⟨b, hb.le⟩) hp
    (PadicInt.isUnit_iff.mpr ha) (PadicInt.isUnit_iff.mpr hb)

/-- **The Hilbert symbol of the uniformiser against a unit**, for `p` odd: it is `1` exactly when
the residue of the unit is a square mod `p`.  One direction is Hensel's lemma, which makes such a
unit a square in `ℚ_[p]`; the other is the norm description of the symbol together with the
parity of the valuation of a norm from the unramified quadratic extension. -/
theorem hilbertSymbol_p_unit (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u) :
    hilbertSymbol ((p : ℚ_[p])) ((u : ℚ_[p])) = 1 ↔ IsSquare (PadicInt.toZMod u) := by
  refine ⟨fun hsym => ?_, fun hsq => ?_⟩
  · by_contra hns
    have hnsq : ¬ IsSquare ((u : ℚ_[p])) := fun hs =>
      hns (((isSquare_coe_iff hu).mp hs).map PadicInt.toZMod)
    obtain ⟨a, b, hab⟩ := (hilbertSymbol_eq_one_iff_exists_sub_sq hnsq).mp hsym
    exact hns (isSquare_toZMod_of_eq_sub_sq hu hab)
  · exact hilbertSymbol_of_isSquare_right _ _
      ((isSquare_coe_iff hu).mpr (isSquare_of_isSquare_toZMod hp hu hsq))

/-- The Hilbert symbol of the uniformiser against its negative is `1`. -/
theorem hilbertSymbol_p_neg_p : hilbertSymbol ((p : ℚ_[p])) (-(p : ℚ_[p])) = 1 :=
  hilbertSymbol_neg_self _

/-- **Two `p`-adic numbers of even valuation have Hilbert symbol `1`**, for `p` odd: strip the
even powers of the uniformiser, which are squares and so do not change the symbol, and apply the
computation for two units. -/
theorem hilbertSymbol_of_even_valuations (hp : p ≠ 2) {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : Even a.valuation) (hvb : Even b.valuation) : hilbertSymbol a b = 1 := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  obtain ⟨m, u, hu, rfl⟩ := exists_unit_mul_zpow ha
  obtain ⟨n, v, hv, rfl⟩ := exists_unit_mul_zpow hb
  have hune : ((u : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  have hvne : ((v : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hv.ne_zero
  rw [Padic.valuation_mul (zpow_ne_zero _ hp0) hune, Padic.valuation_zpow, Padic.valuation_p,
    valuation_coe_eq_zero hu] at hva
  rw [Padic.valuation_mul (zpow_ne_zero _ hp0) hvne, Padic.valuation_zpow, Padic.valuation_p,
    valuation_coe_eq_zero hv] at hvb
  obtain ⟨m', hm'⟩ := hva
  obtain ⟨n', hn'⟩ := hvb
  have hmm : m = m' * 2 := by omega
  have hnn : n = n' * 2 := by omega
  have hA : (p : ℚ_[p]) ^ m * (u : ℚ_[p]) = (u : ℚ_[p]) * ((p : ℚ_[p]) ^ m') ^ (2 : ℕ) := by
    rw [hmm, zpow_mul, mul_comm, ← zpow_natCast ((p : ℚ_[p]) ^ m') 2]
    norm_num
  have hB : (p : ℚ_[p]) ^ n * (v : ℚ_[p]) = (v : ℚ_[p]) * ((p : ℚ_[p]) ^ n') ^ (2 : ℕ) := by
    rw [hnn, zpow_mul, mul_comm, ← zpow_natCast ((p : ℚ_[p]) ^ n') 2]
    norm_num
  rw [hA, hB, hilbertSymbol_mul_sq_left _ _ _ (zpow_ne_zero _ hp0),
    hilbertSymbol_mul_sq_right _ _ _ (zpow_ne_zero _ hp0)]
  exact hilbertSymbol_unit_unit hp hu hv

end InverseGalois.CFT.Local
