import Mathlib
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.PadicSquaresTwo

/-!
# The Hilbert symbol of two dyadic units

At an odd finite place the Hilbert symbol of two units is always `1`, because the residue field
is large enough for a counting argument.  At the dyadic place this fails, and the answer depends
on the residues modulo `4`: for units `u` and `v` of `ℤ_[2]` the conic
`z ^ 2 = u x ^ 2 + v y ^ 2` has a nontrivial dyadic point exactly when `u ≡ 1` or `v ≡ 1`
modulo `4`.  This is Serre, *A Course in Arithmetic*, Chapter III §1, Theorem 2 in the case
`α = β = 0`.

Both directions come from the description of the dyadic squares in
`InverseGalois/CFT/Local/PadicSquaresTwo.lean`, a dyadic integer being a square as soon as it is
congruent to `1` modulo `8`.

* For solvability one exhibits a point with small integral coordinates: `(x, y) = (1, 0)` when
  `u ≡ 1 mod 8` and `(x, y) = (1, 2)` when `u ≡ 5 mod 8`, since `5 + 4 v ≡ 1 mod 8` for every
  dyadic unit `v`.  In both cases `u x ^ 2 + v y ^ 2` is congruent to `1` modulo `8`, hence is a
  square `z ^ 2`, and `z` is nonzero.
* For unsolvability one first normalises a hypothetical rational point: dividing the three
  coordinates by whichever of them has the largest dyadic absolute value produces an integral
  point at least one of whose coordinates is a unit.  Reducing such a point modulo `8` and
  running through the finitely many possibilities gives a contradiction when both `u` and `v`
  are congruent to `3` modulo `4`, the squares of `ZMod 8` being `0`, `1` and `4`.

Congruences modulo `8` and modulo `4` are expressed through the ring homomorphisms
`PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)` and `PadicInt.toZModPow 2 : ℤ_[2] →+* ZMod (2 ^ 2)`.

## Main results

* `InverseGalois.CFT.Local.isHilbertIsotropic_of_exists_toZModPow`: a pair of dyadic integers
  representing a value congruent to `1` modulo `8` has isotropic form.
* `InverseGalois.CFT.Local.exists_primitive_of_isHilbertIsotropic`: an isotropic dyadic form has
  an integral point one of whose coordinates is a unit.
* `InverseGalois.CFT.Local.not_isHilbertIsotropic_of_forall_toZModPow`: the resulting obstruction
  modulo `8`.
* `InverseGalois.CFT.Local.hilbertSymbol_units_two`: **the dyadic symbol of two units**, equal to
  `1` exactly when one of them is congruent to `1` modulo `4`.
* `InverseGalois.CFT.Local.hilbertSymbol_units_two_eq`: the same computation, as a closed formula.
* `InverseGalois.CFT.Local.hilbertSymbol_neg_one_neg_one_two`: the Hamilton quaternions do not
  split over `ℚ_[2]`.
* `InverseGalois.CFT.Local.hilbertSymbol_units_two_mul`: the symbol is multiplicative on the
  units of `ℤ_[2]`.
-/

namespace InverseGalois.CFT.Local

/-- A dyadic integer whose image in `ℚ_[2]` is `1` is a unit. -/
theorem isUnit_of_coe_eq_one {x : ℤ_[2]} (h : (x : ℚ_[2]) = 1) : IsUnit x := by
  rw [PadicInt.isUnit_iff, ← PadicInt.padic_norm_e_of_padicInt, h, norm_one]

/-- A quotient of dyadic numbers whose numerator has absolute value at most that of the
denominator is a dyadic integer. -/
theorem exists_coe_eq_div_of_norm_le {X W : ℚ_[2]} (h : ‖X‖ ≤ ‖W‖) :
    ∃ x : ℤ_[2], (x : ℚ_[2]) = X / W := by
  refine ⟨⟨X / W, ?_⟩, rfl⟩
  rw [norm_div]
  exact div_le_one_of_le₀ h (norm_nonneg _)

/-- **A sufficient condition for isotropy at the dyadic place.**  If the dyadic integers `a` and
`b` represent, at the integral point `(x, y)`, a value congruent to `1` modulo `8`, then that
value is a square `z ^ 2` with `z` nonzero and `(x, y, z)` is a point of the conic. -/
theorem isHilbertIsotropic_of_exists_toZModPow (a b x y : ℤ_[2])
    (h : PadicInt.toZModPow 3 (a * x ^ 2 + b * y ^ 2) = 1) :
    IsHilbertIsotropic (a : ℚ_[2]) (b : ℚ_[2]) := by
  obtain ⟨z, hz⟩ := isSquare_of_toZModPow_three_eq_one h
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [hz, mul_zero, map_zero] at h
    exact absurd h (by decide)
  refine ⟨(x : ℚ_[2]), (y : ℚ_[2]), (z : ℚ_[2]), ?_, ?_⟩
  · rintro ⟨-, -, h0⟩
    exact hzne (Subtype.ext h0)
  · have hq := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
    push_cast at hq
    rw [sq]
    exact hq.symm

/-- **Normalisation of a dyadic point of a conic.**  An isotropic form with dyadic integral
coefficients has an integral point at least one of whose coordinates is a unit: divide a
nontrivial rational point by whichever of its coordinates has the largest absolute value, which
is legitimate because the equation is homogeneous of degree two. -/
theorem exists_primitive_of_isHilbertIsotropic {a b : ℤ_[2]}
    (h : IsHilbertIsotropic (a : ℚ_[2]) (b : ℚ_[2])) :
    ∃ x y z : ℤ_[2], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  obtain ⟨X, Y, Z, hne, heq⟩ := h
  obtain ⟨W, hWmem, hX, hY, hZ⟩ : ∃ W : ℚ_[2], (W = X ∨ W = Y ∨ W = Z) ∧
      ‖X‖ ≤ ‖W‖ ∧ ‖Y‖ ≤ ‖W‖ ∧ ‖Z‖ ≤ ‖W‖ := by
    rcases le_total ‖X‖ ‖Y‖ with h1 | h1 <;> rcases le_total ‖Y‖ ‖Z‖ with h2 | h2 <;>
      rcases le_total ‖X‖ ‖Z‖ with h3 | h3 <;>
      first
        | exact ⟨X, Or.inl rfl, le_rfl, by linarith, by linarith⟩
        | exact ⟨Y, Or.inr (Or.inl rfl), by linarith, le_rfl, by linarith⟩
        | exact ⟨Z, Or.inr (Or.inr rfl), by linarith, by linarith, le_rfl⟩
  have hW : W ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hX hY hZ
    exact hne ⟨norm_le_zero_iff.mp hX, norm_le_zero_iff.mp hY, norm_le_zero_iff.mp hZ⟩
  obtain ⟨x, hx⟩ := exists_coe_eq_div_of_norm_le hX
  obtain ⟨y, hy⟩ := exists_coe_eq_div_of_norm_le hY
  obtain ⟨z, hz⟩ := exists_coe_eq_div_of_norm_le hZ
  refine ⟨x, y, z, ?_, ?_⟩
  · rcases hWmem with rfl | rfl | rfl
    · exact Or.inl (isUnit_of_coe_eq_one (by rw [hx, div_self hW]))
    · exact Or.inr (Or.inl (isUnit_of_coe_eq_one (by rw [hy, div_self hW])))
    · exact Or.inr (Or.inr (isUnit_of_coe_eq_one (by rw [hz, div_self hW])))
  · apply Subtype.coe_injective
    push_cast
    rw [hx, hy, hz]
    field_simp
    linear_combination heq

/-- **The obstruction modulo `8`.**  If the reductions of `a` and `b` modulo `8` represent no
value `z ^ 2` at a point of `ZMod 8` with a unit coordinate, then the form `⟨a, b⟩` is
anisotropic over `ℚ_[2]`: a point would normalise to an integral one with a unit coordinate,
whose reduction modulo `8` is such a representation. -/
theorem not_isHilbertIsotropic_of_forall_toZModPow {a b : ℤ_[2]}
    (h : ∀ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) →
        z ^ 2 ≠ PadicInt.toZModPow 3 a * x ^ 2 + PadicInt.toZModPow 3 b * y ^ 2) :
    ¬ IsHilbertIsotropic (a : ℚ_[2]) (b : ℚ_[2]) := by
  intro hiso
  obtain ⟨x, y, z, hprim, heq⟩ := exists_primitive_of_isHilbertIsotropic hiso
  refine h (PadicInt.toZModPow 3 x) (PadicInt.toZModPow 3 y) (PadicInt.toZModPow 3 z) ?_ ?_
  · rcases hprim with hunit | hunit | hunit
    · exact Or.inl (hunit.map _)
    · exact Or.inr (Or.inl (hunit.map _))
    · exact Or.inr (Or.inr (hunit.map _))
  · have hmap := congrArg (PadicInt.toZModPow 3) heq
    simpa using hmap

/-- A dyadic unit is congruent to `1` modulo `4` exactly when its residue modulo `8` is `1`
or `5`. -/
theorem toZModPow_two_eq_one_iff {u : ℤ_[2]} (hu : IsUnit u) :
    PadicInt.toZModPow 2 u = 1 ↔
      (PadicInt.toZModPow 3 u = 1 ∨ PadicInt.toZModPow 3 u = 5) := by
  rw [← PadicInt.cast_toZModPow 2 3 (by norm_num) u]
  have hr := hu.map (PadicInt.toZModPow 3)
  revert hr
  generalize PadicInt.toZModPow 3 u = r
  revert r
  decide

/-- A dyadic unit congruent to `1` modulo `4` has Hilbert symbol `1` against any dyadic unit:
the point `(1, 0)` works when `u ≡ 1 mod 8`, and the point `(1, 2)` works when `u ≡ 5 mod 8`
because `5 + 4 v ≡ 1 mod 8` for every unit `v`. -/
theorem hilbertSymbol_eq_one_of_toZModPow_three {u v : ℤ_[2]} (hv : IsUnit v)
    (hu : PadicInt.toZModPow 3 u = 1 ∨ PadicInt.toZModPow 3 u = 5) :
    hilbertSymbol (u : ℚ_[2]) (v : ℚ_[2]) = 1 := by
  rw [hilbertSymbol_eq_one_iff]
  have h2 : PadicInt.toZModPow 3 (2 : ℤ_[2]) = 2 := map_ofNat _ 2
  rcases hu with hu | hu
  · refine isHilbertIsotropic_of_exists_toZModPow u v 1 0 ?_
    simpa using hu
  · refine isHilbertIsotropic_of_exists_toZModPow u v 1 2 ?_
    simp only [map_add, map_mul, map_pow, map_one, h2, one_pow, hu]
    have hs := hv.map (PadicInt.toZModPow 3)
    revert hs
    generalize PadicInt.toZModPow 3 v = s
    revert s
    decide

/-- **The anisotropy of `⟨3, 3⟩` modulo `8`.**  If `r` and `s` are congruent to `3` modulo `4`,
no triple of `ZMod 8` with a unit coordinate satisfies `z ^ 2 = r x ^ 2 + s y ^ 2`, the squares
of `ZMod 8` being `0`, `1` and `4`. -/
theorem sq_ne_of_mod_four_eq_three : ∀ r s : ZMod 8, (r = 3 ∨ r = 7) → (s = 3 ∨ s = 7) →
    ∀ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) → z ^ 2 ≠ r * x ^ 2 + s * y ^ 2 := by
  decide

/-- **The Hilbert symbol of two dyadic units.**  For units `u` and `v` of `ℤ_[2]` the form
`⟨u, v⟩` is isotropic over `ℚ_[2]` exactly when `u` or `v` is congruent to `1` modulo `4`.
Compare Serre, *A Course in Arithmetic*, Chapter III §1, Theorem 2. -/
theorem hilbertSymbol_units_two {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol (u : ℚ_[2]) (v : ℚ_[2]) = 1 ↔
      PadicInt.toZModPow 2 u = 1 ∨ PadicInt.toZModPow 2 v = 1 := by
  have hthree : ∀ r : ZMod (2 ^ 3), IsUnit r → ¬(r = 1 ∨ r = 5) → (r = 3 ∨ r = 7) := by decide
  constructor
  · intro h1
    by_contra hcon
    push_neg at hcon
    obtain ⟨hu4, hv4⟩ := hcon
    have hr : PadicInt.toZModPow 3 u = 3 ∨ PadicInt.toZModPow 3 u = 7 :=
      hthree _ (hu.map _) fun h => hu4 ((toZModPow_two_eq_one_iff hu).mpr h)
    have hs : PadicInt.toZModPow 3 v = 3 ∨ PadicInt.toZModPow 3 v = 7 :=
      hthree _ (hv.map _) fun h => hv4 ((toZModPow_two_eq_one_iff hv).mpr h)
    exact not_isHilbertIsotropic_of_forall_toZModPow
      (fun x y z hp => sq_ne_of_mod_four_eq_three _ _ hr hs x y z hp)
      (hilbertSymbol_eq_one_iff.mp h1)
  · rintro (h | h)
    · exact hilbertSymbol_eq_one_of_toZModPow_three hv ((toZModPow_two_eq_one_iff hu).mp h)
    · rw [hilbertSymbol_comm]
      exact hilbertSymbol_eq_one_of_toZModPow_three hu ((toZModPow_two_eq_one_iff hv).mp h)

/-- The dyadic Hilbert symbol of two units, as a closed formula. -/
theorem hilbertSymbol_units_two_eq {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol (u : ℚ_[2]) (v : ℚ_[2]) =
      if PadicInt.toZModPow 2 u = 1 ∨ PadicInt.toZModPow 2 v = 1 then 1 else -1 := by
  split_ifs with h
  · exact (hilbertSymbol_units_two hu hv).mpr h
  · rcases hilbertSymbol_eq_one_or (u : ℚ_[2]) (v : ℚ_[2]) with h1 | h1
    · exact absurd ((hilbertSymbol_units_two hu hv).mp h1) h
    · exact h1

/-- **The Hamilton quaternions do not split over the dyadic numbers**: the conic
`z ^ 2 = -x ^ 2 - y ^ 2` has no dyadic point other than the origin, since `-1` is congruent
to `3` modulo `4`. -/
theorem hilbertSymbol_neg_one_neg_one_two : hilbertSymbol (-1 : ℚ_[2]) (-1 : ℚ_[2]) = -1 := by
  have hunit : IsUnit (-1 : ℤ_[2]) := isUnit_one.neg
  have hcast : ((-1 : ℤ_[2]) : ℚ_[2]) = -1 := by push_cast; ring
  have hres : PadicInt.toZModPow 2 (-1 : ℤ_[2]) = -1 := by rw [map_neg, map_one]
  have hiff := hilbertSymbol_units_two hunit hunit
  rw [hcast] at hiff
  rcases hilbertSymbol_eq_one_or (-1 : ℚ_[2]) (-1 : ℚ_[2]) with h1 | h1
  · rcases hiff.mp h1 with h2 | h2 <;> rw [hres] at h2 <;> exact absurd h2 (by decide)
  · exact h1

/-- The sign attached to a residue modulo `4` by the dyadic Hilbert symbol is multiplicative:
the units of `ZMod 4` are `1` and `3`, and `3 * 3 = 1`. -/
theorem ite_mul_ite_of_isUnit_four : ∀ r r' s : ZMod 4, IsUnit r → IsUnit r' → IsUnit s →
    (if r * r' = 1 ∨ s = 1 then (1 : ℤ) else -1) =
      (if r = 1 ∨ s = 1 then (1 : ℤ) else -1) * (if r' = 1 ∨ s = 1 then (1 : ℤ) else -1) := by
  decide

/-- **The dyadic Hilbert symbol is multiplicative on units.** -/
theorem hilbertSymbol_units_two_mul {u u' v : ℤ_[2]} (hu : IsUnit u) (hu' : IsUnit u')
    (hv : IsUnit v) :
    hilbertSymbol ((u * u' : ℤ_[2]) : ℚ_[2]) (v : ℚ_[2]) =
      hilbertSymbol (u : ℚ_[2]) (v : ℚ_[2]) * hilbertSymbol (u' : ℚ_[2]) (v : ℚ_[2]) := by
  rw [hilbertSymbol_units_two_eq (hu.mul hu') hv, hilbertSymbol_units_two_eq hu hv,
    hilbertSymbol_units_two_eq hu' hv, map_mul]
  exact ite_mul_ite_of_isUnit_four _ _ _ (hu.map _) (hu'.map _) (hv.map _)

end InverseGalois.CFT.Local
