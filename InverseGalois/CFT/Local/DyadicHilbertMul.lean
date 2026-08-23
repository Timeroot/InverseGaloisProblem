import Mathlib
import InverseGalois.CFT.Local.DyadicHilbert
import InverseGalois.CFT.Local.HilbertIdentities
import InverseGalois.CFT.Local.PadicSquares

/-!
# The dyadic Hilbert symbol, and its bimultiplicativity

The symbol of two units of `ℤ_[2]` is computed in `InverseGalois/CFT/Local/DyadicHilbert.lean`.
This file adds the uniformiser `2` and deduces that the Hilbert symbol of `ℚ_[2]` is
bimultiplicative.

Writing a nonzero dyadic number as `2 ^ α u` with `u` a unit, the symbol of `2 ^ α u` against
`2 ^ β v` is `(-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`, where `ε(u)` vanishes exactly when `u` is
congruent to `1` modulo `4` and `ω(u)` vanishes exactly when `u` is congruent to `±1` modulo `8`.
This is Serre, *A Course in Arithmetic*, Chapter III §1, Theorem 2.  The two signs
`(-1) ^ (ε(u) ε(v))` and `(-1) ^ ω(u)` are the functions `dyadicEpsProd` and `dyadicOmegaSign` of
residues modulo `8`, and each is multiplicative on the units of `ZMod 8`.

Every step is a congruence modulo `8`.  On the one hand a pair of dyadic integers whose residues
represent `1` is isotropic, and one may search for the representing point among the residues
themselves; on the other hand an anisotropy statement is an assertion about the finitely many
primitive triples of `ZMod 8`.  So each of the four shapes `⟨u, v⟩`, `⟨2 u, v⟩`, `⟨u, 2 v⟩` and
`⟨2 u, 2 v⟩` is settled by inspection of the sixteen pairs of units of `ZMod 8`, save the last:
the form `2 u x ^ 2 + 2 v y ^ 2` never represents `1`, and the shape `⟨2 u, 2 v⟩` is instead
reduced to the shape `⟨2 u, w⟩` by the identity `⟨a, b⟩ = ⟨a, -a b⟩` together with
`-(2 u)(2 v) = (-(u v)) 2 ^ 2`.

Bimultiplicativity follows because the square class of a nonzero dyadic number is represented by
a unit or by twice a unit, and because a product of two such representatives is again one, up to
a square.

## Main results

* `InverseGalois.CFT.Local.isHilbertIsotropic_of_exists_zmod`: a pair of dyadic integers whose
  residues represent `1` in `ZMod 8` has isotropic form.
* `InverseGalois.CFT.Local.dyadicEpsProd`, `InverseGalois.CFT.Local.dyadicOmegaSign`: the two
  signs attached to residues modulo `8`, with their multiplicativity.
* `InverseGalois.CFT.Local.hilbertSymbol_units_two_eq'`: the symbol of two units, as a sign.
* `InverseGalois.CFT.Local.hilbertSymbol_two_mul_unit`,
  `InverseGalois.CFT.Local.hilbertSymbol_unit_two_mul`,
  `InverseGalois.CFT.Local.hilbertSymbol_two_mul_two_mul`: the three remaining shapes.
* `InverseGalois.CFT.Local.exists_sq_mul_dyadic_normal_form`: the square classes of `ℚ_[2]` are
  represented by the units of `ℤ_[2]` and their doubles.
* `InverseGalois.CFT.Local.hilbertSymbol_dyadic_mul_left`,
  `InverseGalois.CFT.Local.hilbertSymbol_dyadic_mul_right`: **the dyadic Hilbert symbol is
  bimultiplicative.**
* `InverseGalois.CFT.Local.hilbertSymbol_two_two`,
  `InverseGalois.CFT.Local.hilbertSymbol_two_unit`: the symbol of the uniformiser against itself
  and against a unit.
-/

namespace InverseGalois.CFT.Local

/-! ### A decidable criterion for isotropy -/

/-- The dyadic integer `2` maps to `2` in `ℚ_[2]`. -/
theorem coe_two : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := rfl

/-- The dyadic integer named by the canonical representative of a residue modulo `8` reduces to
that residue. -/
theorem toZModPow_natCast_val (x : ZMod 8) :
    PadicInt.toZModPow 3 ((x.val : ℕ) : ℤ_[2]) = x := by
  rw [map_natCast]
  exact ZMod.natCast_rightInverse x

/-- **A decidable sufficient condition for isotropy at the dyadic place.**  If the residues of
the dyadic integers `a` and `b` modulo `8` represent `1` in `ZMod 8`, then the form `⟨a, b⟩` is
isotropic over `ℚ_[2]`: lift the representing point to the canonical integral representatives of
its coordinates. -/
theorem isHilbertIsotropic_of_exists_zmod (a b : ℤ_[2])
    (h : ∃ x y : ZMod 8, PadicInt.toZModPow 3 a * x ^ 2 + PadicInt.toZModPow 3 b * y ^ 2 = 1) :
    IsHilbertIsotropic (a : ℚ_[2]) (b : ℚ_[2]) := by
  obtain ⟨x, y, hxy⟩ := h
  refine isHilbertIsotropic_of_exists_toZModPow a b ((x.val : ℕ) : ℤ_[2]) ((y.val : ℕ) : ℤ_[2]) ?_
  rw [map_add, map_mul, map_mul, map_pow, map_pow, toZModPow_natCast_val, toZModPow_natCast_val]
  exact hxy

/-! ### The two signs -/

/-- The sign `(-1) ^ ω(u)` attached to a residue `r` modulo `8`, equal to `1` exactly for the
residues `±1`. -/
def dyadicOmegaSign (r : ZMod 8) : ℤ := if r = 1 ∨ r = 7 then 1 else -1

/-- The sign `(-1) ^ (ε(u) ε(v))` attached to a pair of residues modulo `8`, equal to `-1`
exactly when both are congruent to `3` modulo `4`. -/
def dyadicEpsProd (r s : ZMod 8) : ℤ := if (r = 3 ∨ r = 7) ∧ (s = 3 ∨ s = 7) then -1 else 1

/-- The factor contributed to the dyadic Hilbert symbol by a uniformiser in one argument: the
sign `(-1) ^ ω` of the residue of the other argument, or nothing. -/
def dyadicOmegaFactor : Bool → ZMod 8 → ℤ
  | true, s => dyadicOmegaSign s
  | false, _ => 1

/-- The units of `ZMod 8` are the four odd residues. -/
theorem isUnit_zmod_eight : ∀ r : ZMod 8, IsUnit r ↔ (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) := by decide

/-- The sign `(-1) ^ ω` is multiplicative on the units of `ZMod 8`, the residues `±1` forming a
subgroup of index two. -/
theorem dyadicOmegaSign_mul : ∀ r s : ZMod 8, IsUnit r → IsUnit s →
    dyadicOmegaSign (r * s) = dyadicOmegaSign r * dyadicOmegaSign s := by decide

/-- The sign `(-1) ^ ω` squares to one. -/
theorem dyadicOmegaSign_sq_eq_one : ∀ r : ZMod 8, dyadicOmegaSign r * dyadicOmegaSign r = 1 := by
  decide

/-- The sign `(-1) ^ (ε ε)` is multiplicative in its first argument on the units of `ZMod 8`. -/
theorem dyadicEpsProd_mul_left : ∀ r r' s : ZMod 8, IsUnit r → IsUnit r' → IsUnit s →
    dyadicEpsProd (r * r') s = dyadicEpsProd r s * dyadicEpsProd r' s := by decide

/-- The sign `(-1) ^ (ε ε)` is symmetric. -/
theorem dyadicEpsProd_comm : ∀ r s : ZMod 8, dyadicEpsProd r s = dyadicEpsProd s r := by decide

/-- A residue congruent to `1` modulo `8` contributes no `ε` sign. -/
theorem dyadicEpsProd_one_mul : ∀ s : ZMod 8,
    dyadicEpsProd 1 s * dyadicOmegaSign s = dyadicOmegaSign s := by decide

/-- The Hilbert symbol of two dyadic units, as the sign `(-1) ^ (ε(u) ε(v))`. -/
theorem hilbertSymbol_units_two_eq' {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol (u : ℚ_[2]) (v : ℚ_[2]) =
      dyadicEpsProd (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) := by
  rw [hilbertSymbol_units_two_eq hu hv]
  simp only [toZModPow_two_eq_one_iff hu, toZModPow_two_eq_one_iff hv]
  have hr := hu.map (PadicInt.toZModPow 3)
  have hs := hv.map (PadicInt.toZModPow 3)
  revert hr hs
  generalize PadicInt.toZModPow 3 u = r
  generalize PadicInt.toZModPow 3 v = s
  revert r s
  decide

/-! ### The uniformiser -/

/-- The residue of `2 u` modulo `8` is twice the residue of `u`. -/
theorem toZModPow_two_mul (u : ℤ_[2]) :
    PadicInt.toZModPow 3 (2 * u) = 2 * PadicInt.toZModPow 3 u := by
  rw [map_mul, map_ofNat]

/-- The sign attached to the shape `⟨2 u, v⟩` takes the two values `±1`. -/
theorem dyadicEpsProd_mul_omega_eq : ∀ r s : ZMod 8,
    dyadicEpsProd r s * dyadicOmegaSign s = 1 ∨ dyadicEpsProd r s * dyadicOmegaSign s = -1 := by
  decide

/-- When the sign attached to the shape `⟨2 u, v⟩` is `1`, the residues of `2 u` and `v`
represent `1` in `ZMod 8`. -/
theorem exists_zmod_of_two_mul_unit : ∀ r s : ZMod 8, IsUnit r → IsUnit s →
    dyadicEpsProd r s * dyadicOmegaSign s = 1 →
    ∃ x y : ZMod 8, 2 * r * x ^ 2 + s * y ^ 2 = 1 := by decide

/-- When the sign attached to the shape `⟨2 u, v⟩` is `-1`, no primitive triple of `ZMod 8`
satisfies `z ^ 2 = 2 r x ^ 2 + s y ^ 2`. -/
theorem sq_ne_of_two_mul_unit : ∀ r s : ZMod 8, (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) →
    (s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 7) → dyadicEpsProd r s * dyadicOmegaSign s = -1 →
    ∀ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) →
      z ^ 2 ≠ 2 * r * x ^ 2 + s * y ^ 2 := by decide

/-- **The Hilbert symbol of twice a unit against a unit.**  Compare Serre, *A Course in
Arithmetic*, Chapter III §1, Theorem 2 in the case `α = 1`, `β = 0`. -/
theorem hilbertSymbol_two_mul_unit {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ((2 * u : ℤ_[2]) : ℚ_[2]) ((v : ℤ_[2]) : ℚ_[2]) =
      dyadicEpsProd (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) *
        dyadicOmegaSign (PadicInt.toZModPow 3 v) := by
  have hr := hu.map (PadicInt.toZModPow 3)
  have hs := hv.map (PadicInt.toZModPow 3)
  rcases dyadicEpsProd_mul_omega_eq (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) with h | h
  · rw [h, hilbertSymbol_eq_one_iff]
    refine isHilbertIsotropic_of_exists_zmod _ _ ?_
    rw [toZModPow_two_mul]
    exact exists_zmod_of_two_mul_unit _ _ hr hs h
  · rw [h, hilbertSymbol_eq_neg_one_iff]
    refine not_isHilbertIsotropic_of_forall_toZModPow ?_
    rw [toZModPow_two_mul]
    exact sq_ne_of_two_mul_unit _ _ ((isUnit_zmod_eight _).mp hr) ((isUnit_zmod_eight _).mp hs) h

/-- **The Hilbert symbol of a unit against twice a unit.** -/
theorem hilbertSymbol_unit_two_mul {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ((u : ℤ_[2]) : ℚ_[2]) ((2 * v : ℤ_[2]) : ℚ_[2]) =
      dyadicEpsProd (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) *
        dyadicOmegaSign (PadicInt.toZModPow 3 u) := by
  rw [hilbertSymbol_comm, hilbertSymbol_two_mul_unit hv hu,
    dyadicEpsProd_comm (PadicInt.toZModPow 3 v)]

/-- The sign identity behind the shape `⟨2 u, 2 v⟩`: replacing the second argument by `-(u v)`
multiplies the sign of the shape `⟨2 u, w⟩` by the two `ω` factors. -/
theorem dyadicEpsProd_neg_mul : ∀ r s : ZMod 8, IsUnit r → IsUnit s →
    dyadicEpsProd r (-(r * s)) * dyadicOmegaSign (-(r * s)) =
      dyadicEpsProd r s * dyadicOmegaSign r * dyadicOmegaSign s := by decide

/-- **The Hilbert symbol of two doubled units.**  The form `2 u x ^ 2 + 2 v y ^ 2` represents no
odd value, so the shape is reached instead from `⟨2 u, v'⟩` through the identity
`⟨a, b⟩ = ⟨a, -a b⟩` and `-(2 u)(2 v) = (-(u v)) 2 ^ 2`. -/
theorem hilbertSymbol_two_mul_two_mul {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ((2 * u : ℤ_[2]) : ℚ_[2]) ((2 * v : ℤ_[2]) : ℚ_[2]) =
      dyadicEpsProd (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) *
        dyadicOmegaSign (PadicInt.toZModPow 3 u) * dyadicOmegaSign (PadicInt.toZModPow 3 v) := by
  have h2ne : ((2 : ℤ_[2]) : ℚ_[2]) ≠ 0 := by rw [coe_two]; norm_num
  have hane : ((2 * u : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
    rw [PadicInt.coe_mul]
    exact mul_ne_zero h2ne (PadicInt.coe_ne_zero.mpr hu.ne_zero)
  have hkey := hilbertSymbol_neg_mul_right ((2 * u : ℤ_[2]) : ℚ_[2])
    ((2 * v : ℤ_[2]) : ℚ_[2]) hane
  have hrewrite : -((2 * u : ℤ_[2]) : ℚ_[2]) * ((2 * v : ℤ_[2]) : ℚ_[2]) =
      ((-(u * v) : ℤ_[2]) : ℚ_[2]) * (2 : ℚ_[2]) ^ 2 := by
    push_cast [coe_two]
    ring
  rw [hrewrite, hilbertSymbol_mul_sq_right _ _ _ (by norm_num : (2 : ℚ_[2]) ≠ 0)] at hkey
  rw [← hkey, hilbertSymbol_two_mul_unit hu (hu.mul hv).neg, map_neg, map_mul]
  exact dyadicEpsProd_neg_mul _ _ (hu.map _) (hv.map _)

/-! ### The square classes at the dyadic place -/

/-- The representative of a square class of `ℚ_[2]`: a unit of `ℤ_[2]`, or twice one. -/
noncomputable def dyadicPart : Bool → ℤ_[2] → ℤ_[2]
  | true, u => 2 * u
  | false, u => u

/-- The product of two square-class representatives is again one, up to a square. -/
theorem dyadicPart_mul (e e' : Bool) (u u' : ℤ_[2]) :
    ∃ c : ℚ_[2], c ≠ 0 ∧ ((dyadicPart e u * dyadicPart e' u' : ℤ_[2]) : ℚ_[2]) =
      ((dyadicPart (xor e e') (u * u') : ℤ_[2]) : ℚ_[2]) * c ^ 2 := by
  have hone : (1 : ℚ_[2]) ≠ 0 := one_ne_zero
  have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
  cases e <;> cases e'
  · refine ⟨1, hone, ?_⟩
    show ((u * u' : ℤ_[2]) : ℚ_[2]) = ((u * u' : ℤ_[2]) : ℚ_[2]) * 1 ^ 2
    ring
  · refine ⟨1, hone, ?_⟩
    show ((u * (2 * u') : ℤ_[2]) : ℚ_[2]) = ((2 * (u * u') : ℤ_[2]) : ℚ_[2]) * 1 ^ 2
    push_cast [coe_two]
    ring
  · refine ⟨1, hone, ?_⟩
    show ((2 * u * u' : ℤ_[2]) : ℚ_[2]) = ((2 * (u * u') : ℤ_[2]) : ℚ_[2]) * 1 ^ 2
    push_cast [coe_two]
    ring
  · refine ⟨2, htwo, ?_⟩
    show ((2 * u * (2 * u') : ℤ_[2]) : ℚ_[2]) = ((u * u' : ℤ_[2]) : ℚ_[2]) * 2 ^ 2
    push_cast [coe_two]
    ring

/-- **The dyadic Hilbert symbol of two square-class representatives.**  This is Serre,
*A Course in Arithmetic*, Chapter III §1, Theorem 2 at the place `2`. -/
theorem hilbertSymbol_dyadicPart (e f : Bool) {u v : ℤ_[2]} (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ((dyadicPart e u : ℤ_[2]) : ℚ_[2]) ((dyadicPart f v : ℤ_[2]) : ℚ_[2]) =
      dyadicEpsProd (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) *
        dyadicOmegaFactor e (PadicInt.toZModPow 3 v) *
        dyadicOmegaFactor f (PadicInt.toZModPow 3 u) := by
  cases e <;> cases f <;> simp only [dyadicPart, dyadicOmegaFactor, mul_one]
  · exact hilbertSymbol_units_two_eq' hu hv
  · exact hilbertSymbol_unit_two_mul hu hv
  · exact hilbertSymbol_two_mul_unit hu hv
  · rw [hilbertSymbol_two_mul_two_mul hu hv]
    ring

/-- **The square classes of `ℚ_[2]`.**  Every nonzero dyadic number is a square times a unit of
`ℤ_[2]`, or a square times twice a unit, according to the parity of its valuation. -/
theorem exists_sq_mul_dyadicPart {b : ℚ_[2]} (hb : b ≠ 0) :
    ∃ (c : ℚ_[2]) (e : Bool) (w : ℤ_[2]), c ≠ 0 ∧ IsUnit w ∧
      b = c ^ 2 * ((dyadicPart e w : ℤ_[2]) : ℚ_[2]) := by
  obtain ⟨n, w, hw, hbn⟩ := exists_unit_mul_zpow hb
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  rw [show (((2 : ℕ) : ℚ_[2])) = 2 by norm_num] at hbn
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨(2 : ℚ_[2]) ^ k, false, w, zpow_ne_zero _ h2, hw, ?_⟩
    have hpow : (2 : ℚ_[2]) ^ n = (2 : ℚ_[2]) ^ k * (2 : ℚ_[2]) ^ k := by
      rw [hk, zpow_add₀ h2]
    rw [hbn, hpow]
    show (2 : ℚ_[2]) ^ k * (2 : ℚ_[2]) ^ k * (w : ℚ_[2]) =
      ((2 : ℚ_[2]) ^ k) ^ 2 * (w : ℚ_[2])
    ring
  · refine ⟨(2 : ℚ_[2]) ^ k, true, w, zpow_ne_zero _ h2, hw, ?_⟩
    have hpow : (2 : ℚ_[2]) ^ n = (2 : ℚ_[2]) ^ k * (2 : ℚ_[2]) ^ k * 2 := by
      rw [hk, two_mul, zpow_add₀ h2, zpow_add₀ h2, zpow_one]
    rw [hbn, hpow]
    show (2 : ℚ_[2]) ^ k * (2 : ℚ_[2]) ^ k * 2 * (w : ℚ_[2]) =
      ((2 : ℚ_[2]) ^ k) ^ 2 * ((2 * w : ℤ_[2]) : ℚ_[2])
    push_cast [coe_two]
    ring

/-- **The square classes of `ℚ_[2]`**, stated as an alternative. -/
theorem exists_sq_mul_dyadic_normal_form {b : ℚ_[2]} (hb : b ≠ 0) :
    ∃ (c : ℚ_[2]) (w : ℤ_[2]), c ≠ 0 ∧ IsUnit w ∧
      (b = c ^ 2 * (w : ℚ_[2]) ∨ b = c ^ 2 * ((2 * w : ℤ_[2]) : ℚ_[2])) := by
  obtain ⟨c, e, w, hc, hw, hb'⟩ := exists_sq_mul_dyadicPart hb
  refine ⟨c, w, hc, hw, ?_⟩
  cases e
  · exact Or.inl hb'
  · exact Or.inr hb'

/-! ### Bimultiplicativity -/

/-- Square factors in either argument do not change the Hilbert symbol. -/
theorem hilbertSymbol_sq_mul_sq_mul {c d A B : ℚ_[2]} (hc : c ≠ 0) (hd : d ≠ 0) :
    hilbertSymbol (c ^ 2 * A) (d ^ 2 * B) = hilbertSymbol A B := by
  rw [mul_comm (c ^ 2) A, mul_comm (d ^ 2) B, hilbertSymbol_mul_sq_left _ _ _ hc,
    hilbertSymbol_mul_sq_right _ _ _ hd]

/-- The sign identity behind bimultiplicativity: the signs of the shapes `⟨e, f⟩` and `⟨e', f⟩`
multiply to the sign of the shape `⟨e xor e', f⟩`. -/
theorem dyadicSign_mul_left (e e' f : Bool) : ∀ r r' s : ZMod 8, IsUnit r → IsUnit r' →
    IsUnit s →
    dyadicEpsProd (r * r') s * dyadicOmegaFactor (xor e e') s *
        dyadicOmegaFactor f (r * r') =
      dyadicEpsProd r s * dyadicOmegaFactor e s * dyadicOmegaFactor f r *
        (dyadicEpsProd r' s * dyadicOmegaFactor e' s * dyadicOmegaFactor f r') := by
  cases e <;> cases e' <;> cases f <;> decide

/-- The Hilbert symbol is multiplicative on square-class representatives. -/
theorem hilbertSymbol_dyadicPart_mul (e e' f : Bool) {u u' v : ℤ_[2]} (hu : IsUnit u)
    (hu' : IsUnit u') (hv : IsUnit v) :
    hilbertSymbol ((dyadicPart (xor e e') (u * u') : ℤ_[2]) : ℚ_[2])
        ((dyadicPart f v : ℤ_[2]) : ℚ_[2]) =
      hilbertSymbol ((dyadicPart e u : ℤ_[2]) : ℚ_[2]) ((dyadicPart f v : ℤ_[2]) : ℚ_[2]) *
        hilbertSymbol ((dyadicPart e' u' : ℤ_[2]) : ℚ_[2])
          ((dyadicPart f v : ℤ_[2]) : ℚ_[2]) := by
  rw [hilbertSymbol_dyadicPart _ _ (hu.mul hu') hv, hilbertSymbol_dyadicPart _ _ hu hv,
    hilbertSymbol_dyadicPart _ _ hu' hv, map_mul]
  exact dyadicSign_mul_left e e' f _ _ _ (hu.map _) (hu'.map _) (hv.map _)

/-- **The dyadic Hilbert symbol is multiplicative in its first argument.** -/
theorem hilbertSymbol_dyadic_mul_left {a a' b : ℚ_[2]} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol (a * a') b = hilbertSymbol a b * hilbertSymbol a' b := by
  obtain ⟨c, e, u, hc, hu, rfl⟩ := exists_sq_mul_dyadicPart ha
  obtain ⟨c', e', u', hc', hu', rfl⟩ := exists_sq_mul_dyadicPart ha'
  obtain ⟨d, f, v, hd, hv, rfl⟩ := exists_sq_mul_dyadicPart hb
  obtain ⟨g, hg, hmul⟩ := dyadicPart_mul e e' u u'
  have hcast : ((dyadicPart e u : ℤ_[2]) : ℚ_[2]) * ((dyadicPart e' u' : ℤ_[2]) : ℚ_[2]) =
      ((dyadicPart (xor e e') (u * u') : ℤ_[2]) : ℚ_[2]) * g ^ 2 := by
    rw [← PadicInt.coe_mul]
    exact hmul
  have hprod : c ^ 2 * ((dyadicPart e u : ℤ_[2]) : ℚ_[2]) *
      (c' ^ 2 * ((dyadicPart e' u' : ℤ_[2]) : ℚ_[2])) =
      (c * c' * g) ^ 2 * ((dyadicPart (xor e e') (u * u') : ℤ_[2]) : ℚ_[2]) := by
    linear_combination (c ^ 2 * c' ^ 2) * hcast
  rw [hprod, hilbertSymbol_sq_mul_sq_mul (mul_ne_zero (mul_ne_zero hc hc') hg) hd,
    hilbertSymbol_sq_mul_sq_mul hc hd, hilbertSymbol_sq_mul_sq_mul hc' hd]
  exact hilbertSymbol_dyadicPart_mul e e' f hu hu' hv

/-- **The dyadic Hilbert symbol is multiplicative in its second argument.** -/
theorem hilbertSymbol_dyadic_mul_right {a b b' : ℚ_[2]} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol a (b * b') = hilbertSymbol a b * hilbertSymbol a b' := by
  rw [hilbertSymbol_comm a (b * b'), hilbertSymbol_comm a b, hilbertSymbol_comm a b',
    hilbertSymbol_dyadic_mul_left hb hb' ha]

/-! ### Two specialisations -/

/-- The Hilbert symbol of the uniformiser against a dyadic unit is the sign `(-1) ^ ω`. -/
theorem hilbertSymbol_two_unit {v : ℤ_[2]} (hv : IsUnit v) :
    hilbertSymbol (2 : ℚ_[2]) ((v : ℤ_[2]) : ℚ_[2]) =
      dyadicOmegaSign (PadicInt.toZModPow 3 v) := by
  have h := hilbertSymbol_two_mul_unit isUnit_one hv
  rw [mul_one, map_one, coe_two] at h
  exact h.trans (dyadicEpsProd_one_mul _)

/-- The Hilbert symbol of the uniformiser against itself is trivial, the conic
`z ^ 2 = 2 x ^ 2 + 2 y ^ 2` having the point `(1, 1, 2)`. -/
theorem hilbertSymbol_two_two : hilbertSymbol (2 : ℚ_[2]) (2 : ℚ_[2]) = 1 := by
  have h := hilbertSymbol_two_mul_two_mul (isUnit_one (M := ℤ_[2])) isUnit_one
  rw [mul_one, map_one, coe_two] at h
  rw [h]
  decide

end InverseGalois.CFT.Local
