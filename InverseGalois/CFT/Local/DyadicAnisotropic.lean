import Mathlib
import InverseGalois.CFT.Global.DiagForm

/-!
# An anisotropic quaternary form at the dyadic place

Five unit variables always suffice to make a diagonal form over `ℚ_[2]` isotropic, and four
variables suffice as soon as one coefficient is ramified.  This file shows that four unit
variables are genuinely not enough: the norm form `⟨1, 1, 1, 1⟩` of the Hamilton quaternions is
anisotropic over `ℚ_[2]`, so the `u`-invariant of the dyadic field is exactly four.

The argument is a single congruence modulo `8`.  Scaling a hypothetical isotropic vector by a
coordinate of largest absolute value produces a vector all of whose entries are dyadic integers
and one of whose entries is `1`.  Reducing the relation modulo `8` leaves four residues, one of
them `1`, whose squares sum to zero.  No such quadruple exists: the squares modulo `8` are
`0, 1, 4`, so a sum of four of them containing at least one `1` is congruent to `k + 4m` with
`1 ≤ k ≤ 4` and `k + m ≤ 4`, and such a number is never divisible by `8`.

## Main results

* `InverseGalois.CFT.Local.no_four_squares_zmod_eight`: four residues modulo `8`, one of which is
  `1`, have squares that do not sum to zero.
* `InverseGalois.CFT.Local.not_isDiagIsotropic_four_squares`: **the sum of four squares is
  anisotropic over `ℚ_[2]`.**
* `InverseGalois.CFT.Local.exists_not_isDiagIsotropic_four`: **the bound `u(ℚ_[2]) ≤ 4` is
  sharp**, since some diagonal form in four variables with nonzero coefficients is anisotropic.
-/

namespace InverseGalois.CFT.Local

set_option maxRecDepth 8000 in
/-- **The congruence obstruction modulo `8`.**  If one of four residues modulo `8` equals `1`,
then their squares do not sum to zero. -/
theorem no_four_squares_zmod_eight (c0 c1 c2 c3 : ZMod 8)
    (h : c0 = 1 ∨ c1 = 1 ∨ c2 = 1 ∨ c3 = 1) :
    c0 ^ 2 + c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≠ 0 := by
  revert h
  revert c0 c1 c2 c3
  decide

/-- **The sum of four squares is anisotropic over `ℚ_[2]`.**  Dividing a nontrivial zero of the
form by a coordinate of largest absolute value gives a zero with dyadic integer coordinates one
of which is `1`, and reducing modulo `8` contradicts the congruence obstruction. -/
theorem not_isDiagIsotropic_four_squares :
    ¬ IsDiagIsotropic (fun _ : Fin 4 => (1 : ℚ_[2])) := by
  rintro ⟨x, hx, hsum⟩
  simp only [one_mul] at hsum
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i => ‖x i‖)
  have hxj : x j ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := hj i
    rw [h0] at this
    simpa using this
  set y : Fin 4 → ℚ_[2] := fun i => x i / x j with hy
  have hyle : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    rw [hy]
    simp only [norm_div]
    exact div_le_one_of_le₀ (hj i) (norm_nonneg _)
  have hyj : y j = 1 := by
    rw [hy]
    exact div_self hxj
  have hysum : ∑ i, y i ^ 2 = 0 := by
    have hdiv : ∑ i, y i ^ 2 = (∑ i, x i ^ 2) / x j ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hy, div_pow]
    rw [hdiv, hsum, zero_div]
  set z : Fin 4 → ℤ_[2] := fun i => ⟨y i, hyle i⟩ with hz
  have hzj : z j = 1 := by
    rw [hz]
    exact Subtype.ext (by simpa using hyj)
  have hzsum : ∑ i, z i ^ 2 = 0 := by
    rw [← PadicInt.coe_eq_zero, PadicInt.coe_sum]
    exact hysum
  set c : Fin 4 → ZMod 8 := fun i => PadicInt.toZModPow 3 (z i) with hc
  have hcj : c j = 1 := by rw [hc]; simp [hzj]
  have hcsum : c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 = 0 := by
    have hmap := congrArg (PadicInt.toZModPow (p := 2) 3) hzsum
    rw [map_sum, map_zero, Fin.sum_univ_four] at hmap
    simpa [hc, map_pow] using hmap
  refine no_four_squares_zmod_eight (c 0) (c 1) (c 2) (c 3) ?_ hcsum
  fin_cases j
  · exact Or.inl hcj
  · exact Or.inr (Or.inl hcj)
  · exact Or.inr (Or.inr (Or.inl hcj))
  · exact Or.inr (Or.inr (Or.inr hcj))

/-- **The bound `u(ℚ_[2]) ≤ 4` is sharp.**  Some diagonal form over `ℚ_[2]` in four variables
with nonzero coefficients represents zero only trivially. -/
theorem exists_not_isDiagIsotropic_four :
    ∃ a : Fin 4 → ℚ_[2], (∀ i, a i ≠ 0) ∧ ¬ IsDiagIsotropic a :=
  ⟨fun _ => 1, fun _ => one_ne_zero, not_isDiagIsotropic_four_squares⟩

end InverseGalois.CFT.Local
