import Mathlib
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Global.TernaryForms

/-!
# Sums of three squares over `ℚ_[p]` for an odd prime `p`

A diagonal ternary form with nonzero coefficients that represents zero nontrivially is
*universal*: it represents every element of the field.  The reason is that an isotropic
nondegenerate form contains a hyperbolic plane, whose values already exhaust the field.  In
diagonal coordinates the argument is completely explicit.  Starting from a nontrivial zero
`(x₀, y₀, z₀)` of `α X ^ 2 + β Y ^ 2 + γ Z ^ 2` with, say, `x₀ ≠ 0`, the substitution
`(X, Y, Z) := (x₀ s + 1, y₀ s, z₀ s)` collapses the quadratic part and leaves the affine-linear
value `2 α x₀ s + α`, which runs over the whole field as `s` does because `2 α x₀ ≠ 0`.

Over `ℚ_[p]` with `p` odd, the form `X ^ 2 + Y ^ 2 + Z ^ 2` is isotropic: the pair `(-1, -1)`
consists of two `p`-adic units, and at an odd finite place the Hilbert symbol of two units is
`1`, so the conic `Z ^ 2 = -X ^ 2 - Y ^ 2` has a nontrivial point.  Combining the two statements,
every `p`-adic number is a sum of three squares at every odd finite place.

## Main results

* `InverseGalois.CFT.exists_repr_of_isTernaryIsotropic_of_ne_zero`: the universality argument in
  the normalised position where the first coordinate of the nontrivial zero is nonzero.
* `InverseGalois.CFT.exists_repr_of_isTernaryIsotropic`: an isotropic diagonal ternary form with
  nonzero coefficients represents every element of the field.
* `InverseGalois.CFT.isTernaryIsotropic_one_one_one_of_odd`: for `p` odd the form
  `X ^ 2 + Y ^ 2 + Z ^ 2` represents zero nontrivially over `ℚ_[p]`, both as a bare existential
  statement and in the vocabulary of `InverseGalois.CFT.Local.IsTernaryIsotropic`.
* `InverseGalois.CFT.exists_three_sq_of_odd`: for `p` odd every element of `ℚ_[p]` is a sum of
  three squares.
-/

namespace InverseGalois.CFT

open Local

/-- **Universality of an isotropic diagonal ternary form, normalised.**  If the coefficient `α`
is nonzero and the form `α X ^ 2 + β Y ^ 2 + γ Z ^ 2` vanishes at a point whose first coordinate
`x₀` is nonzero, then the form represents every `c`: substituting `(x₀ s + 1, y₀ s, z₀ s)` kills
the quadratic part and leaves `2 α x₀ s + α`, and the linear equation `2 α x₀ s + α = c` is
solvable. -/
theorem exists_repr_of_isTernaryIsotropic_of_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {α β γ : K} (hα : α ≠ 0) {x₀ y₀ z₀ : K} (hx₀ : x₀ ≠ 0)
    (h : α * x₀ ^ 2 + β * y₀ ^ 2 + γ * z₀ ^ 2 = 0) (c : K) :
    ∃ x y z : K, c = α * x ^ 2 + β * y ^ 2 + γ * z ^ 2 := by
  set s : K := (c - α) / (2 * α * x₀) with hs
  refine ⟨x₀ * s + 1, y₀ * s, z₀ * s, ?_⟩
  have hden : 2 * α * x₀ ≠ 0 := by simp [h2, hα, hx₀]
  have hkey : 2 * α * x₀ * s = c - α := by rw [hs]; field_simp
  linear_combination -(s ^ 2) * h - hkey

/-- **A diagonal ternary form that represents zero nontrivially represents every element.**  One
of the three coordinates of the nontrivial zero is nonzero; permuting the coefficients so that it
comes first reduces the statement to its normalised form. -/
theorem exists_repr_of_isTernaryIsotropic {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {α β γ : K}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ α * x ^ 2 + β * y ^ 2 + γ * z ^ 2 = 0)
    (c : K) : ∃ x y z : K, c = α * x ^ 2 + β * y ^ 2 + γ * z ^ 2 := by
  obtain ⟨x₀, y₀, z₀, hne, h0⟩ := h
  by_cases hx : x₀ = 0
  · by_cases hy : y₀ = 0
    · have hz : z₀ ≠ 0 := fun hz => hne ⟨hx, hy, hz⟩
      obtain ⟨x, y, z, hxyz⟩ := exists_repr_of_isTernaryIsotropic_of_ne_zero h2 hγ hz
        (β := β) (γ := α) (y₀ := y₀) (z₀ := x₀) (by linear_combination h0) c
      exact ⟨z, y, x, by linear_combination hxyz⟩
    · obtain ⟨x, y, z, hxyz⟩ := exists_repr_of_isTernaryIsotropic_of_ne_zero h2 hβ hy
        (β := α) (γ := γ) (y₀ := x₀) (z₀ := z₀) (by linear_combination h0) c
      exact ⟨y, x, z, by linear_combination hxyz⟩
  · exact exists_repr_of_isTernaryIsotropic_of_ne_zero h2 hα hx h0 c

variable {p : ℕ} [Fact p.Prime]

/-- **For an odd prime `p`, the form `X ^ 2 + Y ^ 2 + Z ^ 2` is isotropic over `ℚ_[p]`.**  Both
`-1` and `-1` have `p`-adic absolute value one, so the Hilbert symbol `⟨-1, -1⟩` is `1` at an odd
finite place and the conic `Z ^ 2 = -X ^ 2 - Y ^ 2` carries a point other than the origin. -/
theorem isTernaryIsotropic_one_one_one_of_odd (hp : p ≠ 2) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
  have hn : ‖(-1 : ℚ_[p])‖ = 1 := by rw [norm_neg, norm_one]
  obtain ⟨x, y, z, hne, hxyz⟩ :=
    hilbertSymbol_eq_one_iff.mp (hilbertSymbol_eq_one_of_norm_eq_one hp hn hn)
  exact ⟨x, y, z, hne, by linear_combination hxyz⟩

/-- The isotropy of `X ^ 2 + Y ^ 2 + Z ^ 2` over `ℚ_[p]` for `p` odd, phrased with
`InverseGalois.CFT.Local.IsTernaryIsotropic`. -/
theorem isTernaryIsotropic_one_one_one_of_odd' (hp : p ≠ 2) :
    IsTernaryIsotropic (1 : ℚ_[p]) 1 1 := by
  obtain ⟨x, y, z, hne, hxyz⟩ := isTernaryIsotropic_one_one_one_of_odd hp
  exact ⟨x, y, z, hne, by linear_combination hxyz⟩

/-- **For an odd prime `p`, every `p`-adic number is a sum of three squares.**  The form
`X ^ 2 + Y ^ 2 + Z ^ 2` is isotropic over `ℚ_[p]`, hence universal. -/
theorem exists_three_sq_of_odd (hp : p ≠ 2) (c : ℚ_[p]) :
    ∃ x y z : ℚ_[p], c = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨x, y, z, hxyz⟩ := exists_repr_of_isTernaryIsotropic (K := ℚ_[p]) two_ne_zero one_ne_zero
    one_ne_zero one_ne_zero
    (by simpa using isTernaryIsotropic_one_one_one_of_odd hp) c
  exact ⟨x, y, z, by linear_combination hxyz⟩

end InverseGalois.CFT
