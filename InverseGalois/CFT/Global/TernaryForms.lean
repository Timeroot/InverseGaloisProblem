import Mathlib
import InverseGalois.CFT.Global.HasseNorm

/-!
# The Hasse principle for diagonal ternary forms and for binary representations

The Hilbert symbol is the isotropy of the particular ternary form `z ^ 2 - a x ^ 2 - b y ^ 2`.
Every diagonal ternary form is a scalar multiple of one of these, so the Hasse principle proved
for the Hilbert symbol is really a statement about an arbitrary diagonal ternary form over the
rational field, and the condition at the real place may be dropped from it, reciprocity supplying
that place from the finite ones.

Dividing out the leading coefficient turns the question of which elements a diagonal binary form
represents into a question about a norm form: the identity
`α * (α x ^ 2 + β y ^ 2) = (α x) ^ 2 + α β y ^ 2` says that `c` is a value of `⟨α, β⟩` exactly when
`α c` is a value of the norm form of a square root of `-α β`.  So representation by a binary form
over the rational field is also a purely local condition.

## Main results

* `InverseGalois.CFT.Local.IsTernaryIsotropic`: a diagonal ternary form represents zero
  nontrivially.
* `InverseGalois.CFT.Local.isTernaryIsotropic_iff_isHilbertIsotropic`: after dividing by the last
  coefficient, that is the isotropy measured by the Hilbert symbol.
* `InverseGalois.CFT.Local.exists_repr_iff_hilbertSymbol`: an element is a value of the diagonal
  binary form `⟨α, β⟩` exactly when a Hilbert symbol vanishes.
* `InverseGalois.CFT.isTernaryIsotropic_rat_iff_forall_local`: a diagonal ternary conic over the
  rational field with a point over every field of `p`-adic numbers has a rational point.
* `InverseGalois.CFT.exists_repr_binary_iff_forall_local`: a rational represented by a diagonal
  binary form over every field of `p`-adic numbers is represented over the rational field.
-/

namespace InverseGalois.CFT.Local

section Isotropy

variable {K : Type*} [Field K]

/-- The diagonal ternary form `⟨α, β, γ⟩` over `K` is **isotropic** when it represents zero at a
point other than the origin. -/
def IsTernaryIsotropic (α β γ : K) : Prop :=
  ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ α * x ^ 2 + β * y ^ 2 + γ * z ^ 2 = 0

/-- **A diagonal ternary form with invertible last coefficient is isotropic exactly when the
Hilbert symbol of the other two coefficients, divided by it and negated, is.**  The two forms
differ by the scalar `γ`, so they have the same zeros. -/
theorem isTernaryIsotropic_iff_isHilbertIsotropic {α β γ : K} (hγ : γ ≠ 0) :
    IsTernaryIsotropic α β γ ↔ IsHilbertIsotropic (-α / γ) (-β / γ) := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, y, z, hne, ?_⟩
    field_simp
    linear_combination h
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, y, z, hne, ?_⟩
    field_simp at h
    linear_combination h

end Isotropy

section Representation

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
/-- **An element is a value of the diagonal binary form `⟨α, β⟩` exactly when `α` times it is a
value of the norm form attached to `-α β`.**  Multiplying the equation `c = α x ^ 2 + β y ^ 2` by
`α` turns it into `α c = (α x) ^ 2 + α β y ^ 2`. -/
theorem exists_repr_iff_exists_sub_sq {α β c : K} (hα : α ≠ 0) :
    (∃ x y : K, c = α * x ^ 2 + β * y ^ 2) ↔ ∃ u v : K, α * c = u ^ 2 - -(α * β) * v ^ 2 := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨α * x, y, by ring⟩
  · rintro ⟨u, v, huv⟩
    refine ⟨u / α, v, ?_⟩
    field_simp
    linear_combination huv

/-- **The values of a diagonal binary form are read off from a Hilbert symbol.** -/
theorem exists_repr_iff_hilbertSymbol {α β c : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∃ x y : K, c = α * x ^ 2 + β * y ^ 2) ↔ hilbertSymbol (α * c) (-(α * β)) = 1 := by
  rw [hilbertSymbol_eq_one_iff_exists_sub_sq' (neg_ne_zero.2 (mul_ne_zero hα hβ))]
  exact exists_repr_iff_exists_sub_sq hα

end Representation

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **The Hasse principle for a diagonal ternary form over the rational field.**  A conic with a
point over every field of `p`-adic numbers has a rational point; nothing is required at the real
place, reciprocity supplying it. -/
theorem isTernaryIsotropic_rat_of_forall_local {α β γ : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsTernaryIsotropic ((α : ℚ_[(p : ℕ)])) ((β : ℚ_[(p : ℕ)]))
      ((γ : ℚ_[(p : ℕ)]))) :
    IsTernaryIsotropic α β γ := by
  have hγ0 : ((γ : ℚ)) ≠ 0 := hγ
  rw [isTernaryIsotropic_iff_isHilbertIsotropic hγ0, ← hilbertSymbol_eq_one_iff]
  have hA : ((-α / γ : ℚ)) ≠ 0 := div_ne_zero (neg_ne_zero.2 hα) hγ
  have hB : ((-β / γ : ℚ)) ≠ 0 := div_ne_zero (neg_ne_zero.2 hβ) hγ
  refine hilbertSymbol_rat_of_forall_finite hA hB fun p => ?_
  have hγp : ((γ : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hγ
  have hp := hloc p
  rw [isTernaryIsotropic_iff_isHilbertIsotropic hγp, ← hilbertSymbol_eq_one_iff] at hp
  unfold hilbertSymbolAt
  rw [show (((-α / γ : ℚ)) : ℚ_[(p : ℕ)]) = -((α : ℚ_[(p : ℕ)])) / ((γ : ℚ_[(p : ℕ)])) by
        push_cast; ring,
    show (((-β / γ : ℚ)) : ℚ_[(p : ℕ)]) = -((β : ℚ_[(p : ℕ)])) / ((γ : ℚ_[(p : ℕ)])) by
        push_cast; ring]
  exact hp

/-- **The Hasse principle for a diagonal ternary form, as an equivalence.** -/
theorem isTernaryIsotropic_rat_iff_forall_local {α β γ : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) :
    IsTernaryIsotropic α β γ ↔ ∀ p : Nat.Primes, IsTernaryIsotropic ((α : ℚ_[(p : ℕ)]))
      ((β : ℚ_[(p : ℕ)])) ((γ : ℚ_[(p : ℕ)])) := by
  refine ⟨fun h p => ?_, isTernaryIsotropic_rat_of_forall_local hα hβ hγ⟩
  obtain ⟨x, y, z, hne, hxyz⟩ := h
  refine ⟨((x : ℚ_[(p : ℕ)])), ((y : ℚ_[(p : ℕ)])), ((z : ℚ_[(p : ℕ)])), ?_, ?_⟩
  · rintro ⟨hx, hy, hz⟩
    exact hne ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz⟩
  · have : (((α * x ^ 2 + β * y ^ 2 + γ * z ^ 2 : ℚ)) : ℚ_[(p : ℕ)]) = 0 := by
      rw [hxyz]; norm_num
    push_cast at this
    linear_combination this

/-- **The Hasse principle for representation by a diagonal binary form over the rational field.**
A rational that the form represents over every field of `p`-adic numbers it already represents
over the rational field. -/
theorem exists_repr_binary_of_forall_local {α β c : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hloc : ∀ p : Nat.Primes, ∃ x y : ℚ_[(p : ℕ)],
      ((c : ℚ_[(p : ℕ)])) = ((α : ℚ_[(p : ℕ)])) * x ^ 2 + ((β : ℚ_[(p : ℕ)])) * y ^ 2) :
    ∃ x y : ℚ, c = α * x ^ 2 + β * y ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, 0, by ring⟩
  rw [exists_repr_iff_hilbertSymbol hα hβ]
  refine hilbertSymbol_rat_of_forall_finite (mul_ne_zero hα hc)
    (neg_ne_zero.2 (mul_ne_zero hα hβ)) fun p => ?_
  have hαp : ((α : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hα
  have hβp : ((β : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hβ
  have hp := (exists_repr_iff_hilbertSymbol hαp hβp).1 (hloc p)
  unfold hilbertSymbolAt
  rw [show (((α * c : ℚ)) : ℚ_[(p : ℕ)]) = ((α : ℚ_[(p : ℕ)])) * ((c : ℚ_[(p : ℕ)])) by
        push_cast; ring,
    show (((-(α * β) : ℚ)) : ℚ_[(p : ℕ)]) = -(((α : ℚ_[(p : ℕ)])) * ((β : ℚ_[(p : ℕ)]))) by
        push_cast; ring]
  exact hp

/-- **The Hasse principle for representation by a diagonal binary form, as an equivalence.** -/
theorem exists_repr_binary_iff_forall_local {α β c : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∃ x y : ℚ, c = α * x ^ 2 + β * y ^ 2) ↔
      ∀ p : Nat.Primes, ∃ x y : ℚ_[(p : ℕ)],
        ((c : ℚ_[(p : ℕ)])) = ((α : ℚ_[(p : ℕ)])) * x ^ 2 + ((β : ℚ_[(p : ℕ)])) * y ^ 2 := by
  refine ⟨fun h p => ?_, exists_repr_binary_of_forall_local hα hβ⟩
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨((x : ℚ_[(p : ℕ)])), ((y : ℚ_[(p : ℕ)])), ?_⟩
  rw [hxy]
  push_cast
  ring

/-- **A rational is a sum of two rational squares as soon as it is one in every field of `p`-adic
numbers.** -/
theorem exists_sq_add_sq_of_forall_local {c : ℚ}
    (hloc : ∀ p : Nat.Primes, ∃ x y : ℚ_[(p : ℕ)], ((c : ℚ_[(p : ℕ)])) = x ^ 2 + y ^ 2) :
    ∃ x y : ℚ, c = x ^ 2 + y ^ 2 := by
  have h := exists_repr_binary_of_forall_local (α := 1) (β := 1) (c := c) one_ne_zero one_ne_zero
    (by simpa using hloc)
  simpa using h

end InverseGalois.CFT
