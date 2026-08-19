import Mathlib

/-!
# A concrete, computable field with four elements

`GaloisField 2 2` (the field `𝔽₄` used to phrase `PSL(3, 4)`) is **noncomputable** in
Mathlib, so no `Fintype`/`native_decide` reasoning is available directly over it.  To carry
out the concrete permutation computations behind `M₂₁ ≅ PSL(3, 4)` we introduce a *computable*
model `F4` of the field with four elements and a ring isomorphism `F4 ≃+* GaloisField 2 2`.

`F4` is `𝔽₂[ω]` with `ω² = ω + 1`; an element `a + b·ω` is stored as the pair of bits `(a, b)`.
All field axioms hold by `decide` over the four elements.
-/

namespace Mathieu

/-- The field with four elements, `𝔽₂[ω]` with `ω² = ω + 1`, stored as a pair of bits
`(a, b)` representing `a + b·ω`. -/
structure F4 where
  a : ZMod 2
  b : ZMod 2
deriving DecidableEq, Fintype

namespace F4

instance : Zero F4 := ⟨⟨0, 0⟩⟩
instance : One F4 := ⟨⟨1, 0⟩⟩
instance : Add F4 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg F4 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
/-- `(a+bω)(c+dω) = (ac+bd) + (ad+bc+bd)·ω`, using `ω² = ω + 1`. -/
instance : Mul F4 := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩
/-- The inverse table: `0⁻¹ = 0`, `1⁻¹ = 1`, `ω⁻¹ = ω+1`, `(ω+1)⁻¹ = ω`. -/
instance : Inv F4 := ⟨fun x => ⟨x.a + x.b, x.b⟩⟩

instance instField : Field F4 := Field.ofMinimalAxioms F4
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide)

/-- `F4` has exactly four elements. -/
theorem card : Fintype.card F4 = 4 := by decide

noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

theorem card_eq_galoisField : Fintype.card F4 = Fintype.card (GaloisField 2 2) := by
  have h2 : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]; norm_num
  rw [card, h2]

/-- A ring isomorphism between the computable model `F4` and `GaloisField 2 2`, obtained
from the uniqueness of finite fields of a given cardinality. -/
noncomputable def equivGaloisField : F4 ≃+* GaloisField 2 2 :=
  FiniteField.ringEquivOfCardEq card_eq_galoisField

/-! ### Sanity facts about `F4` (checks on the definition) -/

/-- `ω := ⟨0,1⟩` satisfies the defining relation `ω² = ω + 1`. -/
theorem omega_sq : (⟨0, 1⟩ : F4) * ⟨0, 1⟩ = ⟨0, 1⟩ + 1 := by decide

/-- `F4` has characteristic two: `x + x = 0`. -/
theorem add_self (x : F4) : x + x = 0 := by
  revert x; decide

/-- Every element of `F4` is a cube root of unity or zero: `x ≠ 0 → x³ = 1`. -/
theorem cube_eq_one (x : F4) (hx : x ≠ 0) : x ^ 3 = 1 := by
  revert x; decide

end F4

end Mathieu
