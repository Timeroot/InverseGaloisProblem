import Mathlib

/-!
# The order of the special linear group over a finite field

This file records the classical order formula for the special linear group `SL(n, 𝔽)` over a
finite field `𝔽`, obtained as a "pen-and-paper" alternative to a brute-force `native_decide`
enumeration.

The key identity is that the determinant `GL(n, 𝔽) →* 𝔽ˣ` is a *surjective* homomorphism whose
kernel is (isomorphic to) `SL(n, 𝔽)`.  Combined with Lagrange's theorem and Mathlib's formula
`Matrix.card_GL_field` for `|GL(n, 𝔽)|`, this yields
`|GL(n, 𝔽)| = |SL(n, 𝔽)| · (|𝔽| - 1)`, from which the orders of the three special linear groups
used in the Mathieu-group development follow by elementary arithmetic:

* `|SL(2, 𝔽₁₁)| = 1320` (see `EnumL211.slCard`),
* `|SL(2, 𝔽₂₃)| = 12144` (see `EnumSL223.slCard`),
* `|SL(3, 𝔽₄)| = 60480` (see `EnumSL34.slCard`).
-/

namespace Mathieu

open Matrix
open scoped MatrixGroups

namespace CardSL

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-
The determinant homomorphism `GL(n, 𝔽) →* 𝔽ˣ` is surjective over a field
(as long as there is at least one coordinate): the diagonal matrix with a single entry `u`
and the rest `1` has determinant `u`.
-/
omit [Fintype 𝔽] [DecidableEq 𝔽] in
theorem det_surjective {n : ℕ} [NeZero n] :
    Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ) := by
  intro x;
  refine' ⟨ Matrix.GeneralLinearGroup.mkOfDetNeZero ( Matrix.diagonal ( fun i => if i = ⟨ 0, Nat.pos_of_ne_zero ( NeZero.ne n ) ⟩ then x else 1 ) ) _, _ ⟩;
  all_goals simp +decide [ Matrix.GeneralLinearGroup.det ]

/-
The special linear group `SL(n, 𝔽)` has the same cardinality as the kernel of the
determinant map on `GL(n, 𝔽)` (indeed `SL(n, 𝔽)` *is* that kernel, up to the canonical
inclusion `SL → GL`).
-/
omit [Fintype 𝔽] [DecidableEq 𝔽] in
theorem card_SL_eq_card_ker {n : ℕ} :
    Nat.card (SL(n, 𝔽)) =
      Nat.card (Matrix.GeneralLinearGroup.det (n := Fin n) (R := 𝔽)).ker := by
  fapply Nat.card_congr;
  refine' Equiv.ofBijective ( fun g => ⟨ g |> Matrix.SpecialLinearGroup.toGL, _ ⟩ ) ⟨ fun a b h => _, fun a => _ ⟩ <;> simp_all +decide;
  rcases a with ⟨ a, ha ⟩;
  refine' ⟨ ⟨ a, _ ⟩, _ ⟩ <;> simp_all +decide [ Matrix.SpecialLinearGroup.toGL ];
  convert congr_arg Units.val ha using 1

/-
**Order of the special linear group.**
`|GL(n, 𝔽)| = |SL(n, 𝔽)| · (|𝔽| - 1)` for a finite field `𝔽` and `n ≥ 1`.
-/
theorem card_GL_eq_card_SL_mul {n : ℕ} [NeZero n] :
    Nat.card (GL (Fin n) 𝔽) = Nat.card (SL(n, 𝔽)) * (Fintype.card 𝔽 - 1) := by
  -- Let `f := (Matrix.GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)`.
  set f : GL (Fin n) 𝔽 →* (Units 𝔽) := Matrix.GeneralLinearGroup.det;
  -- By the first isomorphism theorem, we have $|GL(n, 𝔽)| = |SL(n, 𝔽)| \cdot |𝔽ˣ|$.
  have h_iso : Nat.card (GL (Fin n) 𝔽) = Nat.card (f.ker) * Nat.card (Units 𝔽) := by
    convert Subgroup.card_eq_card_quotient_mul_card_subgroup ( f.ker ) using 1;
    rw [ mul_comm, Nat.card_congr ( QuotientGroup.quotientKerEquivOfSurjective f ( det_surjective ) ).toEquiv ];
  convert h_iso using 2;
  · convert card_SL_eq_card_ker
  · rw [ Nat.card_eq_fintype_card, Fintype.card_units ]

end CardSL

end Mathieu