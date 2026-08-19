import Mathlib
import Mathieu.DefM22
import Mathieu.M22CardClean

/-!
# Basic properties of `M₂₂`

* `|M₂₂| = 443520 = 22 · 21 · 20 · 48`;
* `M₂₂` acts 3-transitively on the 22 points it moves (the complement of `22 : Fin 23`).

Recall `M₂₂` is defined (in `DefM22.lean`) as the stabiliser of the point `22` inside
`M₂₃`.  Realising it as a permutation group on `Fin 22` and proving 3-transitivity there
is recorded as a goal; see `PLAN.md`.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv

/-- The order of `M₂₂` is `443520`.

Proved structurally in `M22CardClean.lean`: 3-transitivity and Golay-code rigidity give the
upper bound, while the projective-plane subgroup gives the matching lower bound. -/
theorem M22_card : Nat.card M22 = 443520 := M22_card_clean

/-- `M₂₂` is nontrivial (sanity check).  The element `m23b * m23a ^ 12` lies in `M₂₃`,
fixes the point `22`, and is nontrivial, so it is a nontrivial element of `M₂₂`. -/
theorem M22_neBot : M22 ≠ ⊥ := by
  have hmem23 : m23b * m23a ^ 12 ∈ M23 := M23.mul_mem m23b_mem (M23.pow_mem m23a_mem 12)
  have hfix : (m23b * m23a ^ 12) • (22 : Fin 23) = 22 := by decide
  have hne : m23b * m23a ^ 12 ≠ 1 := by decide
  have hmem22 : m23b * m23a ^ 12 ∈ M22 :=
    ⟨hmem23, (MulAction.mem_stabilizer_iff).2 hfix⟩
  intro h
  rw [h, Subgroup.mem_bot] at hmem22
  exact hne hmem22

/-
A realisation of `M₂₂` as a permutation group on `Fin 22`.

`M₂₂` fixes the point `22 : Fin 23` and therefore restricts to a permutation of the
remaining `22` points; transporting along an equivalence `{x : Fin 23 // x ≠ 22} ≃ Fin 22`
gives an isomorphic subgroup of `Equiv.Perm (Fin 22)`.  This is recorded as a goal; the
construction is described in `PLAN.md`.
-/
theorem M22_exists_perm22_rep :
    ∃ H : Subgroup (Perm (Fin 22)), Nonempty (M22 ≃* H) := by
      have h_embedding : ∃ (φ : M22 →* Equiv.Perm (Fin 22)), Function.Injective φ := by
        -- Let's choose any bijection between the set {0, 1, ..., 21} and the set {0, 1, ..., 22} \ {22}.
        obtain ⟨e, he⟩ : ∃ e : Fin 22 ≃ {x : Fin 23 // x ≠ 22}, True := by
          exact ⟨ Fintype.equivOfCardEq ( by decide ), trivial ⟩;
        refine' ⟨ _, _ ⟩;
        refine' MonoidHom.mk' _ _;
        refine' fun g => Equiv.permCongr e.symm ( Equiv.Perm.subtypePerm ( g.val ) _ );
        all_goals norm_num [ Function.Injective, Equiv.Perm.ext_iff ];
        · intro x; have := g.2; simp_all +decide [ M22 ] ;
          have := g.2.2; simp_all +decide [ MulAction.mem_stabilizer_iff ] ;
          exact ⟨ fun hx => by rintro rfl; exact hx this, fun hx => by intro H; have := g.1.injective ( H.trans this.symm ) ; aesop ⟩;
        · intro a ha b hb hab x; by_cases hx : x = 22 <;> simp_all +decide [ M22 ] ;
      generalize_proofs at *; (
      cases' h_embedding with φ hφ
      generalize_proofs at *; (
      exact ⟨ φ.range, ⟨ { Equiv.ofInjective _ hφ with map_mul' := by aesop } ⟩ ⟩))

end Mathieu