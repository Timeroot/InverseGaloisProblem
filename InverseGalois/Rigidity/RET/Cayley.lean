/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The regular (Cayley) representation

The faithful regular representation `G ↪ Equiv.Perm (Fin (Nat.card G))`, the permutation model used
by the model-translation step (`RET.Specialization`) to turn an abstract regular Galois realization
of `G` over `ℚ(T)` into an explicit `ℚ[T][X]` family of degree `n = |G|`.

* `Rigidity.cayley` / `Rigidity.cayley_injective` — the regular representation and its faithfulness.
-/

noncomputable section

namespace Rigidity

variable {G : Type*} [Group G] [Finite G]

/-- A chosen bijection `G ≃ Fin (Nat.card G)`, used to model the regular representation inside
`Equiv.Perm (Fin (Nat.card G))`. -/
def eFin (G : Type*) [Finite G] : G ≃ Fin (Nat.card G) := Finite.equivFin G

/-- The **regular (Cayley) representation** of `G` as permutations of `Fin (Nat.card G)`: the
left-multiplication action of `G` on itself, transported along `eFin`. -/
def cayley (G : Type*) [Group G] [Finite G] : G →* Equiv.Perm (Fin (Nat.card G)) :=
  (Equiv.permCongrHom (eFin G)).toMonoidHom.comp (MulAction.toPermHom G G)

/-- The regular representation is faithful. -/
theorem cayley_injective : Function.Injective (cayley G) := by
  rw [cayley, MonoidHom.coe_comp]
  refine (Equiv.permCongrHom (eFin G)).injective.comp ?_
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective

end Rigidity

end
