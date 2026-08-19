import Mathlib
import Mathieu.DefM23
import Mathieu.BasicM22
import Mathieu.Subgroups
import Mathieu.TransM23

/-!
# Basic properties of `M₂₃`

* `|M₂₃| = 10200960 = 23 · 22 · 21 · 20 · 48`;
* `M₂₃` acts 4-transitively on the 23 points.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv

/-- `m₂₃ₐ` is a 23-cycle. -/
theorem m23a_isCycle : m23a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- `m₂₃ₐ` moves every point (it is a full-support cycle). -/
theorem m23a_moves : ∀ x : Fin 23, m23a x ≠ x := by decide

/-- **Base case of `k`-transitivity (PLAN §3.2).**  `M₂₃` acts transitively on the 23
points, because it contains the 23-cycle `m₂₃ₐ` whose support is all of `Fin 23`. -/
theorem M23_isPretransitive : MulAction.IsPretransitive M23 (Fin 23) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, hi⟩ := m23a_isCycle.exists_pow_eq (m23a_moves x) (m23a_moves y)
  exact ⟨⟨m23a ^ i, M23.pow_mem m23a_mem i⟩, by simpa [Submonoid.smul_def] using hi⟩

/-- `M₂₃` acts 4-transitively on the 23 points.

Proved `native_decide`-free by the Wielandt stabiliser recursion: the point stabiliser of `22`
is `M₂₂`, which acts `3`-transitively on the remaining `22` points; see
`TransM23.M23_isMultiplyPretransitive_four` (built on `M₂₁`'s `2`-transitivity, transported
from `PSL(3,4)`). -/
theorem M23_isMultiplyPretransitive_four :
    MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 :=
  TransM23.M23_isMultiplyPretransitive_four

/-- **`M₂₂` is 3-transitive.**  The stabiliser of the point `22` inside `M₂₃` — which is
exactly `M₂₂` (see `M22_eq_ptStab`) — acts 3-transitively on the remaining `22` points
(`SubMulAction.ofStabilizer (↥M₂₃) 22`).

This is the faithful statement of 3-transitivity of `M₂₂` on the 22 points it moves; it is
an immediate corollary of the 4-transitivity of `M₂₃` via the Wielandt stabiliser recursion
(`SubMulAction.ofStabilizer.isMultiplyPretransitive`). -/
theorem M22_isMultiplyPretransitive_three :
    MulAction.IsMultiplyPretransitive
      (MulAction.stabilizer (↥M23) (22 : Fin 23))
      (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) 3 := by
  haveI := M23_isPretransitive
  have h4 : MulAction.IsMultiplyPretransitive (↥M23) (Fin 23) (3 : ℕ).succ :=
    M23_isMultiplyPretransitive_four
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := (22 : Fin 23))).mp h4

/-- The order of `M₂₃` is `10200960`.

Proved by orbit–stabiliser: `M₂₃` is transitive on its 23 points
(`M23_isPretransitive`), and the stabiliser of `22` is exactly `M₂₂`
(`M22_eq_ptStab`), so `|M₂₃| = 23 · |M₂₂| = 23 · 443520`. -/
theorem M23_card : Nat.card M23 = 10200960 := by
  haveI := M23_isPretransitive
  rw [card_eq_of_pretransitive M23 (22 : Fin 23), ← M22_eq_ptStab, M22_card]

/-- `M₂₃` is nontrivial (sanity check). -/
theorem M23_neBot : M23 ≠ ⊥ := by
  intro h
  have : m23a ∈ (⊥ : Subgroup (Perm (Fin 23))) := h ▸ m23a_mem
  rw [Subgroup.mem_bot] at this
  exact m23a_ne_one this

end Mathieu
