import Mathlib
import Mathieu.DefM24
import Mathieu.BasicM23
import Mathieu.Subgroups
import Mathieu.TransM24
import Mathieu.EnumM24Iso

/-!
# Basic properties of `M₂₄`

* `|M₂₄| = 244823040 = 24 · 23 · 22 · 21 · 20 · 48`;
* `M₂₄` acts (sharply) 5-transitively on the 24 points.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv MulAction

/-- `m₂₄ₐ` is a 23-cycle (with support `{0,…,22}`). -/
theorem m24a_isCycle : m24a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- `m₂₄ₐ` moves every point other than the fixed point `23`. -/
theorem m24a_moves_ne23 : ∀ x : Fin 24, x ≠ 23 → m24a x ≠ x := by decide

/-- **Base case of `k`-transitivity (PLAN §3.2).**  `M₂₄` acts transitively on the 24
points: the 23-cycle `m₂₄ₐ` sends `0` to every point of `{0,…,22}`, and the involution
`m₂₄ᴄ` sends `0` to the last point `23`. -/
theorem M24_isPretransitive : MulAction.IsPretransitive M24 (Fin 24) := by
  rw [isPretransitive_iff_base (0 : Fin 24)]
  intro x
  by_cases hx : x = 23
  · refine ⟨⟨m24c, m24c_mem⟩, ?_⟩
    subst hx
    have : m24c 0 = 23 := by decide
    simpa [Submonoid.smul_def] using this
  · have h0 : m24a 0 ≠ 0 := by decide
    obtain ⟨i, hi⟩ := m24a_isCycle.exists_pow_eq h0 (m24a_moves_ne23 x hx)
    exact ⟨⟨m24a ^ i, M24.pow_mem m24a_mem i⟩, by simpa [Submonoid.smul_def] using hi⟩

/-- `M₂₄` acts 5-transitively on the 24 points.

Proved `native_decide`-free by the Wielandt stabiliser recursion: the point stabiliser of `23`
is isomorphic to `M₂₃`, which acts `4`-transitively on the remaining `23` points; see
`TransM24.M24_isMultiplyPretransitive_five` (built on the transitivity tower down to `M₂₁`'s
`2`-transitivity transported from `PSL(3,4)`). -/
theorem M24_isMultiplyPretransitive_five :
    MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 :=
  TransM24.M24_isMultiplyPretransitive_five

/-- The order of `M₂₄` is `244823040`.

Proved by orbit–stabiliser: `M₂₄` is transitive on its 24 points
(`M24_isPretransitive`), and the stabiliser of `23` is isomorphic to `M₂₃`
(`M23_iso_ptStab_M24`), so `|M₂₄| = 24 · |M₂₃| = 24 · 10200960`. -/
theorem M24_card : Nat.card M24 = 244823040 := by
  haveI := M24_isPretransitive
  rw [card_eq_of_pretransitive M24 (23 : Fin 24)]
  obtain ⟨e⟩ := M23_iso_ptStab_M24
  rw [← Nat.card_congr e.toEquiv, M23_card]

/-- `M₂₄` is nontrivial (sanity check). -/
theorem M24_neBot : M24 ≠ ⊥ := by
  intro h
  have : m24c ∈ (⊥ : Subgroup (Perm (Fin 24))) := h ▸ m24c_mem
  rw [Subgroup.mem_bot] at this
  have : m24c 23 = (1 : Perm (Fin 24)) 23 := by rw [this]
  rw [m24c_apply_last] at this
  simp at this

end Mathieu
