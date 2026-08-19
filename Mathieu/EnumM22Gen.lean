import Mathlib
import Mathieu.DefM22

/-!
# Schreier generators for `M₂₂`

`M₂₂` is *defined* as the point stabiliser `M₂₃ ⊓ stab 22`, so it has no generating set
to enumerate directly.  This file sets up **Schreier generators**.

Let `a = m23a` (the 23-cycle) and `b = m23b`.  Using the transversal `tt m = a ^ (m+1)`
(which satisfies `tt m 22 = m`), the Schreier generators of the stabiliser of `22` are
```
schB m = (tt (b m))⁻¹ * b * (tt m)        (m : Fin 23).
```
The Schreier generators coming from `a` are all trivial, since `a` defines the transversal
(`a_tt`).  Each `schB m` lies in `M₂₃` (it is a word in `a, b`) and fixes `22`.

The small `decide` facts about these generators are isolated here (away from the
heavy breadth-first enumeration in `EnumM22.lean`) to keep each module's memory footprint
manageable.
-/

namespace Mathieu

open Equiv

namespace EnumM22

set_option maxRecDepth 100000

/-- The transversal element `tt m = m23a ^ (m+1)`; it satisfies `tt m 22 = m`. -/
def tt (m : Fin 23) : Perm (Fin 23) := m23a ^ (m.val + 1)

/-- The Schreier generator `schB m = (tt (m23b m))⁻¹ * m23b * tt m`. -/
def schB (m : Fin 23) : Perm (Fin 23) := (tt (m23b m))⁻¹ * m23b * tt m

/-- `tt m` sends `22` to `m` (verified). -/
lemma tt_apply22 : ∀ m : Fin 23, tt m 22 = m := by decide

/-- `tt 22 = 1`. -/
lemma tt_22 : tt (22 : Fin 23) = 1 := by
  show m23a ^ (22 + 1) = 1
  exact m23a_pow_eq_one

/-- Each Schreier generator fixes `22` (verified). -/
lemma schB_fixes : ∀ m : Fin 23, schB m 22 = 22 := by decide

/-- Each Schreier generator lies in `M₂₃`. -/
lemma schB_mem23 (m : Fin 23) : schB m ∈ M23 := by
  unfold schB tt
  exact mul_mem (mul_mem (inv_mem (M23.pow_mem m23a_mem _)) m23b_mem) (M23.pow_mem m23a_mem _)

/-- Each Schreier generator (and its inverse) lies in `M₂₂`. -/
lemma schB_mem_M22 (m : Fin 23) : schB m ∈ M22 :=
  ⟨schB_mem23 m, (MulAction.mem_stabilizer_iff).2
    (by simpa [Equiv.Perm.smul_def] using schB_fixes m)⟩

/-- `a * tt m = tt (a m)` (the `a`-Schreier generators are trivial). -/
lemma a_tt : ∀ m : Fin 23, m23a * tt m = tt (m23a m) := by decide

/-- `a⁻¹ * tt m = tt (a⁻¹ m)`. -/
lemma ainv_tt : ∀ m : Fin 23, m23a⁻¹ * tt m = tt (m23a⁻¹ m) := by decide

/-- `b * tt m = tt (b m) * schB m` (definition of the Schreier generator). -/
lemma b_tt (m : Fin 23) : m23b * tt m = tt (m23b m) * schB m := by
  unfold schB
  group

/-- `b⁻¹ * tt m = tt (b⁻¹ m) * (schB (b⁻¹ m))⁻¹`. -/
lemma binv_tt (m : Fin 23) : m23b⁻¹ * tt m = tt (m23b⁻¹ m) * (schB (m23b⁻¹ m))⁻¹ := by
  have hk : m23b (m23b⁻¹ m) = m := by simp
  unfold schB
  rw [hk]
  group

end EnumM22

end Mathieu
