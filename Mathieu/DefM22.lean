import Mathlib
import Mathieu.DefM23

/-!
# The Mathieu group `M₂₂`

The Mathieu group `M₂₂` is most cleanly described as a point stabiliser inside `M₂₃`:
it is the subgroup of `M₂₃` fixing the last point `22 : Fin 23`.  Equivalently it is the
two-point stabiliser inside `M₂₄`.  This is the definition we take here, which is correct
by construction (given the generators of `M₂₃`).

`M₂₂` naturally acts on the remaining `22` points.  Realising it as a permutation group on
`Fin 22`, and giving an explicit two-generator presentation on `Fin 22`, are recorded as
goals in `BasicM22.lean`.
-/

namespace Mathieu

open Equiv

/-- The Mathieu group `M₂₂`, as the subgroup of `M₂₃ ≤ Equiv.Perm (Fin 23)` fixing the
point `22`.  It is, by construction, the point stabiliser of `22` in `M₂₃`. -/
def M22 : Subgroup (Perm (Fin 23)) :=
  M23 ⊓ MulAction.stabilizer (Perm (Fin 23)) (22 : Fin 23)

/-- Every element of `M₂₂` fixes the point `22`. -/
theorem M22_fixes_last {g : Perm (Fin 23)} (hg : g ∈ M22) : g (22 : Fin 23) = 22 :=
  hg.2

/-- `M₂₂` is contained in `M₂₃`. -/
theorem M22_le_M23 : M22 ≤ M23 := inf_le_left

end Mathieu
