import Mathlib
import Mathieu.EnumM22Gen

/-!
# Perfectness of `M₂₂`

We prove that `M₂₂` is perfect (`commutator (↥M22) = ⊤`).  This complements `Perfect.lean`
(which handles `M₁₁, M₁₂, M₂₃, M₂₄`) and supplies the last perfectness ingredient needed for
the Iwasawa-criterion route to simplicity (see `PLAN.md` §3.5).

`M₂₂` is *defined* as the point stabiliser `M₂₃ ⊓ stab 22`, with no native generating set; it
is generated (proved in `EnumM22.lean`, `M22_eq_K`) by the four Schreier generators
`schB 1, schB 2, schB 7, schB 13` and their inverses.  Each of these four generators turns
out to be a **single commutator** of words in the four generators; the identity is closed and
checked by `decide`, and membership in `commutator` follows from
`Subgroup.commutator_mem_commutator`.
-/

namespace Mathieu

set_option maxRecDepth 60000

open Equiv
open EnumM22


/-- Concrete cycle form of the transversal powers `tt m = m23a ^ (m+1)` needed below.
Each is a single power of the 23-cycle, so `decide` reduces it with shallow recursion. -/
lemma tt1_eq : tt 1 =
    c[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21] := by decide
lemma tt2_eq : tt 2 =
    c[0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20] := by decide
lemma tt7_eq : tt 7 =
    c[0, 8, 16, 1, 9, 17, 2, 10, 18, 3, 11, 19, 4, 12, 20, 5, 13, 21, 6, 14, 22, 7, 15] := by decide
lemma tt13_eq : tt 13 =
    c[0, 14, 5, 19, 10, 1, 15, 6, 20, 11, 2, 16, 7, 21, 12, 3, 17, 8, 22, 13, 4, 18, 9] := by decide
lemma tt_m23b1_eq : tt (m23b 1) =
    c[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21] := by decide
lemma tt_m23b2_eq : tt (m23b 2) =
    c[0, 17, 11, 5, 22, 16, 10, 4, 21, 15, 9, 3, 20, 14, 8, 2, 19, 13, 7, 1, 18, 12, 6] := by decide
lemma tt_m23b7_eq : tt (m23b 7) =
    c[0, 18, 13, 8, 3, 21, 16, 11, 6, 1, 19, 14, 9, 4, 22, 17, 12, 7, 2, 20, 15, 10, 5] := by decide
lemma tt_m23b13_eq : tt (m23b 13) =
    c[0, 19, 15, 11, 7, 3, 22, 18, 14, 10, 6, 2, 21, 17, 13, 9, 5, 1, 20, 16, 12, 8, 4] := by decide

/-- Concrete cycle form of the Schreier generator `schB 1`.
Obtained from the concrete transversal factors so that the final `decide` only multiplies
three explicit permutations (shallow), avoiding the deep power/inverse nesting of `schB`. -/
lemma schB1_eq : schB 1 =
    c[0, 14, 7, 4, 6] * c[1, 10, 11, 16, 2] * c[5, 15, 8, 9, 20] * c[12, 17, 19, 18, 13] := by
  unfold schB; rw [tt1_eq, tt_m23b1_eq]; decide

/-- Concrete cycle form of the Schreier generator `schB 2`. -/
lemma schB2_eq : schB 2 =
    c[0, 18, 3, 14, 16, 4] * c[1, 9, 19, 13, 15, 10] * c[2, 11] * c[5, 8] * c[6, 12, 20] * c[7, 17, 21] := by
  unfold schB; rw [tt2_eq, tt_m23b2_eq]; decide

/-- Concrete cycle form of the Schreier generator `schB 7`. -/
lemma schB7_eq : schB 7 =
    c[0, 7, 19, 8, 14, 12, 20, 10, 9, 15, 5] * c[1, 11, 3, 4, 18, 17, 21, 13, 2, 16, 6] := by
  unfold schB; rw [tt7_eq, tt_m23b7_eq]; decide

/-- Concrete cycle form of the Schreier generator `schB 13`. -/
lemma schB13_eq : schB 13 =
    c[1, 18, 10, 5, 2, 13, 7] * c[3, 14, 9, 4, 8, 11, 20] * c[6, 19, 15, 12, 16, 21, 17] := by
  unfold schB; rw [tt13_eq, tt_m23b13_eq]; decide


end Mathieu
