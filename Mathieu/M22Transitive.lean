import Mathieu.EnumM22Gen
import Mathieu.M22Cycles
import Mathieu.DefM22

/-!
# `M₂₂` is transitive on its `22` points — directly from generators

This file proves that `M₂₂` acts transitively on the `22` points `{0, …, 21}` it moves
(everything except its fixed point `22`), **directly from four of its Schreier generators**
`schB 1, schB 2, schB 7, schB 13`.  A short breadth-first search shows these four already
move `21` onto every point `≠ 22`.

The point of proving this here (rather than as a corollary of `M₂₂`'s `3`-transitivity, which
in turn came from the `EnumM23Trans` orbit enumeration) is to break a circular dependency:
`|M₂₁| = |M₂₂| / 22` (`PSL.M21_card`) needs exactly this transitivity, and everything in the
`PSL(3,4) ≅ M₂₁` tower — and hence the Wielandt transitivity proofs of `M₂₂/M₂₃` — rests on
`M21_card`.  Deriving the transitivity from the raw generators makes that chain independent of
the `EnumM23Trans` `native_decide` certificate.
-/

namespace Mathieu

open Equiv MulAction
open EnumM22 (schB schB_mem_M22)

namespace M22Transitive

set_option maxRecDepth 100000

/-- Concrete cycle form of `schB 1`. -/
def p1 : Perm (Fin 23) :=
  c[0, 14, 7, 4, 6] * c[1, 10, 11, 16, 2] * c[5, 15, 8, 9, 20] * c[12, 17, 19, 18, 13]
/-- Concrete cycle form of `schB 2`. -/
def p2 : Perm (Fin 23) :=
  c[0, 18, 3, 14, 16, 4] * c[1, 9, 19, 13, 15, 10] * c[2, 11] * c[5, 8] * c[6, 12, 20] * c[7, 17, 21]
/-- Concrete cycle form of `schB 7`. -/
def p7 : Perm (Fin 23) :=
  c[0, 7, 19, 8, 14, 12, 20, 10, 9, 15, 5] * c[1, 11, 3, 4, 18, 17, 21, 13, 2, 16, 6]
/-- Concrete cycle form of `schB 13`. -/
def p13 : Perm (Fin 23) :=
  c[1, 18, 10, 5, 2, 13, 7] * c[3, 14, 9, 4, 8, 11, 20] * c[6, 19, 15, 12, 16, 21, 17]

theorem p1_mem : p1 ∈ M22 := by rw [show p1 = schB 1 from schB1_eq.symm]; exact schB_mem_M22 1
theorem p2_mem : p2 ∈ M22 := by rw [show p2 = schB 2 from schB2_eq.symm]; exact schB_mem_M22 2
theorem p7_mem : p7 ∈ M22 := by rw [show p7 = schB 7 from schB7_eq.symm]; exact schB_mem_M22 7
theorem p13_mem : p13 ∈ M22 := by rw [show p13 = schB 13 from schB13_eq.symm]; exact schB_mem_M22 13

/-- **`M₂₂` is transitive on the `22` points `≠ 22`.**  For every `x ≠ 22` there is an element
of `M₂₂` sending `21` to `x`; the witness is an explicit word in `p1, p2, p7, p13` found by a
breadth-first search. -/
theorem M22_reaches (x : Fin 23) (hx : x ≠ 22) :
    ∃ g : ↥M22, (g : Perm (Fin 23)) 21 = x := by
  fin_cases x
  · exact ⟨⟨p2 * p1 * p2, mul_mem (mul_mem p2_mem p1_mem) p2_mem⟩, by decide⟩          -- 0
  · exact ⟨⟨p13 * p2, mul_mem p13_mem p2_mem⟩, by decide⟩                               -- 1
  · exact ⟨⟨p7 * p7, mul_mem p7_mem p7_mem⟩, by decide⟩                                 -- 2
  · exact ⟨⟨p2 * p7 * p1 * p2, mul_mem (mul_mem (mul_mem p2_mem p7_mem) p1_mem) p2_mem⟩, by decide⟩  -- 3
  · exact ⟨⟨p1 * p2, mul_mem p1_mem p2_mem⟩, by decide⟩                                 -- 4
  · exact ⟨⟨p7 * p2 * p7, mul_mem (mul_mem p7_mem p2_mem) p7_mem⟩, by decide⟩           -- 5
  · exact ⟨⟨p13 * p13, mul_mem p13_mem p13_mem⟩, by decide⟩                             -- 6
  · exact ⟨⟨p2, p2_mem⟩, by decide⟩                                                     -- 7
  · exact ⟨⟨p13 * p1 * p2, mul_mem (mul_mem p13_mem p1_mem) p2_mem⟩, by decide⟩         -- 8
  · exact ⟨⟨p2 * p13 * p2, mul_mem (mul_mem p2_mem p13_mem) p2_mem⟩, by decide⟩         -- 9
  · exact ⟨⟨p1 * p13 * p2, mul_mem (mul_mem p1_mem p13_mem) p2_mem⟩, by decide⟩         -- 10
  · exact ⟨⟨p7 * p13 * p2, mul_mem (mul_mem p7_mem p13_mem) p2_mem⟩, by decide⟩         -- 11
  · exact ⟨⟨p1 * p7, mul_mem p1_mem p7_mem⟩, by decide⟩                                 -- 12
  · exact ⟨⟨p7, p7_mem⟩, by decide⟩                                                     -- 13
  · exact ⟨⟨p1 * p2 * p1 * p2, mul_mem (mul_mem (mul_mem p1_mem p2_mem) p1_mem) p2_mem⟩, by decide⟩  -- 14
  · exact ⟨⟨p2 * p7, mul_mem p2_mem p7_mem⟩, by decide⟩                                 -- 15
  · exact ⟨⟨p13 * p1 * p7, mul_mem (mul_mem p13_mem p1_mem) p7_mem⟩, by decide⟩         -- 16
  · exact ⟨⟨p13, p13_mem⟩, by decide⟩                                                   -- 17
  · exact ⟨⟨p7 * p1 * p2, mul_mem (mul_mem p7_mem p1_mem) p2_mem⟩, by decide⟩           -- 18
  · exact ⟨⟨p7 * p2, mul_mem p7_mem p2_mem⟩, by decide⟩                                 -- 19
  · exact ⟨⟨p2 * p1 * p7, mul_mem (mul_mem p2_mem p1_mem) p7_mem⟩, by decide⟩           -- 20
  · exact ⟨1, by decide⟩                                                                -- 21
  · exact absurd rfl hx                                                                 -- 22

end M22Transitive

end Mathieu
