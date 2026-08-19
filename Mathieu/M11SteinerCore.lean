import Mathieu.BasicM11

/-!
# The Witt Steiner system on eleven points

This file gives the 66 blocks of the Witt design `S(4,5,11)`, proves the Steiner
property, and identifies its full permutation symmetry group with `M₁₁`.
-/

namespace Mathieu

open Equiv

/-- A finite block family is a `t-(v,k,1)` Steiner system when every block has size `k`
and every `t`-subset lies in exactly one block. -/
def IsSteinerSystem {X : Type*} [Fintype X] [DecidableEq X]
    (t k : ℕ) (blocks : Finset (Finset X)) : Prop :=
  (blocks.filter fun B => B.card ≠ k) = ∅ ∧
    ((((Finset.univ : Finset X).powerset.filter fun T => T.card = t).filter fun T =>
      (blocks.filter fun B => T ⊆ B).card ≠ 1)) = ∅

def M11Blocks : Finset (Finset (Fin 11)) :=
  {{0, 1, 2, 3, 9},
   {0, 1, 2, 4, 7},
   {0, 1, 2, 5, 6},
   {0, 1, 2, 8, 10},
   {0, 1, 3, 4, 8},
   {0, 1, 3, 5, 7},
   {0, 1, 3, 6, 10},
   {0, 1, 4, 5, 10},
   {0, 1, 4, 6, 9},
   {0, 1, 5, 8, 9},
   {0, 1, 6, 7, 8},
   {0, 1, 7, 9, 10},
   {0, 2, 3, 4, 5},
   {0, 2, 3, 6, 8},
   {0, 2, 3, 7, 10},
   {0, 2, 4, 6, 10},
   {0, 2, 4, 8, 9},
   {0, 2, 5, 7, 8},
   {0, 2, 5, 9, 10},
   {0, 2, 6, 7, 9},
   {0, 3, 4, 6, 7},
   {0, 3, 4, 9, 10},
   {0, 3, 5, 6, 9},
   {0, 3, 5, 8, 10},
   {0, 3, 7, 8, 9},
   {0, 4, 5, 6, 8},
   {0, 4, 5, 7, 9},
   {0, 4, 7, 8, 10},
   {0, 5, 6, 7, 10},
   {0, 6, 8, 9, 10},
   {1, 2, 3, 4, 10},
   {1, 2, 3, 5, 8},
   {1, 2, 3, 6, 7},
   {1, 2, 4, 5, 9},
   {1, 2, 4, 6, 8},
   {1, 2, 5, 7, 10},
   {1, 2, 6, 9, 10},
   {1, 2, 7, 8, 9},
   {1, 3, 4, 5, 6},
   {1, 3, 4, 7, 9},
   {1, 3, 5, 9, 10},
   {1, 3, 6, 8, 9},
   {1, 3, 7, 8, 10},
   {1, 4, 5, 7, 8},
   {1, 4, 6, 7, 10},
   {1, 4, 8, 9, 10},
   {1, 5, 6, 7, 9},
   {1, 5, 6, 8, 10},
   {2, 3, 4, 6, 9},
   {2, 3, 4, 7, 8},
   {2, 3, 5, 6, 10},
   {2, 3, 5, 7, 9},
   {2, 3, 8, 9, 10},
   {2, 4, 5, 6, 7},
   {2, 4, 5, 8, 10},
   {2, 4, 7, 9, 10},
   {2, 5, 6, 8, 9},
   {2, 6, 7, 8, 10},
   {3, 4, 5, 7, 10},
   {3, 4, 5, 8, 9},
   {3, 4, 6, 8, 10},
   {3, 5, 6, 7, 8},
   {3, 6, 7, 9, 10},
   {4, 5, 6, 9, 10},
   {4, 6, 7, 8, 9},
   {5, 7, 8, 9, 10}}


/-- The full permutation symmetry group of the Witt design. -/
def M11SteinerAut : Subgroup (Perm (Fin 11)) where
  carrier := {g | ∀ B, B ∈ M11Blocks ↔ B.map g.toEmbedding ∈ M11Blocks}
  one_mem' := by
    intro B
    have heq : B.map (1 : Perm (Fin 11)).toEmbedding = B := by
      ext x
      simp
    rw [heq]
  mul_mem' := by
    intro g h hg hh B
    calc
      B ∈ M11Blocks ↔ B.map h.toEmbedding ∈ M11Blocks := hh B
      _ ↔ (B.map h.toEmbedding).map g.toEmbedding ∈ M11Blocks := hg _
      _ ↔ B.map (g * h).toEmbedding ∈ M11Blocks := by
        have heq : (B.map h.toEmbedding).map g.toEmbedding =
            B.map (g * h).toEmbedding := by
          rw [Finset.map_map]
          congr 1
        rw [heq]
  inv_mem' := by
    intro g hg B
    have h := (hg (B.map g⁻¹.toEmbedding)).symm
    have heq : (B.map g⁻¹.toEmbedding).map g.toEmbedding = B := by
      rw [Finset.map_map]
      convert (Finset.map_refl : B.map (Function.Embedding.refl (Fin 11)) = B) using 1
      ext x
      simp
    rwa [heq] at h

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The displayed blocks form a `(5,4,11)` Steiner system (convention: block size first). -/
theorem M11Blocks_isSteiner : IsSteinerSystem 4 5 M11Blocks := by
  unfold IsSteinerSystem
  decide

/-- Both standard generators preserve the block family. -/
lemma m11a_mem_M11SteinerAut : m11a ∈ M11SteinerAut := by
  intro B
  have hall : M11Blocks.image (fun C => C.map m11a.toEmbedding) = M11Blocks := by
    decide
  constructor
  · intro hB
    rw [← hall]
    simp [hB]
  · intro hB
    have hi : B.map m11a.toEmbedding ∈
        M11Blocks.image (fun C => C.map m11a.toEmbedding) := hall.symm ▸ hB
    simpa using hi

lemma m11b_mem_M11SteinerAut : m11b ∈ M11SteinerAut := by
  intro B
  have hall : M11Blocks.image (fun C => C.map m11b.toEmbedding) = M11Blocks := by
    decide
  constructor
  · intro hB
    rw [← hall]
    simp [hB]
  · intro hB
    have hi : B.map m11b.toEmbedding ∈
        M11Blocks.image (fun C => C.map m11b.toEmbedding) := hall.symm ▸ hB
    simpa using hi

/-- Consequently every element of `M₁₁` is a symmetry of the Steiner system. -/
theorem M11_le_M11SteinerAut : M11 ≤ M11SteinerAut := by
  rw [M11, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact m11a_mem_M11SteinerAut
  · exact m11b_mem_M11SteinerAut


end Mathieu
