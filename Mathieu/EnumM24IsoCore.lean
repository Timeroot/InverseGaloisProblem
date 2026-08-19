import Mathlib
import Mathieu.DefM23
import Mathieu.DefM24

/-!
# The natural copy of `M₂₃` in the point stabiliser of `M₂₄`

This small core file defines the extension of permutations on `Fin 23` to permutations on
`Fin 24` fixing the last point, and proves that it maps `M₂₃` into the stabiliser of `23` in
`M₂₄`.  Surjectivity is proved structurally in `EnumM24Iso.lean` by a cardinality argument;
no enumeration of Schreier elements is needed.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv MulAction

namespace EnumM24Iso

/-- Concrete equivalence `Fin 23 ≃ {x : Fin 24 // x ≠ 23}`. -/
def e24 : Fin 23 ≃ {x : Fin 24 // x ≠ 23} where
  toFun i := ⟨i.castSucc, by simp [Fin.castSucc, Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by rcases x with ⟨v, hv⟩; simpa using hv)
  left_inv i := by simp
  right_inv x := by ext; simp

/-- The natural extension of `M₂₃` is contained in `stab_{M₂₄}(23)`. -/
lemma map_le :
    Subgroup.map (Perm.extendDomainHom e24) M23
      ≤ (M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) := by
  rw [show M23 = Subgroup.closure {m23a, m23b} from rfl, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · refine ⟨?_, (MulAction.mem_stabilizer_iff).2 ?_⟩
    · rw [show Perm.extendDomainHom e24 m23a = m24a from by decide]
      exact m24a_mem
    · rw [show Perm.extendDomainHom e24 m23a = m24a from by decide]
      simpa [Equiv.Perm.smul_def] using m24a_apply_last
  · refine ⟨?_, (MulAction.mem_stabilizer_iff).2 ?_⟩
    · rw [show Perm.extendDomainHom e24 m23b = m24b from by decide]
      exact Subgroup.subset_closure (by right; left; rfl)
    · rw [show Perm.extendDomainHom e24 m23b = m24b from by decide]
      simpa [Equiv.Perm.smul_def] using m24b_apply_last

end EnumM24Iso

end Mathieu
