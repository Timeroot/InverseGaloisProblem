import Mathieu.PSL211

/-!
# Two-transitivity of the exceptional action of `PSL(2,11)`
-/

namespace Mathieu
namespace PSL211

open MulAction Matrix Equiv
open scoped MatrixGroups

set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-- A rotation carrying a specified point to `1`. -/
def rotateToOne (a : Fin 11) : SL(2, ZMod 11) :=
  EnumL211.Tmat ^ ((12 - a.val) % 11)

lemma rotateToOne_apply (a : Fin 11) : rotateToOne a • a = 1 := by
  revert a
  decide

/-- Explicit elements of the index-`11` subgroup, chosen to carry `0` to each point other
than its fixed point `1`. -/
def complementTransporter : Fin 11 → SL(2, ZMod 11) := ![
  1,
  1,
  EnumL211.Amat * EnumL211.Bmat * EnumL211.Bmat * EnumL211.Amat,
  EnumL211.Amat * EnumL211.Bmat * EnumL211.Amat,
  EnumL211.Bmat * EnumL211.Bmat,
  EnumL211.Bmat * EnumL211.Amat * EnumL211.Bmat * EnumL211.Amat,
  EnumL211.Bmat * EnumL211.Amat,
  EnumL211.Bmat,
  EnumL211.Amat * EnumL211.Bmat,
  EnumL211.Bmat * EnumL211.Bmat * EnumL211.Amat,
  EnumL211.Amat]

lemma complementTransporter_fixes (a : Fin 11) : complementTransporter a • (1 : Fin 11) = 1 := by
  revert a
  decide

lemma complementTransporter_apply (a : Fin 11) (ha : a ≠ 1) :
    complementTransporter a • (0 : Fin 11) = a := by
  revert a
  decide

lemma exists_canonicalizer (a b : Fin 11) (hab : a ≠ b) :
    ∃ g : SL(2, ZMod 11), g • a = 1 ∧ g • b = 0 := by
  let r := rotateToOne a
  let z := r • b
  have hra : r • a = 1 := rotateToOne_apply a
  have hz : z ≠ 1 := by
    intro h
    apply hab
    exact (MulAction.injective r) (by simpa [z, hra] using h.symm)
  let q := complementTransporter z
  have hq1 : q • (1 : Fin 11) = 1 := complementTransporter_fixes z
  have hq0 : q • (0 : Fin 11) = z := complementTransporter_apply z hz
  refine ⟨q⁻¹ * r, ?_, ?_⟩
  · rw [SemigroupAction.mul_smul, hra]
    exact (inv_smul_eq_iff).2 hq1.symm
  · rw [SemigroupAction.mul_smul]
    exact (inv_smul_eq_iff).2 hq0.symm

lemma exceptional_pair_transitive :
    ∀ a b c d : Fin 11, a ≠ b → c ≠ d →
      ∃ g : SL(2, ZMod 11), g • a = c ∧ g • b = d := by
  intro a b c d hab hcd
  obtain ⟨g, hga, hgb⟩ := exists_canonicalizer a b hab
  obtain ⟨h, hhc, hhd⟩ := exists_canonicalizer c d hcd
  refine ⟨h⁻¹ * g, ?_, ?_⟩
  · rw [SemigroupAction.mul_smul, hga, ← hhc, inv_smul_smul]
  · rw [SemigroupAction.mul_smul, hgb, ← hhd, inv_smul_smul]

/-- The exceptional action used to embed `PSL(2,11)` in `M₁₁` is 2-transitive. -/
theorem exceptional_two_transitive :
    MulAction.IsMultiplyPretransitive (SL(2, ZMod 11)) (Fin 11) 2 := by
  constructor
  simp only [Function.Embedding.ext_iff, Function.Embedding.smul_apply]
  intro x y
  obtain ⟨g, hg0, hg1⟩ := exceptional_pair_transitive (x 0) (x 1) (y 0) (y 1)
    (x.injective.ne (by decide)) (y.injective.ne (by decide))
  refine ⟨g, fun i => ?_⟩
  fin_cases i
  · exact hg0
  · exact hg1

end PSL211
end Mathieu
