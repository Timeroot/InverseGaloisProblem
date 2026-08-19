import Mathieu.TransM22
import Mathieu.DefM23

/-!
# `M₂₃` is `4`-transitive on its `23` points

The next step of the Wielandt transitivity tower, built on `TransM22.M22_isMultiplyPretransitive_three`
(`M₂₂` is `3`-transitive on its `22` points `Y22`).

`M₂₃ ≤ Perm (Fin 23)` is transitive on all `23` points, and the point stabiliser of `22` is
exactly `M₂₂`, which acts `3`-transitively on the remaining `22` points.  By the Wielandt
stabiliser recursion (`SubMulAction.ofStabilizer.isMultiplyPretransitive`), `M₂₃` is therefore
`4`-transitive on `Fin 23`.

This gives a proof of `M₂₃`'s `4`-transitivity that does **not** use the `EnumM23Trans` orbit
enumeration (it rests only on the `EnumM22` order via the tower base `M21_card`).
-/

namespace Mathieu

open Equiv MulAction Function

namespace TransM23

set_option maxRecDepth 100000

open TransM22 (Y22)

/-! ### `M₂₃` is transitive on `Fin 23` -/

/-- `m₂₃ₐ` is a 23-cycle. -/
theorem m23a_isCycle : m23a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- `m₂₃ₐ` moves every point. -/
theorem m23a_moves : ∀ x : Fin 23, m23a x ≠ x := by decide

/-- **`M₂₃` acts transitively on the `23` points**, via the full-support cycle `m₂₃ₐ`. -/
theorem M23_isPretransitive : MulAction.IsPretransitive M23 (Fin 23) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, hi⟩ := m23a_isCycle.exists_pow_eq (m23a_moves x) (m23a_moves y)
  exact ⟨⟨m23a ^ i, M23.pow_mem m23a_mem i⟩, by simpa [Submonoid.smul_def] using hi⟩

/-! ### Transport of `M₂₂`'s `3`-transitivity to the point stabiliser of `22` -/

/-- The embedding `M₂₂ ↪ stabilizer (↥M₂₃) 22`.  Every element of `M₂₂` lies in `M₂₃` and
fixes `22`. -/
def psiM22toStab : ↥M22 →* ↥(stabilizer (↥M23) (22 : Fin 23)) where
  toFun g := ⟨⟨g.1, M22_le_M23 g.2⟩, by
    rw [mem_stabilizer_iff]
    simpa [Submonoid.smul_def, Equiv.Perm.smul_def] using M22_fixes_last g.2⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; simp

/-- The identification of `Y22` (points `≠ 22`) with the point set of
`SubMulAction.ofStabilizer (↥M₂₃) 22`. -/
def eStab : Y22 ≃ ↥(SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) where
  toFun x := ⟨x.1, by rw [SubMulAction.mem_ofStabilizer_iff]; exact x.2⟩
  invFun y := ⟨y.1, by
    have := (SubMulAction.mem_ofStabilizer_iff (↥M23) (22 : Fin 23)).mp y.2
    exact this⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

@[simp] theorem eStab_val (x : Y22) : ((eStab x : Fin 23)) = x.1 := rfl

/-- `eStab` is equivariant for the embedding `psiM22toStab`. -/
theorem eStab_equivariant (g : ↥M22) (x : Y22) :
    (psiM22toStab g) • (eStab x) = eStab (g • x) := by
  apply Subtype.ext
  rw [SubMulAction.val_smul]
  show (g.1 : Perm (Fin 23)) x.1 = (g.1 : Perm (Fin 23)) x.1
  rfl

/-- The induced equivariant map on `3`-point embeddings. -/
def Femb : (Fin 3 ↪ Y22) →ₑ[psiM22toStab]
    (Fin 3 ↪ ↥(SubMulAction.ofStabilizer (↥M23) (22 : Fin 23))) where
  toFun x := x.trans eStab.toEmbedding
  map_smul' g x := by
    apply Function.Embedding.ext; intro i
    simp only [Embedding.smul_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    exact (eStab_equivariant g (x i)).symm

theorem Femb_surj : Function.Surjective Femb := by
  intro y
  refine ⟨y.trans eStab.symm.toEmbedding, ?_⟩
  apply Function.Embedding.ext; intro i
  show eStab (eStab.symm (y i)) = y i
  simp

/-- **`M₂₃` acts `4`-transitively on the `23` points.**

Native-`decide`-free (modulo the `EnumM22` order that `M21_card` rests on): via the Wielandt
stabiliser recursion, the stabiliser of `22` (namely `M₂₂`) acts `3`-transitively on the
remaining `22` points, so `M₂₃` is `4`-transitive.  In particular this does not use the
`EnumM23Trans` orbit enumeration. -/
theorem M23_isMultiplyPretransitive_four :
    MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := by
  haveI := M23_isPretransitive
  have h3 : IsMultiplyPretransitive (↥M22) Y22 3 :=
    TransM22.M22_isMultiplyPretransitive_three
  have hstab : IsMultiplyPretransitive (stabilizer (↥M23) (22 : Fin 23))
      (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) 3 := by
    unfold MulAction.IsMultiplyPretransitive at h3 ⊢
    exact h3.of_surjective_map (f := Femb) Femb_surj
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := ↥M23) (a := (22 : Fin 23)) (n := 3)).mpr hstab

end TransM23

end Mathieu
