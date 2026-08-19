import Mathieu.TransM23
import Mathieu.EnumM24IsoCore

/-!
# `M₂₄` is `5`-transitive on its `24` points

The top step of the Wielandt transitivity tower, built on
`M23_isMultiplyPretransitive_four` (`M₂₃` is `4`-transitive on `Fin 23`).

`M₂₄ ≤ Perm (Fin 24)` is transitive on all `24` points, and the point stabiliser of `23` is
isomorphic to `M₂₃` via the extension homomorphism `Perm.extendDomainHom e24`
(`EnumM24Iso`).  By the Wielandt stabiliser recursion
(`SubMulAction.ofStabilizer.isMultiplyPretransitive`), `M₂₄` is therefore `5`-transitive on
`Fin 24`.

This gives a proof of `M₂₄`'s `5`-transitivity that does **not** use the `EnumM24Trans` orbit
enumeration.  It uses only the *easy* (extension) direction `EnumM24Iso.map_le` — which is
`native_decide`-free — together with `M₂₃`'s `4`-transitivity, so it rests only on the
`EnumM22` order that the whole tower already rests on (via `M21_card`), **not** on the
`EnumM24Iso` Schreier-closure certificate.
-/

namespace Mathieu

open Equiv MulAction Function

namespace TransM24

set_option maxRecDepth 100000

open EnumM24Iso (e24)

/-! ### `M₂₄` is transitive on `Fin 24` (reproved here to avoid importing `BasicM24`) -/

/-- `m₂₄ₐ` is a 23-cycle (support `{0,…,22}`). -/
theorem m24a_isCycle : m24a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- `m₂₄ₐ` moves every point other than the fixed point `23`. -/
theorem m24a_moves_ne23 : ∀ x : Fin 24, x ≠ 23 → m24a x ≠ x := by decide

/-- **`M₂₄` acts transitively on the `24` points.** -/
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

/-! ### Transport of `M₂₃`'s `4`-transitivity to the point stabiliser of `23` -/

/-- The embedding `M₂₃ ↪ stabilizer (↥M₂₄) 23`, extending a permutation of `Fin 23` by fixing
`23`.  Membership in `M₂₄` and fixing of `23` come from `EnumM24Iso.map_le` (the easy,
`native_decide`-free direction). -/
def psiM23toStab : ↥M23 →* ↥(stabilizer (↥M24) (23 : Fin 24)) where
  toFun g := ⟨⟨Perm.extendDomainHom e24 g.1, (EnumM24Iso.map_le ⟨g.1, g.2, rfl⟩).1⟩, by
    rw [mem_stabilizer_iff]
    have h2 := (EnumM24Iso.map_le ⟨g.1, g.2, rfl⟩).2
    have h2' : (Perm.extendDomainHom e24 g.1) (23 : Fin 24) = 23 := by
      simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp h2)
    simpa [Submonoid.smul_def, Equiv.Perm.smul_def] using h2'⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; simp

/-- The identification of `Fin 23` with the point set of `SubMulAction.ofStabilizer (↥M₂₄) 23`
(via `castSucc`). -/
def eStab : Fin 23 ≃ ↥(SubMulAction.ofStabilizer (↥M24) (23 : Fin 24)) where
  toFun i := ⟨i.castSucc, by rw [SubMulAction.mem_ofStabilizer_iff]; simp [Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by
    have h := (SubMulAction.mem_ofStabilizer_iff (↥M24) (23 : Fin 24)).mp x.2
    simpa [Fin.ext_iff] using h)
  left_inv i := by simp
  right_inv x := by ext; simp

lemma eStab_val (j : Fin 23) : (eStab j : Fin 24) = j.castSucc := rfl

/-- `eStab` is equivariant for the embedding `psiM23toStab`. -/
theorem eStab_equivariant (g : ↥M23) (j : Fin 23) :
    (psiM23toStab g) • (eStab j) = eStab (g • j) := by
  apply Subtype.ext
  rw [SubMulAction.val_smul]
  show (Perm.extendDomainHom e24 g.1) ((eStab j : Fin 24)) = (eStab (g • j) : Fin 24)
  rw [eStab_val, eStab_val, show (g • j : Fin 23) = g.1 j from rfl]
  exact Perm.extendDomain_apply_image g.1 e24 j

/-- The induced equivariant map on `4`-point embeddings. -/
def Femb : (Fin 4 ↪ Fin 23) →ₑ[psiM23toStab]
    (Fin 4 ↪ ↥(SubMulAction.ofStabilizer (↥M24) (23 : Fin 24))) where
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

/-- **`M₂₄` acts `5`-transitively on the `24` points.**

Native-`decide`-free (modulo the `EnumM22` order that `M21_card` rests on): via the Wielandt
stabiliser recursion, the stabiliser of `23` (isomorphic to `M₂₃`) acts `4`-transitively on
the remaining `23` points, so `M₂₄` is `5`-transitive.  In particular this does not use the
`EnumM24Trans` orbit enumeration. -/
theorem M24_isMultiplyPretransitive_five :
    MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 := by
  haveI := M24_isPretransitive
  have h4 : IsMultiplyPretransitive (↥M23) (Fin 23) 4 :=
    TransM23.M23_isMultiplyPretransitive_four
  have hstab : IsMultiplyPretransitive (stabilizer (↥M24) (23 : Fin 24))
      (SubMulAction.ofStabilizer (↥M24) (23 : Fin 24)) 4 := by
    unfold MulAction.IsMultiplyPretransitive at h4 ⊢
    exact h4.of_surjective_map (f := Femb) Femb_surj
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := ↥M24) (a := (23 : Fin 24)) (n := 4)).mpr hstab

/-! ### Consequence: the orbit of the base `5`-tuple is everything -/

/-- The base injective `5`-tuple `![0,1,2,3,4] : Fin 5 ↪ Fin 24`. -/
def baseEmb : Fin 5 ↪ Fin 24 := ⟨![0, 1, 2, 3, 4], by decide⟩

/-- The `M₂₄`-orbit of the base `5`-tuple is all injective `5`-tuples — an immediate
consequence of `5`-transitivity.  (Provides the `native_decide`-free replacement for the old
`EnumM24Trans.orbit_baseEmb_eq_univ`.) -/
theorem orbit_baseEmb_eq_univ :
    MulAction.orbit M24 baseEmb = (Set.univ : Set (Fin 5 ↪ Fin 24)) := by
  haveI : MulAction.IsPretransitive (↥M24) (Fin 5 ↪ Fin 24) :=
    M24_isMultiplyPretransitive_five
  exact MulAction.orbit_eq_univ M24 baseEmb

end TransM24

end Mathieu
