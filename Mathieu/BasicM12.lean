import Mathlib
import Mathieu.DefM12
import Mathieu.EnumM12Clean
import Mathieu.BasicM11

/-!
# Basic properties of `M₁₂`

The headline facts about `M₁₂`:

* its order is `95040 = 12 · 11 · 10 · 9 · 8` (`M12_card`);
* it acts (sharply) 5-transitively on the 12 points (`M12_isMultiplyPretransitive_five`).

Both are proven.  The order is obtained **without any `native_decide`** by orbit–stabiliser
(`M₁₂` transitive, point stabiliser `≅ M₁₁`); see `EnumM12Clean.lean`.

`5`-transitivity is obtained **without any `native_decide`** by the classical *Wielandt
stabiliser recursion*: `M₁₂` acts transitively on its `12` points, and the stabiliser of the
point `11` acts `4`-transitively on the remaining `11` points because it *contains* the copy of
`M₁₁` embedded by extending permutations of `Fin 11` by fixing `11`
(`SubMulAction.ofStabilizer.isMultiplyPretransitive`), and `M₁₁` is `4`-transitive
(`M11_isMultiplyPretransitive_four`, itself `native_decide`-free).  Transitivity of a subgroup
is inherited by the ambient group, so the whole point stabiliser is `4`-transitive; the
recursion then upgrades this to `5`-transitivity of `M₁₂`.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv MulAction Function

/-- The order of `M₁₂` is `95040`.

Proved `native_decide`-free by orbit–stabiliser: `M₁₂` is transitive on its `12` points and its
point stabiliser is the copy of `M₁₁` (`|M₁₁| = 7920`), so `|M₁₂| = 12 · 7920`; see
`EnumM12Clean.lean`. -/
theorem M12_card : Nat.card M12 = 95040 := EnumM12Clean.M12_card_clean

/-- `m₁₂ₐ` is an 11-cycle (with support `{0,…,10}`). -/
theorem m12a_isCycle : m12a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- **Base case of `k`-transitivity (PLAN §3.2).**  `M₁₂` acts transitively on the 12
points: the 11-cycle `m₁₂ₐ` sends `0` to every point of `{0,…,10}`, and the involution
`m₁₂ᴄ` sends `0` to the last point `11`. -/
theorem M12_isPretransitive : MulAction.IsPretransitive M12 (Fin 12) := by
  rw [isPretransitive_iff_base (0 : Fin 12)]
  intro x
  by_cases hx : x = 11
  · refine ⟨⟨m12c, m12c_mem⟩, ?_⟩
    subst hx
    have : m12c 0 = 11 := by decide
    simpa [Submonoid.smul_def] using this
  · have h0 : m12a 0 ≠ 0 := by decide
    have hxm : m12a x ≠ x := by revert hx; revert x; decide
    obtain ⟨i, hi⟩ := m12a_isCycle.exists_pow_eq h0 hxm
    exact ⟨⟨m12a ^ i, M12.pow_mem m12a_mem i⟩, by simpa [Submonoid.smul_def] using hi⟩

/-! ### The clean (native-`decide`-free) copy of `M₁₁` inside the stabiliser of `11`

We embed `Perm (Fin 11)` into `Perm (Fin 12)` by extending a permutation to fix the point
`11`.  This carries `M₁₁` into the point stabiliser `stabilizer (↥M₁₂) 11`, and is equivariant
with respect to the identification `Fin 11 ≃ (Fin 12 ∖ {11})`.  Only the *embedding* is used
(never surjectivity), so no order computation is needed. -/

/-- The identification of `Fin 11` with the non-`11` points of `Fin 12` (via `castSucc`). -/
def emb11to12 : Fin 11 ≃ {x : Fin 12 // x ≠ 11} where
  toFun i := ⟨i.castSucc, by simp [Fin.castSucc, Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by rcases x with ⟨v, hv⟩; simpa using hv)
  left_inv i := by simp
  right_inv x := by ext; simp

/-- Extending an element of `M₁₁` by fixing `11` lands inside `M₁₂`. -/
lemma extHom_mem_M12 (g : Perm (Fin 11)) (hg : g ∈ M11) :
    Perm.extendDomainHom emb11to12 g ∈ M12 := by
  have hmap : Subgroup.map (Perm.extendDomainHom emb11to12) M11 ≤ M12 := by
    rw [show M11 = Subgroup.closure {m11a, m11b} from rfl, MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [(by decide : Perm.extendDomainHom emb11to12 m11a = m12a)]; exact m12a_mem
    · rw [(by decide : Perm.extendDomainHom emb11to12 m11b = m12b)]; exact EnumM12Clean.m12b_mem
  exact hmap ⟨g, hg, rfl⟩

/-- Extending an element of `Perm (Fin 11)` by fixing `11` indeed fixes `11`. -/
lemma extHom_fix11 (g : Perm (Fin 11)) : (Perm.extendDomainHom emb11to12 g) 11 = 11 := by
  apply Perm.extendDomain_apply_not_subtype; simp

/-- The embedding `M₁₁ ↪ stabilizer (↥M₁₂) 11` (extend by fixing `11`). -/
noncomputable def psiM11toM12 : ↥M11 →* ↥(stabilizer (↥M12) (11 : Fin 12)) where
  toFun g := ⟨⟨Perm.extendDomainHom emb11to12 g.1, extHom_mem_M12 g.1 g.2⟩, by
    rw [mem_stabilizer_iff]
    simpa [Submonoid.smul_def, Equiv.Perm.smul_def] using extHom_fix11 g.1⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; simp

/-- The identification of `Fin 11` with the point set of `SubMulAction.ofStabilizer` at `11`. -/
noncomputable def eStabM12 :
    Fin 11 ≃ ↥(SubMulAction.ofStabilizer (↥M12) (11 : Fin 12)) where
  toFun i := ⟨i.castSucc, by rw [SubMulAction.mem_ofStabilizer_iff]; simp [Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by
    have h := (SubMulAction.mem_ofStabilizer_iff (↥M12) (11 : Fin 12)).mp x.2
    simpa [Fin.ext_iff] using h)
  left_inv i := by simp
  right_inv x := by ext; simp

lemma eStabM12_val (j : Fin 11) : (eStabM12 j : Fin 12) = j.castSucc := rfl

/-- `eStabM12` is equivariant for the embedding `psiM11toM12`. -/
lemma eStabM12_equivariant (g : ↥M11) (j : Fin 11) :
    (psiM11toM12 g) • (eStabM12 j) = eStabM12 (g • j) := by
  apply Subtype.ext
  rw [SubMulAction.val_smul]
  show (Perm.extendDomainHom emb11to12 g.1) ((eStabM12 j : Fin 12)) = (eStabM12 (g • j) : Fin 12)
  rw [eStabM12_val, eStabM12_val, show (g • j : Fin 11) = g.1 j from rfl]
  exact Perm.extendDomain_apply_image g.1 emb11to12 j

/-- The induced equivariant map on `4`-point embeddings; postcomposition with `eStabM12`. -/
noncomputable def FembM12 : (Fin 4 ↪ Fin 11) →ₑ[psiM11toM12]
    (Fin 4 ↪ ↥(SubMulAction.ofStabilizer (↥M12) (11 : Fin 12))) where
  toFun x := x.trans eStabM12.toEmbedding
  map_smul' g x := by
    apply Function.Embedding.ext; intro i
    simp only [Embedding.smul_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    exact (eStabM12_equivariant g (x i)).symm

lemma FembM12_surj : Function.Surjective FembM12 := by
  intro y
  refine ⟨y.trans eStabM12.symm.toEmbedding, ?_⟩
  apply Function.Embedding.ext; intro i
  show eStabM12 (eStabM12.symm (y i)) = y i
  simp

/-- **`M₁₂` acts 5-transitively on the 12 points.**

Native-`decide`-free proof via the Wielandt stabiliser recursion: the point stabiliser of
`11` acts `4`-transitively (it contains the `4`-transitive copy of `M₁₁`), so `M₁₂` is
`5`-transitive.  See the module docstring. -/
theorem M12_isMultiplyPretransitive_five :
    MulAction.IsMultiplyPretransitive M12 (Fin 12) 5 := by
  haveI := M12_isPretransitive
  have h4 : IsMultiplyPretransitive (↥M11) (Fin 11) 4 := M11_isMultiplyPretransitive_four
  have hstab : IsMultiplyPretransitive (stabilizer (↥M12) (11 : Fin 12))
      (SubMulAction.ofStabilizer (↥M12) (11 : Fin 12)) 4 := by
    unfold MulAction.IsMultiplyPretransitive at h4 ⊢
    exact h4.of_surjective_map (f := FembM12) FembM12_surj
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := ↥M12) (a := (11 : Fin 12)) (n := 4)).mpr hstab

/-- `M₁₂` is nontrivial (sanity check). -/
theorem M12_neBot : M12 ≠ ⊥ := by
  intro h
  have : m12a ∈ (⊥ : Subgroup (Perm (Fin 12))) := h ▸ m12a_mem
  rw [Subgroup.mem_bot] at this
  exact m12a_ne_one this

end Mathieu
