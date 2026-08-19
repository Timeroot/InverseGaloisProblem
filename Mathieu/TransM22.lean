import Mathieu.TransM21
import Mathieu.EnumM22Gen
import Mathieu.M22Cycles

/-!
# `M₂₂` is `3`-transitive on its `22` points

The next step of the Wielandt transitivity tower for `M₂₂ ≤ M₂₃ ≤ M₂₄`, built on the
`native_decide`-free base `TransM21.M21_two_transitive` (`M₂₁` is `2`-transitive on its `21`
points `Y`).

`M₂₂ ≤ Perm (Fin 23)` fixes the point `22`, so it acts on the `22`-point set
`Y22 = {x : Fin 23 // x ≠ 22}`.  The point stabiliser of `21` inside `M₂₂` is exactly `M₂₁`
(by definition `M₂₁ = M₂₂ ⊓ stabilizer 21`), and it acts `2`-transitively on the remaining
`21` points `Y = {x // x ≠ 21 ∧ x ≠ 22}`.  By the Wielandt stabiliser recursion
(`SubMulAction.ofStabilizer.isMultiplyPretransitive`), `M₂₂` is therefore `3`-transitive on
`Y22`.

This proof uses **no** `native_decide` beyond what `M21_two_transitive` already rests on
(the `EnumM22` order via `M21_card`); in particular it does **not** use the
`EnumM23Trans` orbit enumeration.
-/

namespace Mathieu

open Equiv MulAction Function

namespace TransM22

set_option maxRecDepth 100000

open TransM21 (Y)
open EnumM22 (schB)

/-- The `22` moved points of `M₂₂` (everything except the fixed point `22`). -/
abbrev Y22 : Type := {x : Fin 23 // x ≠ 22}

/-- An element of `M₂₂` maps `Y22` to `Y22` (it fixes `22`, hence never sends a non-`22`
point to `22`). -/
theorem M22_mapsTo (m : M22) (x : Fin 23) (hx : x ≠ 22) :
    (m : Perm (Fin 23)) x ≠ 22 := by
  intro h
  apply hx
  have hfix : (m : Perm (Fin 23)) 22 = 22 := M22_fixes_last m.2
  exact (m : Perm (Fin 23)).injective (h.trans hfix.symm)

instance : SMul M22 Y22 := ⟨fun m y => ⟨(m : Perm (Fin 23)) y.1, M22_mapsTo m y.1 y.2⟩⟩

@[simp] theorem smul_Y22_val (m : M22) (y : Y22) :
    ((m • y).1 : Fin 23) = (m : Perm (Fin 23)) y.1 := rfl

instance : MulAction M22 Y22 where
  one_smul y := by apply Subtype.ext; simp
  mul_smul a b y := by
    apply Subtype.ext
    simp only [smul_Y22_val, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]

/-! ### `M₂₂` is transitive on `Y22` -/

/-- `schB 2 ∈ M₂₂` sends `21` to `7`. -/
theorem schB2_21 : schB 2 (21 : Fin 23) = 7 := by rw [schB2_eq]; decide

/-
**`M₂₂` acts transitively on its `22` points.**

`M₂₁ ≤ M₂₂` is transitive on the `21` points `Y` (from `M21_two_transitive`), so every
point `≠ 21, 22` lies in the orbit of the base point `⟨0⟩`.  The remaining point `21` is
reached because `schB 2 ∈ M₂₂` sends `21 ↦ 7 ∈ Y`.
-/
theorem M22_isPretransitive : MulAction.IsPretransitive M22 Y22 := by
  -- For any `y : Y22`, it suffices to find `g : M22` with `(g : Perm (Fin 23)) 21 = y.1`.
  have hbase : ∀ y : Y22, ∃ g : M22, (g : Perm (Fin 23)) 21 = y.1 := by
    intro y
    by_cases hy : y.1 = 21
    · use 1
      simp [hy]
    ·
      obtain ⟨g, hg⟩ : ∃ g : M21, (g : Perm (Fin 23)) 7 = y.1 := by
        have h_trans : ∀ x y : Y, ∃ g : M21, (g : Perm (Fin 23)) x = y := by
          have := @TransM21.M21_two_transitive;
          have := @isPretransitive_of_is_two_pretransitive ( M21 ) Y;
          exact fun x y => by obtain ⟨ g, hg ⟩ := this.exists_smul_eq x y; exact ⟨ g, by simpa [ Subtype.ext_iff ] using hg ⟩ ;
        convert h_trans ⟨ 7, by decide, by decide ⟩ ⟨ y.1, hy, y.2 ⟩ using 1;
      use ⟨g, M21_le_M22 g.2⟩ * ⟨schB 2, EnumM22.schB_mem_M22 2⟩;
      convert hg using 1;
  refine' ⟨ fun x y => _ ⟩;
  cases' hbase x with g hg ; cases' hbase y with h hh ; use h * g⁻¹ ; aesop

/-! ### Transport of `M₂₁`'s `2`-transitivity to the point stabiliser -/

/-- The base point `21 : Y22` whose stabiliser inside `M₂₂` is `M₂₁`. -/
def a21 : Y22 := ⟨21, by decide⟩

/-- The embedding `M₂₁ ↪ stabilizer (↥M₂₂) a21`.  An element of `M₂₁` lies in `M₂₂` and
fixes `21`, hence stabilises `a21`. -/
def psiM21toStab : ↥M21 →* ↥(stabilizer (↥M22) a21) where
  toFun g := ⟨⟨g.1, M21_le_M22 g.2⟩, by
    rw [mem_stabilizer_iff]
    apply Subtype.ext
    show (g.1 : Perm (Fin 23)) (21 : Fin 23) = 21
    have : g.1 ∈ MulAction.stabilizer (Perm (Fin 23)) (21 : Fin 23) := g.2.2
    simpa [Equiv.Perm.smul_def] using this⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; simp

/-- The identification of `Y` with the point set of `SubMulAction.ofStabilizer` at `a21`. -/
def eStab : Y ≃ ↥(SubMulAction.ofStabilizer (↥M22) a21) where
  toFun x := ⟨⟨x.1, x.2.2⟩, by
    rw [SubMulAction.mem_ofStabilizer_iff]
    intro h
    exact x.2.1 (congrArg Subtype.val h)⟩
  invFun y := ⟨y.1.1, ⟨by
    intro h
    apply (SubMulAction.mem_ofStabilizer_iff (↥M22) a21).mp y.2
    apply Subtype.ext; exact h, y.1.2⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; rfl

@[simp] theorem eStab_val (x : Y) : ((eStab x : Y22).1 : Fin 23) = x.1 := rfl

/-- `eStab` is equivariant for the embedding `psiM21toStab`. -/
theorem eStab_equivariant (g : ↥M21) (x : Y) :
    (psiM21toStab g) • (eStab x) = eStab (g • x) := by
  apply Subtype.ext
  rw [SubMulAction.val_smul]
  apply Subtype.ext
  show (g.1 : Perm (Fin 23)) x.1 = (g.1 : Perm (Fin 23)) x.1
  rfl

/-- The induced equivariant map on `2`-point embeddings. -/
def Femb : (Fin 2 ↪ Y) →ₑ[psiM21toStab]
    (Fin 2 ↪ ↥(SubMulAction.ofStabilizer (↥M22) a21)) where
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

/-- **`M₂₂` acts `3`-transitively on its `22` points `Y22`.**

Native-`decide`-free (modulo the `EnumM22` order that `M21_card` rests on): via the Wielandt
stabiliser recursion, the stabiliser of `21` (namely `M₂₁`) acts `2`-transitively on the
remaining `21` points, so `M₂₂` is `3`-transitive. -/
theorem M22_isMultiplyPretransitive_three :
    MulAction.IsMultiplyPretransitive M22 Y22 3 := by
  haveI := M22_isPretransitive
  have h2 : IsMultiplyPretransitive (↥M21) Y 2 := TransM21.M21_two_transitive
  have hstab : IsMultiplyPretransitive (stabilizer (↥M22) a21)
      (SubMulAction.ofStabilizer (↥M22) a21) 2 := by
    unfold MulAction.IsMultiplyPretransitive at h2 ⊢
    exact h2.of_surjective_map (f := Femb) Femb_surj
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := ↥M22) (a := a21) (n := 2)).mpr hstab

end TransM22

end Mathieu