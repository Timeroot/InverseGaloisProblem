import Mathieu.M21Simple
import Mathieu.TransM22
import Mathieu.InductiveSimple
import Mathieu.M12Simple
import Mathieu.BasicM22
import Mathieu.DefM22

/-!
# Simplicity of `M₂₂`

`M₂₂` is a simple group.

## Route (inductive criterion on the natural `22`-point action)

We use the classical *inductive* simplicity criterion for primitive groups
(`isSimpleGroup_of_isPreprimitive_of_simpleStabilizer`, the same route used for `M₁₂`, `M₂₃`,
`M₂₄`):

* `M₂₂` acts **faithfully and primitively** on its `22` points `Y22 = {x : Fin 23 // x ≠ 22}`
  (`M22_isPreprimitive_Y22`, from `3`-transitivity);
* the point stabiliser of `a21 = 21` is (isomorphic to) `M₂₁ ≅ PSL(3,4)`, which is **simple**
  (`M21_isSimpleGroup`).  We identify the stabiliser with `M₂₁` via the embedding
  `TransM22.psiM21toStab`, injective and — by the order count
  `|stab| = |M₂₂|/22 = 20160 = |M₂₁|` — surjective, hence an isomorphism;
* `M₂₂` has **no regular normal subgroup**: `M₂₂` is `2`-transitive and its point count `22` is
  not a prime power, so `no_regular_normal_of_not_isPrimePow` applies.

This replaces the earlier class-equation proof (which enumerated the `443520` conjugacy-class
data of `M₂₂` via `native_decide` in `EnumM22Classes.lean` / `EnumM22Simple.lean`).  The order
`|M₂₂| = 443520` (`M22_card`) is still used, but no conjugacy-class enumeration.
-/

namespace Mathieu

open MulAction Subgroup TransM22

/-- The `22`-point set `Y22` has `22` elements. -/
theorem card_Y22 : Nat.card Y22 = 22 := by
  rw [Nat.card_eq_fintype_card]; decide

instance : Finite Y22 := Subtype.finite

instance instNontrivialY22 : Nontrivial Y22 := by
  rw [← Finite.one_lt_card_iff_nontrivial, card_Y22]; norm_num

/-- `M₂₂` acts faithfully on its `22` points `Y22` (an element fixing every non-`22` point and
`22` itself is the identity). -/
instance instFaithfulY22 : FaithfulSMul M22 Y22 := by
  refine ⟨fun {m1 m2} h => ?_⟩
  apply Subtype.ext
  ext z : 1
  by_cases hz : z = 22
  · subst hz
    rw [M22_fixes_last m1.2, M22_fixes_last m2.2]
  · have := congrArg Subtype.val (h ⟨z, hz⟩)
    simpa [TransM22.smul_Y22_val] using this

/-- **`M₂₂` acts primitively on `Y22`** (from `3`-transitivity, hence `2`-transitivity). -/
instance M22_isPreprimitive_Y22 : IsPreprimitive M22 Y22 := by
  haveI : IsMultiplyPretransitive M22 Y22 3 := TransM22.M22_isMultiplyPretransitive_three
  have h2 : IsMultiplyPretransitive M22 Y22 2 :=
    isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by rw [card_Y22]; norm_num)
  exact isPreprimitive_of_is_two_pretransitive h2

/-- The point stabiliser of `a21` inside `M₂₂` has order `20160` (`= |M₂₁|`), by
orbit–stabiliser (`M₂₂` is transitive on `Y22` and `|M₂₂| = 443520`). -/
theorem stab_a21_card : Nat.card ↥(stabilizer (↥M22) a21) = 20160 := by
  haveI : IsPretransitive (↥M22) Y22 := TransM22.M22_isPretransitive
  haveI : Fintype ↥M22 := Fintype.ofFinite _
  haveI : Fintype ↥(stabilizer (↥M22) a21) := Fintype.ofFinite _
  haveI : Fintype ↑(MulAction.orbit (↥M22) a21) := Fintype.ofFinite _
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥M22) a21
  have horb : MulAction.orbit (↥M22) a21 = Set.univ := MulAction.orbit_eq_univ (↥M22) a21
  have hoc : Nat.card ↑(MulAction.orbit (↥M22) a21) = 22 := by
    rw [horb, Nat.card_congr (Equiv.Set.univ Y22)]
    exact card_Y22
  simp only [← Nat.card_eq_fintype_card] at key
  rw [hoc, M22_card] at key
  omega

/-- The embedding `psiM21toStab : M₂₁ ↪ stabilizer (↥M₂₂) a21` is injective. -/
theorem psiM21toStab_injective : Function.Injective psiM21toStab := by
  intro g h hgh
  apply Subtype.ext
  have := congrArg
    (fun z : ↥(stabilizer (↥M22) a21) => ((z.val : ↥M22) : Equiv.Perm (Fin 23))) hgh
  simpa [psiM21toStab] using this

/-- The point stabiliser of `a21` inside `M₂₂` is isomorphic to `M₂₁`. -/
noncomputable def stab_a21_mulEquiv_M21 :
    ↥(stabilizer (↥M22) a21) ≃* ↥M21 := by
  have hcard : Nat.card ↥M21 = Nat.card ↥(stabilizer (↥M22) a21) := by
    rw [M21_card, stab_a21_card]
  have hbij : Function.Bijective psiM21toStab :=
    (Nat.bijective_iff_injective_and_card psiM21toStab).mpr ⟨psiM21toStab_injective, hcard⟩
  exact (MulEquiv.ofBijective psiM21toStab hbij).symm

/-- The point stabiliser of `a21` inside `M₂₂` is simple (being isomorphic to `M₂₁`). -/
theorem stab_a21_isSimpleGroup :
    IsSimpleGroup ↥(stabilizer (↥M22) a21) := by
  haveI := M21_isSimpleGroup
  exact stab_a21_mulEquiv_M21.isSimpleGroup

/-- `M₂₂` has no regular normal subgroup on its `22` points. -/
theorem M22_no_regular_normal (N : Subgroup ↥M22) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) a21 = Set.univ)
    (hstabtriv : ∀ n : ↥N, n • a21 = a21 → n = 1) : False := by
  haveI : IsMultiplyPretransitive M22 Y22 3 := TransM22.M22_isMultiplyPretransitive_three
  have h2 : IsMultiplyPretransitive M22 Y22 2 :=
    isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by rw [card_Y22]; norm_num)
  refine no_regular_normal_of_not_isPrimePow a21 h2 ?_ N hN htrans hstabtriv
  rw [card_Y22]; decide

/-- **`M₂₂` is a simple group.**  Proved via the inductive primitive-action criterion: the
natural action on its `22` points is faithful and primitive, the point stabiliser
`M₂₁ ≅ PSL(3,4)` is simple, and there is no regular normal subgroup. -/
theorem M22_isSimpleGroup : IsSimpleGroup M22 :=
  isSimpleGroup_of_isPreprimitive_of_simpleStabilizer a21
    stab_a21_isSimpleGroup
    (fun N hN ht hs => M22_no_regular_normal N hN ht hs)

end Mathieu
