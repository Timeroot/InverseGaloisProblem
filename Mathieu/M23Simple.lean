import Mathlib
import Mathieu.DefM23
import Mathieu.DefM22
import Mathieu.BasicM22
import Mathieu.Subgroups
import Mathieu.Primitivity
import Mathieu.M22Simple
import Mathieu.InductiveSimple

/-!
# Simplicity of `M₂₃`

`M₂₃` is a simple group.

## Route (inductive criterion on the natural action)

Unlike `M₁₁, M₁₂, M₂₂`, the group `M₂₃` (order `10200960`) is far too large to enumerate its
conjugacy classes.  We instead use the classical *inductive* simplicity criterion for primitive
groups, packaged as `isSimpleGroup_of_isPreprimitive_of_simpleStabilizer` in `InductiveSimple.lean`:

* `M₂₃` acts **faithfully and primitively** on its `23` points (`M23_isPreprimitive`);
* the point stabiliser of `22` is `M₂₂`, which is **simple** (`M22_isSimpleGroup`);
* `M₂₃` has **no regular normal subgroup**: such a subgroup `N` would have order `23` (the
  number of points), hence be cyclic; conjugation would embed the stabiliser `M₂₂` (order
  `443520`) into `Aut(C₂₃)` (order `22`), which is absurd.

The last point uses `stabilizer_injective_mulAut_of_regular` and `card_eq_of_regular`.
-/

namespace Mathieu

open MulAction Subgroup

/-- The point stabiliser of `22` inside `M₂₃` is isomorphic to `M₂₂`. -/
noncomputable def stab22_mulEquiv_M22 :
    ↥(MulAction.stabilizer (↥M23) (22 : Fin 23)) ≃* ↥M22 := by
  have hstab : MulAction.stabilizer (↥M23) (22 : Fin 23) = M22.subgroupOf M23 := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, M22,
      Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact ⟨x.2, by simpa using h⟩
    · intro h
      simpa using h.2
  exact (MulEquiv.subgroupCongr hstab).trans (Subgroup.subgroupOfEquivOfLe M22_le_M23)

/-- The point stabiliser of `22` inside `M₂₃` is simple (being isomorphic to `M₂₂`). -/
theorem stab22_isSimpleGroup :
    IsSimpleGroup ↥(MulAction.stabilizer (↥M23) (22 : Fin 23)) := by
  haveI := M22_isSimpleGroup
  exact stab22_mulEquiv_M22.isSimpleGroup

/-- The point stabiliser of `22` inside `M₂₃` has order `443520` (`= |M₂₂|`). -/
theorem stab22_card :
    Nat.card ↥(MulAction.stabilizer (↥M23) (22 : Fin 23)) = 443520 := by
  rw [Nat.card_congr stab22_mulEquiv_M22.toEquiv, M22_card]

/-- `M₂₃` has no regular normal subgroup: a normal subgroup `N` acting regularly on `Fin 23`
would force `|M₂₂| = 443520` to divide `|Aut(C₂₃)| = 22`, which is impossible. -/
theorem M23_no_regular_normal (N : Subgroup ↥M23) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) (22 : Fin 23) = Set.univ)
    (hstabtriv : ∀ n : ↥N, n • (22 : Fin 23) = 22 → n = 1) : False := by
  have hcardN : Nat.card ↥N = 23 := by
    have h := card_eq_of_regular (G := ↥M23) (22 : Fin 23) N htrans hstabtriv
    simpa using h
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  haveI : IsCyclic ↥N := isCyclic_of_prime_card hcardN
  have hAut : Nat.card (MulAut ↥N) = 22 := by
    rw [IsCyclic.card_mulAut, hcardN]; decide
  obtain ⟨f, hf⟩ :=
    stabilizer_injective_mulAut_of_regular (G := ↥M23) (22 : Fin 23) N htrans
  have hdvd : Nat.card ↥(MulAction.stabilizer (↥M23) (22 : Fin 23)) ∣ Nat.card (MulAut ↥N) :=
    card_dvd_of_injective f hf
  rw [stab22_card, hAut] at hdvd
  norm_num at hdvd

/-- **`M₂₃` is a simple group.**  Proved via the inductive primitive-action criterion: the
natural action on `23` points is faithful and primitive, the point stabiliser `M₂₂` is simple,
and there is no regular normal subgroup. -/
theorem M23_isSimpleGroup : IsSimpleGroup M23 :=
  isSimpleGroup_of_isPreprimitive_of_simpleStabilizer (22 : Fin 23)
    stab22_isSimpleGroup
    (fun N hN ht hs => M23_no_regular_normal N hN ht hs)

end Mathieu
