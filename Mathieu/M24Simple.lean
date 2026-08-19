import Mathlib
import Mathieu.DefM24
import Mathieu.DefM23
import Mathieu.BasicM23
import Mathieu.EnumM24Iso
import Mathieu.Subgroups
import Mathieu.Primitivity
import Mathieu.M23Simple
import Mathieu.InductiveSimple

/-!
# Simplicity of `M₂₄`

`M₂₄` is a simple group.

## Route (inductive criterion on the natural action)

As for `M₂₃`, the group `M₂₄` (order `244823040`) is far too large to enumerate.  We use the
inductive simplicity criterion for primitive groups
(`isSimpleGroup_of_isPreprimitive_of_simpleStabilizer`):

* `M₂₄` acts **faithfully and primitively** on its `24` points (`M24_isPreprimitive`);
* the point stabiliser of `23` is `M₂₃`, which is **simple** (`M23_isSimpleGroup`);
* `M₂₄` has **no regular normal subgroup**: such a subgroup `N` would have order `24`, and
  conjugation would embed the stabiliser `M₂₃` (order `10200960`) into `Aut(N)`.  In particular
  `Aut(N)` would contain an automorphism `σ` of order `23` (Cauchy, since `23 ∣ |M₂₃|`).  An
  order-`23` automorphism of a group of order `24 = 23 + 1` permutes the `23` nonidentity
  elements in a single orbit (`orderOf_eq_of_aut_prime_order`), so all of them have the same
  order — contradicting Cauchy, which provides elements of order `2` and of order `3`.
-/

namespace Mathieu

open MulAction Subgroup

/-- The point stabiliser of `23` inside `M₂₄` is isomorphic to `M₂₃`. -/
noncomputable def stab23_mulEquiv_M23 :
    ↥(MulAction.stabilizer (↥M24) (23 : Fin 24)) ≃* ↥M23 := by
  have hstab : MulAction.stabilizer (↥M24) (23 : Fin 24) = (ptStab M24 (23 : Fin 24)).subgroupOf M24 := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ptStab,
      Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact ⟨x.2, by simpa using h⟩
    · intro h
      simpa using h.2
  refine (MulEquiv.subgroupCongr hstab).trans ?_
  refine (Subgroup.subgroupOfEquivOfLe (inf_le_left)).trans ?_
  exact (Classical.choice M23_iso_ptStab_M24).symm

/-- The point stabiliser of `23` inside `M₂₄` is simple (being isomorphic to `M₂₃`). -/
theorem stab23_isSimpleGroup :
    IsSimpleGroup ↥(MulAction.stabilizer (↥M24) (23 : Fin 24)) := by
  haveI := M23_isSimpleGroup
  exact stab23_mulEquiv_M23.isSimpleGroup

/-- The point stabiliser of `23` inside `M₂₄` has order `10200960` (`= |M₂₃|`). -/
theorem stab23_card :
    Nat.card ↥(MulAction.stabilizer (↥M24) (23 : Fin 24)) = 10200960 := by
  rw [Nat.card_congr stab23_mulEquiv_M23.toEquiv, M23_card]

/-- `M₂₄` has no regular normal subgroup.  A normal subgroup `N` acting regularly on `Fin 24`
would have order `24`; conjugation embeds `M₂₃` (order `10200960`) into `Aut(N)`, producing an
automorphism of order `23` which would force all `23` nonidentity elements of `N` to share a
single order — impossible, as `N` (order `24`) has elements of order `2` and of order `3`. -/
theorem M24_no_regular_normal (N : Subgroup ↥M24) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) (23 : Fin 24) = Set.univ)
    (hstabtriv : ∀ n : ↥N, n • (23 : Fin 24) = 23 → n = 1) : False := by
  have hcardN : Nat.card ↥N = 24 := by
    have h := card_eq_of_regular (G := ↥M24) (23 : Fin 24) N htrans hstabtriv
    simpa using h
  -- conjugation embedding of the stabiliser into `Aut N`
  obtain ⟨f, hf⟩ :=
    stabilizer_injective_mulAut_of_regular (G := ↥M24) (23 : Fin 24) N htrans
  have hdvd : Nat.card ↥(MulAction.stabilizer (↥M24) (23 : Fin 24)) ∣ Nat.card (MulAut ↥N) :=
    card_dvd_of_injective f hf
  rw [stab23_card] at hdvd
  -- hence `23 ∣ |Aut N|`, giving an order-23 automorphism by Cauchy
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (MulAut ↥N) := Fintype.ofFinite _
  haveI : Fintype ↥N := Fintype.ofFinite _
  have h23 : (23 : ℕ) ∣ Fintype.card (MulAut ↥N) := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_trans (by norm_num) hdvd
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := MulAut ↥N) 23 h23
  -- Cauchy on `N`: elements of order `2` and `3`
  have h2 : (2 : ℕ) ∣ Fintype.card ↥N := by
    rw [← Nat.card_eq_fintype_card, hcardN]; norm_num
  have h3 : (3 : ℕ) ∣ Fintype.card ↥N := by
    rw [← Nat.card_eq_fintype_card, hcardN]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 2 h2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 3 h3
  have ha1 : a ≠ 1 := by rintro rfl; rw [orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by rintro rfl; rw [orderOf_one] at hb; norm_num at hb
  have hcard24 : Nat.card ↥N = 23 + 1 := by rw [hcardN]
  have heq := orderOf_eq_of_aut_prime_order σ hσ hcard24 ha1 hb1
  rw [ha, hb] at heq
  norm_num at heq

/-- **`M₂₄` is a simple group.**  Proved via the inductive primitive-action criterion: the
natural action on `24` points is faithful and primitive, the point stabiliser `M₂₃` is simple,
and there is no regular normal subgroup. -/
theorem M24_isSimpleGroup : IsSimpleGroup M24 :=
  isSimpleGroup_of_isPreprimitive_of_simpleStabilizer (23 : Fin 24)
    stab23_isSimpleGroup
    (fun N hN ht hs => M24_no_regular_normal N hN ht hs)

end Mathieu
