import Mathlib
import Mathieu.InductiveSimple

/-!
# A native_decide-free simplicity criterion via an index-`12` maximal subgroup

This file packages the classical "pen-and-paper" argument that a finite group `G` with a
**maximal, core-free, simple** subgroup `H` of **index `12`** (with `11 ∣ |H|`) is itself
simple.  It is the abstract engine behind the `native_decide`-free simplicity proof of `M₁₁`:
there `H ≅ PSL(2, 𝔽₁₁)` (order `660`, index `12`), simple by `PSL211S.PSL_isSimpleGroup`.

## Mathematical content

Let `G` act on the coset space `G ⧸ H` (`12` points).  Then:

* the action is **faithful** iff the normal core of `H` is trivial (`Subgroup.normalCore_eq_ker`);
* it is **primitive** iff `H` is a maximal subgroup, i.e. `IsCoatom H`
  (`MulAction.isCoatom_stabilizer_iff_preprimitive` + `MulAction.stabilizer_quotient`);
* the point stabiliser of the base coset is `H` itself, hence **simple**;
* there is **no regular normal subgroup**: a regular normal `N` would have order `12 = 11 + 1`;
  since `11 ∣ |H| = |stabiliser|` and the stabiliser embeds in `Aut N`
  (`stabilizer_injective_mulAut_of_regular`), `Aut N` would contain an order-`11` automorphism
  (Cauchy), forcing all `11` nonidentity elements of `N` to share a single order
  (`orderOf_eq_of_aut_prime_order`) — impossible, as a group of order `12` has elements of
  order `2` and `3`.

Feeding these into the inductive criterion
`isSimpleGroup_of_isPreprimitive_of_simpleStabilizer` yields `IsSimpleGroup G`.
-/

namespace Mathieu

open MulAction Subgroup

/-- **No regular normal subgroup for an index-`12` action with `11 ∣ |stabiliser|`.**

If `G` acts faithfully on a `12`-point set `α`, the stabiliser of a point has order divisible
by `11`, and `N ⊴ G` acts regularly on `α`, we derive a contradiction: `N` has order `12`, so
the (order-`11`-divisible) stabiliser embeds into `Aut N`, giving an order-`11` automorphism
whose single orbit on the `11` nonidentity elements forces them all to have equal order —
contradicting Cauchy (elements of order `2` and `3` exist). -/
theorem no_regular_normal_of_index_twelve
    {G : Type*} [Group G] [Finite G] {α : Type*} [MulAction G α] [Finite α]
    [FaithfulSMul G α] (a : α) (hcard : Nat.card α = 12)
    (h11 : (11 : ℕ) ∣ Nat.card ↥(MulAction.stabilizer G a))
    (N : Subgroup G) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) a = Set.univ)
    (hstabtriv : ∀ n : ↥N, n • a = a → n = 1) : False := by
  haveI := hN
  have hcardN : Nat.card ↥N = 12 := by
    have h := card_eq_of_regular (G := G) a N htrans hstabtriv
    rw [h, hcard]
  obtain ⟨f, hf⟩ := stabilizer_injective_mulAut_of_regular (G := G) a N htrans
  have hdvd : Nat.card ↥(MulAction.stabilizer G a) ∣ Nat.card (MulAut ↥N) :=
    card_dvd_of_injective f hf
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (MulAut ↥N) := Fintype.ofFinite _
  haveI : Fintype ↥N := Fintype.ofFinite _
  have h11aut : (11 : ℕ) ∣ Fintype.card (MulAut ↥N) := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_trans h11 hdvd
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := MulAut ↥N) 11 h11aut
  have h2 : (2 : ℕ) ∣ Fintype.card ↥N := by
    rw [← Nat.card_eq_fintype_card, hcardN]; norm_num
  have h3 : (3 : ℕ) ∣ Fintype.card ↥N := by
    rw [← Nat.card_eq_fintype_card, hcardN]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 2 h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 3 h3
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
  have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hy; norm_num at hy
  have hcard12 : Nat.card ↥N = 11 + 1 := by rw [hcardN]
  have heq := orderOf_eq_of_aut_prime_order σ hσ hcard12 hx1 hy1
  rw [hx, hy] at heq
  norm_num at heq

/-- **Index-`12` maximal core-free simple subgroup ⇒ simple group.**

If a finite group `G` has a subgroup `H` that is
* **simple** (`hsimple`),
* **maximal** (`hmax : IsCoatom H`),
* **core-free** (`hcore : H.normalCore = ⊥`),
* of **index `12`** (`hindex`), with `11 ∣ |H|` (`h11`),

then `G` is simple.  Proof: apply the inductive primitivity criterion to the coset action of
`G` on `G ⧸ H`. -/
theorem isSimpleGroup_of_coatom_index_twelve
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hsimple : IsSimpleGroup ↥H)
    (hmax : IsCoatom H)
    (hcore : H.normalCore = ⊥)
    (hindex : H.index = 12)
    (h11 : (11 : ℕ) ∣ Nat.card ↥H) :
    IsSimpleGroup G := by
  have hcardquot : Nat.card (G ⧸ H) = 12 := by
    rw [← Subgroup.index_eq_card]; exact hindex
  haveI hNontriv : Nontrivial (G ⧸ H) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardquot]; norm_num)
  haveI hfaithful : FaithfulSMul G (G ⧸ H) := by
    rw [faithfulSMul_iff]
    intro g hg
    have hker : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
      rw [MonoidHom.mem_ker]; ext a; simpa using hg a
    rw [← Subgroup.normalCore_eq_ker, hcore, Subgroup.mem_bot] at hker
    exact hker
  haveI hprim : IsPreprimitive G (G ⧸ H) := by
    have h := (MulAction.isCoatom_stabilizer_iff_preprimitive G (X := G ⧸ H) ((1 : G) : G ⧸ H))
    rw [MulAction.stabilizer_quotient] at h
    exact h.mp hmax
  haveI hstab : IsSimpleGroup ↥(MulAction.stabilizer G ((1 : G) : G ⧸ H)) :=
    (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient H)).isSimpleGroup
  refine isSimpleGroup_of_isPreprimitive_of_simpleStabilizer ((1 : G) : G ⧸ H) hstab ?_
  intro N hN htrans hstabtriv
  have h11stab : (11 : ℕ) ∣ Nat.card ↥(MulAction.stabilizer G ((1 : G) : G ⧸ H)) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient H)).toEquiv]
    exact h11
  exact no_regular_normal_of_index_twelve ((1 : G) : G ⧸ H) hcardquot h11stab N hN htrans hstabtriv

end Mathieu
