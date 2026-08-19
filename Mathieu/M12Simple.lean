import Mathlib
import Mathieu.Primitivity
import Mathieu.BasicM12
import Mathieu.BasicM11
import Mathieu.M11Simple
import Mathieu.InductiveSimple
import Mathieu.Subgroups

/-!
# Simplicity of `M₁₂`

`M₁₂` is a simple group.

## Route (inductive criterion on the natural action)

We use the classical *inductive* simplicity criterion for primitive groups, packaged as
`isSimpleGroup_of_isPreprimitive_of_simpleStabilizer` in `InductiveSimple.lean` (the same route
used for `M₂₃` and `M₂₄`):

* `M₁₂` acts **faithfully and primitively** on its `12` points (`M12_isPreprimitive`);
* the point stabiliser of `11` is (isomorphic to) `M₁₁`, which is **simple**
  (`M11_isSimpleGroup`).  We identify the stabiliser with `M₁₁` via the embedding
  `psiM11toM12` (`M₁₁ ↪ stabilizer (↥M₁₂) 11`), which is injective and — by the order count
  `|stab| = |M₁₂|/12 = 7920 = |M₁₁|` — surjective, hence an isomorphism.
* `M₁₂` has **no regular normal subgroup**: a regular normal subgroup `N` would have order `12`;
  since `M₁₂` is `2`-transitive, its point stabiliser acts transitively by conjugation on the
  nonidentity elements of `N`, so those all have the same (prime) order `p`, forcing `|N| = 12`
  to be a power of `p` — impossible, since `12` is not a prime power.

This replaces the earlier class-equation proof (which enumerated the `95040` conjugacy-class
data of `M₁₂` via `native_decide`); the order `|M₁₂| = 95040` (`M12_card`) is still used, but no
conjugacy-class enumeration.

## Historical note

An even earlier session tried to reduce `M12_isSimpleGroup` to an *Iwasawa structure for the
action of `M₁₂` on its `12` points*.  **No such term exists** (the natural action is primitive,
so the point stabiliser `M₁₁` is maximal and simple, leaving no nontrivial abelian normal
subgroup to serve as the Iwasawa data).  The inductive criterion used here does not need
Iwasawa data.
-/

namespace Mathieu

open MulAction Subgroup

/-- From `2`-transitivity, any ordered pair of distinct points can be mapped to any other
ordered pair of distinct points. -/
theorem two_transitive_exists {G α : Type*} [Group G] [MulAction G α]
    (h : MulAction.IsMultiplyPretransitive G α 2)
    {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) : ∃ g : G, g • a = c ∧ g • b = d := by
  have hp : IsPretransitive G (Fin 2 ↪ α) := h
  let p : Fin 2 ↪ α := ⟨![a, b], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  let q : Fin 2 ↪ α := ⟨![c, d], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨g, hg⟩ := hp.exists_smul_eq p q
  refine ⟨g, ?_, ?_⟩
  · have := congrArg (fun (e : Fin 2 ↪ α) => e 0) hg
    simpa [p, q, Function.Embedding.smul_apply] using this
  · have := congrArg (fun (e : Fin 2 ↪ α) => e 1) hg
    simpa [p, q, Function.Embedding.smul_apply] using this

/-- **No regular normal subgroup when the point count is not a prime power.**

If a finite group `G` acts `2`-transitively on a finite set `α` (with at least two points)
whose cardinality is *not* a prime power, then `G` has no regular normal subgroup.

Proof: a regular normal subgroup `N` has `|N| = |α|` (`card_eq_of_regular`).  Because the
action is `2`-transitive, the point stabiliser `Gₐ` is transitive on `α \ {a}`, and via the
regular bijection `n ↦ n • a` this makes the conjugation action of `Gₐ` on `N \ {1}`
transitive; hence all nonidentity elements of `N` are conjugate, so have a common order, which
must be a prime `p`.  Then every nonidentity element of `N` has order `p`, so `N` is a
`p`-group and `|N| = |α|` is a power of `p`, contradicting the hypothesis. -/
theorem no_regular_normal_of_not_isPrimePow
    {G : Type*} [Group G] [Finite G] {α : Type*} [MulAction G α] [Finite α] [Nontrivial α]
    (a : α) (h2 : MulAction.IsMultiplyPretransitive G α 2)
    (hnpp : ¬ IsPrimePow (Nat.card α))
    (N : Subgroup G) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) a = Set.univ)
    (hreg : ∀ n : ↥N, n • a = a → n = 1) : False := by
  haveI : N.Normal := hN
  have hcard : Nat.card ↥N = Nat.card α := card_eq_of_regular a N htrans hreg
  have hinj : Function.Injective (fun n : ↥N => (n : G) • a) := by
    intro n m hnm
    have h1 : (m⁻¹ * n : ↥N) = 1 := by
      apply hreg
      show ((m⁻¹ * n : ↥N) : G) • a = a
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, mul_smul]
      simp only at hnm
      rw [hnm]; simp
    have := congrArg (fun z : ↥N => m * z) h1
    simpa [mul_assoc] using this
  have hcoe : ∀ n : ↥N, orderOf n = orderOf (n : G) :=
    fun n => (orderOf_injective N.subtype N.subtype_injective n).symm
  haveI : Nontrivial ↥N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial α›
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥N)
  have hxa : (x : G) • a ≠ a := fun hcon => hx (hreg x hcon)
  have key : ∀ y : ↥N, y ≠ 1 → orderOf y = orderOf x := by
    intro y hy
    have hya : (y : G) • a ≠ a := fun hcon => hy (hreg y hcon)
    obtain ⟨g, hg1, hg2⟩ := two_transitive_exists h2 hxa hya
    have hgxg : g * (x : G) * g⁻¹ ∈ N := hN.conj_mem (x : G) x.2 g
    have hval : (⟨g * (x : G) * g⁻¹, hgxg⟩ : ↥N) = y := by
      apply hinj
      show (g * (x : G) * g⁻¹) • a = (y : G) • a
      rw [mul_smul, mul_smul]
      have hgia : g⁻¹ • a = a := by rw [inv_smul_eq_iff, hg2]
      rw [hgia, hg1]
    have hord : orderOf (g * (x : G) * g⁻¹) = orderOf (x : G) := by
      have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x : G)
      simpa [MulAut.conj_apply] using h
    rw [hcoe y, hcoe x, ← hval]
    calc orderOf ((⟨g * (x:G) * g⁻¹, hgxg⟩ : ↥N) : G) = orderOf (g * (x:G) * g⁻¹) := rfl
      _ = orderOf (x : G) := hord
  have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hxo : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hxfin).ne'
  have hxo1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hpprime : (orderOf x).Prime := by
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hxo1
    have hqpos : q ≠ 0 := hq.ne_zero
    have hdvd : (orderOf x / q) ∣ orderOf x := Nat.div_dvd_of_dvd hqdvd
    have hdivne : orderOf x / q ≠ 0 := by
      intro h0; rw [Nat.div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact hqpos h0
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hxo) hqdvd) (by omega)
    have hz_ord : orderOf (x ^ (orderOf x / q)) = q := by
      rw [orderOf_pow_of_dvd hdivne hdvd, Nat.div_div_self hqdvd hxo]
    have hzne : x ^ (orderOf x / q) ≠ 1 := by
      intro h; rw [← orderOf_eq_one_iff] at h; rw [hz_ord] at h; exact hq.ne_one h
    have hzk := key (x ^ (orderOf x / q)) hzne
    rw [hz_ord] at hzk
    rw [← hzk]; exact hq
  haveI : Fact (orderOf x).Prime := ⟨hpprime⟩
  have hpg : IsPGroup (orderOf x) ↥N := by
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · refine ⟨1, ?_⟩
      have : orderOf n = orderOf x := key n hn
      rw [pow_one, ← this]
      exact pow_orderOf_eq_one n
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpg
  rw [hcard] at hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · rw [h0, pow_zero] at hk
      have : Nat.card α ≥ 2 := Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial α›
      omega
    · exact h1
  exact hnpp ⟨orderOf x, k, hpprime.prime, hk1, hk.symm⟩

/-- The point stabiliser of `11` inside `M₁₂` has order `7920` (`= |M₁₁|`), by orbit–stabiliser
(`M₁₂` is transitive on its `12` points and `|M₁₂| = 95040`). -/
theorem stab11_M12_card :
    Nat.card ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) = 7920 := by
  haveI : IsPretransitive (↥M12) (Fin 12) := M12_isPretransitive
  haveI : Fintype ↥M12 := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) := Fintype.ofFinite _
  haveI : Fintype ↑(MulAction.orbit (↥M12) (11 : Fin 12)) := Fintype.ofFinite _
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥M12) (11 : Fin 12)
  have horb : MulAction.orbit (↥M12) (11 : Fin 12) = Set.univ := orbit_eq_univ (↥M12) 11
  have hoc : Nat.card ↑(MulAction.orbit (↥M12) (11 : Fin 12)) = 12 := by
    rw [Nat.card_congr (by rw [horb] :
      ↑(MulAction.orbit (↥M12) (11 : Fin 12)) ≃ (Set.univ : Set (Fin 12)))]
    simp
  simp only [← Nat.card_eq_fintype_card] at key
  rw [hoc, M12_card] at key
  omega

/-- The embedding `psiM11toM12 : M₁₁ ↪ stabilizer (↥M₁₂) 11` is injective. -/
theorem psiM11toM12_injective : Function.Injective psiM11toM12 := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.Perm.extendDomainHom_injective (f := emb11to12)
  have : (psiM11toM12 g : Equiv.Perm (Fin 12)) = (psiM11toM12 h : Equiv.Perm (Fin 12)) := by
    rw [hgh]
  simpa [psiM11toM12] using this

/-- The point stabiliser of `11` inside `M₁₂` is isomorphic to `M₁₁`. -/
noncomputable def stab11_mulEquiv_M11 :
    ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) ≃* ↥M11 := by
  have hcard : Nat.card ↥M11 = Nat.card ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) := by
    rw [M11_card, stab11_M12_card]
  have hbij : Function.Bijective psiM11toM12 :=
    (Nat.bijective_iff_injective_and_card psiM11toM12).mpr ⟨psiM11toM12_injective, hcard⟩
  exact (MulEquiv.ofBijective psiM11toM12 hbij).symm

/-- The point stabiliser of `11` inside `M₁₂` is simple (being isomorphic to `M₁₁`). -/
theorem stab11_M12_isSimpleGroup :
    IsSimpleGroup ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) := by
  haveI := M11_isSimpleGroup
  exact stab11_mulEquiv_M11.isSimpleGroup

/-- `M₁₂` has no regular normal subgroup on its `12` points. -/
theorem M12_no_regular_normal (N : Subgroup ↥M12) (hN : N.Normal)
    (htrans : MulAction.orbit (↥N) (11 : Fin 12) = Set.univ)
    (hstabtriv : ∀ n : ↥N, n • (11 : Fin 12) = 11 → n = 1) : False := by
  haveI : MulAction.IsMultiplyPretransitive (↥M12) (Fin 12) 5 :=
    M12_isMultiplyPretransitive_five
  have h2 : MulAction.IsMultiplyPretransitive (↥M12) (Fin 12) 2 :=
    isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by simp)
  refine no_regular_normal_of_not_isPrimePow (11 : Fin 12) h2 ?_ N hN htrans hstabtriv
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; decide

/-- **`M₁₂` is a simple group.**  Proved via the inductive primitive-action criterion: the
natural action on `12` points is faithful and primitive, the point stabiliser `M₁₁` is simple,
and there is no regular normal subgroup. -/
theorem M12_isSimpleGroup : IsSimpleGroup M12 :=
  isSimpleGroup_of_isPreprimitive_of_simpleStabilizer (11 : Fin 12)
    stab11_M12_isSimpleGroup
    (fun N hN ht hs => M12_no_regular_normal N hN ht hs)

end Mathieu
