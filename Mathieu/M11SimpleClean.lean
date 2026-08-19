import Mathieu.CosetSimple
import Mathieu.PSL211Simple
import Mathieu.SL211Perfect
import Mathieu.PSL211
import Mathieu.EnumM11
import Mathieu.EnumL211

/-!
# `M₁₁` is simple — the `native_decide`-free route (reduction)

This file assembles the `native_decide`-free proof of `IsSimpleGroup M₁₁` from:

* the **abstract** index-`12` maximal-subgroup criterion `isSimpleGroup_of_coatom_index_twelve`
  (`CosetSimple.lean`, fully proved, clean axioms);
* the simplicity of `PSL(2, 𝔽₁₁)` (`PSL211S.PSL_isSimpleGroup`, `PSL211Simple.lean`, clean);
* the embedding `PSL(2, 𝔽₁₁) ↪ M₁₁` (`PSL211.embeds`).

Let `H = image of PSL(2,11)` inside `M₁₁` (index `12`, order `660`).  `M₁₁` is simple once we
know that `H` is:

| fact                          | status                                                   |
|-------------------------------|----------------------------------------------------------|
| `IsSimpleGroup ↥H`            | **done** (transport of `PSL_isSimpleGroup`)              |
| `11 ∣ Nat.card ↥H`            | **done** (order-`11` unipotent element, kernel `decide`) |
| `H.index = 12`                | **done** (`|M₁₁| = 7920` kernel-clean, `|H| = 660`)      |
| `IsCoatom H`  (maximal)       | **done** (via `M₁₁` perfect + core-free counting)        |
| `H.normalCore = ⊥` (core-free)| **done** (`H` not normal, via the order-`12` quotient)   |

All inputs are discharged with only the standard axioms (`propext, Classical.choice,
Quot.sound`); in particular `|M₁₁| = 7920` comes from `EnumM11.M11_card_clean` (Lean kernel,
not `native_decide`).  The final synthesis is `M11_isSimpleGroup_clean`, to which the headline
`M11Simple.M11_isSimpleGroup` is now pointed.
-/

namespace Mathieu

namespace M11Clean

open MulAction Subgroup Matrix
open scoped MatrixGroups

/-- A chosen injective homomorphism `PSL(2, 𝔽₁₁) →* M₁₁` (from `PSL211.embeds`). -/
noncomputable def f : PSL(2, ZMod 11) →* ↥M11 := PSL211.embedding

lemma f_inj : Function.Injective f := PSL211.embedding_injective

/-- The image `H ≅ PSL(2, 𝔽₁₁)` of the embedding, a subgroup of `M₁₁` of index `12`. -/
noncomputable def H : Subgroup ↥M11 := f.range

/-- `H ≅ PSL(2, 𝔽₁₁)`. -/
noncomputable def H_mulEquiv_PSL : ↥H ≃* PSL(2, ZMod 11) :=
  (MonoidHom.ofInjective f_inj).symm

/-- **`H` is simple** (isomorphic to `PSL(2, 𝔽₁₁)`, which is simple). -/
theorem H_isSimpleGroup : IsSimpleGroup ↥H := by
  haveI := PSL211S.PSL_isSimpleGroup
  exact H_mulEquiv_PSL.isSimpleGroup

/-- `S = !![1,1;0,1]` as an element of `SL(2, 𝔽₁₁)`; an order-`11` unipotent. -/
noncomputable def Smat : SL(2, ZMod 11) := ⟨!![1,1;0,1], by decide⟩

/-- **`11 ∣ |PSL(2, 𝔽₁₁)|`**, witnessed by the order-`11` image of the unipotent `S`
(native_decide-free: `S ^ 11 = 1` by kernel `decide`, and `S ∉ center` since it is not scalar). -/
theorem psl_card_dvd_11 : (11 : ℕ) ∣ Nat.card (PSL(2, ZMod 11)) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set s : PSL(2, ZMod 11) := QuotientGroup.mk' _ Smat with hs
  have hpow : Smat ^ 11 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    decide
  have hspow : s ^ 11 = 1 := by rw [hs, ← map_pow, hpow, map_one]
  have hsne : s ≠ 1 := by
    simp only [hs, QuotientGroup.mk'_apply, ne_eq, QuotientGroup.eq_one_iff]
    intro hmem
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem
    obtain ⟨r, _, hr⟩ := hmem
    have h01 := congrFun (congrFun hr 0) 1
    simp [Matrix.scalar_apply, Matrix.diagonal, Smat] at h01
  have horder : orderOf s = 11 := orderOf_eq_prime hspow hsne
  have hdvd : orderOf s ∣ Nat.card (PSL(2, ZMod 11)) := orderOf_dvd_natCard s
  rwa [horder] at hdvd

/-- **`11 ∣ |H|`** (transported from `PSL(2, 𝔽₁₁)`). -/
theorem H_card_dvd_11 : (11 : ℕ) ∣ Nat.card ↥H := by
  rw [Nat.card_congr H_mulEquiv_PSL.toEquiv]
  exact psl_card_dvd_11

/-- **The centre of `SL(2, 𝔽₁₁)` has order `2`** (`{±I}`, and `-I ≠ I` since `2 ≠ 0` in `𝔽₁₁`). -/
lemma center_card : Nat.card ↥(Subgroup.center (SL(2, ZMod 11))) = 2 := by
  have hne : (1 : SL(2, ZMod 11)) ≠ -1 := by decide
  have e : ↥(Subgroup.center (SL(2, ZMod 11))) ≃ ↥({1, -1} : Set (SL(2, ZMod 11))) :=
    Equiv.subtypeEquivRight (fun g => by
      rw [PSL211.center_eq_pm_one g]; simp [Set.mem_insert_iff, Set.mem_singleton_iff])
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **`|SL(2, 𝔽₁₁)| = 1320`.** -/
lemma slCardN : Nat.card (SL(2, ZMod 11)) = 1320 := by
  rw [Nat.card_eq_fintype_card]; exact EnumL211.slCard

/-- **`|PSL(2, 𝔽₁₁)| = 660`** = `|SL| / |centre| = 1320 / 2`. -/
lemma psl_card : Nat.card (PSL(2, ZMod 11)) = 660 := by
  have h := Subgroup.index_mul_card (Subgroup.center (SL(2, ZMod 11)))
  rw [center_card, slCardN] at h
  have hpsl : Nat.card (PSL(2, ZMod 11)) = (Subgroup.center (SL(2, ZMod 11))).index := by
    rw [Subgroup.index]
  rw [hpsl]; omega

/-- **`|H| = 660`** (transported from `PSL(2, 𝔽₁₁)`). -/
lemma H_card : Nat.card ↥H = 660 := by
  rw [Nat.card_congr H_mulEquiv_PSL.toEquiv]; exact psl_card

/-- **`[M₁₁ : H] = 12`.**  From `|M₁₁| = 7920` (`EnumM11.M11_card_clean`) and `|H| = 660`. -/
theorem H_index : H.index = 12 := by
  have h := Subgroup.index_mul_card H
  rw [H_card, EnumM11.M11_card_clean] at h
  omega

/-- `↥M₁₁` is generated (as an abstract group) by the images of the two permutation
generators `m11a, m11b`. -/
lemma top_gen : (⊤ : Subgroup ↥M11)
    = Subgroup.closure {(⟨m11a, m11a_mem⟩ : ↥M11), ⟨m11b, m11b_mem⟩} := by
  apply Subgroup.map_injective (Subgroup.subtype_injective M11)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (M11.subtype '' {(⟨m11a, m11a_mem⟩ : ↥M11), ⟨m11b, m11b_mem⟩}) = {m11a, m11b} := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, (rfl|rfl), rfl⟩; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl|rfl); exacts [⟨_, Or.inl rfl, rfl⟩, ⟨_, Or.inr rfl, rfl⟩]
  rw [this]; rfl

set_option maxRecDepth 10000 in
/-- `m11a`, as an element of `↥M₁₁`, is a product of two commutators (found by search), hence
lies in the commutator subgroup. -/
lemma m11a_mem_comm : (⟨m11a, m11a_mem⟩ : ↥M11) ∈ commutator ↥M11 := by
  have hbi : m11b⁻¹ ∈ M11 := inv_mem m11b_mem
  have h1 : m11a * m11b⁻¹ * m11a ∈ M11 := mul_mem (mul_mem m11a_mem hbi) m11a_mem
  have h2 : m11b⁻¹ * m11a⁻¹ ∈ M11 := mul_mem hbi (inv_mem m11a_mem)
  set G2 : ↥M11 := ⟨m11b⁻¹, hbi⟩
  set H2 : ↥M11 := ⟨m11a * m11b⁻¹ * m11a, h1⟩
  set G1 : ↥M11 := ⟨m11b⁻¹, hbi⟩
  set H1 : ↥M11 := ⟨m11b⁻¹ * m11a⁻¹, h2⟩
  have key : (⟨m11a, m11a_mem⟩ : ↥M11) = ⁅G2, H2⁆ * ⁅G1, H1⁆ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, InvMemClass.coe_inv, G1, G2, H1, H2]
    decide
  rw [key]
  exact mul_mem (commutator_mem_commutator (mem_top _) (mem_top _))
    (commutator_mem_commutator (mem_top _) (mem_top _))

set_option maxRecDepth 10000 in
/-- `m11b`, as an element of `↥M₁₁`, is a product of two commutators (found by search), hence
lies in the commutator subgroup. -/
lemma m11b_mem_comm : (⟨m11b, m11b_mem⟩ : ↥M11) ∈ commutator ↥M11 := by
  have hai : m11a⁻¹ ∈ M11 := inv_mem m11a_mem
  have hbi : m11b⁻¹ ∈ M11 := inv_mem m11b_mem
  have hg2 : m11a⁻¹ * m11b⁻¹ * m11a ∈ M11 := mul_mem (mul_mem hai hbi) m11a_mem
  have hh2 : m11a⁻¹ * m11b * m11a⁻¹ ∈ M11 := mul_mem (mul_mem hai m11b_mem) hai
  have hh1 : m11b * m11a ∈ M11 := mul_mem m11b_mem m11a_mem
  set G2 : ↥M11 := ⟨m11a⁻¹ * m11b⁻¹ * m11a, hg2⟩
  set H2 : ↥M11 := ⟨m11a⁻¹ * m11b * m11a⁻¹, hh2⟩
  set G1 : ↥M11 := ⟨m11b⁻¹, hbi⟩
  set H1 : ↥M11 := ⟨m11b * m11a, hh1⟩
  have key : (⟨m11b, m11b_mem⟩ : ↥M11) = ⁅G2, H2⁆ * ⁅G1, H1⁆ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, InvMemClass.coe_inv, G1, G2, H1, H2]
    decide
  rw [key]
  exact mul_mem (commutator_mem_commutator (mem_top _) (mem_top _))
    (commutator_mem_commutator (mem_top _) (mem_top _))

/-- **`M₁₁` is perfect**: its commutator subgroup is everything.  Both generators are products
of commutators (`m11a_mem_comm`, `m11b_mem_comm`), and they generate `↥M₁₁` (`top_gen`). -/
theorem M11_perfect : commutator ↥M11 = ⊤ := by
  rw [eq_top_iff, top_gen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact m11a_mem_comm
  · exact m11b_mem_comm

/-- For any subgroup `M` strictly containing `H`, the order-`11` generator `m11a` lies in the
normal core of `M`.  Indeed `[M₁₁ : M] < 11` (as `|H| = 660 < |M|` and `|M| · [M₁₁:M] = 7920`),
so the permutation `m11a` induces on the `< 11` cosets `M₁₁ ⧸ M` has order dividing `11` and
dividing `[M₁₁:M]!`, hence is trivial. -/
lemma a_mem_normalCore (M : Subgroup ↥M11) (hHM : H < M) :
    (⟨m11a, m11a_mem⟩ : ↥M11) ∈ M.normalCore := by
  set a : ↥M11 := ⟨m11a, m11a_mem⟩ with ha
  have ha11 : a ^ 11 = 1 := by
    apply Subtype.ext; rw [SubmonoidClass.coe_pow]; exact m11a_pow_eq_one
  have hHle : H ≤ M := le_of_lt hHM
  have hdvd : Nat.card ↥H ∣ Nat.card ↥M := card_dvd_of_le hHle
  rw [H_card] at hdvd
  have hmul : M.index * Nat.card ↥M = Nat.card ↥M11 := Subgroup.index_mul_card M
  rw [EnumM11.M11_card_clean] at hmul
  obtain ⟨t, ht⟩ := hdvd
  have ht2 : 2 ≤ t := by
    have hpos : 0 < Nat.card ↥M := Nat.card_pos
    rw [ht] at hpos
    by_contra hlt2
    have ht1 : t = 1 := by omega
    have hcardeq : Nat.card ↥M ≤ Nat.card ↥H := by rw [ht, ht1, H_card]
    exact (ne_of_lt hHM) (Subgroup.eq_of_le_of_card_ge hHle hcardeq)
  rw [ht] at hmul
  have hidx : M.index * t = 12 := by
    have hrw : M.index * (660 * t) = 660 * (M.index * t) := by ring
    rw [hrw] at hmul; omega
  have hlt : M.index < 11 := by
    have h2 : M.index * 2 ≤ 12 := le_trans (Nat.mul_le_mul_left _ ht2) (le_of_eq hidx)
    omega
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
  set σ := MulAction.toPermHom ↥M11 (↥M11 ⧸ M) a with hσ
  have hd1 : orderOf σ ∣ 11 := (orderOf_map_dvd _ a).trans (orderOf_dvd_of_pow_eq_one ha11)
  have hd2 : orderOf σ ∣ (M.index).factorial := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, ← Subgroup.index_eq_card] at this
  have h11 : ¬ (11 ∣ (M.index).factorial) := by
    rw [Nat.Prime.dvd_factorial (by norm_num)]; omega
  have hone : orderOf σ = 1 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hd1 with h | h
    · exact h
    · rw [h] at hd2; exact absurd hd2 h11
  exact orderOf_eq_one_iff.mp hone

/-- **`H` is a maximal subgroup of `M₁₁`.**  `H ≠ ⊤` since `[M₁₁:H] = 12`.  If `H < M ⊊ ⊤`,
then `m11a ∈ M.normalCore =: N` (`a_mem_normalCore`), so in the quotient `↥M₁₁ ⧸ N` the image
of `m11a` is trivial; as `↥M₁₁ = ⟨m11a, m11b⟩`, the quotient is cyclic, hence abelian, so
`commutator ↥M₁₁ ≤ N`.  But `M₁₁` is perfect (`M11_perfect`), forcing `N = ⊤`, hence `M = ⊤`,
a contradiction. -/
theorem H_isCoatom : IsCoatom H := by
  set a : ↥M11 := ⟨m11a, m11a_mem⟩ with ha
  set b : ↥M11 := ⟨m11b, m11b_mem⟩ with hb
  constructor
  · intro htop
    have h12 : H.index = 12 := H_index
    rw [htop, Subgroup.index_top] at h12; norm_num at h12
  · intro M hHM
    by_contra hMtop
    have haN : a ∈ M.normalCore := a_mem_normalCore M hHM
    set N := M.normalCore with hN
    haveI : N.Normal := Subgroup.normalCore_normal M
    set π := QuotientGroup.mk' N with hπ
    have hpa : π a = 1 := (QuotientGroup.eq_one_iff a).mpr haN
    have hgen : (⊤ : Subgroup (↥M11 ⧸ N)) = Subgroup.zpowers (π b) := by
      have hsurj := QuotientGroup.mk'_surjective N
      have h1 : Subgroup.map π ⊤ = ⊤ := by
        rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj]
      rw [← h1, top_gen, MonoidHom.map_closure, Set.image_pair, hpa]
      have hcl : Subgroup.closure ({(1 : ↥M11 ⧸ N), π b}) = Subgroup.closure {π b} := by
        apply le_antisymm
        · rw [Subgroup.closure_le]; intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact one_mem _
          · exact Subgroup.subset_closure rfl
        · apply Subgroup.closure_mono; intro x hx
          simp only [Set.mem_singleton_iff] at hx; simp [hx]
      rw [hcl, ← Subgroup.zpowers_eq_closure]
    have habel : ∀ p q : ↥M11 ⧸ N, Commute p q := by
      intro p q
      have hp : p ∈ Subgroup.zpowers (π b) := by rw [← hgen]; exact Subgroup.mem_top p
      have hq : q ∈ Subgroup.zpowers (π b) := by rw [← hgen]; exact Subgroup.mem_top q
      obtain ⟨m, rfl⟩ := hp
      obtain ⟨n, rfl⟩ := hq
      exact (Commute.refl (π b)).zpow_zpow m n
    have hcle : commutator ↥M11 ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      have hcomm : π ⁅g, h⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]; exact habel _ _
      exact (QuotientGroup.eq_one_iff _).mp hcomm
    rw [M11_perfect] at hcle
    have hNtop : N = ⊤ := top_le_iff.mp hcle
    have hMle : (⊤ : Subgroup ↥M11) ≤ M := hNtop ▸ Subgroup.normalCore_le M
    exact hMtop (top_le_iff.mp hMle)

/-- **`H` is not normal in `M₁₁`.**  If it were, the quotient `↥M₁₁ ⧸ H` (order `12`) would be
generated by the images of `m11a` (order `11`, coprime to `12`, hence trivial in the quotient)
and `m11b` (order dividing `4`); so it would be cyclic of order dividing `4`, contradicting
`|↥M₁₁ ⧸ H| = 12`. -/
lemma H_not_normal : ¬ (H.Normal) := by
  intro hN
  haveI := hN
  have hcardQ : Nat.card (↥M11 ⧸ H) = 12 := by
    rw [← Subgroup.index_eq_card]; exact H_index
  set π := QuotientGroup.mk' H with hπ
  set a : ↥M11 := ⟨m11a, m11a_mem⟩ with ha
  set b : ↥M11 := ⟨m11b, m11b_mem⟩ with hb
  have ha11 : a ^ 11 = 1 := by
    apply Subtype.ext; rw [SubmonoidClass.coe_pow]; exact m11a_pow_eq_one
  have hb4 : b ^ 4 = 1 := by
    apply Subtype.ext; rw [SubmonoidClass.coe_pow]; exact m11b_pow_eq_one
  have hpa : π a = 1 := by
    have hd1 : orderOf (π a) ∣ 11 := (orderOf_map_dvd π a).trans (orderOf_dvd_of_pow_eq_one ha11)
    have hd2 : orderOf (π a) ∣ 12 := by
      have := orderOf_dvd_natCard (π a); rwa [hcardQ] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide) hd1 hd2)
  have hgen : (⊤ : Subgroup (↥M11 ⧸ H)) = Subgroup.zpowers (π b) := by
    have hsurj := QuotientGroup.mk'_surjective H
    have h1 : Subgroup.map π ⊤ = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj]
    rw [← h1, top_gen, MonoidHom.map_closure, Set.image_pair, hpa]
    have hcl : Subgroup.closure ({(1 : ↥M11 ⧸ H), π b}) = Subgroup.closure {π b} := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact one_mem _
        · exact Subgroup.subset_closure rfl
      · apply Subgroup.closure_mono; intro x hx
        simp only [Set.mem_singleton_iff] at hx; simp [hx]
    rw [hcl, ← Subgroup.zpowers_eq_closure]
  have hcard2 : Nat.card (↥M11 ⧸ H) = orderOf (π b) := by
    rw [← Nat.card_zpowers, ← hgen]
    exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
  rw [hcardQ] at hcard2
  have hob : orderOf (π b) ∣ 4 := (orderOf_map_dvd π b).trans (orderOf_dvd_of_pow_eq_one hb4)
  have := Nat.le_of_dvd (by norm_num) hob
  omega

/-- **`H` is core-free.**  Since `H` is simple, its normal core (normal in `M₁₁`, contained in
`H`) is `⊥` or `H`; it is `H` only if `H ⊴ M₁₁`, ruled out by `H_not_normal`. -/
theorem H_normalCore : H.normalCore = ⊥ := by
  haveI := H_isSimpleGroup
  set K := H.normalCore with hK
  have hKle : K ≤ H := Subgroup.normalCore_le H
  haveI hnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normalCore_normal H).subgroupOf H
  rcases hnorm.eq_bot_or_eq_top with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    have h2 : K ⊓ H = ⊥ := disjoint_iff.mp h
    rwa [inf_of_le_left hKle] at h2
  · rw [Subgroup.subgroupOf_eq_top] at h
    have hKH : K = H := le_antisymm hKle h
    exact absurd (hKH ▸ Subgroup.normalCore_normal H) H_not_normal


/-- **`M₁₁` is simple** — assembled from the clean index-`12` criterion, using the fully proved
concrete facts `H_isCoatom`, `H_normalCore`, `H_index`, `H_isSimpleGroup`, `H_card_dvd_11`
(and `PSL211.embeds`).  `native_decide`-free (standard axioms only). -/
theorem M11_isSimpleGroup_clean : IsSimpleGroup ↥M11 :=
  isSimpleGroup_of_coatom_index_twelve H H_isSimpleGroup H_isCoatom H_normalCore
    H_index H_card_dvd_11

end M11Clean

end Mathieu