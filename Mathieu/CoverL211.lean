import Mathieu.ActL211

/-!
# Transversal certificates for the exceptional `SL(2,𝔽₁₁)`-action

The transversal property of `reps` (see `ActL211.lean`): the `11` cosets `reps i · K` are
distinct (`distinctb`), and every element lies in some coset (`cover`).  From these, `cIdx`
genuinely picks the coset of its argument (`cIdx_mem`).

**`native_decide`-free route.**  `distinctb` is a kernel `decide` (only `11 × 11` pairs).  The
covering property `cover` is *not* checked by brute force over all of `SL(2,𝔽₁₁)` (which the
kernel cannot reduce); instead it is a **counting argument**: the map `i ↦ [reps i]` into the
coset space `SL ⧸ K` is injective (that is `distinctb`) between two sets of the same
cardinality `11` (`[SL : K] = |SL|/|K| = 1320/120 = 11`), hence surjective, i.e. every coset is
hit — which is exactly `cover`.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL211

set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-- The order-`120` subgroup `K = ⟨A, B⟩` of `SL(2, 𝔽₁₁)`. -/
def Ksub : Subgroup SL(2, ZMod 11) := Subgroup.closure {EnumL211.Amat, EnumL211.Bmat}

/-- The `11` cosets `reps i · K` are distinct. -/
lemma distinctb (i j : Fin 11) (h : inKb ((reps i)⁻¹ * reps j) = true) : i = j := by
  revert i j h; decide

/-- `inKb` is exactly the membership test for `K = ⟨A, B⟩`. -/
lemma inKb_iff_memK (g : SL(2, ZMod 11)) : inKb g = true ↔ g ∈ Ksub := by
  rw [inKb, decide_eq_true_eq]
  exact (EnumL211.memK_iff g).symm

/-- The image of `K` under the code map `φ` is exactly the enumerated set `KK`. -/
lemma image_eqK :
    EnumL211.φ '' (Ksub : Set SL(2, ZMod 11)) = (EnumL211.KK : Set ℕ) := by
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact EnumL211.forwardK p hp
  · intro hc
    obtain ⟨p, hp, rfl⟩ := EnumL211.backwardK c hc
    exact ⟨p, hp, rfl⟩

/-- **`|K| = 120`.** -/
lemma card_Ksub : Nat.card Ksub = 120 := by
  have h1 : Nat.card Ksub = (Ksub : Set SL(2, ZMod 11)).ncard := Nat.card_coe_set_eq _
  rw [h1, ← Set.ncard_image_of_injective _ EnumL211.φ_injective, image_eqK,
    Set.ncard_coe_finset, EnumL211.KK_card]

/-- **`[SL(2,𝔽₁₁) : K] = 11`.** -/
lemma card_quot : Nat.card (SL(2, ZMod 11) ⧸ Ksub) = 11 := by
  have hSL : Nat.card SL(2, ZMod 11) = 1320 := by
    rw [Nat.card_eq_fintype_card]; exact EnumL211.slCard
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup Ksub
  rw [hSL, card_Ksub] at hmul
  omega

/-- **Every element lies in some coset `reps i · K`.**  Proved by the counting/surjectivity
argument (no brute force over `SL`). -/
lemma cover_exists (g : SL(2, ZMod 11)) : ∃ i : Fin 11, inKb ((reps i)⁻¹ * g) = true := by
  -- the map `i ↦ [reps i]` in the coset space
  set q : Fin 11 → SL(2, ZMod 11) ⧸ Ksub := fun i => QuotientGroup.mk (reps i) with hq
  have hqinj : Function.Injective q := by
    intro i j hij
    rw [hq] at hij
    simp only at hij
    rw [QuotientGroup.eq] at hij
    exact distinctb i j ((inKb_iff_memK _).2 hij)
  haveI : Fintype (SL(2, ZMod 11) ⧸ Ksub) := Fintype.ofFinite _
  have hcard : Fintype.card (SL(2, ZMod 11) ⧸ Ksub) = 11 := by
    rw [← Nat.card_eq_fintype_card]; exact card_quot
  have hqsurj : Function.Surjective q := by
    have := Fintype.bijective_iff_injective_and_card q
    rw [Fintype.card_fin, hcard] at this
    exact (this.2 ⟨hqinj, rfl⟩).2
  obtain ⟨i, hi⟩ := hqsurj (QuotientGroup.mk g)
  refine ⟨i, ?_⟩
  rw [hq] at hi
  simp only at hi
  rw [QuotientGroup.eq] at hi
  exact (inKb_iff_memK _).2 hi

/-- Every element lies in some coset (Boolean `any` form). -/
lemma cover (g : SL(2, ZMod 11)) :
    (List.finRange 11).any (fun i => inKb ((reps i)⁻¹ * g)) = true := by
  obtain ⟨i, hi⟩ := cover_exists g
  rw [List.any_eq_true]
  exact ⟨i, List.mem_finRange i, hi⟩

/-- `cIdx g` does index a coset containing `g`. -/
lemma cIdx_mem (g : SL(2, ZMod 11)) : inKb ((reps (cIdx g))⁻¹ * g) = true := by
  obtain ⟨i, hi⟩ := cover_exists g
  have hsome : ((List.finRange 11).find? (fun j => inKb ((reps j)⁻¹ * g))).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨i, List.mem_finRange i, hi⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  have hpred := List.find?_some hj
  simp only [] at hpred
  have hcidx : cIdx g = j := by unfold cIdx; rw [hj]; rfl
  rw [hcidx]; exact hpred

end PSL211

end Mathieu
