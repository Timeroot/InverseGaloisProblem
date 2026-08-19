import Mathieu.GolayCore
import Mathieu.BasicM24

namespace Mathieu

open Equiv

set_option maxRecDepth 40000

/-
**(S1)** The pointwise stabiliser of the five points `0,1,2,3,4` inside `M₂₄` has order
`48`.  By orbit–stabiliser applied to the `5`-transitive action of `M₂₄` on the
`5100480 = 24·23·22·21·20` injective `5`-tuples, `|M₂₄| = 5100480 · |stab|`, so
`|stab| = 244823040 / 5100480 = 48`.
-/
lemma card_stab5_M24 : Nat.card (stab5 M24) = 48 := by
  -- By orbit–stabiliser, the order of the stabilizer is given by |M24| / |orbit|.
  have h_orbit : Nat.card (MulAction.orbit (↥(M24)) (Mathieu.TransM24.baseEmb)) = 5100480 := by
    rw [ show ( MulAction.orbit ( ↥M24 ) TransM24.baseEmb : Set ( Fin 5 ↪ Fin 24 ) ) = Set.univ from ?_ ];
    · simp +zetaDelta at *;
    · convert Mathieu.TransM24.orbit_baseEmb_eq_univ;
  have h_stabilizer : Nat.card (MulAction.stabilizer (↥(Mathieu.M24)) (Mathieu.TransM24.baseEmb)) = 48 := by
    have h_stabilizer : (Nat.card (MulAction.orbit (↥(Mathieu.M24)) (Mathieu.TransM24.baseEmb))) * (Nat.card (MulAction.stabilizer (↥(Mathieu.M24)) (Mathieu.TransM24.baseEmb))) = (Nat.card (↥(Mathieu.M24))) := by
      convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group ( ↥M24 ) TransM24.baseEmb;
      convert Nat.card_eq_fintype_card;
      any_goals exact Fintype.ofFinite _;
      · convert Nat.card_eq_fintype_card;
      · convert Nat.card_eq_fintype_card;
    nlinarith [ show Nat.card M24 = 244823040 from by simpa using Mathieu.M24_card ];
  convert h_stabilizer using 1;
  fapply Nat.card_congr;
  refine' Equiv.ofBijective _ ⟨ fun x y h => _, fun x => _ ⟩;
  use fun x => ⟨ ⟨ x.val, x.property.1 ⟩, by
    ext i
    fin_cases i <;> simp +decide [ x.2.2 ] ⟩
  all_goals generalize_proofs at *;
  · grind;
  · rcases x with ⟨ ⟨ g, hg ⟩, hx ⟩;
    simp +decide [ Function.Embedding.ext_iff, Fin.forall_fin_succ ] at hx ⊢;
    exact ⟨ hg, fun i hi => by fin_cases i <;> simp +decide at hi ⊢ <;> tauto ⟩


/-- **(combiner)** The pointwise `5`-point stabilisers of `M₂₄` and of `Aut(G₂₄)` coincide.
Synthesis of (S1) and (S2): `stab5 M₂₄ ⊆ stab5 (Aut G₂₄)` because `M₂₄ ≤ Aut(G₂₄)`; both are
finite (subsets of the finite `Perm (Fin 24)`), and
`|stab5 (Aut G₂₄)| ≤ 48 = |stab5 M₂₄|`, so the inclusion is an equality of sets. -/
lemma stab5_codeAut_eq_stab5_M24 :
    stab5 (codeAut GolayCode24.golayCode) = stab5 M24 := by
  have hsub : stab5 M24 ⊆ stab5 (codeAut GolayCode24.golayCode) := by
    rintro k ⟨hkM, hkfix⟩
    exact ⟨M24_le_codeAut hkM, hkfix⟩
  have hfin : (stab5 (codeAut GolayCode24.golayCode)).Finite := Set.toFinite _
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have h1 : (stab5 M24).ncard = 48 := by
    rw [← Nat.card_coe_set_eq]; exact card_stab5_M24
  have h2 : (stab5 (codeAut GolayCode24.golayCode)).ncard ≤ 48 := by
    rw [← Nat.card_coe_set_eq]; exact card_stab5_codeAut_le
  omega

/-- **Rigidity of the 5-point stabiliser.** Any code automorphism of the (extended binary)
Golay code that fixes the five points `0,1,2,3,4` pointwise already lies in `M₂₄`.

This is the genuinely deep part of `codeAut_le_M24`.  It is now a one-line synthesis of the
decomposition above: `k` lies in the pointwise `5`-point stabiliser of `Aut(G₂₄)`, which
equals that of `M₂₄` (`stab5_codeAut_eq_stab5_M24`), so `k ∈ M₂₄`. -/
lemma codeAut_stab5_le_M24 (k : Perm (Fin 24))
    (hk : k ∈ codeAut GolayCode24.golayCode)
    (hfix : ∀ i : Fin 24, (i : ℕ) < 5 → k i = i) : k ∈ M24 := by
  have hmem : k ∈ stab5 (codeAut GolayCode24.golayCode) := ⟨hk, hfix⟩
  rw [stab5_codeAut_eq_stab5_M24] at hmem
  exact hmem.1

/-
**`Aut(G₂₄) ≤ M₂₄`.** The reverse inclusion — equivalently `|Aut(G₂₄)| = |M₂₄|`.  This is
the deep half of the theorem that `M₂₄` is the full automorphism group of the extended binary
Golay code.

Reduction: given `g ∈ Aut(G₂₄)`, use the (proved) `5`-transitivity of `M₂₄` on `Fin 24`
(`M24_isMultiplyPretransitive_five`) to find `m ∈ M₂₄` agreeing with `g` on the five points
`0,1,2,3,4`.  Then `k := m⁻¹ * g ∈ Aut(G₂₄)` fixes those five points pointwise, so
`codeAut_stab5_le_M24` gives `k ∈ M₂₄`, whence `g = m * k ∈ M₂₄`.
-/
lemma codeAut_le_M24 : codeAut GolayCode24.golayCode ≤ M24 := by
  intro g hg;
  obtain ⟨m, hm⟩ : ∃ m : ↥Mathieu.M24, m • (Fin.castLEEmb (by norm_num : (5:ℕ) ≤ 24)) = (Fin.castLEEmb (by norm_num : (5:ℕ) ≤ 24)).trans g.toEmbedding := by
    have := @Mathieu.M24_isMultiplyPretransitive_five;
    exact this.1 _ _;
  -- `m` agrees with `g` on the five base points `0,1,2,3,4`; correct `g` by `m⁻¹`.
  set k : Perm (Fin 24) := (m : Perm (Fin 24))⁻¹ * g
  have hk : k ∈ codeAut GolayCode24.golayCode := by
    exact Subgroup.mul_mem _ ( Subgroup.inv_mem _ ( M24_le_codeAut m.2 ) ) hg
  have hk_fix : ∀ i : Fin 24, (i : ℕ) < 5 → k i = i := by
    intro i hi
    have h_eq : (m : Perm (Fin 24)) i = g i := by
      convert congr_arg ( fun f : Fin 5 ↪ Fin 24 => f ⟨ i, hi ⟩ ) hm using 1
    simp only [k, Perm.coe_mul, Function.comp_apply, ← h_eq]
    exact m.1.symm_apply_apply i
  have := codeAut_stab5_le_M24 k hk hk_fix;
  convert Subgroup.mul_mem _ m.2 this using 1 ; aesop

/-- **`M₂₄ ≅ Aut(G₂₄)`.** There is an extended binary Golay code whose coordinate
automorphism group is isomorphic to `M₂₄`.  The witness is the `M₂₄`-invariant code
`GolayCode24.golayCode`; the isomorphism is obtained from the equality of subgroups
`M₂₄ = Aut(G₂₄)` (forward inclusion `M24_le_codeAut`; reverse inclusion `codeAut_le_M24`). -/
theorem M24_iso_codeAut_golay :
    ∃ C : Submodule (ZMod 2) (Fin 24 → ZMod 2),
      IsExtendedBinaryGolay C ∧ Nonempty (M24 ≃* codeAut C) :=
  ⟨GolayCode24.golayCode, GolayCode24.golayCode_isGolay,
    ⟨MulEquiv.subgroupCongr (le_antisymm M24_le_codeAut codeAut_le_M24)⟩⟩

/-- A predicate characterising the **ternary Golay code** `G₁₂ ⊆ 𝔽₃¹²`:
a 6-dimensional ternary linear code whose nonzero codewords have Hamming weight ≥ 6. -/
structure IsTernaryGolay (C : Submodule (ZMod 3) (Fin 12 → ZMod 3)) : Prop where
  /-- The code has dimension 6. -/
  dim : Module.finrank (ZMod 3) C = 6
  /-- Every nonzero codeword has Hamming weight at least 6. -/
  minWeight : ∀ v ∈ C, v ≠ 0 → 6 ≤ hammingNorm v

/-!
## A concrete ternary Golay code

The same scheme over `𝔽₃`: the row span of `[I₆ | B₃]`, where `B₃` is the bordered circulant
of `(0, 1, -1, -1, 1)` (the quadratic-residue pattern mod `5`).  Its weight enumerator is
`1 + 264 x⁶ + 440 x⁹ + 24 x¹²`, so it has dimension `6` and minimum weight `6`.
-/

namespace TernaryGolayCode

open scoped BigOperators
open Matrix

/-- The quadratic-residue circulant pattern mod `5` over `𝔽₃`: `0 ↦ 0`, residues `±1 ↦ 1`,
non-residues `±2 ↦ -1 = 2`. -/
def circ : ZMod 5 → ZMod 3 := fun k => if k = 0 then 0 else if k = 1 ∨ k = 4 then 1 else 2

/-- The `6 × 6` bordered circulant matrix `B₃` over `𝔽₃`. -/
def B3mat (r c : Fin 6) : ZMod 3 :=
  if r = 0 ∧ c = 0 then 0
  else if r = 0 ∨ c = 0 then 1
  else circ ((c.val : ZMod 5) - (r.val : ZMod 5))

/-- The `12 × 6` generator matrix `[I₆ | B₃]ᵀ`. -/
def G3mat : Matrix (Fin 12) (Fin 6) (ZMod 3) := fun j i =>
  if h : j.val < 6 then (if i = (⟨j.val, h⟩ : Fin 6) then 1 else 0)
  else B3mat i ⟨j.val - 6, by omega⟩

/-- The `6 × 12` projection onto the first `6` coordinates; a left inverse of `G3mat`. -/
def P3mat : Matrix (Fin 6) (Fin 12) (ZMod 3) := fun i j =>
  if j.val = i.val then 1 else 0

/-- The ternary Golay encoding linear map `m ↦ G₃ · m`. -/
noncomputable def golayEnc3 : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 12 → ZMod 3) := G3mat.mulVecLin

/-- The concrete ternary Golay code: the range of the encoding. -/
noncomputable def golayCode3 : Submodule (ZMod 3) (Fin 12 → ZMod 3) := LinearMap.range golayEnc3

/-
`P3mat` is a left inverse of `G3mat`.
-/
lemma PG3_eq_one : P3mat * G3mat = 1 := by
  decide +kernel

/-- The encoding is injective. -/
lemma golayEnc3_injective : Function.Injective golayEnc3 := by
  convert Function.LeftInverse.injective _
  exact fun v => v ∘ (fun i => ⟨i.val, by linarith [Fin.is_lt i]⟩ : Fin 6 → Fin 12)
  intro v; ext i; simp +decide [golayEnc3]
  simp +decide [Matrix.mulVec, dotProduct, G3mat]

set_option maxHeartbeats 400000 in
/-- Minimum-weight certificate: every nonzero message encodes to a word of weight `≥ 6`.
Checked over all `729` messages. -/
lemma golay3_mulVec_minWeight :
    ∀ m : Fin 6 → ZMod 3, m ≠ 0 → 6 ≤ hammingNorm (G3mat.mulVec m) := by
  decide +kernel

/-
The concrete code has dimension `6`.
-/
lemma golayCode3_finrank : Module.finrank (ZMod 3) golayCode3 = 6 := by
  rw [ golayCode3, LinearMap.finrank_range_of_inj golayEnc3_injective ];
  norm_num

/-
The concrete code satisfies `IsTernaryGolay`.
-/
lemma golayCode3_isGolay : IsTernaryGolay golayCode3 := by
  constructor;
  · convert TernaryGolayCode.golayCode3_finrank;
  · intro v hv hv_ne_zero
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hv
    have hm_ne_zero : m ≠ 0 := by
      aesop_cat
    have h_golay3_mulVec_minWeight : 6 ≤ hammingNorm (G3mat.mulVec m) := by
      exact golay3_mulVec_minWeight m hm_ne_zero
    have h_v_eq_golay3_mulVec_m : v = G3mat.mulVec m := by
      exact hm.symm
    rw [h_v_eq_golay3_mulVec_m]
    exact h_golay3_mulVec_minWeight

end TernaryGolayCode

/-- **A ternary Golay code exists.** -/
theorem exists_isTernaryGolay :
    ∃ C : Submodule (ZMod 3) (Fin 12 → ZMod 3), IsTernaryGolay C :=
  ⟨TernaryGolayCode.golayCode3, TernaryGolayCode.golayCode3_isGolay⟩

end Mathieu