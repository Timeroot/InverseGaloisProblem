import Mathlib
import Mathieu.ProjF4

/-!
# `2`-transitivity of `PSL(3,4)` on the projective plane `PG(2,4)`

`SL(3, F4)` acts on the `21` points `P` of the projective plane (`ProjF4.lean`).  This action
is **`2`-transitive**: the induced action on ordered pairs of distinct projective points is
transitive.  (This descends to the faithful `PSL(3,4)`-action, but `2`-transitivity is a
property of the underlying `SL`-action.)

This is the bottom of the Wielandt transitivity tower for `M₂₂ ≤ M₂₃ ≤ M₂₄` (see
`NATIVE_DECIDE_STATUS.md`): via `M₂₁ ≅ PSL(3,4)` it should give `native_decide`-free
`k`-transitivity of `M₂₂/M₂₃/M₂₄`, exactly as the clean `M₁₂` `5`-transitivity descends from the
`4`-transitivity of `M₁₁`.

## Proof outline

`2`-transitivity is equivalent (via `SubMulAction.ofStabilizer.isMultiplyPretransitive`) to:

* `SL(3,4)` is transitive on `P` (`psiP_transitive`); and
* the stabiliser of the base point `p0 = [1:0:0]` is transitive on the remaining points
  (`stab_p0_transitive`).

Both are classical linear algebra over `F4`: any nonzero vector extends to a basis, and a
suitable change-of-basis matrix (rescaled to determinant `1`) realises the required map.
-/

namespace Mathieu.PSL34

open Matrix Equiv MulAction
open scoped MatrixGroups

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- The base projective point `[1 : 0 : 0]`. -/
noncomputable def p0 : P := ⟨![1, 0, 0], by decide⟩

/-
`SL(3, F4)` acts transitively on the projective plane.
-/
theorem psiP_transitive : IsPretransitive (SL(3, F4)) P := by
  have h_basis : ∀ (v : Fin 3 → F4), v ≠ 0 → ∃ A : Matrix.SpecialLinearGroup (Fin 3) F4, A.val.mulVec ![1, 0, 0] = v := by
    intro v hv_nonzero
    obtain ⟨b, c, hb, hc, h_basis⟩ : ∃ b c : Fin 3 → F4, b ≠ 0 ∧ c ≠ 0 ∧ LinearIndependent F4 ![v, b, c] := by
      obtain ⟨b, hb⟩ : ∃ b : Fin 3 → F4, b ≠ 0 ∧ LinearIndependent F4 ![v, b] := by
        by_contra h_contra;
        simp_all +decide [ linearIndependent_fin2 ];
        obtain ⟨ a, ha ⟩ := h_contra ( fun i => if i = 0 then 1 else 0 ) ( by decide ) ; obtain ⟨ b, hb ⟩ := h_contra ( fun i => if i = 1 then 1 else 0 ) ( by decide ) ; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
        grind;
      obtain ⟨c, hc⟩ : ∃ c : Fin 3 → F4, c ≠ 0 ∧ c ∉ Submodule.span F4 {v, b} := by
        have h_subspace : Submodule.span F4 {v, b} ≠ ⊤ := by
          have h_subspace : Module.finrank F4 (Submodule.span F4 {v, b}) ≤ 2 := by
            refine' le_trans ( finrank_span_le_card _ ) _ ; simp +decide;
            exact Finset.card_insert_le _ _;
          exact fun h => by rw [ h ] at h_subspace; norm_num at h_subspace;
        contrapose! h_subspace;
        exact eq_top_iff.mpr fun x hx => if hx0 : x = 0 then hx0.symm ▸ Submodule.zero_mem _ else h_subspace x hx0;
      refine' ⟨ b, c, hb.1, hc.1, _ ⟩;
      rw [ Fintype.linearIndependent_iff ] at *;
      intro g hg i; simp_all +decide [ Fin.sum_univ_three, Fin.forall_fin_succ ] ;
      by_cases h : g 2 = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
      · have := hb.2 ( fun i => if i = 0 then g 0 else g 1 ) hg; fin_cases i <;> aesop;
      · contrapose! hc;
        intro hc_nonzero
        have h_comb : c = -(g 2)⁻¹ • (g 0 • v + g 1 • b) := by
          simp_all +decide [ smul_smul ];
        exact h_comb.symm ▸ Submodule.smul_mem _ _ ( Submodule.add_mem _ ( Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_insert _ _ ) ) ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ) );
    -- Form the matrix $M$ whose columns are $v$, $b$, and $c$.
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F4, M.det ≠ 0 ∧ M.mulVec ![1, 0, 0] = v ∧ M.mulVec ![0, 1, 0] = b ∧ M.mulVec ![0, 0, 1] = c := by
      refine' ⟨ Matrix.of ( fun i j => if j = 0 then v i else if j = 1 then b i else c i ), _, _, _, _ ⟩ <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
      · rw [ Fintype.linearIndependent_iff ] at h_basis;
        contrapose! h_basis;
        obtain ⟨ g, hg ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_basis;
        simp_all +decide [ funext_iff, Fin.sum_univ_three, Matrix.mulVec, dotProduct ];
        exact ⟨ g, fun x => by simpa only [ mul_comm ] using hg.2 x, hg.1 ⟩;
      · exact ⟨ rfl, rfl, rfl ⟩;
      · exact ⟨ rfl, rfl, rfl ⟩;
      · exact ⟨ rfl, rfl, rfl ⟩;
    -- Scale the third column of $M$ by $M.det⁻¹$ to obtain a matrix $A$ with determinant $1$.
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) F4, A.det = 1 ∧ A.mulVec ![1, 0, 0] = v ∧ A.mulVec ![0, 1, 0] = b ∧ A.mulVec ![0, 0, 1] = M.det⁻¹ • c := by
      refine' ⟨ Matrix.of ( fun i j => if j = 2 then M.det⁻¹ • M i 2 else M i j ), _, _, _, _ ⟩ <;> simp_all +decide [ Matrix.det_fin_three ];
      · grind;
      · simp_all +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec ];
        simp_all +decide [ vecHead, vecTail ];
      · ext i; fin_cases i <;> simp +decide [ ← hM.2.2.1 ] ;
        · simp +decide [ vecHead, vecTail, Matrix.mulVec ];
        · simp +decide [ vecHead, vecTail, Matrix.mulVec ];
        · simp +decide [ vecHead, vecTail, Matrix.mulVec ];
      · simp_all +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec ];
        simp_all +decide [ vecHead, vecTail ];
    exact ⟨ ⟨ A, hA.1 ⟩, hA.2.1 ⟩;
  constructor;
  intro x y;
  obtain ⟨A, hA⟩ := h_basis y.1 y.2.1
  obtain ⟨B, hB⟩ := h_basis x.1 x.2.1;
  use A * B⁻¹;
  have h_eq : (A * B⁻¹ : Matrix (Fin 3) (Fin 3) F4) *ᵥ x.1 = y.1 := by
    simp +decide [ ← hA, ← hB, Matrix.mulVec_mulVec ];
    simp +decide [ Matrix.mul_assoc, Matrix.adjugate_mul ];
  have h_eq : nrm ((A * B⁻¹ : Matrix (Fin 3) (Fin 3) F4) *ᵥ x.1) = y.1 := by
    rw [ h_eq, y.2.2 ];
  exact Subtype.ext h_eq

/-- The base projective point `[0 : 1 : 0]` (distinct from `p0`). -/
noncomputable def p1 : P := ⟨![0, 1, 0], by decide⟩

/-
**Key construction.**  Every projective point `q ≠ p0` is the image of `p1` under a matrix
that *fixes* `p0` (its first column is a scalar multiple of `e0`).  Extend `{e0, q}` to a basis
`e0, q, c`, form the change-of-basis matrix (first two columns `e0, q`) and rescale the third
column to make the determinant `1`.
-/
lemma stab_reach (q : P) (hq : q ≠ p0) :
    ∃ g : SL(3, F4), g • p0 = p0 ∧ g • p1 = q := by
  have h_basis : ∃ b c : Fin 3 → F4, LinearIndependent F4 ![![1, 0, 0], q.1, b] ∧ c ∉ Submodule.span F4 {![1, 0, 0], q.1} ∧ LinearIndependent F4 ![![1, 0, 0], q.1, c] := by
    have h_basis : ∃ b : Fin 3 → F4, LinearIndependent F4 ![![1, 0, 0], q.1, b] := by
      have h_basis : LinearIndependent F4 ![![1, 0, 0], q.1] := by
        refine' Fintype.linearIndependent_iff.2 _;
        decide +revert;
      obtain ⟨b, hb⟩ : ∃ b : Fin 3 → F4, b ∉ Submodule.span F4 {![1, 0, 0], q.1} := by
        have h_subspace : Module.finrank F4 (Submodule.span F4 {![1, 0, 0], q.1}) ≤ 2 := by
          refine' le_trans ( finrank_span_le_card _ ) _ ; simp +decide;
          exact Finset.card_insert_le _ _;
        contrapose! h_subspace;
        rw [ show Submodule.span F4 { _, _ } = ⊤ from eq_top_iff.mpr fun x hx => h_subspace x ] ; norm_num;
      use b;
      rw [ Fintype.linearIndependent_iff ] at *;
      intro g hg i; simp_all +decide [ Fin.sum_univ_three, Fin.forall_fin_succ ] ;
      by_cases h : g 2 = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
      · specialize h_basis ( fun i => if i = 0 then g 0 else g 1 ) ; simp_all +decide [ ];
        fin_cases i <;> aesop;
      · contrapose! hb;
        have h_comb : b = -(g 2)⁻¹ • (g 0 • ![1, 0, 0] + g 1 • q.1) := by
          ext i; fin_cases i <;> simp_all +decide [ vecHead, vecTail ] ;
        exact h_comb.symm ▸ Submodule.smul_mem _ _ ( Submodule.add_mem _ ( Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_insert _ _ ) ) ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ) );
    obtain ⟨ b, hb ⟩ := h_basis;
    refine' ⟨ b, b, hb, _, hb ⟩;
    intro h;
    rw [ Submodule.mem_span_pair ] at h;
    obtain ⟨ a, b, rfl ⟩ := h; have := hb.ne_zero 2; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
    rw [ Fintype.linearIndependent_iff ] at hb;
    specialize hb ( fun i => if i = 0 then -a else if i = 1 then -b else 1 ) ; simp_all +decide [ Fin.sum_univ_three ];
    simp_all +decide [ Fin.forall_fin_succ, add_assoc ];
  obtain ⟨ b, c, hb, hc, hbc ⟩ := h_basis;
  -- Form the matrix $M$ whose columns are $e0$, $q$, and $c$.
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F4, M.det ≠ 0 ∧ M.mulVec ![1, 0, 0] = ![1, 0, 0] ∧ M.mulVec ![0, 1, 0] = q.1 ∧ M.mulVec ![0, 0, 1] = c := by
    refine' ⟨ Matrix.of ( fun i j => if j = 0 then ![1, 0, 0] i else if j = 1 then q.1 i else c i ), _, _, _, _ ⟩ <;> simp_all +decide [ Matrix.det_fin_three ];
    · rw [ Fintype.linearIndependent_iff ] at hbc;
      contrapose! hbc;
      obtain ⟨ g, hg ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ( show Matrix.det ( Matrix.of ( fun i j => if j = 0 then ![1, 0, 0] i else if j = 1 then q.1 i else c i ) ) = 0 from by
                                                                  simp +decide [ Matrix.det_fin_three, hbc ] );
      simp_all +decide [ funext_iff, Fin.sum_univ_three, Matrix.mulVec, dotProduct ];
      simp_all +decide [ Fin.forall_fin_succ, vecHead, vecTail ];
      exact ⟨ g, ⟨ by simpa only [ mul_comm ] using hg.2.1, by simpa only [ mul_comm ] using hg.2.2.1, by simpa only [ mul_comm ] using hg.2.2.2 ⟩, hg.1 ⟩;
    · exact funext fun i => by fin_cases i <;> rfl;
    · exact funext fun i => by fin_cases i <;> rfl;
    · exact funext fun i => by fin_cases i <;> rfl;
  -- Scale the third column of $M$ by $M.det⁻¹$ to obtain a matrix $A$ with determinant $1$.
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) F4, A.det = 1 ∧ A.mulVec ![1, 0, 0] = ![1, 0, 0] ∧ A.mulVec ![0, 1, 0] = q.1 ∧ A.mulVec ![0, 0, 1] = M.det⁻¹ • c := by
    refine' ⟨ Matrix.of ( fun i j => if j = 2 then M.det⁻¹ • M i 2 else M i j ), _, _, _, _ ⟩ <;> simp_all +decide [ Matrix.det_fin_three ];
    · grind;
    · simp_all +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec ];
      simp_all +decide [ vecHead, vecTail ];
    · simp_all +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec ];
      simp_all +decide [ vecHead, vecTail ];
    · simp +decide [ ← hM.2.2.2, funext_iff, Fin.forall_fin_succ ];
      simp +decide [ vecHead, vecTail, Matrix.mulVec ];
  refine' ⟨ ⟨ A, hA.1 ⟩, _, _ ⟩ <;> simp_all +decide [ ];
  · refine' Subtype.ext _;
    simp +decide [ smul_def ];
    exact hA.2.1.symm ▸ by decide;
  · refine' Subtype.ext _;
    convert nrm_eq_smul _ using 1;
    simp +decide [ hA.2.2.1, p1 ];
    convert q.2.2.symm using 1

/-- The stabiliser of the base point `[1:0:0]` acts transitively on the remaining
projective points. -/
theorem stab_p0_transitive :
    IsPretransitive (stabilizer (SL(3, F4)) p0)
      (SubMulAction.ofStabilizer (SL(3, F4)) p0) := by
  refine ⟨fun x y => ?_⟩
  have hx : x.val ≠ p0 := (SubMulAction.mem_ofStabilizer_iff _ _).mp x.2
  have hy : y.val ≠ p0 := (SubMulAction.mem_ofStabilizer_iff _ _).mp y.2
  obtain ⟨g, hg0, hgx⟩ := stab_reach x.val hx
  obtain ⟨h, hh0, hhy⟩ := stab_reach y.val hy
  refine ⟨(⟨h, hh0⟩ : ↑(stabilizer (SL(3, F4)) p0)) * (⟨g, hg0⟩)⁻¹, ?_⟩
  apply Subtype.ext
  rw [SubMulAction.val_smul]
  show (h * g⁻¹) • x.val = y.val
  rw [← smul_smul]
  have hgi : g⁻¹ • x.val = p1 := by rw [← hgx, inv_smul_smul]
  rw [hgi, hhy]

/-- **`PSL(3,4)` is `2`-transitive on `PG(2,4)`.**  (Stated for the `SL(3,4)`-action.) -/
theorem SL34_two_transitive : IsMultiplyPretransitive (SL(3, F4)) P 2 := by
  haveI := psiP_transitive
  have h1 : IsMultiplyPretransitive (stabilizer (SL(3, F4)) p0)
      (SubMulAction.ofStabilizer (SL(3, F4)) p0) 1 := by
    rw [is_one_pretransitive_iff]
    exact stab_p0_transitive
  have := (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := SL(3, F4)) (a := p0) (n := 1)).mpr h1
  simpa using this

end Mathieu.PSL34