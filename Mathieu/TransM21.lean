import Mathieu.TransPSL34
import Mathieu.PSL34

/-!
# `M₂₁` is `2`-transitive on its `21` points

The bottom of the Wielandt transitivity tower for `M₂₂ ≤ M₂₃ ≤ M₂₄`.  We transport the
`native_decide`-free `2`-transitivity of `PSL(3,4)` on the projective plane `PG(2,4)`
(`Mathieu.PSL34.SL34_two_transitive`) to the concrete permutation group `M₂₁ ≤ Perm (Fin 23)`
acting on its `21` moved points `Y = {x : Fin 23 // x ≠ 21 ∧ x ≠ 22}`.

The transport uses the surjective homomorphism `cpsi : SL(3, F4) →* M₂₁`, `g ↦ σ · psi34 g · σ⁻¹`
(the relabelled plane action, `σ = sigmaPerm`), together with the equivariant bijection
`f : P ≃ Y`, `p ↦ σ (embed (eP.symm p))`, and Mathlib's
`MulAction.IsPretransitive.of_embedding_congr`.
-/

namespace Mathieu

open Matrix Equiv MulAction
open scoped MatrixGroups

namespace TransM21

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The `21` moved points of `M₂₁` (everything except the two fixed points `21`, `22`). -/
abbrev Y : Type := {x : Fin 23 // x ≠ 21 ∧ x ≠ 22}

/-! ### `M₂₁` fixes the two extra points -/

/-- Every element of `M₂₁` fixes the point `21`. -/
theorem M21_fix21 (m : M21) : (m : Perm (Fin 23)) 21 = 21 := by
  have hm : (m : Perm (Fin 23)) ∈ MulAction.stabilizer (Perm (Fin 23)) (21 : Fin 23) :=
    (m.2.2)
  simpa [Equiv.Perm.smul_def] using hm

/-- Every element of `M₂₁` fixes the point `22`. -/
theorem M21_fix22 (m : M21) : (m : Perm (Fin 23)) 22 = 22 := by
  have hm22 : (m : Perm (Fin 23)) ∈ M22 := M21_le_M22 m.2
  have : (m : Perm (Fin 23)) ∈ MulAction.stabilizer (Perm (Fin 23)) (22 : Fin 23) := hm22.2
  simpa [Equiv.Perm.smul_def] using this

/-- An element of `M₂₁` maps `Y` to `Y`. -/
theorem M21_mapsTo (m : M21) (x : Fin 23) (hx : x ≠ 21 ∧ x ≠ 22) :
    (m : Perm (Fin 23)) x ≠ 21 ∧ (m : Perm (Fin 23)) x ≠ 22 := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hx.1
    have := M21_fix21 m
    have := (m : Perm (Fin 23)).injective (h.trans this.symm)
    exact this
  · intro h
    apply hx.2
    have := M21_fix22 m
    exact (m : Perm (Fin 23)).injective (h.trans this.symm)

/-! ### The `M₂₁`-action on `Y` -/

instance : SMul M21 Y := ⟨fun m y => ⟨(m : Perm (Fin 23)) y.1, M21_mapsTo m y.1 y.2⟩⟩

@[simp] theorem smul_Y_val (m : M21) (y : Y) :
    ((m • y).1 : Fin 23) = (m : Perm (Fin 23)) y.1 := rfl

instance : MulAction M21 Y where
  one_smul y := by apply Subtype.ext; simp
  mul_smul a b y := by
    apply Subtype.ext
    simp only [smul_Y_val, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]

/-! ### The relabelling homomorphism `cpsi : SL(3,F4) →* M₂₁` -/

open PSL34 (psi34 sigmaPerm psiP psi21 eP incl21 p0)
open EnumSL34 (g1 g2 g3)

/-- `g ↦ σ · psi34 g · σ⁻¹` as a homomorphism into `Perm (Fin 23)`. -/
noncomputable def cpsiF4 : SL(3, F4) →* Perm (Fin 23) :=
  ((MulAut.conj sigmaPerm).toMonoidHom).comp psi34

/-- `cpsiF4` agrees with conjugation of `psi34` by `sigmaPerm`. -/
theorem cpsiF4_apply (g : SL(3, F4)) :
    cpsiF4 g = (MulAut.conj sigmaPerm) (psi34 g) := by
  simp only [cpsiF4, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- `PSL34.w1` lies in `M₂₂`. -/
theorem w1_mem_M22 : PSL34.w1 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (inv_mem (EnumM22.schB_mem_M22 7)) (EnumM22.schB_mem_M22 1)) (EnumM22.schB_mem_M22 1))
    (EnumM22.schB_mem_M22 7)) (inv_mem (EnumM22.schB_mem_M22 2)))
    (inv_mem (EnumM22.schB_mem_M22 7))) (EnumM22.schB_mem_M22 1)

/-- `PSL34.w2` lies in `M₂₂`. -/
theorem w2_mem_M22 : PSL34.w2 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (EnumM22.schB_mem_M22 2) (EnumM22.schB_mem_M22 1)) (EnumM22.schB_mem_M22 1))
    (EnumM22.schB_mem_M22 13)) (inv_mem (EnumM22.schB_mem_M22 7)))
    (inv_mem (EnumM22.schB_mem_M22 13))) (EnumM22.schB_mem_M22 2))
    (inv_mem (EnumM22.schB_mem_M22 7))

/-- `PSL34.w3` lies in `M₂₂`. -/
theorem w3_mem_M22 : PSL34.w3 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (EnumM22.schB_mem_M22 2) (EnumM22.schB_mem_M22 2)) (inv_mem (EnumM22.schB_mem_M22 7)))
    (inv_mem (EnumM22.schB_mem_M22 1))) (inv_mem (EnumM22.schB_mem_M22 1)))
    (inv_mem (EnumM22.schB_mem_M22 13))) (EnumM22.schB_mem_M22 2)

/-- `PSL34.w1` fixes the point `21`. -/
theorem w1_fix21 : PSL34.w1 (21 : Fin 23) = 21 := by
  have hw : PSL34.w1 =
      c[1,9]*c[3,6]*c[4,7]*c[5,13]*c[8,19]*c[10,15]*c[12,16]*c[17,18] := by
    unfold PSL34.w1; rw [schB1_eq, schB2_eq, schB7_eq]; decide
  rw [hw]; decide

/-- `PSL34.w2` fixes the point `21`. -/
theorem w2_fix21 : PSL34.w2 (21 : Fin 23) = 21 := by
  have hw : PSL34.w2 =
      c[1,18]*c[3,13]*c[4,10]*c[5,6]*c[7,15]*c[8,12]*c[9,17]*c[16,19] := by
    unfold PSL34.w2; rw [schB1_eq, schB2_eq, schB7_eq, schB13_eq]; decide
  rw [hw]; decide

/-- `PSL34.w3` fixes the point `21`. -/
theorem w3_fix21 : PSL34.w3 (21 : Fin 23) = 21 := by
  have hw : PSL34.w3 =
      c[0,2,1]*c[3,11,9]*c[4,16,13]*c[5,8,10]*c[12,20,17]*c[14,18,15] := by
    unfold PSL34.w3; rw [schB1_eq, schB2_eq, schB7_eq, schB13_eq]; decide
  rw [hw]; decide

/-- `PSL34.w1` lies in `M₂₁`. -/
theorem w1_mem_M21 : PSL34.w1 ∈ M21 :=
  Subgroup.mem_inf.2 ⟨w1_mem_M22,
    (MulAction.mem_stabilizer_iff).2 (by rw [Equiv.Perm.smul_def]; exact w1_fix21)⟩

/-- `PSL34.w2` lies in `M₂₁`. -/
theorem w2_mem_M21 : PSL34.w2 ∈ M21 :=
  Subgroup.mem_inf.2 ⟨w2_mem_M22,
    (MulAction.mem_stabilizer_iff).2 (by rw [Equiv.Perm.smul_def]; exact w2_fix21)⟩

/-- `PSL34.w3` lies in `M₂₁`. -/
theorem w3_mem_M21 : PSL34.w3 ∈ M21 :=
  Subgroup.mem_inf.2 ⟨w3_mem_M22,
    (MulAction.mem_stabilizer_iff).2 (by rw [Equiv.Perm.smul_def]; exact w3_fix21)⟩

/-- Every conjugated plane action lands in `M₂₁`. -/
theorem cpsiF4_mem (g : SL(3, F4)) : cpsiF4 g ∈ M21 := by
  have hsub : (⊤ : Subgroup (SL(3, F4))) ≤ Subgroup.comap cpsiF4 M21 := by
    rw [← PSL34.closure_gens34_eq_top, Subgroup.closure_le]
    rintro x hx
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · rw [cpsiF4_apply, PSL34.conj_psi34_g1_eq_w1]; exact w1_mem_M21
    · rw [cpsiF4_apply, PSL34.conj_psi34_g2_eq_w2]; exact w2_mem_M21
    · rw [cpsiF4_apply, PSL34.conj_psi34_g3_eq_w3]; exact w3_mem_M21
  exact hsub (Subgroup.mem_top g)

/-- The relabelling homomorphism `SL(3, F4) →* M₂₁`. -/
noncomputable def cpsi : SL(3, F4) →* M21 :=
  cpsiF4.codRestrict M21 cpsiF4_mem

theorem cpsi_coe (g : SL(3, F4)) : (cpsi g : Perm (Fin 23)) = cpsiF4 g := rfl

/-- The kernel of `cpsi` is the centre of `SL(3, F4)`. -/
theorem ker_cpsi : cpsi.ker = Subgroup.center (SL(3, F4)) := by
  rw [cpsi, MonoidHom.ker_codRestrict]
  rw [← PSL34.ker_psi34]
  ext g
  simp only [MonoidHom.mem_ker, cpsiF4_apply, EmbeddingLike.map_eq_one_iff]

/-
The order of the centre of `SL(3, F4)` is `3`.
-/
theorem card_center : Nat.card (Subgroup.center (SL(3, F4))) = 3 := by
  -- The center of $SL(3, F4)$ consists of scalar matrices with determinant 1.
  have h_center : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F4, g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) ↔ ∃ r : F4, r ^ 3 = 1 ∧ g = Matrix.scalar (Fin 3) r := by
    intro g
    rw [Matrix.SpecialLinearGroup.mem_center_iff];
    simp +decide [ eq_comm ];
  -- Therefore, the center of $SL(3, F4)$ is isomorphic to the set of cube roots of unity in $F4$.
  have h_iso : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) ≃ {r : F4 | r ^ 3 = 1} := by
    symm;
    refine' Equiv.ofBijective ( fun r => ⟨ ⟨ Matrix.scalar ( Fin 3 ) r, _ ⟩, _ ⟩ ) ⟨ _, _ ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    grind +revert;
    · aesop;
    · simp +decide [ Matrix.SpecialLinearGroup.ext_iff ];
    · intro g hg; specialize h_center g; aesop;
  rw [ Nat.card_congr h_iso, Nat.card_eq_fintype_card ] ; aesop

/-! ### The equivariant bijection `P ≃ Y` -/

/-- The embedding `Fin 21 ↪ Fin 23` (as the initial segment). -/
def emb2123 (i : Fin 21) : Fin 23 := Fin.castLE (by omega) i

theorem emb2123_lt (i : Fin 21) : (emb2123 i).val < 21 := i.isLt

theorem emb2123_injective : Function.Injective emb2123 := by
  intro a b h; simpa [emb2123, Fin.ext_iff] using h

/-- `sigmaPerm` fixes `21`. -/
theorem sigmaPerm_21 : sigmaPerm 21 = 21 := by
  simp only [sigmaPerm, Equiv.Perm.mul_apply]; decide

/-- `sigmaPerm` fixes `22`. -/
theorem sigmaPerm_22 : sigmaPerm 22 = 22 := by
  simp only [sigmaPerm, Equiv.Perm.mul_apply]; decide

attribute [local irreducible] PSL34.sigmaPerm

/-
The action of `psi34 g` on an embedded point is the embedded image of `psi21 g`.
-/
theorem psi34_emb2123 (g : SL(3, F4)) (i : Fin 21) :
    psi34 g (emb2123 i) = emb2123 (psi21 g i) := by
  convert Equiv.Perm.extendDomain_apply_image _ _ _ using 1

/-
`psi21 g` acts on the label of `p` as `eP.symm` of `g • p`.
-/
theorem psi21_eP_symm (g : SL(3, F4)) (p : PSL34.P) :
    psi21 g (eP.symm p) = eP.symm (g • p) := by
  unfold psi21; aesop;

/-- The `Fin 23` label of a projective point under the relabelling `σ`. -/
noncomputable def ptFin (p : PSL34.P) : Fin 23 :=
  sigmaPerm (emb2123 (eP.symm p))

theorem ptFin_ne (p : PSL34.P) : ptFin p ≠ 21 ∧ ptFin p ≠ 22 := by
  refine ⟨?_, ?_⟩
  · intro h
    have := sigmaPerm.injective (h.trans sigmaPerm_21.symm)
    have := emb2123_lt (eP.symm p); omega
  · intro h
    have := sigmaPerm.injective (h.trans sigmaPerm_22.symm)
    have := emb2123_lt (eP.symm p); omega

/-- The core equivariance identity at the level of `Fin 23`. -/
theorem ptFin_equivariant (g : SL(3, F4)) (p : PSL34.P) :
    cpsiF4 g (ptFin p) = ptFin (g • p) := by
  rw [cpsiF4_apply, MulAut.conj_apply]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [show ptFin p = sigmaPerm (emb2123 (eP.symm p)) from rfl,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, psi34_emb2123, psi21_eP_symm]
  rfl

/-- The underlying function `P → Y`. -/
noncomputable def fY (p : PSL34.P) : Y := ⟨ptFin p, ptFin_ne p⟩

@[simp] theorem fY_val (p : PSL34.P) : (fY p).1 = ptFin p := rfl

/-- The equivariant map `P →ₑ[cpsi] Y`. -/
noncomputable def fEq : PSL34.P →ₑ[cpsi] Y where
  toFun := fY
  map_smul' g p := by
    apply Subtype.ext
    rw [smul_Y_val, cpsi_coe, fY_val, fY_val]
    exact (ptFin_equivariant g p).symm

/-- `ptFin` is injective. -/
theorem ptFin_injective : Function.Injective ptFin := by
  intro a b h
  apply eP.symm.injective
  apply emb2123_injective
  exact sigmaPerm.injective h

theorem fEq_apply (p : PSL34.P) : fEq p = fY p := rfl

theorem fEq_injective : Function.Injective fEq := by
  intro a b h
  apply ptFin_injective
  rw [fEq_apply, fEq_apply] at h
  exact congrArg Subtype.val h

theorem fEq_bijective : Function.Bijective fEq := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fEq_injective, ?_⟩
  decide

/-! ### The transport -/

/-
**`M₂₁` is `2`-transitive** on its `21` moved points `Y`.  The subgroup given by the
projective-plane action is already `2`-transitive, so surjectivity onto all of `M₂₁` is not
needed here.  This keeps the transitivity tower independent of the order computation.
-/
set_option maxHeartbeats 2000000 in
theorem M21_two_transitive : IsMultiplyPretransitive M21 Y 2 := by
  let e : PSL34.P ≃ Y := Equiv.ofBijective fEq fEq_bijective
  constructor
  intro x y
  let xP : Fin 2 ↪ PSL34.P := x.trans e.symm.toEmbedding
  let yP : Fin 2 ↪ PSL34.P := y.trans e.symm.toEmbedding
  obtain ⟨g, hg⟩ := PSL34.SL34_two_transitive.exists_smul_eq xP yP
  refine ⟨cpsi g, ?_⟩
  apply Function.Embedding.ext
  intro i
  have hi := congrArg (fun z => z i) hg
  change cpsi g • x i = y i
  have hi' := congrArg e hi
  calc
    cpsi g • x i = fEq (g • e.symm (x i)) := by
      have hm := fEq.map_smul' g (e.symm (x i))
      have heq : fEq (e.symm (x i)) = x i := e.apply_symm_apply (x i)
      exact (congrArg (fun z : Y => cpsi g • z) heq).symm.trans hm.symm
    _ = y i := by
      change e (g • e.symm (x i)) = y i
      rw [← e.apply_symm_apply (y i)]
      exact hi'

end TransM21

end Mathieu