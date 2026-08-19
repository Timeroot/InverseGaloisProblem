import Mathieu.EnumSL223
import Mathieu.DefM24

/-!
# `PSL(2, 𝔽₂₃)` embeds into `M₂₄`

We construct an injective homomorphism `PSL(2, ZMod 23) →* M₂₄`.

The group `SL(2, 𝔽₂₃)` acts on the projective line `ℙ¹(𝔽₂₃)` by Möbius transformations.
Mathlib supplies this action as the `GL (Fin 2) K`-action on the one-point compactification
`OnePoint K` (`OnePoint.instGLAction`).  We identify `OnePoint (ZMod 23) ≃ Fin 24`
(`e2324`, sending the finite point `k` to `k` and `∞` to `23`) and transport the action to
`Equiv.Perm (Fin 24)`, giving a homomorphism `psi24 : SL(2, ZMod 23) →* Equiv.Perm (Fin 24)`.

Two facts pin the image down:

* `psi24 Tmat = m24a` and `psi24 Smat = m24c`: the standard `SL₂` generators `T` (translation
  `z ↦ z+1`) and `S` (inversion `z ↦ -1/z`) act, under this labelling, exactly as the `M₂₄`
  generators `m24a` (the 23-cycle) and `m24c` (an involution).  As `T, S` generate `SL(2,𝔽₂₃)`
  (`EnumSL223.closure_eq_top`), the whole image lies in `M₂₄` (`range_le`).
* `ker psi24 = center (SL(2,𝔽₂₃))`: the Möbius action is faithful modulo scalars (an element
  fixing `0, 1, ∞` is a scalar matrix).

Quotienting by the centre, `PSL(2, 𝔽₂₃) = SL(2,𝔽₂₃) ⧸ center` therefore embeds into `M₂₄`.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL223

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

/-- The identification of the projective line `ℙ¹(𝔽₂₃) = OnePoint (ZMod 23)` with `Fin 24`:
the finite point `k` goes to `k`, and `∞` goes to `23`. -/
def e2324 : OnePoint (ZMod 23) ≃ Fin 24 := finSuccEquivLast.symm

/-- The Möbius action homomorphism `SL(2, 𝔽₂₃) →* Perm (ℙ¹(𝔽₂₃))`. -/
noncomputable def psiOP : SL(2, ZMod 23) →* Equiv.Perm (OnePoint (ZMod 23)) :=
  (MulAction.toPermHom (GL (Fin 2) (ZMod 23)) (OnePoint (ZMod 23))).comp
    (Matrix.SpecialLinearGroup.toGL)

/-- The Möbius action transported to `Perm (Fin 24)`. -/
noncomputable def psi24 : SL(2, ZMod 23) →* Equiv.Perm (Fin 24) :=
  (e2324.permCongrHom.toMonoidHom).comp psiOP

/-! ### The Möbius action on points, in closed form -/

/-- The Möbius action on a finite point `k`. -/
lemma psiOP_some (g : SL(2, ZMod 23)) (k : ZMod 23) :
    psiOP g (k : OnePoint (ZMod 23)) =
      if (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 * k + (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 1 = 0
        then OnePoint.infty
        else (((g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 0 * k + (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 1) /
              ((g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 * k + (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 1) : ZMod 23) := by
  have H : (↑(Matrix.SpecialLinearGroup.toGL g) : Matrix (Fin 2) (Fin 2) (ZMod 23))
      = (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) := by simp
  simp only [psiOP, MonoidHom.comp_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  rw [OnePoint.smul_some_eq_ite, H]

/-- The Möbius action on the point at infinity. -/
lemma psiOP_infty (g : SL(2, ZMod 23)) :
    psiOP g OnePoint.infty =
      if (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 = 0 then OnePoint.infty
      else (((g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 0 / (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 : ZMod 23)) := by
  have H : (↑(Matrix.SpecialLinearGroup.toGL g) : Matrix (Fin 2) (Fin 2) (ZMod 23))
      = (g : Matrix (Fin 2) (Fin 2) (ZMod 23)) := by simp
  simp only [psiOP, MonoidHom.comp_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  rw [OnePoint.smul_infty_eq_ite, H]

/-! ### Generators map to `M₂₄` generators -/

lemma psiOP_Tmat_coe (k : ZMod 23) :
    psiOP EnumSL223.Tmat (k : OnePoint (ZMod 23)) = ((k + 1 : ZMod 23) : OnePoint (ZMod 23)) := by
  rw [psiOP_some]
  have e00 : (EnumSL223.Tmat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 0 = 1 := by decide
  have e01 : (EnumSL223.Tmat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 1 = 1 := by decide
  have e10 : (EnumSL223.Tmat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 = 0 := by decide
  have e11 : (EnumSL223.Tmat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 1 = 1 := by decide
  rw [e00, e01, e10, e11]; simp

lemma psiOP_Tmat_infty : psiOP EnumSL223.Tmat OnePoint.infty = OnePoint.infty := by
  rw [psiOP_infty]
  have e10 : (EnumSL223.Tmat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 = 0 := by decide
  rw [e10]; simp

lemma psiOP_Smat_coe (k : ZMod 23) :
    psiOP EnumSL223.Smat (k : OnePoint (ZMod 23))
      = (if k = 0 then OnePoint.infty else ((22 / k : ZMod 23) : OnePoint (ZMod 23))) := by
  rw [psiOP_some]
  have e00 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 0 = 0 := by decide
  have e01 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 1 = 22 := by decide
  have e10 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 = 1 := by decide
  have e11 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 1 = 0 := by decide
  rw [e00, e01, e10, e11]; simp

lemma psiOP_Smat_infty :
    psiOP EnumSL223.Smat OnePoint.infty = ((0 : ZMod 23) : OnePoint (ZMod 23)) := by
  rw [psiOP_infty]
  have e00 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 0 0 = 0 := by decide
  have e10 : (EnumSL223.Smat : Matrix (Fin 2) (Fin 2) (ZMod 23)) 1 0 = 1 := by decide
  rw [e00, e10]; simp

/-- The translation generator acts as the `23`-cycle `m24a`. -/
theorem psi24_Tmat : psi24 EnumSL223.Tmat = m24a := by
  have step : ∀ y : OnePoint (ZMod 23), e2324 (psiOP EnumSL223.Tmat y) = m24a (e2324 y) := by
    intro y
    cases y with
    | infty => rw [psiOP_Tmat_infty]; decide
    | coe k => rw [psiOP_Tmat_coe]; fin_cases k <;> decide
  ext x
  have hx : psi24 EnumSL223.Tmat x = e2324 (psiOP EnumSL223.Tmat (e2324.symm x)) := rfl
  rw [hx, step, Equiv.apply_symm_apply]

/-- The inversion generator acts as the involution `m24c`. -/
theorem psi24_Smat : psi24 EnumSL223.Smat = m24c := by
  have step : ∀ y : OnePoint (ZMod 23), e2324 (psiOP EnumSL223.Smat y) = m24c (e2324 y) := by
    intro y
    cases y with
    | infty => rw [psiOP_Smat_infty]; decide
    | coe k => rw [psiOP_Smat_coe]; fin_cases k <;> decide
  ext x
  have hx : psi24 EnumSL223.Smat x = e2324 (psiOP EnumSL223.Smat (e2324.symm x)) := rfl
  rw [hx, step, Equiv.apply_symm_apply]

/-! ### The image is inside `M₂₄` -/

theorem range_le : MonoidHom.range psi24 ≤ M24 := by
  rw [MonoidHom.range_eq_map, ← EnumSL223.closure_eq_top, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [psi24_Tmat]; exact m24a_mem
  · rw [psi24_Smat]; exact m24c_mem

/-! ### Faithfulness modulo the centre -/

/-- `psi24 g` is trivial iff the underlying Möbius permutation `psiOP g` is. -/
lemma psi24_eq_one_iff (g : SL(2, ZMod 23)) : psi24 g = 1 ↔ psiOP g = 1 := by
  simp only [psi24, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact (e2324.permCongrHom).map_eq_one_iff

/-- An element of the kernel of the Möbius action is a scalar matrix: it fixes `∞`, `0` and `1`,
which forces its off-diagonal entries to vanish and its diagonal entries to agree. -/
lemma ker_le_center : psi24.ker ≤ Subgroup.center (SL(2, ZMod 23)) := by
  intro x hx
  have h_eq : psiOP x = 1 := (psi24_eq_one_iff x).mp (MonoidHom.mem_ker.mp hx)
  have h_scalar : ∃ a : ZMod 23, x.1 = a • 1 := by
    have h_c : x.1 1 0 = 0 := by
      have := congr_arg ( fun f : Equiv.Perm ( OnePoint ( ZMod 23 ) ) => f OnePoint.infty ) h_eq; simp +decide [ psiOP_infty ] at this; aesop;
    have h_b : x.1 0 1 = 0 := by
      have := congr_arg ( fun f => f ( 0 : ZMod 23 ) ) h_eq; norm_num [ psiOP_some, h_c ] at this;
      split_ifs at this <;> simp_all +decide
    have h_a_d : x.1 0 0 = x.1 1 1 := by
      have := congr_arg ( fun f : Equiv.Perm ( OnePoint ( ZMod 23 ) ) => f ( ( 1 : ZMod 23 ) : OnePoint ( ZMod 23 ) ) ) h_eq; simp +decide [ psiOP_some, h_c, h_b ] at this;
      grind only [OnePoint.coe_ne_infty, OnePoint.coe_eq_coe];
    use x.1 0 0;
    ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ * ] ;
  obtain ⟨ a, ha ⟩ := h_scalar;
  simp_all +decide [ Subgroup.mem_center_iff, Matrix.SpecialLinearGroup.ext_iff ]

/-- A central element of `SL(2, 𝔽₂₃)` is a scalar matrix `±1`, which acts trivially. -/
lemma center_le_ker : Subgroup.center (SL(2, ZMod 23)) ≤ psi24.ker := by
  intro g hg; simp_all +decide [ MonoidHom.mem_ker ] ;
  -- Since $g$ is in the center, it commutes with $Tmat$ and $Smat$, implying that $g$ is a scalar matrix.
  have h_scalar : ∃ a : ZMod 23, g.1 = !![a, 0; 0, a] := by
    have h_comm_T : g * EnumSL223.Tmat = EnumSL223.Tmat * g := by
      rw [ hg.comm ]
    have h_comm_S : g * EnumSL223.Smat = EnumSL223.Smat * g := by
      exact hg.comm _;
    simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_two ];
    have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 0 0 ) h_comm_T; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 0 1 ) h_comm_T; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 1 0 ) h_comm_T; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 1 1 ) h_comm_T; norm_num [ Matrix.mul_apply ] at *;
    have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 0 0 ) h_comm_S; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 0 1 ) h_comm_S; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 1 0 ) h_comm_S; have := congr_arg ( fun x : SL(2, ZMod 23) => x.val 1 1 ) h_comm_S; norm_num [ Matrix.mul_apply ] at *;
    simp_all +decide [ EnumSL223.Tmat, EnumSL223.Smat ];
  obtain ⟨ a, ha ⟩ := h_scalar; have := g.2; simp_all +decide [ Matrix.det_fin_two ] ;
  fin_cases a <;> simp +decide at this ⊢;
  · rw [ show g = 1 from by exact Subtype.ext <| by simpa [ ← Matrix.ext_iff ] using ha ] ; simp +decide ;
  · rw [ show g = ⟨ !![22, 0; 0, 22], by decide ⟩ from Subtype.ext ha ];
    unfold psi24 psiOP; simp +decide ;

/-- The kernel of the Möbius action is exactly the centre of `SL(2, 𝔽₂₃)`. -/
theorem ker_psi24 : psi24.ker = Subgroup.center (SL(2, ZMod 23)) :=
  le_antisymm ker_le_center center_le_ker

/-! ### Assembling the embedding -/

/-- **`PSL(2, 𝔽₂₃) ↪ M₂₄`.** -/
theorem embeds : ∃ f : PSL(2, ZMod 23) →* M24, Function.Injective f := by
  have hmem : ∀ g : SL(2, ZMod 23), psi24 g ∈ M24 := fun g => range_le ⟨g, rfl⟩
  let f0 : SL(2, ZMod 23) →* M24 := psi24.codRestrict M24 hmem
  have hkerf0 : f0.ker = Subgroup.center (SL(2, ZMod 23)) := by
    rw [show f0 = psi24.codRestrict M24 hmem from rfl, MonoidHom.ker_codRestrict, ker_psi24]
  refine ⟨(QuotientGroup.kerLift f0).comp
      (QuotientGroup.quotientMulEquivOfEq hkerf0.symm).toMonoidHom, ?_⟩
  exact (QuotientGroup.kerLift_injective f0).comp
    (QuotientGroup.quotientMulEquivOfEq hkerf0.symm).injective

end PSL223

end Mathieu