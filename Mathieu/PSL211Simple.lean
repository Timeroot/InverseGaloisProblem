import Mathieu.SL211Perfect

/-!
# Simplicity of `PSL(2, 𝔽₁₁)` (native_decide-free route)

This file develops the classical proof that `PSL(2, 𝔽₁₁)` is a **simple group**, via Mathlib's
Iwasawa criterion `MulAction.IwasawaStructure.isSimpleGroup` applied to the action of
`PSL(2, 𝔽₁₁)` on the projective line `ℙ¹(𝔽₁₁)` (`12` points).

This is the group needed as the point stabiliser in the exceptional `12`-point action of `M₁₁`;
its simplicity is the linchpin of the `native_decide`-free simplicity proof for `M₁₁`
(see `PLAN.md`).

## Structure of the argument

* `V = Fin 2 → 𝔽₁₁`, `P1 = ℙ¹(𝔽₁₁) = Projectivization 𝔽₁₁ V` (`12` points).
* `SL(2, 𝔽₁₁)` acts on `P1` through `SL → GL → LinearMap.GL` (`actSL`).
* The action factors through the centre, giving an action of `PSL = SL ⧸ center` on `P1`
  (`actPSL`).
* **Faithfulness** (`faithfulPSL`): the kernel of `SL → Perm P1` is exactly the centre.
* **Quasi-preprimitivity**: `PSL` acts `2`-transitively on `P1`, hence preprimitively.
* **Perfectness** (`perfectPSL`): `commutator PSL = ⊤` (image of `SL`'s perfectness).
* **Iwasawa structure** (`iwa`): the root (unipotent) subgroups fixing each point.
* Assemble via `IwasawaStructure.isSimpleGroup`.

All pieces of this argument are proved; remaining project-wide computational cleanup is tracked
in `PLAN.md` and `NATIVE_DECIDE_STATUS.md`.
-/

namespace Mathieu

open Matrix MulAction
open scoped MatrixGroups Pointwise
open Projectivization

namespace PSL211S

/-- `11` is prime (needed for `ZMod 11` to be a field). -/
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- The `2`-dimensional `𝔽₁₁`-vector space. -/
abbrev V := Fin 2 → ZMod 11

/-- The projective line `ℙ¹(𝔽₁₁)` — `12` points. -/
abbrev P1 := Projectivization (ZMod 11) V

/-- `SL(2, 𝔽₁₁)` as invertible linear maps of `V`. -/
noncomputable def slToLinGL : SL(2, ZMod 11) →* LinearMap.GeneralLinearGroup (ZMod 11) V :=
  (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL)

/-- The action of `SL(2, 𝔽₁₁)` on the projective line. -/
noncomputable instance actSL : MulAction (SL(2, ZMod 11)) P1 := MulAction.compHom P1 slToLinGL

noncomputable instance : Fintype P1 := Fintype.ofFinite P1

/-- The projective line has `12` points. -/
theorem card_P1 : Nat.card P1 = 12 := by
  have := Projectivization.card_of_finrank (ZMod 11) V (n := 2)
    (by simp [Module.finrank_fintype_fun_eq_card])
  simpa [Finset.sum_range_succ, ZMod.card] using this

/-- How the `SL`-action computes on a representative: `g` sends the line spanned by `v` to the
line spanned by `g.mulVec v`. -/
theorem actSL_mk (g : SL(2, ZMod 11)) (v : V) (hv : v ≠ 0) (hv' : g.1.mulVec v ≠ 0) :
    g • Projectivization.mk (ZMod 11) v hv = Projectivization.mk (ZMod 11) (g.1.mulVec v) hv' := by
  show slToLinGL g • Projectivization.mk (ZMod 11) v hv = _
  rw [Projectivization.generalLinearGroup_smul_def, Projectivization.map_mk]
  have : (slToLinGL g).toLinearEquiv v = g.1.mulVec v := by
    simp [slToLinGL, Matrix.GeneralLinearGroup.toLin, Matrix.SpecialLinearGroup.toGL]
  refine (Projectivization.mk_eq_mk_iff (ZMod 11) _ _ _ _).mpr ⟨1, ?_⟩
  simpa using this.symm

/-- The permutation representation of `SL(2, 𝔽₁₁)` on the projective line. -/
noncomputable def slPerm : SL(2, ZMod 11) →* Equiv.Perm P1 :=
  MulAction.toPermHom (SL(2, ZMod 11)) P1

/-- `PSL(2, 𝔽₁₁) = SL(2, 𝔽₁₁) ⧸ Z`. -/
abbrev PSL := SL(2, ZMod 11) ⧸ Subgroup.center (SL(2, ZMod 11))

/-
**The centre acts trivially on the projective line** (scalar matrices fix every line).
-/
theorem center_le_slPerm_ker : Subgroup.center (SL(2, ZMod 11)) ≤ slPerm.ker := by
  intro g hg; have := Subgroup.mem_center_iff.mp hg; simp_all +decide [ MonoidHom.mem_ker ] ;
  -- By `Matrix.SpecialLinearGroup.mem_center_iff`, there is `r : ZMod 11` with `r ^ (Fintype.card (Fin 2)) = 1` and `(Matrix.scalar (Fin 2)) r = ↑g` (so `g` is the scalar matrix `r • I`).
  obtain ⟨r, hr1, hrA⟩ : ∃ r : ZMod 11, r ^ 2 = 1 ∧ (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) (ZMod 11)) = g.1 := by
    have := Matrix.SpecialLinearGroup.mem_center_iff.mp hg; aesop;
  ext x; simp +decide [ slPerm ] ;
  induction x using Projectivization.ind;
  rw [ actSL_mk ];
  all_goals rename_i v hv; simp_all +decide [ ← hrA, funext_iff, Fin.forall_fin_two ] ;
  all_goals rcases hr1 with ( rfl | rfl ) <;> simp_all +decide [ Projectivization.mk_eq_mk_iff ] ;
  exact ⟨ -1, by simp +decide ⟩

/-- The descended permutation representation of `PSL(2, 𝔽₁₁)`. -/
noncomputable def pslPerm : PSL →* Equiv.Perm P1 :=
  QuotientGroup.lift _ slPerm center_le_slPerm_ker

/-- The action of `PSL(2, 𝔽₁₁)` on the projective line. -/
noncomputable instance actPSL : MulAction PSL P1 := MulAction.compHom P1 pslPerm

/-
**Faithfulness**: an element of `SL(2, 𝔽₁₁)` fixing every point of the projective line is
central, so the kernel of `slPerm` is exactly the centre, and `PSL` acts faithfully.
-/
theorem slPerm_ker_le_center : slPerm.ker ≤ Subgroup.center (SL(2, ZMod 11)) := by
  intro g hg;
  -- Since $g$ is in the kernel of $slPerm$, it fixes every point of the projective line. This implies that $g$ is a scalar matrix.
  have h_scalar : ∃ r : ZMod 11, g.1 = Matrix.scalar (Fin 2) r := by
    have h_scalar : ∀ v : V, v ≠ 0 → ∃ r : ZMod 11, g.1.mulVec v = r • v := by
      intro v hv
      have h_eq : Projectivization.mk (ZMod 11) (g.1.mulVec v) (by
      have := g.2;
      exact fun h => hv <| by simpa [ this ] using congr_arg ( fun w => ( g : Matrix ( Fin 2 ) ( Fin 2 ) ( ZMod 11 ) ) ⁻¹.mulVec w ) h;) = Projectivization.mk (ZMod 11) v hv := by
        convert congr_arg ( fun x : Equiv.Perm P1 => x ( Projectivization.mk ( ZMod 11 ) v hv ) ) hg using 1
      generalize_proofs at *;
      rw [ Projectivization.mk_eq_mk_iff ] at h_eq;
      tauto;
    obtain ⟨ r₀, hr₀ ⟩ := h_scalar ( Pi.single 0 1 ) ( ne_of_apply_ne ( fun v => v 0 ) ( by simp +decide ) ) ; obtain ⟨ r₁, hr₁ ⟩ := h_scalar ( Pi.single 1 1 ) ( ne_of_apply_ne ( fun v => v 1 ) ( by simp +decide ) ) ; simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_two ] ;
    obtain ⟨ r₂, hr₂ ⟩ := h_scalar ( Pi.single 0 1 + Pi.single 1 1 ) ( ne_of_apply_ne ( fun v => v 0 ) ( by simp +decide ) ) ; simp_all +decide [ funext_iff, Fin.forall_fin_two, Matrix.mulVec ] ;
  obtain ⟨ r, hr ⟩ := h_scalar; simp_all +decide [ Matrix.SpecialLinearGroup.mem_center_iff ] ;
  have := g.2; simp_all +decide [ ] ;

instance faithfulPSL : FaithfulSMul PSL P1 := by
  -- To prove faithfulness, we show that the kernel of `pslPerm` is trivial.
  have h_kernel_trivial : MonoidHom.ker pslPerm = ⊥ := by
    convert Subgroup.eq_bot_iff_forall _ |>.mpr _;
    intro x hx; obtain ⟨ g, rfl ⟩ := QuotientGroup.mk_surjective x; simp_all +decide [ MonoidHom.mem_ker ] ;
    exact slPerm_ker_le_center ( by simpa [ pslPerm ] using hx );
  refine' ⟨ fun { g h } hgh => _ ⟩;
  rw [ MonoidHom.ker_eq_bot_iff ] at h_kernel_trivial;
  exact h_kernel_trivial <| Equiv.ext fun x => by simpa using hgh x;

/-
Two nonzero vectors span the same line iff the determinant of the matrix with those columns
vanishes; contrapositive form used below.
-/
theorem det_ne_of_mk_ne (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk (ZMod 11) v hv ≠ Projectivization.mk (ZMod 11) w hw) :
    v 0 * w 1 - v 1 * w 0 ≠ 0 := by
  intro hdet
  apply h
  rw [Projectivization.mk_eq_mk_iff]
  have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hw (funext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  rcases hw' with hw0 | hw1
  · have hv0 : v 0 ≠ 0 := by
      intro h0; apply hv; funext i; fin_cases i
      · exact h0
      · have : v 1 * w 0 = 0 := by rw [h0] at hdet; linear_combination -hdet
        exact (mul_eq_zero.mp this).resolve_right hw0
    have c0 : (v 0 / w 0) * w 0 = v 0 := by field_simp
    have c1 : (v 0 / w 0) * w 1 = v 1 := by
      rw [div_mul_eq_mul_div, div_eq_iff hw0]; linear_combination hdet
    refine ⟨Units.mk0 (v 0 / w 0) (div_ne_zero hv0 hw0), funext (fun i => ?_)⟩
    fin_cases i <;> simp only [Units.smul_def, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
    · exact c0
    · exact c1
  · have hv1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i
      · have : v 0 * w 1 = 0 := by rw [h1] at hdet; linear_combination hdet
        exact (mul_eq_zero.mp this).resolve_right hw1
      · exact h1
    have c0 : (v 1 / w 1) * w 0 = v 0 := by
      rw [div_mul_eq_mul_div, div_eq_iff hw1]; linear_combination -hdet
    have c1 : (v 1 / w 1) * w 1 = v 1 := by field_simp
    refine ⟨Units.mk0 (v 1 / w 1) (div_ne_zero hv1 hw1), funext (fun i => ?_)⟩
    fin_cases i <;> simp only [Units.smul_def, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
    · exact c0
    · exact c1

/-
**Reachability of an arbitrary ordered pair of distinct lines from the standard pair.**
-/
theorem exists_sl_map (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hd : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ∃ g : SL(2, ZMod 11),
      g • Projectivization.mk (ZMod 11) (![1, 0] : V) (by decide)
          = Projectivization.mk (ZMod 11) v hv ∧
      g • Projectivization.mk (ZMod 11) (![0, 1] : V) (by decide)
          = Projectivization.mk (ZMod 11) w hw := by
  let d : ZMod 11 := v 0 * w 1 - v 1 * w 0
  let g : Matrix (Fin 2) (Fin 2) (ZMod 11) :=
    Matrix.of ![![v 0, d⁻¹ * w 0], ![v 1, d⁻¹ * w 1]]
  have hgdet : g.det = 1 := by
    simp +decide [g, d, Matrix.det_fin_two]
    field_simp
  have hg0 : g.mulVec ![1, 0] = v := by
    ext i
    fin_cases i <;> simp [g, Matrix.mulVec, dotProduct]
  have hg1 : g.mulVec ![0, 1] = d⁻¹ • w := by
    ext i
    fin_cases i <;> simp [g, Matrix.mulVec, dotProduct, Pi.smul_apply]
  let gs : SL(2, ZMod 11) := ⟨g, hgdet⟩
  have hgs0 : gs.1.mulVec ![1, 0] ≠ 0 := by
    rw [show gs.1.mulVec ![1, 0] = v by simpa [gs] using hg0]
    exact hv
  have hgs1_eq : gs.1.mulVec ![0, 1] = d⁻¹ • w := by simpa [gs] using hg1
  have hdinv : d⁻¹ ≠ 0 := inv_ne_zero (by simpa [d] using hd)
  have hgs1 : gs.1.mulVec ![0, 1] ≠ 0 := by
    rw [hgs1_eq]
    exact smul_ne_zero hdinv hw
  refine ⟨gs, ?_, ?_⟩
  · rw [actSL_mk gs _ _ hgs0]
    apply (Projectivization.mk_eq_mk_iff (ZMod 11) _ _ _ _).2
    exact ⟨1, by simpa [gs] using hg0.symm⟩
  · rw [actSL_mk gs _ _ hgs1]
    apply (Projectivization.mk_eq_mk_iff (ZMod 11) _ _ _ _).2
    exact ⟨Units.mk0 d⁻¹ hdinv, by
      rw [hgs1_eq]
      ext i
      simp [Units.smul_def, Pi.smul_apply]⟩

/-- **`SL(2, 𝔽₁₁)` acts `2`-transitively on the projective line.** -/
instance slTwoTrans : IsMultiplyPretransitive (SL(2, ZMod 11)) P1 2 := by
  have hbase : Projectivization.mk (ZMod 11) (![1, 0] : V) (by decide)
      ≠ Projectivization.mk (ZMod 11) (![0, 1] : V) (by decide) := by
    rw [Ne, Projectivization.mk_eq_mk_iff]
    rintro ⟨a, ha⟩
    have := congrArg (fun f : V => f 0) ha
    simp [Pi.smul_apply] at this
  set p0 := Projectivization.mk (ZMod 11) (![1, 0] : V) (by decide) with hp0
  set p1 := Projectivization.mk (ZMod 11) (![0, 1] : V) (by decide) with hp1
  have hinj : Function.Injective (![p0, p1] : Fin 2 → P1) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p0, p1]
  show IsPretransitive (SL(2, ZMod 11)) (Fin 2 ↪ P1)
  refine (MulAction.isPretransitive_iff_base (⟨![p0, p1], hinj⟩ : Fin 2 ↪ P1)).mpr (fun y => ?_)
  set v := (y 0).rep with hv_def
  set w := (y 1).rep with hw_def
  have hv : v ≠ 0 := (y 0).rep_nonzero
  have hw : w ≠ 0 := (y 1).rep_nonzero
  have hvrep : Projectivization.mk (ZMod 11) v hv = y 0 := (y 0).mk_rep
  have hwrep : Projectivization.mk (ZMod 11) w hw = y 1 := (y 1).mk_rep
  have hmkne : Projectivization.mk (ZMod 11) v hv ≠ Projectivization.mk (ZMod 11) w hw := by
    rw [hvrep, hwrep]; exact fun hh => by simpa using y.injective hh
  obtain ⟨g, hg0, hg1⟩ := exists_sl_map v w hv hw (det_ne_of_mk_ne v w hv hw hmkne)
  refine ⟨g, Function.Embedding.ext (fun i => ?_)⟩
  fin_cases i <;>
    simp only [Function.Embedding.smul_apply, Function.Embedding.coeFn_mk]
  · exact hg0.trans hvrep
  · exact hg1.trans hwrep

/-- **`PSL(2, 𝔽₁₁)` acts `2`-transitively on the projective line** (descends from `SL`). -/
instance twoTransPSL : IsMultiplyPretransitive PSL P1 2 := by
  rw [isMultiplyPretransitive_iff]
  intro x y
  obtain ⟨g, hg⟩ := (isMultiplyPretransitive_iff.mp slTwoTrans) x y
  refine ⟨QuotientGroup.mk g, ?_⟩
  ext i
  have : (QuotientGroup.mk g : PSL) • (x i) = g • (x i) := rfl
  simpa [Function.Embedding.smul_apply, this] using congrArg (fun e => e i) hg

/-
The `PSL(2, 𝔽₁₁)`-action on the projective line is preprimitive.
-/
instance preprimitivePSL : IsPreprimitive PSL P1 :=
  isPreprimitive_of_is_two_pretransitive twoTransPSL

/-
**`PSL(2, 𝔽₁₁)` is perfect** (image of the perfectness of `SL(2, 𝔽₁₁)`).
-/
theorem perfectPSL : commutator PSL = ⊤ := by
  have h_comm : Subgroup.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11))))
      (commutator (SL(2, ZMod 11))) = commutator PSL := by
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rfl
  rw [← h_comm, Mathieu.SL211Gen.commutator_eq_top, Subgroup.map_top_of_surjective]
  exact QuotientGroup.mk'_surjective _

instance : Nontrivial PSL := by
  refine' ⟨ _, _ ⟩;
  exact QuotientGroup.mk ( ⟨ !![1, 1; 0, 1], by decide ⟩ : SL(2, ZMod 11) );
  refine' ⟨ 1, _ ⟩;
  simp +decide [ Subgroup.mem_center_iff ];
  exists ⟨ !![1, 0; 1, 1], by decide ⟩;
  exact ne_of_apply_ne ( fun x => x.1 0 0 ) ( by simp +decide )

/-! ### The root (transvection) subgroups and the Iwasawa structure -/

/-- The transvection matrix with centre the line spanned by `v` and parameter `c`:
`I + c · (v ⊗ φ_v)` where `φ_v = (v₁, -v₀)` is the covector vanishing on `v`. -/
noncomputable def transMat (v : V) (c : ZMod 11) : Matrix (Fin 2) (Fin 2) (ZMod 11) :=
  !![1 + c * (v 0 * v 1), -(c * (v 0 * v 0)); c * (v 1 * v 1), 1 - c * (v 0 * v 1)]

theorem transMat_det (v : V) (c : ZMod 11) : (transMat v c).det = 1 := by
  simp only [transMat, Matrix.det_fin_two_of]; ring

/-- The transvection as an element of `SL(2, 𝔽₁₁)`. -/
noncomputable def transvec (v : V) (c : ZMod 11) : SL(2, ZMod 11) :=
  ⟨transMat v c, transMat_det v c⟩

theorem transvec_zero (v : V) : transvec v 0 = 1 := by
  apply Subtype.ext
  simp only [transvec, transMat, zero_mul, add_zero, sub_zero, neg_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp []

theorem transvec_add (v : V) (c d : ZMod 11) :
    transvec v (c + d) = transvec v c * transvec v d := by
  apply Subtype.ext
  show transMat v (c + d) = transMat v c * transMat v d
  simp only [transMat]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The transvections at a fixed line form a one-parameter (abelian) subgroup: this is the
underlying homomorphism `(𝔽₁₁, +) → SL(2, 𝔽₁₁)`. -/
noncomputable def transvecHom (v : V) : Multiplicative (ZMod 11) →* SL(2, ZMod 11) where
  toFun c := transvec v (Multiplicative.toAdd c)
  map_one' := transvec_zero v
  map_mul' c d := transvec_add v (Multiplicative.toAdd c) (Multiplicative.toAdd d)

/-- The root subgroup of `SL(2, 𝔽₁₁)` attached to the line spanned by `v`. -/
noncomputable def rootSL (v : V) : Subgroup (SL(2, ZMod 11)) := (transvecHom v).range

/-
Conjugating a transvection with centre `v` by `h` yields the transvection with centre
`h · v` and the *same* parameter.
-/
theorem transvec_conj (h : SL(2, ZMod 11)) (v : V) (c : ZMod 11) :
    h * transvec v c * h⁻¹ = transvec (h.1.mulVec v) c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.mul_apply, Matrix.adjugate_fin_two ] <;> ring;
  · simp +decide [ transvec ] ; ring!;
    simp +decide [ Matrix.mulVec, transMat ] ; ring!;
    grind +suggestions;
  · simp +decide [ transvec ];
    simp +decide [ Matrix.mulVec, transMat ] ; ring!;
  · simp +decide [ transvec, transMat ];
    simp +decide [ Matrix.mulVec, dotProduct ] ; ring;
  · simp +decide [ transvec, transMat ] ; ring;
    simp +decide [ Matrix.mulVec, dotProduct ] ; ring;
    grind +suggestions

/-
Scaling the centre vector by `a ≠ 0` reparametrises the transvection.
-/
theorem transvec_smul (v : V) (a c : ZMod 11) :
    transvec (a • v) c = transvec v (a ^ 2 * c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ transvec, transMat ] <;> ring!;

/-
The root subgroup depends only on the line, not on the chosen representative.
-/
theorem rootSL_smul (v : V) (a : ZMod 11) (ha : a ≠ 0) : rootSL (a • v) = rootSL v := by
  apply le_antisymm;
  · intro x hx;
    obtain ⟨ c, rfl ⟩ := hx;
    use Multiplicative.ofAdd (a^2 * Multiplicative.toAdd c);
    convert transvec_smul v a ( Multiplicative.toAdd c ) |> Eq.symm using 1;
  · intro x hx; obtain ⟨ c, rfl ⟩ := hx; simp_all +decide [ rootSL ] ;
    obtain ⟨ k, hk ⟩ := ( show ∃ k : ZMod 11, a ^ 2 * k = c.toAdd from ⟨ c.toAdd * ( a ^ 2 ) ⁻¹, by simp +decide [ ha, mul_comm ] ⟩ ) ; use k; simp_all +decide [ transvecHom, transvec_smul ] ;

/-
`rootSL` depends only on the line, not the chosen representative.
-/
theorem rootSL_line (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : Projectivization.mk (ZMod 11) v hv = Projectivization.mk (ZMod 11) w hw) :
    rootSL v = rootSL w := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod 11, a ≠ 0 ∧ a • w = v := by
    rw [ Projectivization.mk_eq_mk_iff ] at hvw;
    obtain ⟨ a, rfl ⟩ := hvw; use a; aesop;
  rw [ ← ha.2, rootSL_smul ] ; aesop

/-
Conjugation by `h` carries the root subgroup of `v` to that of `h · v`.
-/
theorem rootSL_conj (h : SL(2, ZMod 11)) (v : V) :
    rootSL (h.1.mulVec v) = MulAut.conj h • rootSL v := by
  refine' le_antisymm _ _ <;> norm_num [ rootSL, Subgroup.mem_pointwise_smul_iff_inv_smul_mem ];
  · rintro x ⟨ c, rfl ⟩;
    refine' ⟨ transvecHom v c, _, _ ⟩ <;> simp +decide [ transvecHom, transvec_conj ];
  · intro x hx
    obtain ⟨ y, hy, rfl ⟩ := hx
    simp [transvecHom] at *;
    obtain ⟨ a, rfl ⟩ := hy; use a; simp +decide [ transvec_conj ] ;

/-- The image of `rootSL v` in `PSL(2, 𝔽₁₁)`, attached to a projective point via its rep. -/
noncomputable def rootSubgroup (p : P1) : Subgroup PSL :=
  (rootSL p.rep).map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11))))

theorem rootSubgroup_comm (p : P1) : IsMulCommutative (rootSubgroup p) := by
  constructor;
  constructor;
  simp +decide [ rootSubgroup ];
  simp +decide [ rootSL ];
  simp +decide [ ← QuotientGroup.mk_mul, transvecHom ];
  simp +decide [ ← transvec_add ];
  exact fun a b => by rw [ add_comm ] ;

theorem rootSubgroup_conj (g : PSL) (p : P1) :
    rootSubgroup (g • p) = MulAut.conj g • rootSubgroup p := by
  obtain ⟨ h, rfl ⟩ := QuotientGroup.mk'_surjective _ g;
  have h1 : rootSubgroup (h • p) = (rootSL (h.1.mulVec p.rep)).map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11)))) := by
    have h1 : rootSubgroup (h • p) = (rootSL (h • p).rep).map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11)))) := by
      rfl;
    have h2 : h • p = Projectivization.mk (ZMod 11) (h.1.mulVec p.rep) (by
    exact fun h' => p.rep_nonzero <| by simpa [ h.2 ] using congr_arg ( fun w => ( h : Matrix ( Fin 2 ) ( Fin 2 ) ( ZMod 11 ) ) ⁻¹.mulVec w ) h';) := by
      exact congr_arg _ ( Eq.symm ( Projectivization.mk_rep p ) )
    generalize_proofs at *;
    grind +suggestions;
  have h2 : rootSL (h.1.mulVec p.rep) = MulAut.conj h • rootSL p.rep := by
    convert rootSL_conj h p.rep using 1;
  convert h1 using 1;
  ext; simp [h2, rootSubgroup];
  simp +decide [ Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map ];
  constructor <;> rintro ⟨ x, hx, hx' ⟩;
  · use h * x * h⁻¹; simp_all +decide [ mul_assoc ] ;
  · exact ⟨ _, hx, by aesop ⟩

theorem rootSubgroup_iSup : iSup rootSubgroup = ⊤ := by
  refine' eq_top_iff.mpr _;
  rw [ ← Subgroup.map_top_of_surjective ( QuotientGroup.mk' ( Subgroup.center ( SL(2, ZMod 11) ) ) ) ( QuotientGroup.mk'_surjective _ ) ];
  -- By definition of $rootSubgroup$, we know that $Smat$ and $Tmat$ are in the image of the root subgroup under the quotient map.
  have hSmat : QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11))) (SL211Gen.Smat) ∈ iSup rootSubgroup := by
    have hSmat : SL211Gen.Smat ∈ rootSL (![1, 0] : V) := by
      refine' ⟨ Multiplicative.ofAdd ( -1 ), _ ⟩ ; simp +decide [ SL211Gen.Smat ] ; ring;
      exact Subtype.ext ( by ext i j; fin_cases i <;> fin_cases j <;> simp +decide );
    refine' Subgroup.mem_iSup_of_mem ( Projectivization.mk ( ZMod 11 ) ( ![1, 0] : V ) ( by decide ) ) _;
    refine' Subgroup.mem_map_of_mem _ _;
    convert hSmat using 1;
    exact rootSL_line _ _ _ _ ( Projectivization.mk_rep _ )
  have hTmat : QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11))) (SL211Gen.Tmat) ∈ iSup rootSubgroup := by
    -- By definition of $rootSubgroup$, we know that $Tmat$ is in the image of the root subgroup under the quotient map.
    have hTmat : SL211Gen.Tmat ∈ rootSL (![0, 1] : V) := by
      refine' ⟨ Multiplicative.ofAdd 1, _ ⟩ ; simp +decide [ transvecHom, transvec ];
      exact Subtype.ext <| by ext i j; fin_cases i <;> fin_cases j <;> rfl;
    refine' le_iSup ( fun p : Projectivization ( ZMod 11 ) ( Fin 2 → ZMod 11 ) => Subgroup.map ( QuotientGroup.mk' ( Subgroup.center ( SL(2, ZMod 11) ) ) ) ( rootSL p.rep ) ) ( Projectivization.mk ( ZMod 11 ) ![0, 1] ( by decide ) ) _;
    refine' Subgroup.mem_map_of_mem _ _;
    convert hTmat using 1;
    exact rootSL_line _ _ _ _ ( Projectivization.mk_rep _ );
  rw [ Subgroup.map_le_iff_le_comap ];
  rw [ ← Mathieu.SL211Gen.closure_eq_top ];
  simp_all +decide [ Subgroup.closure_le, Set.insert_subset_iff ]

/-- The Iwasawa structure on the `PSL(2, 𝔽₁₁)`-action on the projective line: the root
(unipotent) subgroups fixing each point. -/
noncomputable def iwa : IwasawaStructure PSL P1 where
  T := rootSubgroup
  is_comm := rootSubgroup_comm
  is_conj := rootSubgroup_conj
  is_generator := rootSubgroup_iSup

/-- **`PSL(2, 𝔽₁₁)` is a simple group.** -/
theorem PSL_isSimpleGroup : IsSimpleGroup PSL := by
  haveI : IsQuasiPreprimitive PSL P1 := (preprimitivePSL).isQuasiPreprimitive
  exact iwa.isSimpleGroup perfectPSL faithfulPSL

end PSL211S

end Mathieu