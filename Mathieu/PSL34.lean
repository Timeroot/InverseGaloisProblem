import Mathieu.ProjF4
import Mathieu.Subgroups
import Mathieu.EnumSL34
import Mathieu.M22Cycles

/-!
# `PSL(3, 4) ↪ M₂₁` (indeed `PSL(3,4) ≅ M₂₁`)

Building on `ProjF4.lean`, which constructs the computable projective plane `PG(2, 4)` with the
action homomorphism `psi34 : SL(3, F4) →* Perm (Fin 23)` (the plane action on the `21` points,
extended by the identity on `21, 22`), we assemble the injective homomorphism

  `PSL(3, GaloisField 2 2) →* M₂₁`.

There are three ingredients:

* **Faithfulness modulo the centre** (`ker_psiP`, `ker_psi34`): the kernel of the plane action
  is exactly the centre of `SL(3, F4)` (the scalar matrices).  `center ≤ ker` because a scalar
  matrix acts trivially on projective points; `ker ≤ center` because a matrix fixing every
  projective point sends every vector to a scalar multiple of itself, hence is scalar.
* **Image containment** (`range_psi34_le_M21`): every `psi34 g` lies in `M₂₁`.  This is the deep
  computational half, matching the images of the `SL(3, F4)` generators against `M₂₁`.
* **Transport of the base field** (`mapEquiv`): `GaloisField 2 2 ≃+* F4` (`F4.equivGaloisField`)
  induces `SL(3, GaloisField 2 2) ≃* SL(3, F4)`, so the embedding phrased over `F4` transfers to
  the Mathlib group `PSL(3, GaloisField 2 2)`.

Quotienting by the centre assembles the embedding `PSL(3, GaloisField 2 2) ↪ M₂₁`.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL34

set_option maxRecDepth 4000

/-! ### Transport of the base field along a ring isomorphism -/

/-- A ring isomorphism `R ≃+* S` induces `SL(n, R) ≃* SL(n, S)`. -/
def mapEquiv {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : SpecialLinearGroup n R ≃* SpecialLinearGroup n S where
  toFun := SpecialLinearGroup.map (e : R →+* S)
  invFun := SpecialLinearGroup.map (e.symm : S →+* R)
  left_inv g := by ext i j; simp [SpecialLinearGroup.map]
  right_inv g := by ext i j; simp [SpecialLinearGroup.map]
  map_mul' := map_mul _

/-- The centre is preserved (as a subgroup) by comap along a group isomorphism. -/
theorem comap_center_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    Subgroup.comap φ.toMonoidHom (Subgroup.center H) = Subgroup.center G := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h y
    have := h (φ y)
    apply φ.injective
    simp only [map_mul] at *
    rw [this]
  · intro h y
    obtain ⟨z, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, h]

/-! ### Faithfulness modulo the centre -/

/-
A matrix fixing every projective point is scalar: if `g ∈ ker psiP` then `g` is central.
-/
theorem ker_psiP_le_center : psiP.ker ≤ Subgroup.center (SL(3, F4)) := by
  intro g hg; simp_all +decide [ Subgroup.mem_center_iff ] ;
  -- Since $g$ is in the kernel of $\psi_P$, it fixes every projective point. Therefore, for any $v \in \mathbb{F}_4^3 \setminus \{0\}$, we have $g \cdot v = \lambda v$ for some $\lambda \in \mathbb{F}_4^\times$.
  have h_fix : ∀ v : Fin 3 → F4, v ≠ 0 → ∃ lambda : F4, lambda ≠ 0 ∧ (g.val *ᵥ v) = lambda • v := by
    intro v hv_nonzero
    have h_fix : nrm (g.val *ᵥ v) = nrm v := by
      convert congr_arg Subtype.val ( congr_arg ( fun f => f ⟨ nrm v, nrm_isPt v hv_nonzero ⟩ ) hg ) using 1;
      simp +decide [ psiP, smul_def ];
      rw [ nrm_eq_smul v ];
      rw [ Matrix.mulVec_smul, nrm_smul ];
      exact inv_ne_zero ( leadIdx_spec v hv_nonzero );
    rw [ nrm_eq_smul, nrm_eq_smul ] at h_fix;
    refine' ⟨ ( v ( leadIdx v ) ) ⁻¹ / ( ( g.val *ᵥ v ) ( leadIdx ( g.val *ᵥ v ) ) ) ⁻¹, _, _ ⟩;
    · exact div_ne_zero ( inv_ne_zero ( leadIdx_spec v hv_nonzero ) ) ( inv_ne_zero ( leadIdx_spec _ ( mulVec_ne_zero g v hv_nonzero ) ) );
    · convert congr_arg ( fun x => ( ( g.val *ᵥ v ) ( leadIdx ( g.val *ᵥ v ) ) ) ⁻¹⁻¹ • x ) h_fix using 1 <;> norm_num [ div_eq_inv_mul, smul_smul ];
      rw [ mul_inv_cancel₀ ( leadIdx_spec _ ( mulVec_ne_zero g v hv_nonzero ) ), one_smul ];
  -- Since $g$ fixes every projective point, it must be a scalar matrix.
  have h_scalar : ∃ lambda : F4, g.val = Matrix.scalar (Fin 3) lambda := by
    have h_scalar : ∀ i j : Fin 3, i ≠ j → g.val i j = 0 := by
      intro i j hij; obtain ⟨ lambda, hlambda, h ⟩ := h_fix ( Pi.single j 1 ) ( by fin_cases j <;> simp +decide ) ; replace h := congr_fun h i ; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      simp_all +decide [ Pi.single_apply ];
    have h_diag : ∃ lambda : F4, g.val 0 0 = lambda ∧ g.val 1 1 = lambda ∧ g.val 2 2 = lambda := by
      obtain ⟨lambda₁, hlambda₁⟩ := h_fix ( ![1, 1, 0] ) ( by decide )
      obtain ⟨lambda₂, hlambda₂⟩ := h_fix ( ![1, 0, 1] ) ( by decide )
      obtain ⟨lambda₃, hlambda₃⟩ := h_fix ( ![0, 1, 1] ) ( by decide );
      simp_all +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec ];
      simp_all +decide [ vecHead, vecTail ];
    obtain ⟨lambda, hlambda⟩ := h_diag; use lambda; ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ * ] ;
  obtain ⟨lambda, hlambda⟩ := h_scalar
  have h_det : lambda ^ 3 = 1 := by
    have := g.2; aesop;
  have h_center : g ∈ Subgroup.center (SL(3, F4)) := by
    rw [ Subgroup.mem_center_iff ] ; intro h ; ext i j ; simp +decide [ hlambda, Matrix.mul_apply, Matrix.diagonal ] ; ring;
  exact fun g_1 => h_center.comm g_1 |> Eq.symm

/-
Scalar (central) matrices act trivially on projective points.
-/
theorem center_le_ker_psiP : Subgroup.center (SL(3, F4)) ≤ psiP.ker := by
  intro g hg;
  obtain ⟨r, hr⟩ : ∃ r : F4, r ^ 3 = 1 ∧ (Matrix.scalar (Fin 3)) r = g.val := by
    convert Matrix.SpecialLinearGroup.mem_center_iff.mp hg;
  ext p;
  refine' Subtype.ext _;
  convert PSL34.nrm_smul r ( show r ≠ 0 from by aesop_cat ) p.1 using 1;
  · convert PSL34.smul_def g p using 1;
    simp +decide [ ← hr.2 ];
  · exact p.2.2.symm

/-- The kernel of the plane action is exactly the centre of `SL(3, F4)`. -/
theorem ker_psiP : psiP.ker = Subgroup.center (SL(3, F4)) :=
  le_antisymm ker_psiP_le_center center_le_ker_psiP

/-
`psi34` and `psiP` have the same kernel (`psi34` is `psiP` composed with two injective
transports: `permCongrHom` of `eP.symm` and `extendDomainHom` of `incl21`).
-/
theorem ker_psi34_eq_ker_psiP : psi34.ker = psiP.ker := by
  apply le_antisymm;
  · intro g hg;
    simp_all +decide [ MonoidHom.mem_ker, PSL34.psi34, PSL34.psi21, PSL34.psiP ];
    ext x; replace hg := congr_arg ( fun f => f ( eP.symm x ) ) hg; aesop;
  · intro g hg;
    simp_all +decide [ PSL34.psi34, PSL34.psi21 ]

/-- The kernel of the full action `psi34` is exactly the centre of `SL(3, F4)`. -/
theorem ker_psi34 : psi34.ker = Subgroup.center (SL(3, F4)) :=
  ker_psi34_eq_ker_psiP.trans ker_psiP

/-! ### Image containment (the computational half)

We pin the image down through three explicit generators of `SL(3, F4)`:
* `g1 = t₁₂(1)` (an elementary transvection),
* `g2 = t₁₂(ω)` (a transvection with the field generator `ω = ⟨0,1⟩`),
* `g3` the cyclic coordinate permutation `e₀ ↦ e₁ ↦ e₂ ↦ e₀`.

These generate `SL(3, F4)` (`closure_gens34_eq_top`).

**Caveat on the labelling.**  The plane action `psi34` is built from an *arbitrary* labelling
`eP : Fin 21 ≃ P` of the projective points.  Consequently `psi34.range` is only a *conjugate*
copy of `M₂₁` inside `Sym (Fin 23)`, not `M₂₁` on the nose (indeed the raw generator images do
**not** lie in `M₂₂`).  Both `psi34.range` and `M₂₁` are `2`-transitive `PSL(3,4)`-subgroups of
`Sym (Fin 23)` acting on the same `21` points, hence they are conjugate; a relabelling
permutation `σ` conjugates one onto the other.  We therefore build the embedding from the
*conjugated* action `g ↦ σ · psi34 g · σ⁻¹`.  The existence of a suitable `σ`
(`exists_conjugator_gens`) is the remaining geometric input; see `PLAN.md`. -/

open EnumSL34 (g1 g2 g3)

/-- The chosen generating set of `SL(3, F4)` (the three matrices `g1, g2, g3` of
`EnumSL34.lean`). -/
def gens34 : List (SL(3, F4)) := [g1, g2, g3]

/-- **`{g1, g2, g3}` generate `SL(3, F4)`.**  Proved in `EnumSL34.lean` by an integer-encoded
breadth-first enumeration of the closure. -/
theorem closure_gens34_eq_top :
    Subgroup.closure ({g1, g2, g3} : Set (SL(3, F4))) = ⊤ :=
  EnumSL34.closure_eq_top

/-- Each generator image fixes the point `21` (`psi34` fixes `21, 22` by construction). -/
theorem psi34_gen_fixes_21 : ∀ g ∈ gens34, psi34 g (21 : Fin 23) = 21 := by
  decide

/-- The explicit relabelling permutation `σ`, found as a line-design isomorphism of the
projective plane `PG(2,4)` between the arbitrary labelling used by `psi34` and the labelling of
`M₂₁`.  It fixes `0, 1, 9` (and `21, 22`), with the two nontrivial cycles below. -/
def sigmaPerm : Perm (Fin 23) :=
  c[2,3,12,10,6,11,16,19,7,14,4,15,5] * c[8,20,13,17,18]

/-- The conjugated image of `g1` written as a word in the `M₂₂` Schreier generators `schB`. -/
def w1 : Perm (Fin 23) :=
  (EnumM22.schB 7)⁻¹ * EnumM22.schB 1 * EnumM22.schB 1 * EnumM22.schB 7 *
    (EnumM22.schB 2)⁻¹ * (EnumM22.schB 7)⁻¹ * EnumM22.schB 1

/-- The conjugated image of `g2` written as a word in the `M₂₂` Schreier generators `schB`. -/
def w2 : Perm (Fin 23) :=
  EnumM22.schB 2 * EnumM22.schB 1 * EnumM22.schB 1 * EnumM22.schB 13 *
    (EnumM22.schB 7)⁻¹ * (EnumM22.schB 13)⁻¹ * EnumM22.schB 2 * (EnumM22.schB 7)⁻¹

/-- The conjugated image of `g3` written as a word in the `M₂₂` Schreier generators `schB`. -/
def w3 : Perm (Fin 23) :=
  EnumM22.schB 2 * EnumM22.schB 2 * (EnumM22.schB 7)⁻¹ * (EnumM22.schB 1)⁻¹ *
    (EnumM22.schB 1)⁻¹ * (EnumM22.schB 13)⁻¹ * EnumM22.schB 2

private lemma w1_mem_M22 : w1 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (inv_mem (EnumM22.schB_mem_M22 7)) (EnumM22.schB_mem_M22 1)) (EnumM22.schB_mem_M22 1))
    (EnumM22.schB_mem_M22 7)) (inv_mem (EnumM22.schB_mem_M22 2)))
    (inv_mem (EnumM22.schB_mem_M22 7))) (EnumM22.schB_mem_M22 1)

private lemma w2_mem_M22 : w2 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (EnumM22.schB_mem_M22 2) (EnumM22.schB_mem_M22 1)) (EnumM22.schB_mem_M22 1))
    (EnumM22.schB_mem_M22 13)) (inv_mem (EnumM22.schB_mem_M22 7)))
    (inv_mem (EnumM22.schB_mem_M22 13))) (EnumM22.schB_mem_M22 2))
    (inv_mem (EnumM22.schB_mem_M22 7))

private lemma w3_mem_M22 : w3 ∈ M22 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (EnumM22.schB_mem_M22 2) (EnumM22.schB_mem_M22 2)) (inv_mem (EnumM22.schB_mem_M22 7)))
    (inv_mem (EnumM22.schB_mem_M22 1))) (inv_mem (EnumM22.schB_mem_M22 1)))
    (inv_mem (EnumM22.schB_mem_M22 13))) (EnumM22.schB_mem_M22 2)

set_option maxRecDepth 100000 in
/-- The conjugated image of `g1` is the explicit word `w1`.  Kernel-checkable (avoiding
`native_decide`): reduce `psi34 g1` and `w1` to explicit disjoint-cycle form first (the latter
via the `schB` cycle lemmas of `M22Cycles`), then the conjugation is a shallow `decide`. -/
theorem conj_psi34_g1_eq_w1 : (MulAut.conj sigmaPerm) (psi34 g1) = w1 := by
  have hpsi : psi34 g1 =
      c[1,9]*c[2,10]*c[3,11]*c[4,12]*c[13,17]*c[14,19]*c[15,20]*c[16,18] := by decide
  have hw : w1 = c[1,9]*c[3,6]*c[4,7]*c[5,13]*c[8,19]*c[10,15]*c[12,16]*c[17,18] := by
    unfold w1; rw [schB1_eq, schB2_eq, schB7_eq]; decide
  rw [hpsi, hw]; decide

set_option maxRecDepth 100000 in
/-- The conjugated image of `g2` is the explicit word `w2`. -/
theorem conj_psi34_g2_eq_w2 : (MulAut.conj sigmaPerm) (psi34 g2) = w2 := by
  have hpsi : psi34 g2 =
      c[1,17]*c[2,20]*c[3,18]*c[4,19]*c[9,13]*c[10,15]*c[11,16]*c[12,14] := by decide
  have hw : w2 = c[1,18]*c[3,13]*c[4,10]*c[5,6]*c[7,15]*c[8,12]*c[9,17]*c[16,19] := by
    unfold w2; rw [schB1_eq, schB2_eq, schB7_eq, schB13_eq]; decide
  rw [hpsi, hw]; decide

set_option maxRecDepth 100000 in
/-- The conjugated image of `g3` is the explicit word `w3`. -/
theorem conj_psi34_g3_eq_w3 : (MulAut.conj sigmaPerm) (psi34 g3) = w3 := by
  have hpsi : psi34 g3 =
      c[0,5,1]*c[2,6,9]*c[3,8,13]*c[4,7,17]*c[11,20,14]*c[12,15,18] := by decide
  have hw : w3 = c[0,2,1]*c[3,11,9]*c[4,16,13]*c[5,8,10]*c[12,20,17]*c[14,18,15] := by
    unfold w3; rw [schB1_eq, schB2_eq, schB7_eq, schB13_eq]; decide
  rw [hpsi, hw]; decide

/-- **There is a relabelling `σ` under which the three generator images land in `M₂₁`.**

This is the remaining geometric content of `M₂₁ ≅ PSL(3,4)`.  `psi34.range` and `M₂₁` are both
`2`-transitive `PSL(3,4)`-subgroups of `Sym (Fin 23)` on the same `21` points, hence conjugate;
`σ = sigmaPerm` is the conjugating (relabelling) permutation, obtained as a line-design
isomorphism of `PG(2,4)`.  For each generator, the conjugated image is exhibited as an explicit
word (`w1, w2, w3`) in the `M₂₂` Schreier generators (`conj_psi34_gᵢ_eq_wᵢ`, kernel `decide`),
hence lies in `M₂₂`; it fixes `21` (kernel `decide`), hence lies in `M₂₁`. -/
theorem exists_conjugator_gens :
    ∃ σ : Perm (Fin 23), ∀ g ∈ gens34, (MulAut.conj σ) (psi34 g) ∈ M21 := by
  refine ⟨sigmaPerm, ?_⟩
  intro g hg
  simp only [gens34, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hstab : ∀ g : SL(3, F4), (MulAut.conj sigmaPerm) (psi34 g) (21 : Fin 23) = 21 →
      (MulAut.conj sigmaPerm) (psi34 g) ∈ MulAction.stabilizer (Perm (Fin 23)) (21 : Fin 23) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; exact hg
  rcases hg with rfl | rfl | rfl
  · have hm : (MulAut.conj sigmaPerm) (psi34 g1) ∈ M22 := by
      rw [conj_psi34_g1_eq_w1]; exact w1_mem_M22
    exact ⟨hm, hstab g1 (by decide)⟩
  · have hm : (MulAut.conj sigmaPerm) (psi34 g2) ∈ M22 := by
      rw [conj_psi34_g2_eq_w2]; exact w2_mem_M22
    exact ⟨hm, hstab g2 (by decide)⟩
  · have hm : (MulAut.conj sigmaPerm) (psi34 g3) ∈ M22 := by
      rw [conj_psi34_g3_eq_w3]; exact w3_mem_M22
    exact ⟨hm, hstab g3 (by decide)⟩

/-- **The conjugated action lands in `M₂₁` on all of `SL(3, F4)`.**  Extends
`exists_conjugator_gens` from the generators to the whole group using
`closure_gens34_eq_top`. -/
theorem exists_conjugator_into_M21 :
    ∃ σ : Perm (Fin 23), ∀ g : SL(3, F4), (MulAut.conj σ) (psi34 g) ∈ M21 := by
  obtain ⟨σ, hσ⟩ := exists_conjugator_gens
  refine ⟨σ, ?_⟩
  have hsub : (⊤ : Subgroup (SL(3, F4)))
      ≤ Subgroup.comap (((MulAut.conj σ).toMonoidHom).comp psi34) M21 := by
    rw [← closure_gens34_eq_top, Subgroup.closure_le]
    rintro x hx
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact hσ g1 (by simp [gens34])
    · exact hσ g2 (by simp [gens34])
    · exact hσ g3 (by simp [gens34])
  intro g
  have := hsub (Subgroup.mem_top g)
  simpa only [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using this

/-! ### Assembling the embedding over `GaloisField 2 2` -/

/-- Transport `SL(3, GaloisField 2 2) ≃* SL(3, F4)` from `F4.equivGaloisField`. -/
noncomputable def phiSL : SL(3, GaloisField 2 2) ≃* SL(3, F4) :=
  mapEquiv (F4.equivGaloisField.symm)

/-- The plane action pulled back to `SL(3, GaloisField 2 2)`. -/
noncomputable def psi34GF : SL(3, GaloisField 2 2) →* Perm (Fin 23) :=
  psi34.comp phiSL.toMonoidHom

/-- The kernel of the pulled-back action is the centre of `SL(3, GaloisField 2 2)`. -/
theorem ker_psi34GF : psi34GF.ker = Subgroup.center (SL(3, GaloisField 2 2)) := by
  have hcomp : psi34GF.ker = Subgroup.comap phiSL.toMonoidHom psi34.ker := by
    ext x
    simp only [MonoidHom.mem_ker, psi34GF, MonoidHom.comp_apply, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom]
  rw [hcomp, ker_psi34, comap_center_eq]

/-- The conjugated pulled-back action `g ↦ σ · psi34GF g · σ⁻¹`, for a fixed relabelling `σ`
taken from `exists_conjugator_into_M21`. -/
noncomputable def cpsiGF (σ : Perm (Fin 23)) : SL(3, GaloisField 2 2) →* Perm (Fin 23) :=
  ((MulAut.conj σ).toMonoidHom).comp psi34GF

/-- The conjugated action has the same kernel (the centre), since conjugation is injective. -/
theorem ker_cpsiGF (σ : Perm (Fin 23)) :
    (cpsiGF σ).ker = Subgroup.center (SL(3, GaloisField 2 2)) := by
  have hinj : Function.Injective ((MulAut.conj σ).toMonoidHom) := (MulAut.conj σ).injective
  have hker : (cpsiGF σ).ker = psi34GF.ker := by
    ext x
    constructor
    · intro h
      simp only [cpsiGF, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
      exact MonoidHom.mem_ker.mpr (hinj (by rw [map_one]; exact h))
    · intro h
      simp only [cpsiGF, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [MonoidHom.mem_ker.mp h, map_one]
  rw [hker, ker_psi34GF]

/-- **`PSL(3, 4) ↪ M₂₁`.** There is an injective homomorphism `PSL(3, GaloisField 2 2) →* M₂₁`. -/
theorem embeds : ∃ f : PSL(3, GaloisField 2 2) →* M21, Function.Injective f := by
  obtain ⟨σ, hσ⟩ := exists_conjugator_into_M21
  have hmem : ∀ g : SL(3, GaloisField 2 2), cpsiGF σ g ∈ M21 := by
    intro g
    have := hσ (phiSL g)
    simpa only [cpsiGF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, psi34GF] using this
  let f0 : SL(3, GaloisField 2 2) →* M21 := (cpsiGF σ).codRestrict M21 hmem
  have hkerf0 : f0.ker = Subgroup.center (SL(3, GaloisField 2 2)) := by
    rw [show f0 = (cpsiGF σ).codRestrict M21 hmem from rfl, MonoidHom.ker_codRestrict,
      ker_cpsiGF]
  refine ⟨(QuotientGroup.kerLift f0).comp
      (QuotientGroup.quotientMulEquivOfEq hkerf0.symm).toMonoidHom, ?_⟩
  exact (QuotientGroup.kerLift_injective f0).comp
    (QuotientGroup.quotientMulEquivOfEq hkerf0.symm).injective

end PSL34

end Mathieu