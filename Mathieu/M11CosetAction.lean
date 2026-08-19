import Mathieu.M11SimpleClean
import Mathieu.M11ExceptionalTrans

/-!
# The twelve-point action of `M₁₁`

The exceptional copy of `PSL(2,11)` in `M₁₁` has index twelve. Hence the left-coset
action gives the natural twelve-point action of `M₁₁`; its distinguished point has exactly
that copy of `PSL(2,11)` as stabilizer. We prove that this action is 3-transitive.
-/

namespace Mathieu
namespace M11CosetAction

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

open MulAction Subgroup Matrix Equiv
open scoped MatrixGroups

/-- The twelve points of the coset action. -/
abbrev Points := ↥M11 ⧸ M11Clean.H

/-- The coset space has twelve points. -/
theorem card_points : Nat.card Points = 12 := by
  rw [← Subgroup.index_eq_card]
  exact M11Clean.H_index

/-- The distinguished point whose stabilizer is the embedded `PSL(2,11)`. -/
def basePoint : Points := (1 : ↥M11)

/-- The embedded copy of `PSL(2,11)` is exactly the stabilizer of the distinguished
point in the twelve-point action. -/
theorem stabilizer_basePoint :
    MulAction.stabilizer ↥M11 basePoint = M11Clean.H := by
  exact MulAction.stabilizer_quotient M11Clean.H

/-- Thus the point stabilizer is isomorphic to `PSL(2,11)`. -/
noncomputable def stabilizerBasePointMulEquivPSL :
    ↥(MulAction.stabilizer ↥M11 basePoint) ≃* (PSL(2, ZMod 11)) :=
  (MulEquiv.subgroupCongr stabilizer_basePoint).trans M11Clean.H_mulEquiv_PSL

/-! ### The outer twist

The exceptional action used to define `M11Clean.H` must be twisted by the nontrivial
diagonal outer automorphism before it agrees with the action on the other eleven cosets.
-/

private def diagTwo : Matrix (Fin 2) (Fin 2) (ZMod 11) := !![2,0;0,1]
private def diagTwoInv : Matrix (Fin 2) (Fin 2) (ZMod 11) := !![6,0;0,1]

/-- Conjugation by `diag(2,1)`, the required outer automorphism of `SL(2,11)`. -/
def outerTwist : SL(2, ZMod 11) →* SL(2, ZMod 11) where
  toFun g := ⟨diagTwo * g.1 * diagTwoInv, by
    rw [Matrix.det_mul, Matrix.det_mul, g.2]
    norm_num [diagTwo, diagTwoInv, Matrix.det_fin_two]
    decide⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  map_mul' g h := by
    apply Subtype.ext
    change diagTwo * (g.1 * h.1) * diagTwoInv =
      (diagTwo * g.1 * diagTwoInv) * (diagTwo * h.1 * diagTwoInv)
    have hi : diagTwoInv * diagTwo = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> decide
    simp only [mul_assoc]
    rw [← mul_assoc diagTwoInv diagTwo, hi, one_mul]

lemma m11a_mem_H : (⟨m11a, m11a_mem⟩ : ↥M11) ∈ M11Clean.H := by
  use QuotientGroup.mk EnumL211.Tmat
  convert PSL211.psi11_Tmat using 1
  exact Subtype.ext_iff

lemma wS_mem_H : (⟨PSL211.wS, PSL211.wS_mem⟩ : ↥M11) ∈ M11Clean.H := by
  use QuotientGroup.mk EnumL211.Smat
  convert PSL211.psi11_Smat using 1
  exact Subtype.ext_iff.trans (by rfl)

/-- A concrete conjugating element inside the exceptional copy of `PSL(2,11)`. -/
def twistConjugatorPerm : Perm (Fin 11) :=
  PSL211.wS⁻¹ * m11a⁻¹ ^ 2 * PSL211.wS⁻¹ * m11a⁻¹ ^ 3

lemma twistConjugatorPerm_mem : twistConjugatorPerm ∈ M11 := by
  unfold twistConjugatorPerm
  exact mul_mem (mul_mem (mul_mem (inv_mem PSL211.wS_mem) (pow_mem (inv_mem m11a_mem) 2))
    (inv_mem PSL211.wS_mem)) (pow_mem (inv_mem m11a_mem) 3)

/-- The conjugating element, regarded as an element of `M11`. -/
def twistConjugator : ↥M11 :=
  (⟨PSL211.wS, PSL211.wS_mem⟩ : ↥M11)⁻¹ *
    (⟨m11a, m11a_mem⟩ : ↥M11)⁻¹ ^ 2 *
    (⟨PSL211.wS, PSL211.wS_mem⟩ : ↥M11)⁻¹ *
    (⟨m11a, m11a_mem⟩ : ↥M11)⁻¹ ^ 3

lemma twistConjugator_coe : (twistConjugator : Perm (Fin 11)) = twistConjugatorPerm := rfl

/-- The twisted exceptional homomorphism into `M11`. -/
noncomputable def twistedEmbeddingSL : SL(2, ZMod 11) →* ↥M11 where
  toFun g := twistConjugator * M11Clean.f (QuotientGroup.mk' _ (outerTwist g)) *
    twistConjugator⁻¹
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    group

/-- The action on the twelve cosets obtained by restricting the `M11` action along the
outer-twisted exceptional embedding. -/
noncomputable instance twistedActionPoints : MulAction (SL(2, ZMod 11)) Points :=
  MulAction.compHom Points twistedEmbeddingSL

lemma twistConjugator_mem_H : twistConjugator ∈ M11Clean.H := by
  unfold twistConjugator
  exact mul_mem (mul_mem (mul_mem (inv_mem wS_mem_H) (pow_mem (inv_mem m11a_mem_H) 2))
    (inv_mem wS_mem_H)) (pow_mem (inv_mem m11a_mem_H) 3)

lemma twistedEmbeddingSL_mem_H (g : SL(2, ZMod 11)) : twistedEmbeddingSL g ∈ M11Clean.H := by
  change twistConjugator * M11Clean.f (QuotientGroup.mk' _ (outerTwist g)) *
    twistConjugator⁻¹ ∈ M11Clean.H
  exact mul_mem (mul_mem twistConjugator_mem_H ⟨_, rfl⟩) (inv_mem twistConjugator_mem_H)

lemma mem_H_iff_exists_psi11 (q : ↥M11) :
    q ∈ M11Clean.H ↔ ∃ x : SL(2, ZMod 11),
      (PSL211.psi11 x : Perm (Fin 11)) = (q : Perm (Fin 11)) := by
  constructor <;> rintro ⟨ x, hx ⟩;
  · obtain ⟨ y, rfl ⟩ := QuotientGroup.mk'_surjective _ x; use y;
    convert congr_arg Subtype.val hx using 1;
  · use QuotientGroup.mk x;
    exact Subtype.ext hx

lemma twistedEmbeddingSL_coe (g : SL(2, ZMod 11)) :
    (twistedEmbeddingSL g : Perm (Fin 11)) =
      twistConjugatorPerm * PSL211.psi11 (outerTwist g) * twistConjugatorPerm⁻¹ := by
  rfl

private def bridgeA : SL(2, ZMod 11) :=
  ⟨EnumL211.decM 4749, by decide⟩

private def bridgeB : SL(2, ZMod 11) :=
  ⟨EnumL211.decM 2156, by decide⟩

private lemma bridgeA_eq :
    PSL211.psi11 bridgeA = m11b⁻¹ *
      (twistConjugatorPerm * PSL211.psi11 (outerTwist EnumL211.Amat) *
        twistConjugatorPerm⁻¹)⁻¹ * m11b := by
  decide

private lemma bridgeB_eq :
    PSL211.psi11 bridgeB = m11b⁻¹ *
      (twistConjugatorPerm * PSL211.psi11 (outerTwist EnumL211.Bmat) *
        twistConjugatorPerm⁻¹)⁻¹ * m11b := by
  decide

private lemma twisted_A_fixes_coset :
    twistedEmbeddingSL EnumL211.Amat •
      (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) =
        (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) := by
  refine' QuotientGroup.eq.mpr _;
  have := @bridgeA_eq;
  use bridgeA;
  simp +decide

private lemma twisted_B_fixes_coset :
    twistedEmbeddingSL EnumL211.Bmat •
      (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) =
        (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) := by
  refine' QuotientGroup.eq.mpr _;
  simp_all +decide [ mem_H_iff_exists_psi11 ]

/-- Concrete forward half of the outer-twist bridge.  It is proved on the two generators
of `K`; closure then supplies every element of `K`. -/
lemma twisted_K_fixes_coset (g : SL(2, ZMod 11)) (hg : g ∈ PSL211.Ksub) :
    twistedEmbeddingSL g • (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) =
      (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) := by
  let S := (MulAction.stabilizer ↥M11
    (show Points from (⟨m11b, m11b_mem⟩ : ↥M11))).comap twistedEmbeddingSL
  have hgen : ({EnumL211.Amat, EnumL211.Bmat} : Set (SL(2, ZMod 11))) ⊆ S := by
    intro x hx
    rcases hx with (rfl | rfl)
    · exact MulAction.mem_stabilizer_iff.mpr twisted_A_fixes_coset
    · exact MulAction.mem_stabilizer_iff.mpr twisted_B_fixes_coset
  have hKS : PSL211.Ksub ≤ S := (Subgroup.closure_le _).2 hgen
  exact MulAction.mem_stabilizer_iff.mp (hKS hg)

/-- The stabilizer in `SL(2,11)` of `m11b H` under the twisted embedding has at most 120
elements.  The intended proof exhibits the eleven distinct translates by powers of `m11a`
and applies orbit--stabilizer. -/
lemma twisted_T_not_fix :
    twistedEmbeddingSL EnumL211.Tmat •
        (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) ≠
      (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) := by
  simp +contextual [QuotientGroup.eq, mem_H_iff_exists_psi11, twistedEmbeddingSL_coe]
  -- Kernel evaluation replaces the former compiled exhaustive check.  The larger recursion
  -- allowance is needed to normalize the explicit `SL(2,11)` action and its 1320 cases.
  set_option maxRecDepth 100000 in
    decide

lemma card_twisted_coset_stabilizer_le :
    Nat.card ↥((MulAction.stabilizer ↥M11
      (show Points from (⟨m11b, m11b_mem⟩ : ↥M11))).comap twistedEmbeddingSL) ≤ 120 := by
  let S := (MulAction.stabilizer ↥M11
    (show Points from (⟨m11b, m11b_mem⟩ : ↥M11))).comap twistedEmbeddingSL
  have hKS : PSL211.Ksub ≤ S := by
    intro g hg
    exact MulAction.mem_stabilizer_iff.mpr (twisted_K_fixes_coset g hg)
  have h120dvd : 120 ∣ Nat.card ↥S := by
    rw [← PSL211.card_Ksub]
    exact Subgroup.card_dvd_of_le hKS
  have hSLcard : Nat.card (SL(2, ZMod 11)) = 1320 := by
    rw [Nat.card_eq_fintype_card, EnumL211.slCard]
  have hSd1320 : Nat.card ↥S ∣ 1320 := by
    rw [← hSLcard]
    exact Subgroup.card_subgroup_dvd_card S
  have hSne : S ≠ ⊤ := by
    intro htop
    have hmem : EnumL211.Tmat ∈ S := by rw [htop]; exact Subgroup.mem_top _
    exact twisted_T_not_fix (MulAction.mem_stabilizer_iff.mp hmem)
  have hcardne : Nat.card ↥S ≠ 1320 := by
    rw [← hSLcard]
    exact fun h => hSne ((Subgroup.card_eq_iff_eq_top S).mp h)
  change Nat.card ↥S ≤ 120
  obtain ⟨k, hk⟩ := h120dvd
  have hk_le : k ≤ 11 := by
    have hcard_le : Nat.card ↥S ≤ 1320 := by
      rw [← hSLcard]
      exact Subgroup.card_le_card_group S
    omega
  have hk_ne : k ≠ 11 := by
    intro h
    subst k
    exact hcardne (by omega)
  have hk_le' : k ≤ 10 := by omega
  interval_cases k <;> rw [hk] at hSd1320 ⊢
  all_goals try norm_num
  all_goals exfalso; norm_num at hSd1320

/-- The index-`60` subgroup in the twisted exceptional action is exactly the subgroup fixing
`m11b H`. This finite generator calculation is the concrete bridge that accounts for the
outer automorphism. -/
theorem twisted_K_is_coset_stabilizer (g : SL(2, ZMod 11)) :
    g ∈ PSL211.Ksub ↔
      twistedEmbeddingSL g • (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) =
        (show Points from (⟨m11b, m11b_mem⟩ : ↥M11)) := by
  let S := (MulAction.stabilizer ↥M11
    (show Points from (⟨m11b, m11b_mem⟩ : ↥M11))).comap twistedEmbeddingSL
  have hle : PSL211.Ksub ≤ S := by
    intro x hx
    exact (MulAction.mem_stabilizer_iff.mpr (twisted_K_fixes_coset x hx))
  have heq : PSL211.Ksub = S := Subgroup.eq_of_le_of_card_ge hle (by
    rw [PSL211.card_Ksub]
    exact card_twisted_coset_stabilizer_le)
  constructor
  · exact twisted_K_fixes_coset g
  · intro hg
    have : g ∈ S := MulAction.mem_stabilizer_iff.mpr hg
    rwa [← heq] at this

private def exceptionalOrbitPoint : Points :=
  (show Points from (⟨m11b, m11b_mem⟩ : ↥M11))

private lemma exceptionalOrbitPoint_ne_base : exceptionalOrbitPoint ≠ basePoint := by
  intro h
  have hbH : (⟨m11b, m11b_mem⟩ : ↥M11) ∈ M11Clean.H := by
    rw [basePoint, exceptionalOrbitPoint, QuotientGroup.eq] at h
    simpa using h
  have htop : M11Clean.H = ⊤ := by
    apply top_unique
    rw [M11Clean.top_gen, Subgroup.closure_le]
    intro x hx
    rcases hx with (rfl | rfl)
    · exact m11a_mem_H
    · exact hbH
  have hindex := M11Clean.H_index
  rw [htop, Subgroup.index_top] at hindex
  norm_num at hindex

/-- The orbit map from the exceptional action's concrete `K`-coset transversal to the
non-base cosets in the twelve-point action. -/
noncomputable def exceptionalCosetMap
    (i : Fin 11) : ↥(SubMulAction.ofStabilizer ↥M11 basePoint) :=
  ⟨twistedEmbeddingSL (PSL211.reps i) • exceptionalOrbitPoint, by
    intro h
    have hfix : twistedEmbeddingSL (PSL211.reps i) • basePoint = basePoint :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_basePoint]
        exact twistedEmbeddingSL_mem_H (PSL211.reps i))
    exact exceptionalOrbitPoint_ne_base
      ((MulAction.injective (twistedEmbeddingSL (PSL211.reps i))) (h.trans hfix.symm))⟩

private lemma exceptionalCosetMap_equivariant
    (g : SL(2, ZMod 11)) (i : Fin 11) :
    (show MulAction.stabilizer ↥M11 basePoint from
      ⟨twistedEmbeddingSL g, by
        rw [stabilizer_basePoint]
        exact twistedEmbeddingSL_mem_H g⟩) • exceptionalCosetMap i =
      exceptionalCosetMap (g • i) := by
  apply Subtype.ext
  let k := (PSL211.reps (g • i))⁻¹ * (g * PSL211.reps i)
  have hk : k ∈ PSL211.Ksub := by
    apply (PSL211.inKb_iff_memK k).mp
    simpa only [k, PSL211.smul_def] using PSL211.cIdx_mem (g * PSL211.reps i)
  have hfix := twisted_K_fixes_coset k hk
  change twistedEmbeddingSL k • exceptionalOrbitPoint = exceptionalOrbitPoint at hfix
  change twistedEmbeddingSL g •
      (twistedEmbeddingSL (PSL211.reps i) • exceptionalOrbitPoint) =
    twistedEmbeddingSL (PSL211.reps (g • i)) • exceptionalOrbitPoint
  rw [← SemigroupAction.mul_smul, ← map_mul]
  have hdecomp : g * PSL211.reps i = PSL211.reps (g • i) * k := by
    simp only [k]
    group
  rw [hdecomp, map_mul, SemigroupAction.mul_smul, hfix]

private lemma exceptionalCosetMap_injective : Function.Injective exceptionalCosetMap := by
  intro i j hij
  have hij' : twistedEmbeddingSL (PSL211.reps i) • exceptionalOrbitPoint =
      twistedEmbeddingSL (PSL211.reps j) • exceptionalOrbitPoint :=
    congr_arg Subtype.val hij
  let k := (PSL211.reps i)⁻¹ * PSL211.reps j
  have hfix : twistedEmbeddingSL k • exceptionalOrbitPoint = exceptionalOrbitPoint := by
    change twistedEmbeddingSL ((PSL211.reps i)⁻¹ * PSL211.reps j) •
      exceptionalOrbitPoint = exceptionalOrbitPoint
    rw [map_mul, SemigroupAction.mul_smul, map_inv, ← hij', inv_smul_smul]
  have hk : k ∈ PSL211.Ksub := (twisted_K_is_coset_stabilizer k).2 hfix
  exact PSL211.distinctb i j ((PSL211.inKb_iff_memK k).2 hk)

/-- The twisted exceptional eleven-point action is equivariantly equivalent to the action of
`H` on the eleven non-base cosets. The equivalence sends the `K`-coset represented by
`PSL211.reps i` to the `H`-coset obtained from `m11b`; `twisted_K_is_coset_stabilizer` gives
well-definedness and injectivity, and both sides have cardinality eleven. -/
theorem exists_exceptionalCosetEquiv :
    ∃ e : Fin 11 ≃ ↥(SubMulAction.ofStabilizer ↥M11 basePoint),
      ∀ (g : SL(2, ZMod 11)) (i : Fin 11),
        (show MulAction.stabilizer ↥M11 basePoint from
          ⟨twistedEmbeddingSL g, by
            rw [stabilizer_basePoint]
            exact twistedEmbeddingSL_mem_H g⟩) • e i = e (g • i) := by
  have hcard : Nat.card ↥(SubMulAction.ofStabilizer ↥M11 basePoint) = 11 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, card_points]
  have hbij : Function.Bijective exceptionalCosetMap :=
    exceptionalCosetMap_injective.bijective_of_nat_card_le (by simp [hcard])
  let e := Equiv.ofBijective exceptionalCosetMap hbij
  refine ⟨e, ?_⟩
  intro g i
  exact exceptionalCosetMap_equivariant g i

/-- A fixed equivariant identification supplied by `exists_exceptionalCosetEquiv`. -/
noncomputable def exceptionalCosetEquiv :
    Fin 11 ≃ ↥(SubMulAction.ofStabilizer ↥M11 basePoint) :=
  exists_exceptionalCosetEquiv.choose

/-- Equivariance of `exceptionalCosetEquiv` for the twisted embedding. -/
theorem exceptionalCosetEquiv_equivariant (g : SL(2, ZMod 11)) (i : Fin 11) :
    (show MulAction.stabilizer ↥M11 basePoint from
      ⟨twistedEmbeddingSL g, by rw [stabilizer_basePoint]; exact twistedEmbeddingSL_mem_H g⟩) •
      exceptionalCosetEquiv i = exceptionalCosetEquiv (g • i) :=
  exists_exceptionalCosetEquiv.choose_spec g i

/-
The embedded `PSL(2,11)` is 2-transitive on the eleven cosets other than its own.
-/
theorem stabilizer_two_transitive :
    MulAction.IsMultiplyPretransitive (MulAction.stabilizer ↥M11 basePoint)
      (SubMulAction.ofStabilizer ↥M11 basePoint) 2 := by
  refine' ⟨ fun x y => _ ⟩;
  -- Pull back the embeddings x and y to SL(2, ZMod 11) using the exceptionalCosetEquiv.
  obtain ⟨x', hx'⟩ : ∃ x' : Fin 2 ↪ Fin 11, ∀ i, x i = exceptionalCosetEquiv (x' i) := by
    exact ⟨ ⟨ fun i => exceptionalCosetEquiv.symm ( x i ), fun i j hij => by simpa using hij ⟩, fun i => by simp +decide ⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Fin 2 ↪ Fin 11, ∀ i, y i = exceptionalCosetEquiv (y' i) := by
    exact ⟨ ⟨ fun i => exceptionalCosetEquiv.symm ( y i ), fun i j hij => by simpa using hij ⟩, fun i => by simp +decide ⟩;
  -- Use the exceptional_two_transitive property to find g such that g • x' = y'.
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ZMod 11), g • x' = y' := by
    have := PSL211.exceptional_two_transitive;
    exact this.1 x' y';
  -- Use the exceptionalCosetEquiv_equivariant property to show that the stabilizer element built from twistedEmbeddingSL g and exceptionalCosetEquiv_equivariant pointwise works.
  have h_stabilizer : (show MulAction.stabilizer ↥M11 basePoint from ⟨twistedEmbeddingSL g, by rw [stabilizer_basePoint]; exact twistedEmbeddingSL_mem_H g⟩) • x = y := by
                        ext i; simp +decide [ hx', hy', exceptionalCosetEquiv_equivariant ] ;
                        exact congr_arg ( fun f => f i ) hg;
  exact ⟨ _, h_stabilizer ⟩

/-- The natural action of `M₁₁` on the twelve cosets of its embedded `PSL(2,11)` is
3-transitive. -/
theorem three_transitive :
    MulAction.IsMultiplyPretransitive ↥M11 Points 3 := by
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := ↥M11) (a := basePoint) (n := 2)).mpr stabilizer_two_transitive

end M11CosetAction
end Mathieu