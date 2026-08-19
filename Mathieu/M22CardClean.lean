import Mathieu.GolayCore
import Mathieu.TransM22
import Mathieu.TransM24

/-!
# A structural upper bound for the order of M22

This file bounds `M₂₂` through its 3-transitive action and the Golay-code rigidity bound,
without using the `EnumM22` breadth-first order certificate.
-/

namespace Mathieu

open Equiv MulAction Function Matrix
open scoped MatrixGroups
open EnumM24Iso (e24)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The ordered triple `0,1,2` in the 22-point action of `M₂₂`. -/
def M22CardClean.base3 : Fin 3 ↪ TransM22.Y22 where
  toFun i := ⟨Fin.castLE (by omega) i, by
    intro h
    have := congrArg Fin.val h
    simp [Fin.castLE] at this
    omega⟩
  inj' := by intro a b h; simpa [Fin.ext_iff] using congrArg (fun x => x.1.val) h

/-- The corresponding ordered five-tuple `0,1,2,22,23` in `Fin 24`. -/
def M22CardClean.source5 : Fin 5 ↪ Fin 24 where
  toFun i := match i.1 with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 22 | _ => 23
  inj' := by decide

/-- The standard ordered five-tuple `0,1,2,3,4`. -/
def M22CardClean.target5 : Fin 5 ↪ Fin 24 := Fin.castLEEmb (by omega)

/-
The stabiliser of `base3` embeds into the pointwise five-point stabiliser of the Golay-code
automorphism group.  Extend an `M₂₂` permutation to `Fin 24`; it already fixes `22,23`, and
then conjugate by a cleanly supplied `M₂₄` element carrying `source5` to `target5`.
-/
lemma M22CardClean.tripleStab_card_le :
    Nat.card (MulAction.stabilizer (↥M22) M22CardClean.base3) ≤
      Nat.card (stab5 (codeAut GolayCode24.golayCode)) := by
  have h_inj : ∃ f : (stabilizer (M22) base3) → stab5 (codeAut GolayCode24.golayCode), Function.Injective f := by
    have h_orbit : ∃ m : Perm (Fin 24), m ∈ M24 ∧ m ∘ (M22CardClean.target5 : Fin 5 → Fin 24) = M22CardClean.source5 := by
      have := TransM24.M24_isMultiplyPretransitive_five;
      obtain ⟨ m, hm ⟩ := this.1 ( M22CardClean.target5 ) ( M22CardClean.source5 );
      exact ⟨ m, m.2, funext fun i => by simpa using congr_arg ( fun f => f i ) hm ⟩
    obtain ⟨m, hm⟩ := h_orbit
    have h_conj : ∀ g : stabilizer (M22) base3, (m⁻¹ * Perm.extendDomainHom e24 (g.val) * m) ∈ stab5 (codeAut GolayCode24.golayCode) := by
      intro g
      have h_conj : ∀ i : Fin 24, (i : ℕ) < 5 → (m⁻¹ * Perm.extendDomainHom e24 (g.val) * m) i = i := by
        intro i hi
        have h_conj : (Perm.extendDomainHom e24 (g.val)) (m i) = m i := by
          have h_conj : m i ∈ ({0, 1, 2, 22, 23} : Set (Fin 24)) := by
            have := congr_fun hm.2 ⟨ i, hi ⟩ ; fin_cases i <;> simp +decide at this ⊢ <;> tauto;
          have h_conj : ∀ x : Fin 23, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 22 → g.val.val x = x := by
            intro x hx
            have h_conj : ∀ i : Fin 3, g.val.val (base3 i) = base3 i := by
              intro i
              have h_conj : g.val • (base3 i) = base3 i := by
                exact congr_arg ( fun f => f i ) g.2;
              convert congr_arg Subtype.val h_conj using 1;
            rcases hx with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Fin.forall_fin_succ ];
            · exact h_conj.1;
            · exact h_conj.2.1;
            · exact h_conj.2.2;
            · exact g.1.2.2;
          cases ‹m i ∈ _› <;> simp_all +decide [ Perm.extendDomain ];
          · simp +decide [ h_conj, e24 ];
          · rcases ‹_› with ( h | h | h | h ) <;> simp_all +decide [ Equiv.Perm.subtypeCongr ];
            · erw [ h_conj.2.1 ] ; rfl;
            · erw [ h_conj.2.2.1 ] ; rfl;
            · exact h_conj.2.2.2.symm ▸ rfl;
        simp_all +decide [mul_assoc];
      have h_conj : (Perm.extendDomainHom e24 (g.val)) ∈ codeAut GolayCode24.golayCode := by
        apply M24_le_codeAut;
        exact EnumM24Iso.map_le ⟨ g.val, g.val.2.1, rfl ⟩ |>.1;
      exact ⟨ Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( Subgroup.inv_mem _ ( show m ∈ codeAut GolayCode24.golayCode from M24_le_codeAut hm.1 ) ) h_conj ) ( show m ∈ codeAut GolayCode24.golayCode from M24_le_codeAut hm.1 ), by aesop ⟩;
    refine' ⟨ fun g => ⟨ m⁻¹ * Perm.extendDomainHom e24 g * m, h_conj g ⟩, fun g₁ g₂ h => _ ⟩ ; simp_all +decide [ mul_assoc ];
    exact Subtype.ext <| Subtype.ext <| Perm.extendDomainHom_injective e24 h;
  convert Nat.card_le_card_of_injective h_inj.choose h_inj.choose_spec using 1

/-
The structural upper bound needed to replace the M22 breadth-first enumeration.
-/
theorem M22_card_le_clean : Nat.card M22 ≤ 443520 := by
  -- By First Isomorphism Theorem, it suffices to show that M22 is isomorphic to a subgroup of M23.
  have h_iso : Nat.card (MulAction.stabilizer (↥M22) M22CardClean.base3) ≤ 48 := by
    convert M22CardClean.tripleStab_card_le.trans card_stab5_codeAut_le using 1;
  have := @TransM22.M22_isMultiplyPretransitive_three;
  convert Nat.mul_le_mul_left ( Nat.card ( MulAction.orbit ( ↥M22 ) ( M22CardClean.base3 : Fin 3 ↪ TransM22.Y22 ) ) ) h_iso using 1;
  · rw [ Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( M22 ) ( M22CardClean.base3 : Fin 3 ↪ TransM22.Y22 ) ) ];
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( stabilizer ( M22 ) ( M22CardClean.base3 : Fin 3 ↪ TransM22.Y22 ) ) ; aesop;
  · rw [ show ( MulAction.orbit ( ↥M22 ) M22CardClean.base3 : Set ( Fin 3 ↪ TransM22.Y22 ) ) = Set.univ from ?_ ] ; norm_num;
    convert this.1 M22CardClean.base3;
    simp +decide [ Set.ext_iff, orbit ]

/-- The projective-plane action has an image of order `20160` inside `M₂₁`. -/
lemma M22CardClean.cpsi_range_card : Nat.card TransM21.cpsi.range = 20160 := by
  have hker : Nat.card TransM21.cpsi.ker = 3 := by
    rw [TransM21.ker_cpsi]
    exact TransM21.card_center
  have hSL : Nat.card (SL(3, F4)) = 60480 := by
    rw [Nat.card_eq_fintype_card]
    exact EnumSL34.slCard
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup TransM21.cpsi.ker
  have hrange : Nat.card TransM21.cpsi.range =
      Nat.card (SL(3, F4) ⧸ TransM21.cpsi.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange TransM21.cpsi).toEquiv).symm
  rw [hSL, hker] at hq
  rw [hrange]
  omega

/-
The projective-plane subgroup supplies the matching lower bound.
-/
theorem M22_card_ge_clean : 443520 ≤ Nat.card M22 := by
  have hM22_ge : Nat.card TransM21.cpsi.range ≤ Nat.card M21 := by
    apply_rules [ Nat.card_le_card_of_injective ];
    exact Subtype.val_injective;
  have hM22_ge : 20160 ≤ Nat.card M21 := by
    exact le_trans ( by rw [ M22CardClean.cpsi_range_card ] ) hM22_ge;
  have hM22_ge : Nat.card (MulAction.orbit (↥M22) (TransM22.a21 : TransM22.Y22)) * Nat.card (MulAction.stabilizer (↥M22) (TransM22.a21 : TransM22.Y22)) = Nat.card M22 := by
    rw [ Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( M22 ) ( TransM22.a21 : TransM22.Y22 ) ) ];
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( stabilizer ( M22 ) ( TransM22.a21 : TransM22.Y22 ) ) ; aesop;
  have hM22_ge : Nat.card (MulAction.orbit (↥M22) (TransM22.a21 : TransM22.Y22)) = 22 := by
    have horbit : MulAction.orbit (↥M22) (TransM22.a21 : TransM22.Y22) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      exact TransM22.M22_isPretransitive.exists_smul_eq _ x
    rw [horbit]
    norm_num [Nat.card_eq_fintype_card]
  have hM22_ge : Nat.card (MulAction.stabilizer (↥M22) (TransM22.a21 : TransM22.Y22)) ≥ Nat.card M21 := by
    have hM22_ge : Function.Injective (TransM22.psiM21toStab : M21 → ↥(stabilizer (↥M22) (TransM22.a21 : TransM22.Y22))) := by
      intro x y hxy;
      injection hxy;
      aesop;
    apply_rules [ Nat.card_le_card_of_injective ];
  nlinarith

/-- The order of `M₂₂`, proved without the breadth-first enumeration certificate. -/
theorem M22_card_clean : Nat.card M22 = 443520 :=
  Nat.le_antisymm M22_card_le_clean M22_card_ge_clean

end Mathieu