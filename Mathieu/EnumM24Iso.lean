import Mathieu.EnumM24IsoCore
import Mathieu.BasicM23
import Mathieu.GolayCore
import Mathieu.TransM24

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mathieu

open Equiv MulAction

namespace EnumM24Iso

/-- The natural extension embeds `M₂₃` in the point stabiliser of `23`. -/
def psi : M23 →* ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) where
  toFun g := ⟨Perm.extendDomainHom e24 g.1, map_le ⟨g.1, g.2, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

lemma psi_injective : Function.Injective psi := by
  intro a b hab
  exact Subtype.ext (Perm.extendDomainHom_injective e24 (congrArg Subtype.val hab))

/-- Evaluation of a permutation fixing `23` on four further distinct points. -/
def evalFour
    (g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24))) :
    Fin 4 ↪ {x : Fin 24 // x ≠ 23} where
  toFun i := ⟨g.1 (Fin.castLE (by omega) i), by
    intro h
    have hfix : g.1 23 = 23 := by
      simpa [Equiv.Perm.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g.2.2)
    have hi : (Fin.castLE (by omega) i : Fin 24) ≠ 23 := by
      intro he
      have hv : (Fin.castLE (by omega) i : Fin 24).val = 23 := congrArg Fin.val he
      simp only [Fin.val_castLE] at hv
      omega
    exact hi (g.1.injective (h.trans hfix.symm))⟩
  inj' i j h := by
    have := g.1.injective (Subtype.ext_iff.mp h)
    simpa [Fin.ext_iff] using this

/-
A fiber of `evalFour` has at most `48` elements.  Two elements in one fiber differ by
an element fixing five points; five-transitivity conjugates that pointwise stabiliser into
`stab5 M24`, and `M24_le_codeAut` plus Golay rigidity bounds it by `48`.
-/
lemma evalFour_fiber_card_le (e : Fin 4 ↪ {x : Fin 24 // x ≠ 23}) :
    Nat.card {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) //
      evalFour g = e} ≤ 48 := by
  by_cases h_card : Nat.card {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) | evalFour g = e} > 0;
  · obtain ⟨g0, hg0⟩ : ∃ g0 : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)), evalFour g0 = e := by
      exact Set.nonempty_of_ncard_ne_zero h_card.ne';
    -- By five-transitivity of M24, there exists $\sigma \in M24$ such that $\sigma(0)=0, \sigma(1)=1, \sigma(2)=2, \sigma(3)=3$, and $\sigma(23)=4$.
    obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin 24), σ ∈ M24 ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 23 = 4 := by
      have := TransM24.M24_isMultiplyPretransitive_five;
      have := this.1;
      obtain ⟨ g, hg ⟩ := this ( ⟨ fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 23, by decide ⟩ ) ( ⟨ fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4, by decide ⟩ );
      exact ⟨ g, g.2, by simpa using congr_arg ( fun f => f ( 0 : Fin 5 ) ) hg, by simpa using congr_arg ( fun f => f ( 1 : Fin 5 ) ) hg, by simpa using congr_arg ( fun f => f ( 2 : Fin 5 ) ) hg, by simpa using congr_arg ( fun f => f ( 3 : Fin 5 ) ) hg, by simpa using congr_arg ( fun f => f ( 4 : Fin 5 ) ) hg ⟩;
    -- Consider the map from the fiber to `stab5 codeAut` given by $g \mapsto \sigma * g0⁻¹ * g * \sigma⁻¹$.
    have h_map : ∀ g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)), evalFour g = e → σ * g0.val⁻¹ * g.val * σ⁻¹ ∈ codeAut GolayCode24.golayCode ∧ ∀ i : Fin 24, i.val < 5 → (σ * g0.val⁻¹ * g.val * σ⁻¹) i = i := by
      intro g hg
      have h_diff : ∀ i : Fin 4, (g0.val⁻¹ * g.val) (Fin.castLE (by omega) i) = Fin.castLE (by omega) i := by
        intro i
        have h_eval : evalFour g0 i = evalFour g i := by
          rw [hg0, hg];
        simp +decide [ evalFour ] at h_eval ⊢;
        rw [ ← h_eval, Equiv.symm_apply_apply ]
      have h_diff_23 : (g0.val⁻¹ * g.val) 23 = 23 := by
        have := g0.2.2; have := g.2.2; simp_all +decide [ MulAction.mem_stabilizer_iff ] ;
        grind +splitIndPred
      have h_diff_4 : (σ * g0.val⁻¹ * g.val * σ⁻¹) 4 = 4 := by
        simp +decide [ ← hσ.2.2.2.2.2 ];
        simp_all +decide
      have h_diff_0 : (σ * g0.val⁻¹ * g.val * σ⁻¹) 0 = 0 := by
        have := h_diff 0; simp_all +decide [ mul_assoc ] ;
        rw [ show ( Equiv.symm σ ) 0 = 0 from by simp +decide [ Equiv.symm_apply_eq, hσ ] ] ; aesop;
      have h_diff_1 : (σ * g0.val⁻¹ * g.val * σ⁻¹) 1 = 1 := by
        have := h_diff 1; simp_all +decide [ Fin.castLE ] ;
        grind
      have h_diff_2 : (σ * g0.val⁻¹ * g.val * σ⁻¹) 2 = 2 := by
        have := h_diff 2; simp_all +decide [ Fin.castLE ] ;
        rw [ show ( Equiv.symm σ ) 2 = 2 from by rw [ Equiv.symm_apply_eq ] ; aesop ] ; aesop;
      have h_diff_3 : (σ * g0.val⁻¹ * g.val * σ⁻¹) 3 = 3 := by
        have := h_diff 3; simp_all +decide [ mul_assoc ] ;
        rw [ show ( Equiv.symm σ ) 3 = 3 from by rw [ Equiv.symm_apply_eq ] ; aesop ] ; aesop;
      exact ⟨by
      have h_diff_codeAut : ∀ g : Perm (Fin 24), g ∈ M24 → g ∈ codeAut GolayCode24.golayCode := by
        exact fun g hg => M24_le_codeAut hg;
      exact h_diff_codeAut _ ( Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( Subgroup.mul_mem _ hσ.1 ( Subgroup.inv_mem _ g0.2.1 ) ) g.2.1 ) ( Subgroup.inv_mem _ hσ.1 ) ), by
        grind +qlia⟩;
    -- This map is injective, so the cardinality of the fiber is at most the cardinality of `stab5 codeAut`.
    have h_inj : Function.Injective (fun g : {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) | evalFour g = e} => ⟨σ * g0.val⁻¹ * g.val * σ⁻¹, h_map g.val g.property |>.1, h_map g.val g.property |>.2⟩ : {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) | evalFour g = e} → stab5 (codeAut GolayCode24.golayCode)) := by
      intro g1 g2 h_eq;
      simp_all +decide [ mul_assoc ];
      exact Subtype.ext h_eq;
    have := Nat.card_le_card_of_injective _ h_inj;
    exact this.trans ( by simpa using card_stab5_codeAut_le );
  · aesop

/-
The point stabiliser has order at most `|M₂₃|`, by counting the possible ordered images
of four further points (`23·22·21·20`) and the at-most-`48` elements in each fiber.
-/
lemma ptStab_card_le :
    Nat.card ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) ≤ 10200960 := by
  have h_finite : Finite (↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24))) := by
    exact Set.Finite.to_subtype <| Set.toFinite _;
  have h_finite : Fintype (↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24))) := by
    exact Fintype.ofFinite _;
  have h_card_bound : ∑ e : Fin 4 ↪ {x : Fin 24 // x ≠ 23}, Nat.card {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) | evalFour g = e} = Nat.card (↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24))) := by
    simp +decide only [Nat.card_eq_fintype_card, Fintype.card_ofFinset];
    rw [ ← Finset.card_biUnion ];
    · convert Finset.card_univ;
      ext g; simp [evalFour];
    · exact fun x _ y _ hxy => Finset.disjoint_filter.mpr fun z => by aesop;
  have h_card_bound : ∑ e : Fin 4 ↪ {x : Fin 24 // x ≠ 23}, Nat.card {g : ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) | evalFour g = e} ≤ 48 * Nat.card (Fin 4 ↪ {x : Fin 24 // x ≠ 23}) := by
    exact le_trans ( Finset.sum_le_sum fun _ _ => evalFour_fiber_card_le _ ) ( by norm_num [ mul_comm ] );
  simp_all +decide [ Nat.card_eq_fintype_card ]

/-- The natural extension `M₂₃ → stab_{M₂₄}(23)` is onto, by injectivity and the matching
finite cardinality bound. -/
lemma psi_surjective : Function.Surjective psi := by
  letI : Fintype M23 := Fintype.ofFinite _
  letI : Fintype ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) :=
    Fintype.ofFinite _
  have hcard : Fintype.card M23 =
      Fintype.card ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, M23_card]
    apply Nat.le_antisymm
    · rw [← M23_card]
      exact Nat.card_le_card_of_injective psi psi_injective
    · exact ptStab_card_le
  exact ((Fintype.bijective_iff_injective_and_card psi).2 ⟨psi_injective, hcard⟩).2

/-- **`M₂₃ ≅ stab_{M₂₄}(23)`.** -/
theorem M23_iso :
    Nonempty (M23 ≃* ↥(M24 ⊓ MulAction.stabilizer (Perm (Fin 24)) (23 : Fin 24))) :=
  ⟨MulEquiv.ofBijective psi ⟨psi_injective, psi_surjective⟩⟩

end EnumM24Iso

/-- **`M₂₃ < M₂₄`.** `M₂₃` is isomorphic to the stabiliser of the point `23` inside `M₂₄`. -/
theorem M23_iso_ptStab_M24 :
    Nonempty (M23 ≃* ptStab M24 (23 : Fin 24)) := EnumM24Iso.M23_iso

end Mathieu