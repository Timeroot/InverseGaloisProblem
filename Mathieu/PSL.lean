import Mathlib
import Mathieu.Subgroups
import Mathieu.BasicM22
import Mathieu.M22Transitive
import Mathieu.PSL223
import Mathieu.PSL211

/-!
# The Mathieu groups and projective special linear groups

Several Mathieu groups are closely related to projective special linear groups:

* `M₂₁ ≅ PSL(3, 4)` (the linear group over the field `GF(4)` acting on the projective
  plane of order 4, the 21 points of which are permuted);
* `PSL(2, 11) ↪ M₁₁` (a subgroup);
* `PSL(2, 23) ↪ M₂₄` (a subgroup; it acts on the projective line `P¹(F₂₃)`, the 24 points).

Here `GF(4)` is `GaloisField 2 2`.  These relations are stated as goals; see `PLAN.md`.
-/

namespace Mathieu

open Equiv Matrix
open scoped MatrixGroups

/-- **Orbit–stabiliser (general point).** For any `H ≤ Perm (Fin n)` and any point `k`,
`|H| = |orbit H k| · |ptStab H k|`.  Unlike `card_eq_of_pretransitive`, this does not assume
transitivity, so the orbit factor need not be `n`. -/
theorem card_eq_orbit_mul_ptStab {n : ℕ} (H : Subgroup (Perm (Fin n))) (k : Fin n) :
    Nat.card H = Nat.card (MulAction.orbit H k) * Nat.card (ptStab H k) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (↥H) k) := Fintype.ofFinite _
  haveI : Fintype ↑(MulAction.orbit (↥H) k) := Fintype.ofFinite _
  have hstab : (MulAction.stabilizer (↥H) k)
      = (ptStab H k).subgroupOf H := by
    ext x
    simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ptStab]
    rfl
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥H) k
  simp only [← Nat.card_eq_fintype_card] at key
  have hstabcard : Nat.card ↥(MulAction.stabilizer (↥H) k) = Nat.card (ptStab H k) := by
    rw [Nat.card_congr (by rw [hstab] : (MulAction.stabilizer (↥H) k) ≃ _)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  rw [hstabcard] at key
  rw [← key]

/-
The number of points `≠ 22` in `Fin 23` is `22`.
-/
theorem card_ne_22 : Nat.card {x : Fin 23 // x ≠ (22 : Fin 23)} = 22 := by
  aesop

/-
**The orbit of `21` under `M₂₂` has `22` points.**  `M₂₂` fixes `22`, so the orbit is
contained in the `22` points `{0,…,21}`; and `M₂₂` is transitive on those `22` points
(`M22Transitive.M22_reaches`, proved directly from the generators), so the orbit is all of
them.
-/
theorem M22_orbit21_card : Nat.card (MulAction.orbit (↥M22) (21 : Fin 23)) = 22 := by
  have h_orbit : ∀ x : Fin 23, x ≠ 22 → ∃ g : ↥M22, g • (21 : Fin 23) = x := by
    intro x hx
    obtain ⟨g, hg⟩ := M22Transitive.M22_reaches x hx
    exact ⟨g, by simpa [Submonoid.smul_def, Equiv.Perm.smul_def] using hg⟩
  rw [ show ( MulAction.orbit ( ↥M22 ) 21 : Set ( Fin 23 ) ) = { x : Fin 23 | x ≠ 22 } from ?_ ] ; simp +decide [ ] ;
  ext x; simp [MulAction.orbit];
  constructor;
  · rintro ⟨ g, hg, rfl ⟩ hx; simp_all +decide [ M22 ] ;
    exact absurd ( g.injective ( hx.trans hg.2.symm ) ) ( by decide );
  · exact fun hx => by obtain ⟨ g, hg ⟩ := h_orbit x hx; exact ⟨ g, g.2, hg ⟩ ;

/-- **`|M₂₁| = 20160`.** The Mathieu group `M₂₁` (the point stabiliser of `21` in `M₂₂`,
equivalently the stabiliser of three points in `M₂₄`) has order `20160`.

Proof: orbit–stabiliser for the `M₂₂`-action on `Fin 23`.  `M₂₂` fixes `22` and is transitive
on the remaining `22` points `{0,…,21}`, so the orbit of `21` has `22` elements and its
stabiliser is `M₂₁`; hence `|M₂₁| = |M₂₂| / 22 = 443520 / 22 = 20160`. -/
theorem M21_card : Nat.card M21 = 20160 := by
  have h := card_eq_orbit_mul_ptStab M22 (21 : Fin 23)
  rw [M22_card, M22_orbit21_card] at h
  show Nat.card (ptStab M22 (21 : Fin 23)) = 20160
  omega

/-
**`|PSL(3,4)| = 20160`.** The projective special linear group `PSL(3, 4)` over the field
with four elements has order `20160`.

Proof: `|GL(3,4)| = (4³-1)(4³-4)(4³-4²) = 181440` (`Matrix.card_GL_field`); dividing by the
`q-1 = 3` scalars gives `|SL(3,4)| = 60480`; the centre of `SL(3,4)` (scalar matrices with
determinant one, i.e. the cube roots of unity in `GF(4)`) has order `gcd(3, 4-1) = 3`, so
`|PSL(3,4)| = 60480 / 3 = 20160`.
-/
set_option maxHeartbeats 4000000 in
theorem PSL34_card : Nat.card (PSL(3, GaloisField 2 2)) = 20160 := by
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)) = 181440 := by
    rw [Matrix.card_GL_field]
    have hc : Fintype.card (GaloisField 2 2) = 4 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [hc]
    norm_num [Fin.prod_univ_succ]
  -- The center of $SL(3,4)$ is the set of scalar matrices with determinant 1, which has order 3.
  have h_center : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) = 3 := by
    have h_center : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)), g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ↔ ∃ c : GaloisField 2 2, c ^ 3 = 1 ∧ g.val = Matrix.diagonal (fun _ => c) := by
      intro g
      constructor
      intro hg
      obtain ⟨c, hc⟩ : ∃ c : GaloisField 2 2, g.val = Matrix.diagonal (fun _ => c) := by
        have h_scalar : ∀ (h : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)), h.det = 1 → g.val * h = h * g.val := by
          intro h hh; have := hg.comm; simp_all +decide [ Subgroup.mem_center_iff ] ;
          convert congr_arg Subtype.val ( this ⟨ h, hh ⟩ ) using 1;
        have h_scalar : ∀ (i j : Fin 3), i ≠ j → g.val i j = 0 := by
          intro i j hij
          have h_comm : g.val * Matrix.of (fun k l => if k = i ∧ l = j then 1 else if k = l then 1 else 0) = Matrix.of (fun k l => if k = i ∧ l = j then 1 else if k = l then 1 else 0) * g.val := by
            apply h_scalar;
            fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.det_fin_three ] at hij ⊢;
          have h_comm : g.val * Matrix.of (fun k l => if k = j ∧ l = i then 1 else if k = l then 1 else 0) = Matrix.of (fun k l => if k = j ∧ l = i then 1 else if k = l then 1 else 0) * g.val := by
            apply h_scalar;
            fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.det_fin_three ] at hij ⊢;
          replace h_comm := congr_fun ( congr_fun h_comm j ) j; simp_all +decide [ Matrix.mul_apply, Finset.sum_ite ] ;
          simp_all +decide [ eq_comm ];
          simp_all +decide [ Finset.filter_eq ];
        have := ‹∀ h : Matrix ( Fin 3 ) ( Fin 3 ) ( GaloisField 2 2 ), h.det = 1 → ( g : Matrix ( Fin 3 ) ( Fin 3 ) ( GaloisField 2 2 ) ) * h = h * ( g : Matrix ( Fin 3 ) ( Fin 3 ) ( GaloisField 2 2 ) ) › ( Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else if i = j then 1 else 0 ) ; simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ] ;
        rename_i h; have := h ( Matrix.of fun i j => if i = 0 ∧ j = 2 then 1 else if i = j then 1 else 0 ) ; simp_all +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ;
        have := h ( Matrix.of fun i j => if i = 1 ∧ j = 2 then 1 else if i = j then 1 else 0 ) ; simp_all +decide [ Matrix.det_fin_three ] ;
      have hc_det : c ^ 3 = 1 := by
        have := g.2; aesop;
      use c, hc_det, hc
      intro ⟨c, hc_det, hc⟩
      have hc_center : ∀ h : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2), g * h = h * g := by
        intro h; ext i j; simp +decide [ hc, Matrix.mul_apply, Matrix.diagonal ] ; ring;
      exact (by
      exact Subgroup.mem_center_iff.mpr fun h => by simp +decide [ hc_center h ] ;);
    have h_center_card : Nat.card {c : GaloisField 2 2 | c ^ 3 = 1} = 3 := by
      have h_center_card : Nat.card {c : (GaloisField 2 2)ˣ | c ^ 3 = 1} = 3 := by
        have h_center_card : ∀ (G : Type) [Group G] [Fintype G], Nat.card G = 3 → Nat.card {c : G | c ^ 3 = 1} = 3 := by
          intros G _ _ hG; simp_all +decide [ Nat.card_eq_fintype_card ] ;
          simp +decide [ ← hG, Nat.card_eq_fintype_card ];
        convert h_center_card ( Units ( GaloisField 2 2 ) ) _;
        · exact Fintype.ofFinite _;
        · rw [Nat.card_units]
          have hc : Nat.card (GaloisField 2 2) = 4 := by
            rw [GaloisField.card 2 2 (by norm_num)]
            norm_num
          rw [hc]
      convert h_center_card using 1;
      rw [ ← Nat.card_congr ];
      refine' Equiv.ofBijective _ ⟨ fun x y h => _, fun x => _ ⟩;
      use fun x => ⟨ x.val, by simpa [ Units.ext_iff ] using x.2 ⟩;
      · aesop;
      · rcases x with ⟨ x, hx ⟩;
        exact ⟨ ⟨ Units.mk0 x ( by rintro rfl; simp +decide at hx ), by simpa [ Units.ext_iff ] using hx ⟩, rfl ⟩;
    convert h_center_card using 1;
    fapply Nat.card_congr;
    refine' Equiv.ofBijective ( fun x => ⟨ x.val 0 0, _ ⟩ ) ⟨ _, _ ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    · obtain ⟨ c, hc₁, hc₂ ⟩ := h_center x.1 |>.1 x.2; aesop;
    · intro g hg h hh hgh; obtain ⟨ c, hc, hg ⟩ := h_center g |>.1 hg; obtain ⟨ d, hd, hh ⟩ := h_center h |>.1 hh; aesop;
    · intro c hc; use ⟨ Matrix.diagonal ( fun _ => c ), by
        simp +decide [ hc, Matrix.det_diagonal ] ⟩ ; aesop;
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
    have h_det : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) * Nat.card (Units (GaloisField 2 2)) := by
      have h_det : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) * Nat.card (Units (GaloisField 2 2)) := by
        have h_det : Function.Surjective (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2) → Units (GaloisField 2 2)) := by
          intro x;
          refine' ⟨ Matrix.GeneralLinearGroup.mkOfDetNeZero ( Matrix.diagonal ( fun i => if i = 0 then x else 1 ) ) _, _ ⟩ ; simp +decide [ ];
          simp +decide [ GeneralLinearGroup.det ]
        have h_det : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) * Nat.card (Units (GaloisField 2 2)) := by
          have h_det : ∀ (g : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)), Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = Nat.card (MonoidHom.ker (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2) →* Units (GaloisField 2 2))) := by
            intro g
            apply Nat.card_congr
            exact Equiv.ofBijective (fun x => ⟨x, by
              simp +decide [ MonoidHom.mem_ker ]⟩) ⟨by
            exact fun x y h => by simpa [ SpecialLinearGroup.ext_iff ] using congr_arg Subtype.val h;, by
              intro x; use ⟨x.val, by
                convert x.2 using 1;
                simp +decide [ GeneralLinearGroup.det ];
                simp +decide [ Units.ext_iff ]⟩; aesop;⟩
          have := Subgroup.card_mul_index ( MonoidHom.ker ( Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup ( Fin 3 ) ( GaloisField 2 2 ) →* Units ( GaloisField 2 2 ) ) ) ; simp_all +decide [ Subgroup.index_ker ] ;
        exact h_det;
      exact h_det;
    rw [ show Nat.card ( GaloisField 2 2 )ˣ = 3 by
          rw [ Nat.card_units, GaloisField.card ] ; norm_num;
          decide +revert ] at h_det ; linarith!;
  have hPSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2)) * Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) := by
    convert Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.center ( Matrix.SpecialLinearGroup ( Fin 3 ) ( GaloisField 2 2 ) ) ) using 1;
  grind

/-
**`PSL(3,4) ↪ M₂₁`** and the synthesis **`M₂₁ ≅ PSL(3,4)`** now live in
`Mathieu/M21IsoPSL34.lean` (as `Mathieu.PSL34_embeds_M21` and
`Mathieu.M21_iso_PSL34`).  They were moved out of this file because their proof imports the
computable-field groundwork `F4.lean`/`ProjF4.lean`/`PSL34.lean`, whose global
`Fintype (GaloisField 2 2)` instance conflicts with the explicit `Fintype.ofFinite` instances
used in the fragile `native_decide`/`+decide` cardinality proofs `PSL34_card`, `M21_card`
above.  Keeping this file free of that import preserves those proofs unchanged.
-/

/-- **`PSL(2,11) ↪ M₁₁`.** There is an injective homomorphism `PSL(2, 11) → M₁₁`;
equivalently `M₁₁` contains a subgroup isomorphic to `PSL(2, 11)`.
Proved in `Mathieu.PSL211` (`Mathieu.PSL211.embeds`): `SL(2,𝔽₁₁)` acts on the
`11` cosets of an index-`11` subgroup `K ≅ 2.A₅` (the exceptional `2`-transitive action), the
generators `T, S` map to elements of `M₁₁`, and the action is faithful modulo the centre. -/
theorem PSL211_embeds_M11 :
    ∃ f : PSL(2, ZMod 11) →* M11, Function.Injective f :=
  PSL211.embeds

/-- **`PSL(2,23) ↪ M₂₄`.** There is an injective homomorphism `PSL(2, 23) → M₂₄`.
Proved in `Mathieu.PSL223` (`Mathieu.PSL223.embeds`): `SL(2,𝔽₂₃)` acts on the
projective line `ℙ¹(𝔽₂₃) ≃ Fin 24` by Möbius transformations; the generators `T, S` map to the
`M₂₄` generators `m24a, m24c`, and the action is faithful modulo the centre. -/
theorem PSL223_embeds_M24 :
    ∃ f : PSL(2, ZMod 23) →* M24, Function.Injective f :=
  PSL223.embeds

end Mathieu