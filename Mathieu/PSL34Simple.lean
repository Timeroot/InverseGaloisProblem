import Mathieu.EnumSL34
import Mathieu.TransPSL34
import Mathieu.PSL34

/-!
# Simplicity of `PSL(3, 4)` — step 1: perfectness of `SL(3, F4)`

Towards `IsSimpleGroup (PSL(3, GaloisField 2 2))` (hence `M₂₁` simple, and thence a clean,
`native_decide`-free inductive simplicity proof of `M₂₂`), the first ingredient is that
`SL(3, F4)` is a **perfect** group: its commutator subgroup is everything.

The argument is the classical one: over a field with `> 2` elements (here `F4`), every
elementary transvection `t_{ij}(c)` is a commutator of two transvections — for `n = 3` we always
have a third index `k`, and `[t_{ik}(1), t_{kj}(c)] = t_{ij}(c)`.  In characteristic two every
transvection is its own inverse, so the commutator `⁅a, b⁆ = a b a⁻¹ b⁻¹` is the plain product
`a b a b`, exactly matching the identities already used in `EnumSL34.lean`.  Since the
transvections generate `SL(3, F4)`, the commutator subgroup is everything.
-/

namespace Mathieu

open Matrix
open scoped MatrixGroups

namespace PSL34

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The transvection `t_{ij}(c)` as an element of `SL(3, F4)`. -/
noncomputable def tSL (i j : Fin 3) (hij : i ≠ j) (c : F4) : SL(3, F4) :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

@[simp] lemma coe_tSL (i j : Fin 3) (hij : i ≠ j) (c : F4) :
    (tSL i j hij c : Matrix (Fin 3) (Fin 3) F4) = Matrix.transvection i j c := rfl

/-- In characteristic two, each transvection is its own inverse. -/
lemma tSL_inv (i j : Fin 3) (hij : i ≠ j) (c : F4) : (tSL i j hij c)⁻¹ = tSL i j hij c := by
  have h : tSL i j hij c * tSL i j hij c = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tSL, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.transvection_mul_transvection_same _ _ hij,
      show c + c = 0 from by decide +revert, Matrix.transvection_zero]
  exact inv_eq_of_mul_eq_one_right h

/-
Every elementary transvection lies in the commutator subgroup of `SL(3, F4)`.
For `n = 3`, pick the third index `k`; then `t_{ij}(c) = ⁅t_{ik}(1), t_{kj}(c)⁆`.
-/
lemma tSL_mem_commutator (i j : Fin 3) (hij : i ≠ j) (c : F4) :
    tSL i j hij c ∈ commutator (SL(3, F4)) := by
  have h : tSL i j hij c = ⁅tSL i (if i = 0 then if j = 1 then 2 else 1 else if i = 1 then if j = 0 then 2 else 0 else if j = 0 then 1 else 0) (by fin_cases i <;> fin_cases j <;> trivial) 1, tSL (if i = 0 then if j = 1 then 2 else 1 else if i = 1 then if j = 0 then 2 else 0 else if j = 0 then 1 else 0) j (by fin_cases i <;> fin_cases j <;> trivial) c⁆ := by
    rw [ commutatorElement_def, tSL_inv, tSL_inv ];
    refine' Subtype.ext _;
    fin_cases i <;> fin_cases j <;> simp +decide [ coe_tSL ] at hij ⊢;
    all_goals revert c; decide;
  exact h.symm ▸ Subgroup.commutator_mem_commutator ( Subgroup.mem_top _ ) ( Subgroup.mem_top _ )

/-! ### Any subgroup containing all transvections is everything

A reusable packaging (mirroring `EnumSL34`'s `InCl` machinery, but parametrised over an
arbitrary target subgroup `H` that contains every elementary transvection).  Instantiated at
`H = commutator (SL(3,F4))` it gives perfectness; instantiated at a transvection-closure it gives
the generation statement used for the Iwasawa structure. -/

section Generate

/-- `M` is the underlying matrix of some element of `H`. -/
def InSub (H : Subgroup (SL(3, F4))) (M : Matrix (Fin 3) (Fin 3) F4) : Prop :=
  ∃ s : SL(3, F4), s ∈ H ∧ (s : Matrix (Fin 3) (Fin 3) F4) = M

variable {H : Subgroup (SL(3, F4))}

lemma InSub.one : InSub H 1 := ⟨1, one_mem _, by simp⟩

lemma InSub.mul {A B} (hA : InSub H A) (hB : InSub H B) : InSub H (A * B) := by
  obtain ⟨s, hs, rfl⟩ := hA; obtain ⟨t, ht, rfl⟩ := hB
  exact ⟨s * t, mul_mem hs ht, by rw [Matrix.SpecialLinearGroup.coe_mul]⟩

/-- Every elementary transvection matrix lies in `H`. -/
lemma InSub.trans (hH : ∀ i j (hij : i ≠ j) c, tSL i j hij c ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (c : F4) : InSub H (transvection i j c) :=
  ⟨tSL i j hij c, hH i j hij c, rfl⟩

/-- The "top" torus word `diag(x, x⁻¹, 1)` is a product of transvections (`EnumSL34.Htop`). -/
lemma InSub.diagTop (hH : ∀ i j (hij : i ≠ j) c, tSL i j hij c ∈ H) (x : F4) (hx : x ≠ 0) :
    InSub H (diagonal ![x, x⁻¹, 1]) := by
  rw [show (diagonal ![x, x⁻¹, 1] : Matrix (Fin 3) (Fin 3) F4)
      = transvection 0 1 x * transvection 1 0 x⁻¹ * transvection 0 1 x
        * transvection 0 1 1 * transvection 1 0 1 * transvection 0 1 1
      from by revert x hx; decide]
  exact ((((((InSub.trans hH 0 1 (by decide) x).mul (InSub.trans hH 1 0 (by decide) x⁻¹)).mul
    (InSub.trans hH 0 1 (by decide) x)).mul (InSub.trans hH 0 1 (by decide) 1)).mul
    (InSub.trans hH 1 0 (by decide) 1)).mul (InSub.trans hH 0 1 (by decide) 1))

/-- The "bottom" torus word `diag(1, x, x⁻¹)` is a product of transvections (`EnumSL34.Hbot`). -/
lemma InSub.diagBot (hH : ∀ i j (hij : i ≠ j) c, tSL i j hij c ∈ H) (x : F4) (hx : x ≠ 0) :
    InSub H (diagonal ![1, x, x⁻¹]) := by
  rw [show (diagonal ![1, x, x⁻¹] : Matrix (Fin 3) (Fin 3) F4)
      = transvection 1 2 x * transvection 2 1 x⁻¹ * transvection 1 2 x
        * transvection 1 2 1 * transvection 2 1 1 * transvection 1 2 1
      from by revert x hx; decide]
  exact ((((((InSub.trans hH 1 2 (by decide) x).mul (InSub.trans hH 2 1 (by decide) x⁻¹)).mul
    (InSub.trans hH 1 2 (by decide) x)).mul (InSub.trans hH 1 2 (by decide) 1)).mul
    (InSub.trans hH 2 1 (by decide) 1)).mul (InSub.trans hH 1 2 (by decide) 1))

/-- Every determinant-one diagonal matrix lies in `H` (`EnumSL34.incl_diagonal`). -/
lemma InSub.diag_det_one (hH : ∀ i j (hij : i ≠ j) c, tSL i j hij c ∈ H)
    (D : Fin 3 → F4) (hdet : (Matrix.diagonal D).det = 1) : InSub H (Matrix.diagonal D) := by
  have hD : D = ![D 0, D 1, D 2] := by funext i; fin_cases i <;> rfl
  rw [hD]
  have hprod : D 0 * D 1 * D 2 = 1 := by
    have h2 := hdet; rw [hD] at h2
    simpa [Matrix.det_diagonal, Fin.prod_univ_three] using h2
  have ha : D 0 ≠ 0 := by rintro h; rw [h] at hprod; simp at hprod
  have hb : D 1 ≠ 0 := by rintro h; rw [h] at hprod; simp at hprod
  have hab : D 0 * D 1 ≠ 0 := mul_ne_zero ha hb
  rw [show (Matrix.diagonal ![D 0, D 1, D 2] : Matrix (Fin 3) (Fin 3) F4)
      = Matrix.diagonal ![D 0, (D 0)⁻¹, 1] * Matrix.diagonal ![1, D 0 * D 1, (D 0 * D 1)⁻¹]
      from by
        revert hprod; generalize D 0 = a; generalize D 1 = b; generalize D 2 = c
        revert a b c; decide]
  exact (InSub.diagTop hH (D 0) ha).mul (InSub.diagBot hH (D 0 * D 1) hab)

/-- **If a subgroup `H ≤ SL(3, F4)` contains every elementary transvection, then `H = ⊤`.**
Since `SL` over a field is generated by transvections and det-one diagonal matrices, and the
latter are themselves products of transvections. -/
theorem tSL_generate (hH : ∀ i j (hij : i ≠ j) c, tSL i j hij c ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  have hgdet : ((g : Matrix (Fin 3) (Fin 3) F4)).det = 1 := g.2
  have hP : InSub H (g : Matrix (Fin 3) (Fin 3) F4) := by
    refine Matrix.diagonal_transvection_induction (InSub H) _ ?_ ?_ ?_
    · intro D hD; exact InSub.diag_det_one hH D (hD.trans hgdet)
    · intro t; rw [Matrix.TransvectionStruct.toMatrix]
      exact InSub.trans hH t.i t.j t.hij t.c
    · intro A B hA hB; exact hA.mul hB
  obtain ⟨s, hs, hse⟩ := hP
  have hsg : s = g := Subtype.ext hse
  rwa [hsg] at hs

end Generate

/-- **`SL(3, F4)` is perfect.** The commutator subgroup is everything: the transvections
generate `SL(3, F4)` and each is a commutator. -/
theorem SL34_perfect : commutator (SL(3, F4)) = ⊤ :=
  tSL_generate (fun i j hij c => tSL_mem_commutator i j hij c)

/-! ## The faithful action of `PSL(3, F4)` on the projective plane `P` -/

section Action

open MulAction Equiv
open scoped Pointwise

/-- The plane action of `SL(3, F4)` descends to `PSL(3, F4)`, since the centre (= kernel of the
action, `ker_psiP`) acts trivially. -/
noncomputable def psiPbar : PSL(3, F4) →* Perm P :=
  QuotientGroup.lift (Subgroup.center (SL(3, F4))) psiP (by rw [ker_psiP])

@[simp] lemma psiPbar_mk (g : SL(3, F4)) :
    psiPbar (QuotientGroup.mk g) = psiP g := QuotientGroup.lift_mk' _ _ g

lemma psiPbar_injective : Function.Injective psiPbar := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [psiPbar_mk] at hq
  rw [QuotientGroup.eq_one_iff, ← ker_psiP]
  exact hq

/-- The induced faithful `MulAction` of `PSL(3, F4)` on the `21` projective points. -/
noncomputable instance instMulActionPSL : MulAction (PSL(3, F4)) P := MulAction.compHom P psiPbar

lemma psl_smul_def (q : PSL(3, F4)) (x : P) : q • x = psiPbar q x := rfl

/-- The `PSL`-action agrees with the `SL`-action through the quotient map. -/
lemma psl_smul_mk (g : SL(3, F4)) (x : P) : (QuotientGroup.mk g : PSL(3, F4)) • x = g • x := by
  rw [psl_smul_def, psiPbar_mk]
  rfl

instance instFaithfulPSL : FaithfulSMul (PSL(3, F4)) P := by
  refine ⟨fun {q1 q2} h => psiPbar_injective (Equiv.ext fun x => ?_)⟩
  have := h x
  rwa [psl_smul_def, psl_smul_def] at this

/-
Multiple transitivity transfers from `SL(3, F4)` to the quotient `PSL(3, F4)`, since the
two actions agree through the surjection `SL → PSL`.
-/
lemma isMultiplyPretransitive_of_mk {n : ℕ}
    (h : IsMultiplyPretransitive (SL(3, F4)) P n) :
    IsMultiplyPretransitive (PSL(3, F4)) P n := by
  have h_trans : IsMultiplyPretransitive (PSL(3, F4)) P n := by
    have h_eq : psiPbar.range = psiP.range := by
      ext; simp [psiPbar];
      constructor <;> rintro ⟨ x, rfl ⟩;
      · obtain ⟨ y, rfl ⟩ := QuotientGroup.mk_surjective x; exact ⟨ y, rfl ⟩ ;
      · exact ⟨ QuotientGroup.mk x, rfl ⟩
    have h_psiPbar_trans : IsMultiplyPretransitive (PSL(3, F4)) P n := by
      have h_psiP_trans : IsMultiplyPretransitive (SL(3, F4)) P n := h
      exact ⟨ fun f₁ f₂ => by obtain ⟨ g, hg ⟩ := h_psiP_trans.exists_smul_eq f₁ f₂; exact ⟨ QuotientGroup.mk g, by aesop ⟩ ⟩
    exact h_psiPbar_trans;
  exact h_trans

/-- **`PSL(3, F4)` is `2`-transitive on the projective plane.** -/
theorem PSL34_two_transitive : IsMultiplyPretransitive (PSL(3, F4)) P 2 :=
  isMultiplyPretransitive_of_mk SL34_two_transitive

instance instPretransitivePSL : IsPretransitive (PSL(3, F4)) P := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := (psiP_transitive).exists_smul_eq x y
  exact ⟨QuotientGroup.mk g, by rw [psl_smul_mk]; exact hg⟩

instance instPreprimitivePSL : IsPreprimitive (PSL(3, F4)) P :=
  isPreprimitive_of_is_two_pretransitive PSL34_two_transitive

instance instNontrivialPSL : Nontrivial (PSL(3, F4)) := by
  obtain ⟨q, hq⟩ : ∃ q : PSL(3, F4), q ≠ 1 := by
    have := instPretransitivePSL.exists_smul_eq ( PSL34.p0 ) ( PSL34.p1 ) ; simp_all +decide [ ] ;
    obtain ⟨ g, hg ⟩ := this; use g; intro hg'; simp_all +decide [ ] ;
  exact ⟨ q, 1, hq ⟩

/-- **`PSL(3, F4)` is perfect** (quotient of the perfect group `SL(3, F4)`). -/
theorem PSL34_perfect : commutator (PSL(3, F4)) = ⊤ := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center (SL(3, F4)))) :=
    QuotientGroup.mk'_surjective _
  have hmap : Subgroup.map (QuotientGroup.mk' (Subgroup.center (SL(3, F4))))
      (commutator (SL(3, F4))) = commutator (PSL(3, F4)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj]
  rw [← hmap, SL34_perfect, Subgroup.map_top_of_surjective _ hsurj]

end Action

/-! ## Root subgroups and the Iwasawa structure

For a projective point `x = [v]`, the *root subgroup* consists of the elations with centre `[v]`
that fix the representative `v`: the `g ∈ SL(3, F4)` with `g w - w ∈ ⟨v⟩` for all `w` and
`g v = v`.  These subgroups are abelian, are permuted by conjugation (`R (g • x) = conj g • R x`),
and together generate `SL(3, F4)` (they contain all transvections).  Pushed to `PSL(3, F4)` they
form an Iwasawa structure, which — with perfectness, faithfulness and (quasi)primitivity —
yields simplicity by the Iwasawa criterion. -/

section Iwasawa

open MulAction Equiv
open scoped Pointwise

/-- The three coordinate projective points `[e₀], [e₁], [e₂]`. -/
def pe : Fin 3 → P :=
  ![⟨![1, 0, 0], by decide⟩, ⟨![0, 1, 0], by decide⟩, ⟨![0, 0, 1], by decide⟩]

/-- The carrier of the root subgroup at a projective point `x = [v]`: elations with centre `[v]`
that fix `v`. -/
def RSLcarrier (x : P) : Set (SL(3, F4)) :=
  {g | (∀ w, (↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w ∈ Submodule.span F4 {x.val}) ∧
       (↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ x.val = x.val}

lemma RSL_one_mem (x : P) : (1 : SL(3, F4)) ∈ RSLcarrier x := by
  constructor <;> aesop

lemma RSL_mul_mem (x : P) {a b : SL(3, F4)} (ha : a ∈ RSLcarrier x) (hb : b ∈ RSLcarrier x) :
    a * b ∈ RSLcarrier x := by
  constructor;
  · intro w
    have h1 := ha.1 ((b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w)
    have h2 := hb.1 w
    have h3 : ((a * b : SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = ((a : Matrix (Fin 3) (Fin 3) F4) *ᵥ ((b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) - (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) + ((b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w) := by
      simp +decide [ Matrix.mulVec_mulVec, sub_add_sub_cancel ];
    exact h3.symm ▸ Submodule.add_mem _ h1 h2;
  · simp_all +decide [ RSLcarrier ];
    rw [ ← Matrix.mulVec_mulVec, hb.2, ha.2 ]

lemma RSL_inv_mem (x : P) {a : SL(3, F4)} (ha : a ∈ RSLcarrier x) : a⁻¹ ∈ RSLcarrier x := by
  simp_all +decide [ RSLcarrier ];
  have h_inv : (a : Matrix (Fin 3) (Fin 3) F4) * (a⁻¹ : SL(3, F4)).val = 1 := by
    simp +decide [ Matrix.mul_adjugate ];
  simp_all +decide [ ];
  have h_inv : ∀ w : Fin 3 → F4, (a : Matrix (Fin 3) (Fin 3) F4).adjugate *ᵥ w - w ∈ Submodule.span F4 {x.val} := by
    intro w
    have h_inv : (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ ((a⁻¹ : SL(3, F4)).val *ᵥ w) - ((a⁻¹ : SL(3, F4)).val *ᵥ w) ∈ Submodule.span F4 {x.val} := by
      exact ha.1 _;
    simp_all +decide [ Matrix.mulVec_mulVec ];
    simpa using Submodule.neg_mem _ h_inv;
  have := ha.2; simp_all +decide [ ] ;
  replace := congr_arg ( fun w => ( a : Matrix ( Fin 3 ) ( Fin 3 ) F4 ).adjugate *ᵥ w ) this; simp_all +decide [ Matrix.mulVec_mulVec ] ;
  rw [ ← this, Matrix.adjugate_mul ] ; aesop

/-- The root subgroup at a projective point `x`. -/
def RSL (x : P) : Subgroup (SL(3, F4)) where
  carrier := RSLcarrier x
  one_mem' := RSL_one_mem x
  mul_mem' ha hb := RSL_mul_mem x ha hb
  inv_mem' ha := RSL_inv_mem x ha

lemma mem_RSL {x : P} {g : SL(3, F4)} :
    g ∈ RSL x ↔ (∀ w, (↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w ∈ Submodule.span F4 {x.val}) ∧
      (↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ x.val = x.val := Iff.rfl

/-
**Root subgroups are abelian.**
-/
lemma RSL_comm (x : P) {a b : SL(3, F4)} (ha : a ∈ RSL x) (hb : b ∈ RSL x) : a * b = b * a := by
  simp_all +decide [ mem_RSL ];
  -- By definition of $RSL$, we know that $a * b = b * a$.
  have h_comm : ∀ w : Fin 3 → F4, (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ ((b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) = (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ ((a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) := by
    intro w
    have h_comm : (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w + (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w := by
      obtain ⟨t, ht⟩ : ∃ t : F4, (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = t • x.val := by
        exact Submodule.mem_span_singleton.mp ( hb.1 w ) |> fun ⟨ t, ht ⟩ => ⟨ t, ht ▸ rfl ⟩;
      simp_all +decide [ sub_eq_iff_eq_add', Matrix.mulVec_add, Matrix.mulVec_smul ];
      abel1;
    have h_comm : (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = (b : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w + (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w := by
      obtain ⟨t, ht⟩ : ∃ t : F4, (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = t • x.val := by
        simpa [ eq_comm ] using Submodule.mem_span_singleton.mp ( ha.1 w );
      simp_all +decide [ sub_eq_iff_eq_add, Matrix.mulVec_add, Matrix.mulVec_smul ];
      exact add_comm _ _;
    grind;
  exact Subtype.ext ( Matrix.toLin'.injective ( LinearMap.ext fun w => by simpa [ Matrix.mulVec_mulVec ] using h_comm w ) )

/-
**Conjugation permutes the root subgroups**: `R (h • x) = conj h • R x`.
-/
lemma RSL_conj (h : SL(3, F4)) (x : P) :
    (RSL x).map (MulAut.conj h).toMonoidHom = RSL (h • x) := by
  ext g';
  constructor <;> intro hg' <;> simp_all +decide [ RSL, Subgroup.mem_map ];
  · obtain ⟨ g, hg, rfl ⟩ := hg';
    constructor <;> simp_all +decide [ RSLcarrier ];
    · intro w
      have h_comm : (h * g * h⁻¹ : SL(3, F4)).val *ᵥ w - w = h.val *ᵥ ((g : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h⁻¹.val *ᵥ w)) - h.val *ᵥ (h⁻¹.val *ᵥ w) := by
        simp +decide [ ← Matrix.mul_assoc, Matrix.mul_adjugate ];
      have h_comm : (h.val *ᵥ ((g : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h⁻¹.val *ᵥ w)) - h.val *ᵥ (h⁻¹.val *ᵥ w)) ∈ Submodule.span F4 {h.val *ᵥ x.val} := by
        have h_comm : (g : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h⁻¹.val *ᵥ w) - h⁻¹.val *ᵥ w ∈ Submodule.span F4 {x.val} := by
          exact hg.1 _;
        rw [ Submodule.mem_span_singleton ] at *;
        obtain ⟨ a, ha ⟩ := h_comm; use a; simp_all +decide [ ← Matrix.mulVec_smul ] ;
        simp +decide [ Matrix.mulVec_sub ];
      convert h_comm using 1;
      rw [ PSL34.smul_def, PSL34.nrm_eq_smul ];
      rw [ Submodule.span_singleton_smul_eq ];
      exact isUnit_iff_ne_zero.mpr ( inv_ne_zero <| by have := PSL34.leadIdx_spec ( h.val *ᵥ x.val ) ( PSL34.mulVec_ne_zero _ _ x.2.1 ) ; aesop );
    · rw [ PSL34.smul_def ];
      rw [ nrm_eq_smul ];
      simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul ];
      simp_all +decide [ Matrix.adjugate_mul, Matrix.mulVec_smul ];
  · refine' ⟨ h⁻¹ * g' * h, _, _ ⟩;
    · constructor;
      · intro w
        have h_comm : (h⁻¹ * g' * h : Matrix (Fin 3) (Fin 3) F4) *ᵥ w - w = h⁻¹.val *ᵥ ((g' : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h.val *ᵥ w) - (h.val *ᵥ w)) := by
          simp +decide [ Matrix.mulVec_sub, Matrix.mulVec_mulVec ];
          simp +decide [ Matrix.mul_assoc, Matrix.adjugate_mul ];
        have h_comm : (g' : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h.val *ᵥ w) - (h.val *ᵥ w) ∈ Submodule.span F4 {(h • x).val} := by
          exact hg'.1 _;
        have h_comm : (h⁻¹.val *ᵥ ((g' : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h.val *ᵥ w) - (h.val *ᵥ w))) ∈ Submodule.span F4 {h⁻¹.val *ᵥ (h.val *ᵥ x.val)} := by
          have h_comm : (g' : Matrix (Fin 3) (Fin 3) F4) *ᵥ (h.val *ᵥ w) - (h.val *ᵥ w) ∈ Submodule.span F4 {h.val *ᵥ x.val} := by
            have h_comm : (nrm (h.val *ᵥ x.val)) ∈ Submodule.span F4 {h.val *ᵥ x.val} := by
              exact nrm_eq_smul _ |> fun h => h.symm ▸ Submodule.smul_mem _ _ ( Submodule.mem_span_singleton_self _ );
            exact Submodule.span_le.mpr ( Set.singleton_subset_iff.mpr h_comm ) ‹_›;
          obtain ⟨ t, ht ⟩ := Submodule.mem_span_singleton.mp h_comm;
          rw [ ← ht ];
          simp +decide [ Matrix.mulVec_smul, Submodule.mem_span_singleton ];
        simp_all +decide [ Matrix.adjugate_mul ];
      · have := hg'.2; simp_all +decide [ ] ;
        simp_all +decide [ PSL34.smul_def, nrm_eq_smul ];
        simp_all +decide [ Matrix.mul_assoc, Matrix.mulVec_smul, Matrix.mulVec_mulVec ];
        replace this := congr_arg ( fun w => ( h : Matrix ( Fin 3 ) ( Fin 3 ) F4 ).adjugate *ᵥ w ) this ; simp_all +decide [ Matrix.mulVec_smul, Matrix.mulVec_mulVec ];
        simp_all +decide [ Matrix.adjugate_mul ];
        exact smul_right_injective _ ( inv_ne_zero <| show ( h.val *ᵥ x.val ) ( leadIdx ( h.val *ᵥ x.val ) ) ≠ 0 from mulVec_ne_zero _ _ x.2.1 |> fun h => leadIdx_spec _ h ) this;
    · simp +decide [ ← mul_assoc ]

/-
Every transvection `t_{ij}(c)` lies in the root subgroup at its centre `[eᵢ]`.
-/
lemma RSL_transvection (i j : Fin 3) (hij : i ≠ j) (c : F4) : tSL i j hij c ∈ RSL (pe i) := by
  refine' ⟨ _, _ ⟩;
  · fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.transvection ] at hij ⊢;
    all_goals simp +decide [ Submodule.mem_span_singleton, Matrix.single ] ;
    all_goals simp +decide [ funext_iff, Fin.forall_fin_succ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pe ];
  · fin_cases i <;> fin_cases j <;> simp +decide [ tSL, pe ] at hij ⊢ <;>
      (revert c; decide)

/-- The root subgroups generate all of `SL(3, F4)`. -/
lemma RSL_iSup : (⨆ x, RSL x) = ⊤ :=
  tSL_generate (fun i j hij c => (le_iSup RSL (pe i)) (RSL_transvection i j hij c))

/-- The image of the root subgroup at `x` in `PSL(3, F4)`. -/
def T (x : P) : Subgroup (PSL(3, F4)) :=
  (RSL x).map (QuotientGroup.mk' (Subgroup.center (SL(3, F4))))

lemma T_comm (x : P) : IsMulCommutative (T x) := by
  refine' ⟨ ⟨ _ ⟩ ⟩;
  simp +zetaDelta at *;
  intros a ha b hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_mul, ← map_mul, RSL_comm x ha' hb']

lemma T_conj (g : PSL(3, F4)) (x : P) : T (g • x) = MulAut.conj g • T x := by
  obtain ⟨ h, rfl ⟩ := QuotientGroup.mk_surjective g;
  ext;
  constructor <;> rintro ⟨ a, ha, rfl ⟩;
  · obtain ⟨ b, hb, rfl ⟩ := RSL_conj h x |>.ge ha;
    exact ⟨ _, ⟨ b, hb, rfl ⟩, rfl ⟩;
  · obtain ⟨ b, hb, rfl ⟩ := ha;
    convert Subgroup.mem_map_of_mem _ ( RSL_conj h x ▸ Subgroup.mem_map_of_mem _ hb ) using 1

lemma T_iSup : (⨆ x, T x) = ⊤ := by
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center (SL(3, F4)))
  simp only [T]
  rw [← Subgroup.map_iSup, RSL_iSup, Subgroup.map_top_of_surjective _ hsurj]

/-- The Iwasawa structure of `PSL(3, F4)` acting on the projective plane. -/
def iwa : IwasawaStructure (PSL(3, F4)) P where
  T := T
  is_comm := T_comm
  is_conj := T_conj
  is_generator := T_iSup

/-- **`PSL(3, F4)` is a simple group.** -/
theorem PSL34_isSimpleGroup : IsSimpleGroup (PSL(3, F4)) :=
  iwa.isSimpleGroup PSL34_perfect instFaithfulPSL

/-- The base-field iso `F4 ≃+* GaloisField 2 2` induces `SL(3, F4) ≃* SL(3, GaloisField 2 2)`. -/
noncomputable def eSL : SL(3, F4) ≃* SL(3, GaloisField 2 2) := mapEquiv F4.equivGaloisField

/-- **`PSL(3, GaloisField 2 2)` is a simple group** (transport of `PSL34_isSimpleGroup` along the
base-field isomorphism `F4 ≃+* GaloisField 2 2`).  This is the Mathlib spelling `PSL(3, 4)`. -/
theorem PSL34GF_isSimpleGroup : IsSimpleGroup (PSL(3, GaloisField 2 2)) := by
  haveI := PSL34_isSimpleGroup
  have hmap : Subgroup.map eSL.toMonoidHom (Subgroup.center (SL(3, F4)))
      = Subgroup.center (SL(3, GaloisField 2 2)) := by
    rw [← comap_center_eq eSL]
    exact Subgroup.map_comap_eq_self_of_surjective eSL.surjective _
  let E : PSL(3, F4) ≃* PSL(3, GaloisField 2 2) :=
    QuotientGroup.congr (Subgroup.center (SL(3, F4))) (Subgroup.center (SL(3, GaloisField 2 2)))
      eSL hmap
  exact MulEquiv.isSimpleGroup E.symm

end Iwasawa

end PSL34

end Mathieu