/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckKernel
import InverseGalois.Rigidity.RET.Analytic.Algebraicity

/-!
# The largest algebraic quotient of a covering

A covering of a punctured plane is cut out by a monic equation exactly when its functions of
moderate growth see its deck group (`RET/Analytic/Algebraicity.lean`).  The deck transformations
those functions do not see form a normal subgroup of the deck group, the kernel of the action on
the ring of functions (`RET/Analytic/DeckKernel.lean`).  Dividing the covering by that subgroup
costs nothing — the functions are constant on its orbits — and what is left is algebraic.

The quotient of the total space by a subgroup of the deck group is again a space over the plane,
and the projection is again a local homeomorphism: a chart of the covering, read through the
projection to the quotient, is a chart of the quotient, because the coordinate of the chart of the
covering inverts the projection of the quotient just as well.  Functions constant on the orbits of
the subgroup descend, and holomorphy and moderate growth descend with them, since the descended
function in the descended chart is the original function in the original chart.

## Main definitions

* `Rigidity.RET.CoverQuot` — the quotient of the total space of a covering by a subgroup of its
  deck group.
* `Rigidity.RET.quotBase` — the projection of the quotient to the plane.
* `Rigidity.RET.quotFun` — the function on the quotient a function constant on the orbits defines.

## Main results

* `Rigidity.RET.isLocalHomeomorph_quotBase` — the quotient is again a space over the plane whose
  projection is a local homeomorphism.
* `Rigidity.RET.quotFun_mem_coverRing` — a function of moderate growth constant on the orbits of
  the subgroup is a function of moderate growth on the quotient.
* `Rigidity.RET.exists_algebraic_model_quotient` — **the quotient of a covering of a punctured
  plane by the deck transformations its functions of moderate growth do not see is cut out by a
  monic equation**, away from finitely many points of the base.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

/-- **The quotient of the total space of a covering by a subgroup of its deck group.** -/
abbrev CoverQuot {H : Type*} [Group H] (Y : Type*) [MulAction H Y] (N : Subgroup H) : Type _ :=
  Quotient (MulAction.orbitRel ↥N Y)

section Space

variable {Y : Type*} [TopologicalSpace Y] {H : Type*} [Group H] [MulAction H Y] {N : Subgroup H}

omit [TopologicalSpace Y] in
/-- **Two points of the covering have the same image in the quotient exactly when a member of the
subgroup carries one to the other.** -/
theorem coverQuot_eq_iff {y y' : Y} :
    (Quotient.mk _ y : CoverQuot Y N) = Quotient.mk _ y' ↔ ∃ n ∈ N, n • y' = y := by
  refine ⟨fun h => ?_, fun ⟨n, hn, h⟩ => Quotient.sound ⟨⟨n, hn⟩, h⟩⟩
  obtain ⟨n, hn⟩ := Quotient.exact h
  exact ⟨(n : H), n.2, hn⟩

omit [TopologicalSpace Y] in
/-- A member of the subgroup does not move the image of a point in the quotient. -/
theorem coverQuot_mk_smul {n : H} (hn : n ∈ N) (y : Y) :
    (Quotient.mk _ (n • y) : CoverQuot Y N) = Quotient.mk _ y :=
  coverQuot_eq_iff.2 ⟨n, hn, rfl⟩

/-- The projection of the covering to the quotient is a surjective open map. -/
theorem isOpenQuotientMap_coverQuot (N : Subgroup H) [ContinuousConstSMul H Y] :
    IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel ↥N Y) : Y → CoverQuot Y N) :=
  letI : ContinuousConstSMul ↥N Y := ⟨fun n => continuous_const_smul (n : H)⟩
  MulAction.isOpenQuotientMap_quotientMk

instance coverQuot_nonempty [Nonempty Y] (N : Subgroup H) : Nonempty (CoverQuot Y N) :=
  ⟨Quotient.mk _ (Classical.arbitrary Y)⟩

instance coverQuot_preconnectedSpace [PreconnectedSpace Y] (N : Subgroup H) :
    PreconnectedSpace (CoverQuot Y N) :=
  Quot.mk_surjective.denseRange.preconnectedSpace continuous_quot_mk

/-! ### The deck group of the quotient -/

/-- **The deck group acts on the quotient by a normal subgroup of it.** -/
instance coverQuotSMul (N : Subgroup H) [N.Normal] : SMul H (CoverQuot Y N) where
  smul a := Quotient.map (a • ·) fun y y' h => by
    obtain ⟨n, hn⟩ := h
    refine ⟨⟨a * (n : H) * a⁻¹, ‹N.Normal›.conj_mem _ n.2 a⟩, ?_⟩
    show (a * (n : H) * a⁻¹) • (a • y') = a • y
    rw [← hn]
    show (a * (n : H) * a⁻¹) • (a • y') = a • ((n : H) • y')
    rw [smul_smul, smul_smul]
    congr 1
    group

omit [TopologicalSpace Y] in
@[simp]
theorem coverQuot_smul_mk [N.Normal] (a : H) (y : Y) :
    a • (Quotient.mk _ y : CoverQuot Y N) = Quotient.mk _ (a • y) := rfl

instance coverQuotMulAction (N : Subgroup H) [N.Normal] : MulAction H (CoverQuot Y N) where
  one_smul := Quotient.ind fun y => congrArg (Quotient.mk _) (one_smul H y)
  mul_smul a b := Quotient.ind fun y => congrArg (Quotient.mk _) (mul_smul a b y)

omit [TopologicalSpace Y] in
/-- The subgroup itself acts trivially on the quotient by it. -/
theorem coverQuot_toPermHom_eq_one [N.Normal] {n : H} (hn : n ∈ N) :
    MulAction.toPermHom H (CoverQuot Y N) n = 1 := by
  refine Equiv.ext ?_
  intro z
  induction z using Quotient.ind with
  | _ y => exact coverQuot_mk_smul hn y

/-- **The quotient of the deck group by a normal subgroup acts on the quotient of the covering by
that subgroup.** -/
instance coverQuotQuotientAction (N : Subgroup H) [N.Normal] :
    MulAction (H ⧸ N) (CoverQuot Y N) :=
  MulAction.compHom _ (QuotientGroup.lift N (MulAction.toPermHom H (CoverQuot Y N))
    fun _ hn => coverQuot_toPermHom_eq_one hn)

omit [TopologicalSpace Y] in
@[simp]
theorem coverQuot_quotient_smul_mk [N.Normal] (a : H) (y : Y) :
    (QuotientGroup.mk a : H ⧸ N) • (Quotient.mk _ y : CoverQuot Y N) = Quotient.mk _ (a • y) :=
  rfl

instance coverQuot_continuousConstSMul [ContinuousConstSMul H Y] (N : Subgroup H) [N.Normal] :
    ContinuousConstSMul H (CoverQuot Y N) := by
  refine ⟨fun a => ?_⟩
  rw [(isOpenQuotientMap_coverQuot N).isQuotientMap.continuous_iff]
  exact continuous_quot_mk.comp (continuous_const_smul a)

instance coverQuot_quotient_continuousConstSMul [ContinuousConstSMul H Y] (N : Subgroup H)
    [N.Normal] : ContinuousConstSMul (H ⧸ N) (CoverQuot Y N) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  exact continuous_const_smul (a : H)

end Space

/-! ### The projection of the quotient to the plane -/

section Base

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {H : Type*} [Group H] [MulAction H Y]
  {N : Subgroup H}

/-- **The projection of the quotient of a covering to the plane.** -/
def quotBase (f : Y → ℂ) (N : Subgroup H) [IsOverBase H f] : CoverQuot Y N → ℂ :=
  Quotient.lift f fun y y' h => by
    obtain ⟨n, hn⟩ := h
    rw [← hn]
    exact IsOverBase.smul_eq (n : H) y'

omit [TopologicalSpace Y] in
@[simp]
theorem quotBase_mk [IsOverBase H f] (y : Y) :
    quotBase f N (Quotient.mk _ y) = f y := rfl

theorem continuous_quotBase [IsOverBase H f] (hcont : Continuous f) :
    Continuous (quotBase f N) := hcont.quotient_lift _

omit [TopologicalSpace Y] in
theorem range_quotBase [IsOverBase H f] : Set.range (quotBase f N) = Set.range f := by
  refine Set.Subset.antisymm ?_ (fun _ ⟨y, hy⟩ => ⟨Quotient.mk _ y, hy⟩)
  rintro _ ⟨z, rfl⟩
  induction z using Quotient.ind with
  | _ y => exact ⟨y, rfl⟩

instance quotBase_isOverBase [IsOverBase H f] (N : Subgroup H) [N.Normal] :
    IsOverBase (H ⧸ N) (quotBase f N) where
  smul_eq x z := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    induction z using Quotient.ind with
    | _ y => exact IsOverBase.smul_eq a y

omit [TopologicalSpace Y] in
/-- **The points of a fibre of the quotient are carried to one another by the deck group of the
quotient**, as soon as the points of a fibre of the covering are. -/
theorem quotBase_transitive [IsOverBase H f] [N.Normal]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y) (z z' : CoverQuot Y N)
    (h : quotBase f N z = quotBase f N z') : ∃ x : H ⧸ N, z' = x • z := by
  induction z using Quotient.ind with
  | _ y =>
    induction z' using Quotient.ind with
    | _ y' =>
      obtain ⟨c, rfl⟩ := htrans y y' h
      exact ⟨QuotientGroup.mk c, rfl⟩

end Base

/-! ### Charts on the quotient -/

section Chart

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {H : Type*} [Group H] [MulAction H Y]
  [ContinuousConstSMul H Y] [IsOverBase H f]

/-- **A local coordinate on the quotient of a covering**: the projection of the quotient to the
plane, inverted by the image in the quotient of the inverse of a local coordinate of the
covering. -/
def quotChart (N : Subgroup H) (hf : IsLocalHomeomorph f) (d : OpenPartialHomeomorph Y ℂ)
    (hd : f = ⇑d) : OpenPartialHomeomorph (CoverQuot Y N) ℂ where
  toFun := quotBase f N
  invFun w := Quotient.mk _ (d.symm w)
  source := (Quotient.mk (MulAction.orbitRel ↥N Y)) '' d.source
  target := d.target
  map_source' := by
    rintro _ ⟨u, hu, rfl⟩
    show quotBase f N (Quotient.mk _ u) ∈ d.target
    rw [quotBase_mk, congrFun hd u]
    exact d.map_source hu
  map_target' w hw := ⟨d.symm w, d.map_target hw, rfl⟩
  left_inv' := by
    rintro _ ⟨u, hu, rfl⟩
    show Quotient.mk _ (d.symm (quotBase f N (Quotient.mk _ u))) = Quotient.mk _ u
    rw [quotBase_mk, congrFun hd u, d.left_inv hu]
  right_inv' w hw := by
    show quotBase f N (Quotient.mk _ (d.symm w)) = w
    rw [quotBase_mk, congrFun hd (d.symm w), d.right_inv hw]
  open_source := (isOpenQuotientMap_coverQuot N).isOpenMap _ d.open_source
  open_target := d.open_target
  continuousOn_toFun := (continuous_quotBase hf.continuous).continuousOn
  continuousOn_invFun := continuous_quot_mk.comp_continuousOn d.continuousOn_symm

/-- **The projection of the quotient of a covering to the plane is a local homeomorphism.** -/
theorem isLocalHomeomorph_quotBase (hf : IsLocalHomeomorph f) (N : Subgroup H) :
    IsLocalHomeomorph (quotBase f N) := by
  intro z
  induction z using Quotient.ind with
  | _ y =>
    obtain ⟨d, hy, hd⟩ := hf y
    exact ⟨quotChart N hf d hd, ⟨y, hy, rfl⟩, rfl⟩

end Chart

/-! ### Functions on the quotient -/

section Descend

variable {Y : Type*} [TopologicalSpace Y] {f F : Y → ℂ} {S : Finset ℂ} {H : Type*} [Group H]
  [MulAction H Y] [ContinuousConstSMul H Y] [IsOverBase H f] {N : Subgroup H}

/-- **The function on the quotient defined by a function constant on the orbits of the
subgroup.** -/
def quotFun (N : Subgroup H) (F : Y → ℂ) (hinv : ∀ n ∈ N, ∀ y : Y, F (n • y) = F y) :
    CoverQuot Y N → ℂ :=
  Quotient.lift F fun y y' h => by
    obtain ⟨n, hn⟩ := h
    rw [← hn]
    exact hinv (n : H) n.2 y'

omit [TopologicalSpace Y] [ContinuousConstSMul H Y] in
@[simp]
theorem quotFun_mk {hinv : ∀ n ∈ N, ∀ y : Y, F (n • y) = F y} (y : Y) :
    quotFun N F hinv (Quotient.mk _ y) = F y := rfl

/-- **A holomorphic function constant on the orbits of the subgroup is holomorphic on the
quotient**: in the local coordinate of the quotient read off a local coordinate of the covering it
is the original function in the original coordinate. -/
theorem isHolo_quotFun (hf : IsLocalHomeomorph f) (hF : IsHolo f F)
    (hinv : ∀ n ∈ N, ∀ y : Y, F (n • y) = F y) :
    IsHolo (quotBase f N) (quotFun N F hinv) := by
  intro z
  induction z using Quotient.ind with
  | _ y =>
    obtain ⟨d, hy, hd⟩ := hf y
    exact ⟨quotChart N hf d hd, ⟨⟨y, hy, rfl⟩, rfl⟩, (hF y).analyticAt_of_chart ⟨hy, hd⟩⟩

omit [TopologicalSpace Y] [ContinuousConstSMul H Y] in
/-- **A function of moderate growth constant on the orbits of the subgroup is of moderate growth on
the quotient.** -/
theorem isModerate_quotFun (hF : IsModerate f S F)
    (hinv : ∀ n ∈ N, ∀ y : Y, F (n • y) = F y) :
    IsModerate (quotBase f N) S (quotFun N F hinv) where
  punct s hs := by
    obtain ⟨ρ, hρ, C, hC, m, hbdd⟩ := hF.punct s hs
    exact ⟨ρ, hρ, C, hC, m, Quotient.ind fun y hy => hbdd y hy⟩
  infty := by
    obtain ⟨A, R₀, m, hA, hbdd⟩ := hF.infty
    exact ⟨A, R₀, m, hA, Quotient.ind fun y hy => hbdd y hy⟩

/-- **A function of moderate growth constant on the orbits of the subgroup is a function of the
quotient.** -/
theorem quotFun_mem_coverRing (hf : IsLocalHomeomorph f) (hF : F ∈ coverRing hf S)
    (hinv : ∀ n ∈ N, ∀ y : Y, F (n • y) = F y) :
    quotFun N F hinv ∈ coverRing (isLocalHomeomorph_quotBase hf N) S :=
  ⟨isHolo_quotFun hf hF.1 hinv, isModerate_quotFun hF.2 hinv⟩

/-! ### Functions pulled back from the quotient -/

/-- **A holomorphic function on the quotient is holomorphic on the covering**: it is read in a
local coordinate of the covering exactly as it is read in the local coordinate of the quotient that
coordinate defines. -/
theorem isHolo_comp_mk (hf : IsLocalHomeomorph f) {G : CoverQuot Y N → ℂ}
    (hG : IsHolo (quotBase f N) G) : IsHolo f fun y => G (Quotient.mk _ y) := by
  intro y
  obtain ⟨d, hy, hd⟩ := hf y
  have hchart : IsChartAt (quotBase f N) (quotChart N hf d hd) (Quotient.mk _ y) :=
    ⟨⟨y, hy, rfl⟩, rfl⟩
  exact ⟨d, ⟨hy, hd⟩, (hG _).analyticAt_of_chart hchart⟩

omit [TopologicalSpace Y] [ContinuousConstSMul H Y] in
/-- **A function of moderate growth on the quotient is of moderate growth on the covering.** -/
theorem isModerate_comp_mk {G : CoverQuot Y N → ℂ} (hG : IsModerate (quotBase f N) S G) :
    IsModerate f S fun y => G (Quotient.mk _ y) where
  punct s hs := by
    obtain ⟨ρ, hρ, C, hC, m, hbdd⟩ := hG.punct s hs
    exact ⟨ρ, hρ, C, hC, m, fun y hy => hbdd (Quotient.mk _ y) hy⟩
  infty := by
    obtain ⟨A, R₀, m, hA, hbdd⟩ := hG.infty
    exact ⟨A, R₀, m, hA, fun y hy => hbdd (Quotient.mk _ y) hy⟩

/-- **A function of the quotient is a function of the covering.** -/
theorem comp_mk_mem_coverRing (hf : IsLocalHomeomorph f) {G : CoverQuot Y N → ℂ}
    (hG : G ∈ coverRing (isLocalHomeomorph_quotBase hf N) S) :
    (fun y => G (Quotient.mk _ y)) ∈ coverRing hf S :=
  ⟨isHolo_comp_mk hf hG.1, isModerate_comp_mk hG.2⟩

end Descend

/-! ### The quotient by the unseen deck transformations -/

section Unseen

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ} {H : Type*} [Group H]
  [MulAction H Y] [ContinuousConstSMul H Y] [IsOverBase H f]

/-- **The functions of moderate growth of the quotient by the unseen deck transformations see its
deck group.**  A deck transformation outside the kernel is moved by a function of moderate growth
of the covering, and that function, being constant on the orbits of the kernel, is a function of
the quotient. -/
theorem forall_ne_quotBase (hf : IsLocalHomeomorph f) :
    ∀ x : H ⧸ deckKernel H hf S, x ≠ 1 →
      ∃ G ∈ coverRing (isLocalHomeomorph_quotBase hf (deckKernel H hf S)) S,
        ∃ z : CoverQuot Y (deckKernel H hf S), G (x • z) ≠ G z := by
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a ∉ deckKernel H hf S := by
    simpa [QuotientGroup.eq_one_iff] using hx
  rw [mem_deckKernel_iff] at ha
  push_neg at ha
  obtain ⟨F, hF, y, hy⟩ := ha
  have hinv : ∀ n ∈ deckKernel H hf S, ∀ y : Y, F (n • y) = F y :=
    fun n hn y => (mem_deckKernel_iff.1 hn) F hF y
  exact ⟨quotFun _ F hinv, quotFun_mem_coverRing hf hF hinv, Quotient.mk _ y, hy⟩

/-- **Dividing by the unseen deck transformations costs no functions**: the functions of moderate
growth of the covering are exactly the functions of moderate growth of the quotient, read on the
covering. -/
theorem image_comp_mk_coverRing (hf : IsLocalHomeomorph f) :
    (fun G : CoverQuot Y (deckKernel H hf S) → ℂ => fun y => G (Quotient.mk _ y)) ''
        (coverRing (isLocalHomeomorph_quotBase hf (deckKernel H hf S)) S : Set _) =
      (coverRing hf S : Set (Y → ℂ)) := by
  refine Set.Subset.antisymm ?_ fun F hF => ?_
  · rintro _ ⟨G, hG, rfl⟩
    exact comp_mk_mem_coverRing hf hG
  · have hinv : ∀ n ∈ deckKernel H hf S, ∀ y : Y, F (n • y) = F y :=
      fun n hn y => (mem_deckKernel_iff.1 hn) F hF y
    exact ⟨quotFun _ F hinv, quotFun_mem_coverRing hf hF hinv, rfl⟩

/-- **The quotient of a covering of a punctured plane by the deck transformations its functions of
moderate growth do not see is cut out by a monic equation**, away from finitely many further points
of the base.

No hypothesis is made on the covering beyond the ones a covering of a punctured plane satisfies:
the deck transformations the functions cannot tell apart are divided out, and over what is left the
functions separate the fibres, so the quotient is the root variety of a monic equation of degree
the number of deck transformations the functions do see. -/
theorem exists_algebraic_model_quotient [Nonempty Y] [PreconnectedSpace Y] [Finite H]
    (hf : IsLocalHomeomorph f) (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ) :
    ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧
      P.natDegree = Nat.card (H ⧸ deckKernel H hf S) ∧
      (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      ∃ Φ : ↥(quotBase f (deckKernel H hf S) ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ z, rootBase P S' (Φ z) = quotBase f (deckKernel H hf S) (z : CoverQuot Y _) :=
  exists_algebraic_model_of_forall_ne (H := H ⧸ deckKernel H hf S)
    (isLocalHomeomorph_quotBase hf (deckKernel H hf S))
    (quotBase_transitive htrans) (by rw [range_quotBase, hrange]) (forall_ne_quotBase hf)

end Unseen

end Rigidity.RET

end
