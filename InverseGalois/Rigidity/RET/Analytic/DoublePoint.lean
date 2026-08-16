/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Wall
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane

/-!
# The projection has to be a covering

The statement the existence direction of the Riemann existence theorem rests on asks that the
functions of moderate growth on a covering of a punctured plane see its deck group.  A covering is a
local homeomorphism, and both the ring of functions and the growth conditions make sense for any
local homeomorphism onto the punctured plane, so it is tempting to ask for the functions in that
generality.  One must not: a local homeomorphism can have a connected total space and a faithful
finite group acting on it over the base, transitively on every fibre, and still admit no function at
all that the group moves.

The example is the punctured plane with one further point doubled.  Two copies of the plane
punctured at `S` are glued along the complement of a point `z₁`, and the two-element group swaps
them.  The result is a connected space, the projection to the punctured plane is a local
homeomorphism whose fibres are single points away from `z₁` and a pair at `z₁`, and the swap is a
faithful deck transformation.  But the two copies of `z₁` cannot be told apart by any continuous
function: the two sheets agree off a single point, and a point of an open subset of the plane is
never isolated, so continuity forces the two values at `z₁` to agree as well.  Holomorphy and
moderate growth are not needed — continuity alone kills the statement.

## Main definitions

* `Rigidity.RET.doubledSetoid`, `Rigidity.RET.Doubled` — a space with one of its points doubled.
* `Rigidity.RET.dproj`, `Rigidity.RET.dincl`, `Rigidity.RET.dtwist`, `Rigidity.RET.dswap` — its
  projection, its two sheets, and the transformation exchanging them.
* `Rigidity.RET.HasEnoughFunctionsNonCovering` — the requirement of
  `Rigidity.RET.HasEnoughFunctions` with the hypothesis that the projection is a covering dropped.

## Main results

* `Rigidity.RET.isOpen_range_dincl` — each sheet is open.
* `Rigidity.RET.isLocalHomeomorph_dprojC` — the projection of a doubled open subset of the plane is
  a local homeomorphism.
* `Rigidity.RET.eq_of_continuous_dswap` — a continuous function does not see the doubling.
* `Rigidity.RET.not_hasEnoughFunctionsNonCovering` — the requirement without the covering
  hypothesis is false.
-/

open Set Topology

noncomputable section

namespace Rigidity.RET

/-! ### A space with one point doubled -/

section Setoid

variable {B : Type u}

/-- **Doubling one point of a space.**  Two copies of `B`, indexed by `Bool`, glued along the
complement of `x₁`. -/
def doubledSetoid (x₁ : B) : Setoid (B × Bool) where
  r p p' := p.1 = p'.1 ∧ (p.1 = x₁ → p.2 = p'.2)
  iseqv :=
    { refl := fun _ => ⟨rfl, fun _ => rfl⟩
      symm := fun {_ _} h => ⟨h.1.symm, fun hx => (h.2 (h.1.trans hx)).symm⟩
      trans := fun {_ _ _} h k => ⟨h.1.trans k.1, fun hx => (h.2 hx).trans (k.2 (h.1 ▸ hx))⟩ }

/-- **The space `B` with the point `x₁` doubled.** -/
abbrev Doubled (x₁ : B) : Type u := Quotient (doubledSetoid x₁)

/-- A point of `B × Bool`, read in the doubled space. -/
def dmk (x₁ : B) (p : B × Bool) : Doubled x₁ := Quotient.mk (doubledSetoid x₁) p

/-- One of the two sheets of the doubled space. -/
def dincl (x₁ : B) (b : Bool) (z : B) : Doubled x₁ := dmk x₁ (z, b)

/-- The projection of the doubled space back to `B`. -/
def dproj (x₁ : B) : Doubled x₁ → B := Quotient.lift Prod.fst fun _ _ h => h.1

/-- **Exchanging the two copies of `x₁` when `c` is `true`.** -/
def dtwist (x₁ : B) (c : Bool) : Doubled x₁ → Doubled x₁ :=
  Quotient.lift (fun p => dmk x₁ (p.1, xor c p.2)) fun _ _ h =>
    Quotient.sound ⟨h.1, fun hx => by rw [h.2 hx]⟩

/-- The transformation of the doubled space exchanging the two copies of `x₁`. -/
def dswap (x₁ : B) : Doubled x₁ → Doubled x₁ := dtwist x₁ true

theorem dmk_eq_dmk_iff (x₁ : B) (p p' : B × Bool) :
    dmk x₁ p = dmk x₁ p' ↔ p.1 = p'.1 ∧ (p.1 = x₁ → p.2 = p'.2) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

@[simp] theorem dproj_dmk (x₁ : B) (p : B × Bool) : dproj x₁ (dmk x₁ p) = p.1 := rfl

@[simp] theorem dproj_dincl (x₁ : B) (b : Bool) (z : B) : dproj x₁ (dincl x₁ b z) = z := rfl

@[simp] theorem dtwist_dmk (x₁ : B) (c : Bool) (p : B × Bool) :
    dtwist x₁ c (dmk x₁ p) = dmk x₁ (p.1, xor c p.2) := rfl

@[simp] theorem dtwist_dincl (x₁ : B) (c b : Bool) (z : B) :
    dtwist x₁ c (dincl x₁ b z) = dincl x₁ (xor c b) z := rfl

@[simp] theorem dtwist_false (x₁ : B) (y : Doubled x₁) : dtwist x₁ false y = y := by
  induction y using Quotient.ind with
  | _ p =>
    obtain ⟨z, b⟩ := p
    cases b <;> rfl

theorem dtwist_dtwist (x₁ : B) (c c' : Bool) (y : Doubled x₁) :
    dtwist x₁ c (dtwist x₁ c' y) = dtwist x₁ (xor c c') y := by
  induction y using Quotient.ind with
  | _ p =>
    obtain ⟨z, b⟩ := p
    cases c <;> cases c' <;> cases b <;> rfl

@[simp] theorem dproj_dtwist (x₁ : B) (c : Bool) (y : Doubled x₁) :
    dproj x₁ (dtwist x₁ c y) = dproj x₁ y := by
  induction y using Quotient.ind with
  | _ p => rfl

@[simp] theorem dswap_dincl (x₁ : B) (b : Bool) (z : B) :
    dswap x₁ (dincl x₁ b z) = dincl x₁ (!b) z := by cases b <;> rfl

@[simp] theorem dproj_dswap (x₁ : B) (y : Doubled x₁) : dproj x₁ (dswap x₁ y) = dproj x₁ y :=
  dproj_dtwist x₁ true y

theorem preimage_range_dincl (x₁ : B) (b : Bool) :
    dmk x₁ ⁻¹' (range (dincl x₁ b)) = {p : B × Bool | p.2 = b} ∪ {p : B × Bool | p.1 ≠ x₁} := by
  ext p
  simp only [mem_preimage, mem_range, mem_union, mem_setOf_eq]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := (dmk_eq_dmk_iff x₁ (z, b) p).1 hz
    by_cases hp : p.1 = x₁
    · exact Or.inl (hz2 (hz1.trans hp)).symm
    · exact Or.inr hp
  · rintro (h | h)
    · exact ⟨p.1, (dmk_eq_dmk_iff x₁ (p.1, b) p).2 ⟨rfl, fun _ => h.symm⟩⟩
    · exact ⟨p.1, (dmk_eq_dmk_iff x₁ (p.1, b) p).2 ⟨rfl, fun hx => absurd hx h⟩⟩

/-- **Off the doubled point the two sheets agree.** -/
theorem dincl_eq_dincl {x₁ z : B} (hz : z ≠ x₁) (b b' : Bool) :
    dincl x₁ b z = dincl x₁ b' z :=
  Quotient.sound ⟨rfl, fun hx => absurd hx hz⟩

/-- **The doubled point really is doubled.** -/
theorem dincl_ne_dincl (x₁ : B) : dincl x₁ false x₁ ≠ dincl x₁ true x₁ := fun h =>
  Bool.noConfusion (((dmk_eq_dmk_iff x₁ (x₁, false) (x₁, true)).1 h).2 rfl)

end Setoid

/-! ### The topology of the doubled space -/

section Topology

variable {B : Type u} [TopologicalSpace B]

theorem continuous_dmk (x₁ : B) : Continuous (dmk x₁) := continuous_quotient_mk'

theorem continuous_dincl (x₁ : B) (b : Bool) : Continuous (dincl x₁ b) :=
  (continuous_dmk x₁).comp (continuous_id.prodMk continuous_const)

theorem continuous_dproj (x₁ : B) : Continuous (dproj x₁) := continuous_fst.quotient_lift _

theorem continuous_dtwist (x₁ : B) (c : Bool) : Continuous (dtwist x₁ c) :=
  Continuous.quotient_lift
    ((continuous_dmk x₁).comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun b : Bool => xor c b)).comp continuous_snd))) _

theorem continuous_dswap (x₁ : B) : Continuous (dswap x₁) := continuous_dtwist x₁ true

/-- The doubled space carries the quotient topology of `B × Bool`. -/
theorem isOpen_doubled_iff {x₁ : B} (V : Set (Doubled x₁)) :
    IsOpen V ↔ IsOpen (dmk x₁ ⁻¹' V) :=
  ((isQuotientMap_quotient_mk' (s := doubledSetoid x₁)).isOpen_preimage (s := V)).symm

/-- **Each sheet of the doubled space is open.**  Its preimage is the copy of `B` it comes from
together with the complement of the fibre over the doubled point. -/
theorem isOpen_range_dincl [T1Space B] (x₁ : B) (b : Bool) : IsOpen (range (dincl x₁ b)) := by
  rw [isOpen_doubled_iff, preimage_range_dincl]
  exact ((isOpen_discrete {b}).preimage continuous_snd).union
    ((isClosed_singleton (x := x₁)).isOpen_compl.preimage continuous_fst)

/-- **The doubled space is connected** as soon as `B` is and `x₁` is not its only point: the two
sheets are connected and they meet. -/
theorem preconnectedSpace_doubled [PreconnectedSpace B] {x₁ z₀ : B} (hz₀ : z₀ ≠ x₁) :
    PreconnectedSpace (Doubled x₁) := by
  refine preconnectedSpace_iff_univ.2 ?_
  have huniv : (univ : Set (Doubled x₁)) = range (dincl x₁ false) ∪ range (dincl x₁ true) := by
    refine (eq_univ_of_forall ?_).symm
    intro y
    induction y using Quotient.ind with
    | _ p =>
      obtain ⟨z, b⟩ := p
      cases b
      · exact Or.inl ⟨z, rfl⟩
      · exact Or.inr ⟨z, rfl⟩
  have hpre : ∀ b : Bool, IsPreconnected (range (dincl x₁ b)) := by
    intro b
    rw [← image_univ]
    exact isPreconnected_univ.image _ (continuous_dincl x₁ b).continuousOn
  rw [huniv]
  exact IsPreconnected.union (dincl x₁ false z₀) ⟨z₀, rfl⟩
    ⟨z₀, dincl_eq_dincl hz₀ true false⟩ (hpre false) (hpre true)

end Topology

/-! ### The two-element group exchanging the copies -/

section Action

variable {B : Type u}

/-- The parity of an element of `ZMod 2`, as a Boolean. -/
def zmodBit (u : ZMod 2) : Bool := decide (u = 1)

/-- A Boolean, as an element of `ZMod 2`. -/
def bitZmod (c : Bool) : ZMod 2 := if c then 1 else 0

theorem zmodBit_add : ∀ u v : ZMod 2, zmodBit (u + v) = xor (zmodBit u) (zmodBit v) := by decide

theorem zmodBit_injective : ∀ u v : ZMod 2, zmodBit u = zmodBit v → u = v := by decide

theorem zmodBit_bitZmod : ∀ c : Bool, zmodBit (bitZmod c) = c := by decide

/-- **The two-element group acts on the doubled space by exchanging the two copies.** -/
instance mulActionDoubled (x₁ : B) : MulAction (Multiplicative (ZMod 2)) (Doubled x₁) where
  smul a y := dtwist x₁ (zmodBit (Multiplicative.toAdd a)) y
  one_smul y := dtwist_false x₁ y
  mul_smul a b y := by
    show dtwist x₁ (zmodBit (Multiplicative.toAdd a + Multiplicative.toAdd b)) y
      = dtwist x₁ (zmodBit (Multiplicative.toAdd a))
          (dtwist x₁ (zmodBit (Multiplicative.toAdd b)) y)
    rw [dtwist_dtwist, zmodBit_add]

theorem smul_doubled_eq (x₁ : B) (a : Multiplicative (ZMod 2)) (y : Doubled x₁) :
    a • y = dtwist x₁ (zmodBit (Multiplicative.toAdd a)) y := rfl

theorem ofAdd_one_smul_doubled (x₁ : B) (y : Doubled x₁) :
    (Multiplicative.ofAdd (1 : ZMod 2)) • y = dswap x₁ y := rfl

/-- **The action of the two-element group is faithful**: the element that is not the identity
exchanges the two copies of the doubled point. -/
instance faithfulSMulDoubled (x₁ : B) :
    FaithfulSMul (Multiplicative (ZMod 2)) (Doubled x₁) := by
  refine ⟨fun {a b} h => ?_⟩
  have hval := h (dincl x₁ false x₁)
  rw [smul_doubled_eq, smul_doubled_eq, dtwist_dincl, dtwist_dincl] at hval
  have hv : dmk x₁ (x₁, zmodBit (Multiplicative.toAdd a))
      = dmk x₁ (x₁, zmodBit (Multiplicative.toAdd b)) := by simpa using hval
  exact Multiplicative.toAdd.injective
    (zmodBit_injective _ _ (((dmk_eq_dmk_iff x₁ _ _).1 hv).2 rfl))

/-- **The action is transitive on the fibres of the projection.** -/
theorem exists_smul_eq_doubled (x₁ : B) : ∀ y y' : Doubled x₁, dproj x₁ y = dproj x₁ y' →
    ∃ a : Multiplicative (ZMod 2), y' = a • y := by
  refine Quotient.ind fun p => Quotient.ind fun p' => ?_
  obtain ⟨z, b⟩ := p
  obtain ⟨z', b'⟩ := p'
  intro h
  refine ⟨Multiplicative.ofAdd (bitZmod (xor b b')), ?_⟩
  rw [smul_doubled_eq]
  show dmk x₁ (z', b') = dtwist x₁ (zmodBit (bitZmod (xor b b'))) (dmk x₁ (z, b))
  rw [zmodBit_bitZmod, dtwist_dmk]
  refine congrArg (dmk x₁) (Prod.ext h.symm ?_)
  cases b <;> cases b' <;> rfl

end Action

/-! ### The doubled point of an open subset of the plane -/

section Plane

variable {X : Set ℂ}

/-- **The projection of a doubled open subset of the plane is a local homeomorphism.**  Each sheet
is an open set carried homeomorphically onto the subset. -/
theorem isLocalHomeomorph_dprojC (hX : IsOpen X) (x₁ : ↥X) :
    IsLocalHomeomorph fun y : Doubled x₁ => ((dproj x₁ y : ↥X) : ℂ) := by
  classical
  intro y
  obtain ⟨b, z, rfl⟩ : ∃ (b : Bool) (z : ↥X), y = dincl x₁ b z := by
    induction y using Quotient.ind with
    | _ p => exact ⟨p.2, p.1, rfl⟩
  refine ⟨{ toFun := fun y => ((dproj x₁ y : ↥X) : ℂ)
            invFun := fun w => if h : w ∈ X then dincl x₁ b ⟨w, h⟩ else dincl x₁ b x₁
            source := range (dincl x₁ b)
            target := X
            map_source' := fun y _ => (dproj x₁ y).2
            map_target' := fun w hw => by rw [dif_pos hw]; exact ⟨⟨w, hw⟩, rfl⟩
            left_inv' := ?_
            right_inv' := fun w hw => by rw [dif_pos hw]; rfl
            open_source := isOpen_range_dincl x₁ b
            open_target := hX
            continuousOn_toFun :=
              (continuous_subtype_val.comp (continuous_dproj x₁)).continuousOn
            continuousOn_invFun := ?_ }, ⟨z, rfl⟩, rfl⟩
  · rintro _ ⟨z', rfl⟩
    show (if h : ((z' : ℂ)) ∈ X then dincl x₁ b ⟨(z' : ℂ), h⟩ else dincl x₁ b x₁)
      = dincl x₁ b z'
    rw [dif_pos z'.2]
  · rw [continuousOn_iff_continuous_restrict]
    have hres : (X.restrict fun w => if h : w ∈ X then dincl x₁ b ⟨w, h⟩ else dincl x₁ b x₁)
        = fun w : ↥X => dincl x₁ b w := funext fun w => dif_pos w.2
    rw [hres]
    exact continuous_dincl x₁ b

theorem range_dprojC (x₁ : ↥X) : range (fun y : Doubled x₁ => ((dproj x₁ y : ↥X) : ℂ)) = X := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    exact (dproj x₁ y).2
  · intro hw
    exact ⟨dincl x₁ false ⟨w, hw⟩, rfl⟩

instance continuousConstSMulDoubled (x₁ : ↥X) :
    ContinuousConstSMul (Multiplicative (ZMod 2)) (Doubled x₁) :=
  ⟨fun a => continuous_dtwist x₁ (zmodBit (Multiplicative.toAdd a))⟩

instance isOverBaseDoubled (x₁ : ↥X) :
    IsOverBase (Multiplicative (ZMod 2)) fun y : Doubled x₁ => ((dproj x₁ y : ↥X) : ℂ) :=
  ⟨fun a y => by rw [smul_doubled_eq, dproj_dtwist]⟩

/-- **A continuous function does not see the doubling.**  The two sheets agree off a single point,
and a point of an open subset of the plane is not isolated, so the two values at the doubled point
agree too. -/
theorem eq_of_continuous_dswap [PerfectSpace ↥X] {x₁ : ↥X} {F : Doubled x₁ → ℂ}
    (hF : Continuous F) (y : Doubled x₁) : F (dswap x₁ y) = F y := by
  have hsheet : (fun z : ↥X => F (dincl x₁ false z)) = fun z : ↥X => F (dincl x₁ true z) := by
    refine Continuous.ext_on (dense_compl_singleton x₁) (hF.comp (continuous_dincl x₁ false))
      (hF.comp (continuous_dincl x₁ true)) ?_
    intro z hz
    exact congrArg F (dincl_eq_dincl (by simpa using hz) false true)
  have key : ∀ z : ↥X, F (dincl x₁ false z) = F (dincl x₁ true z) := fun z => congrFun hsheet z
  induction y using Quotient.ind with
  | _ p =>
    obtain ⟨z, b⟩ := p
    cases b
    · exact (key z).symm
    · exact key z

end Plane

/-! ### The requirement without the covering hypothesis -/

/-- The requirement of `Rigidity.RET.HasEnoughFunctions` with the hypothesis that the projection is
a covering dropped: the functions of moderate growth are asked to see the deck group of any local
homeomorphism onto the punctured plane. -/
def HasEnoughFunctionsNonCovering : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)),
      ∀ hf : IsLocalHomeomorph fun y => ((q y : ℂ)),
        Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
        [IsOverBase H fun y => ((q y : ℂ))],
        (∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) →
        ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y

/-- **Without the covering hypothesis the requirement is false.**  The plane with one point doubled
is a connected local homeomorphism onto the plane, the two-element group exchanges the two copies
faithfully and transitively on the fibres, and no continuous function — in particular no holomorphic
function of moderate growth — takes different values at the two copies. -/
theorem not_hasEnoughFunctionsNonCovering : ¬ HasEnoughFunctionsNonCovering := by
  intro hwall
  classical
  have hX : IsOpen ((((∅ : Finset ℂ) : Set ℂ))ᶜ) :=
    (Finset.finite_toSet ∅).isClosed.isOpen_compl
  haveI : PathConnectedSpace ↥((((∅ : Finset ℂ) : Set ℂ))ᶜ) :=
    pathConnectedSpace_punctured (Finset.finite_toSet ∅).countable
  have h0 : (0 : ℂ) ∈ (((∅ : Finset ℂ) : Set ℂ))ᶜ := by simp
  have h1 : (1 : ℂ) ∈ (((∅ : Finset ℂ) : Set ℂ))ᶜ := by simp
  haveI : Nontrivial ↥((((∅ : Finset ℂ) : Set ℂ))ᶜ) := ⟨⟨⟨0, h0⟩, ⟨1, h1⟩, by simp⟩⟩
  haveI : PerfectSpace ↥((((∅ : Finset ℂ) : Set ℂ))ᶜ) := inferInstance
  set x₁ : ↥((((∅ : Finset ℂ) : Set ℂ))ᶜ) := ⟨0, h0⟩ with hx₁
  have hz₀ : (⟨1, h1⟩ : ↥((((∅ : Finset ℂ) : Set ℂ))ᶜ)) ≠ x₁ := by
    simp [hx₁, Subtype.ext_iff]
  haveI : Nonempty (Doubled x₁) := ⟨dincl x₁ false x₁⟩
  haveI : PreconnectedSpace (Doubled x₁) := preconnectedSpace_doubled hz₀
  have hf : IsLocalHomeomorph fun y : Doubled x₁ => ((dproj x₁ y).1 : ℂ) :=
    isLocalHomeomorph_dprojC hX x₁
  have hrange : range (fun y : Doubled x₁ => ((dproj x₁ y).1 : ℂ))
      = (((∅ : Finset ℂ) : Set ℂ))ᶜ := range_dprojC x₁
  have htrans : ∀ y y' : Doubled x₁, ((dproj x₁ y).1 : ℂ) = ((dproj x₁ y').1 : ℂ) →
      ∃ a : Multiplicative (ZMod 2), y' = a • y := fun y y' h =>
    exists_smul_eq_doubled x₁ y y' (Subtype.ext h)
  have ha : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  obtain ⟨F, hF, y, hy⟩ :=
    hwall ∅ (Doubled x₁) (dproj x₁) hf hrange (Multiplicative (ZMod 2)) htrans
      (Multiplicative.ofAdd (1 : ZMod 2)) ha
  refine hy ?_
  rw [ofAdd_one_smul_doubled]
  exact eq_of_continuous_dswap ((mem_coverRing.1 hF).1.continuous hf) y

end Rigidity.RET

end
