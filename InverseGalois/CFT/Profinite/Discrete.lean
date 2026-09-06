/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.InfRes

/-!
# The smooth cohomology of a discrete group is its ordinary cohomology

On a discrete group every cochain is constant on the cosets of the trivial subgroup, so the
smoothness condition is empty and the smooth cocycles are all the cocycles.  The smooth cohomology
of such a group is therefore the ordinary cohomology of the multiplicative module, which in the
library is the cohomology of the additive copy of that module in degrees one and two.

This is the bridge between the two languages the development uses.  Everything above a fixed finite
Galois extension is written with smooth cochains on an infinite Galois group, because that is the
language in which a class can be inflated from, or restricted to, a level; everything below it is
written with representations and complete cohomology, because that is the language of class field
theory and of the theorems of Tate and Nakayama.  A class of the quotient can be carried from one
side to the other exactly here.

## Main definitions

* `InverseGalois.CFT.discreteSmoothH1Hom`, `InverseGalois.CFT.discreteSmoothH2Hom`: the comparison
  homomorphisms from the smooth cohomology of a discrete group to the ordinary cohomology of the
  additive copy of the coefficients.

## Main results

* `InverseGalois.CFT.discreteSmoothH1Equiv`: **the smooth first cohomology of a discrete group is
  the first cohomology of the additive copy of the coefficients.**
* `InverseGalois.CFT.discreteSmoothH2Equiv`: **the same in degree two.**

## Tags

group cohomology, discrete group, smooth cochain, comparison
-/

namespace InverseGalois.CFT

open groupCohomology

section Discrete

variable {G M : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [CommGroup M]
variable [MulDistribMulAction G M]

/-- Every action of a discrete group is smooth. -/
theorem isSmoothAction_of_discreteTopology : IsSmoothAction G M :=
  ⟨⊥, isOpenNormal_bot, fun n hn m => by rw [Subgroup.mem_bot.mp hn, one_smul]⟩

end Discrete

/-! ### Degree one -/

section One

variable (G M : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [CommGroup M]
variable [MulDistribMulAction G M]

/-- **A smooth one cocycle on a discrete group, as a class in the first cohomology** of the
additive copy of the coefficients. -/
noncomputable def discreteH1Hom :
    smoothCocycle₁ G M →* Multiplicative ↥(H1 (Rep.ofMulDistribMulAction G M)) where
  toFun u := Multiplicative.ofAdd (H1π _ (cocyclesOfIsMulCocycle₁ u.2.1))
  map_one' := by
    have h : cocyclesOfIsMulCocycle₁ (1 : ↥(smoothCocycle₁ G M)).2.1 = 0 := Subtype.ext rfl
    rw [h, map_zero]
    rfl
  map_mul' u v := by
    have h : cocyclesOfIsMulCocycle₁ (u * v).2.1
        = cocyclesOfIsMulCocycle₁ u.2.1 + cocyclesOfIsMulCocycle₁ v.2.1 := Subtype.ext rfl
    rw [h, map_add]
    rfl

variable {G M}

omit [DiscreteTopology G] in
/-- The comparison sends a coboundary to the trivial class. -/
theorem discreteH1Hom_eq_one_of_mem (u : ↥(smoothCocycle₁ G M))
    (hu : u ∈ (smoothCoboundary₁ G M).subgroupOf (smoothCocycle₁ G M)) :
    discreteH1Hom G M u = 1 := by
  obtain ⟨t, ht⟩ : ∃ t : M, (fun g : G => g • t / t) = (u : G → M) := hu
  have hcb : IsMulCoboundary₁ (u : G → M) := ⟨t, fun g => congrFun ht g⟩
  have h : ⇑(cocyclesOfIsMulCocycle₁ u.2.1) ∈ coboundaries₁ (Rep.ofMulDistribMulAction G M) :=
    (coboundariesOfIsMulCoboundary₁ hcb).2
  show Multiplicative.ofAdd (H1π _ (cocyclesOfIsMulCocycle₁ u.2.1)) = Multiplicative.ofAdd 0
  rw [(H1π_eq_zero_iff (A := Rep.ofMulDistribMulAction G M) _).2 h]

variable (G M)

/-- **The comparison homomorphism** from the smooth first cohomology of a discrete group to the
first cohomology of the additive copy of the coefficients. -/
noncomputable def discreteSmoothH1Hom :
    SmoothH1 G M →* Multiplicative ↥(H1 (Rep.ofMulDistribMulAction G M)) :=
  QuotientGroup.lift _ (discreteH1Hom G M) discreteH1Hom_eq_one_of_mem

variable {G M}

omit [DiscreteTopology G] in
@[simp]
theorem discreteSmoothH1Hom_smoothH1Mk {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    discreteSmoothH1Hom G M (smoothH1Mk u hu hs)
      = Multiplicative.ofAdd (H1π _ (cocyclesOfIsMulCocycle₁ hu)) := rfl

variable (G M)

omit [DiscreteTopology G] in
/-- The comparison is injective: a cocycle whose additive class vanishes is a coboundary. -/
theorem discreteSmoothH1Hom_injective : Function.Injective (discreteSmoothH1Hom G M) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rw [discreteSmoothH1Hom_smoothH1Mk] at hx
  have h0 : H1π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₁ hu) = 0 :=
    Multiplicative.ofAdd.injective hx
  obtain ⟨t, ht⟩ := isMulCoboundary₁_of_mem_coboundaries₁ (M := M) _
    ((H1π_eq_zero_iff (A := Rep.ofMulDistribMulAction G M) _).1 h0)
  exact (smoothH1Mk_eq_one_iff hu hs).2 ⟨t, funext ht⟩

/-- The comparison is surjective: every cocycle for the additive copy of the coefficients is
smooth. -/
theorem discreteSmoothH1Hom_surjective : Function.Surjective (discreteSmoothH1Hom G M) := by
  intro y
  suffices h : ∀ c : ↥(cocycles₁ (Rep.ofMulDistribMulAction G M)),
      ∃ x, discreteSmoothH1Hom G M x = Multiplicative.ofAdd (H1π _ c) from
    H1_induction_on (A := Rep.ofMulDistribMulAction G M)
      (C := fun z => ∃ x, discreteSmoothH1Hom G M x = Multiplicative.ofAdd z)
      (Multiplicative.toAdd y) h
  intro c
  refine ⟨smoothH1Mk (Additive.toMul ∘ (c : G → Additive M))
    (isMulCocycle₁_of_mem_cocycles₁ _ c.2) (isSmooth₁_of_discreteTopology _), ?_⟩
  rw [discreteSmoothH1Hom_smoothH1Mk]
  exact congrArg (fun z => Multiplicative.ofAdd (H1π _ z)) (Subtype.ext rfl)

/-- **The smooth first cohomology of a discrete group is the first cohomology of the additive copy
of the coefficients.** -/
noncomputable def discreteSmoothH1Equiv :
    SmoothH1 G M ≃* Multiplicative ↥(H1 (Rep.ofMulDistribMulAction G M)) :=
  MulEquiv.ofBijective (discreteSmoothH1Hom G M)
    ⟨discreteSmoothH1Hom_injective G M, discreteSmoothH1Hom_surjective G M⟩

variable {G M}

@[simp]
theorem discreteSmoothH1Equiv_smoothH1Mk {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    discreteSmoothH1Equiv G M (smoothH1Mk u hu hs)
      = Multiplicative.ofAdd (H1π _ (cocyclesOfIsMulCocycle₁ hu)) := rfl

end One

/-! ### Degree two -/

section Two

variable (G M : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [CommGroup M]
variable [MulDistribMulAction G M]

/-- **A smooth two cocycle on a discrete group, as a class in the second cohomology** of the
additive copy of the coefficients. -/
noncomputable def discreteH2Hom :
    smoothCocycle₂ G M →* Multiplicative ↥(H2 (Rep.ofMulDistribMulAction G M)) where
  toFun a := Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ a.2.1))
  map_one' := by
    have h : cocyclesOfIsMulCocycle₂ (1 : ↥(smoothCocycle₂ G M)).2.1 = 0 := Subtype.ext rfl
    rw [h, map_zero]
    rfl
  map_mul' a b := by
    have h : cocyclesOfIsMulCocycle₂ (a * b).2.1
        = cocyclesOfIsMulCocycle₂ a.2.1 + cocyclesOfIsMulCocycle₂ b.2.1 := Subtype.ext rfl
    rw [h, map_add]
    rfl

variable {G M}

omit [DiscreteTopology G] in
/-- The comparison sends the coboundary of a smooth cochain to the trivial class. -/
theorem discreteH2Hom_eq_one_of_mem (a : ↥(smoothCocycle₂ G M))
    (ha : a ∈ (smoothCoboundary₂ G M).subgroupOf (smoothCocycle₂ G M)) :
    discreteH2Hom G M a = 1 := by
  obtain ⟨u, -, hu⟩ : ∃ u : G → M, IsSmooth₁ u ∧ coboundary₂ u = (a : G × G → M) := ha
  have hcb : IsMulCoboundary₂ (a : G × G → M) := ⟨u, fun g h => congrFun hu (g, h)⟩
  have h : ⇑(cocyclesOfIsMulCocycle₂ a.2.1) ∈ coboundaries₂ (Rep.ofMulDistribMulAction G M) :=
    (coboundariesOfIsMulCoboundary₂ hcb).2
  show Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ a.2.1)) = Multiplicative.ofAdd 0
  rw [(H2π_eq_zero_iff (A := Rep.ofMulDistribMulAction G M) _).2 h]

variable (G M)

/-- **The comparison homomorphism** from the smooth second cohomology of a discrete group to the
second cohomology of the additive copy of the coefficients. -/
noncomputable def discreteSmoothH2Hom :
    SmoothH2 G M →* Multiplicative ↥(H2 (Rep.ofMulDistribMulAction G M)) :=
  QuotientGroup.lift _ (discreteH2Hom G M) discreteH2Hom_eq_one_of_mem

variable {G M}

omit [DiscreteTopology G] in
@[simp]
theorem discreteSmoothH2Hom_smoothH2Mk {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    discreteSmoothH2Hom G M (smoothH2Mk a ha hs)
      = Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ ha)) := rfl

variable (G M)

/-- The comparison is injective: a cocycle whose additive class vanishes is a coboundary. -/
theorem discreteSmoothH2Hom_injective : Function.Injective (discreteSmoothH2Hom G M) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rw [discreteSmoothH2Hom_smoothH2Mk] at hx
  have h0 : H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ ha) = 0 :=
    Multiplicative.ofAdd.injective hx
  obtain ⟨u, hu⟩ := isMulCoboundary₂_of_mem_coboundaries₂ (M := M) _
    ((H2π_eq_zero_iff (A := Rep.ofMulDistribMulAction G M) _).1 h0)
  refine (smoothH2Mk_eq_one_iff ha hs).2 ⟨u, isSmooth₁_of_discreteTopology u, ?_⟩
  exact funext fun p => hu p.1 p.2

/-- The comparison is surjective: every cocycle for the additive copy of the coefficients is
smooth. -/
theorem discreteSmoothH2Hom_surjective : Function.Surjective (discreteSmoothH2Hom G M) := by
  intro y
  suffices h : ∀ c : ↥(cocycles₂ (Rep.ofMulDistribMulAction G M)),
      ∃ x, discreteSmoothH2Hom G M x = Multiplicative.ofAdd (H2π _ c) from
    H2_induction_on (A := Rep.ofMulDistribMulAction G M)
      (C := fun z => ∃ x, discreteSmoothH2Hom G M x = Multiplicative.ofAdd z)
      (Multiplicative.toAdd y) h
  intro c
  refine ⟨smoothH2Mk (Additive.toMul ∘ (c : G × G → Additive M))
    (isMulCocycle₂_of_mem_cocycles₂ _ c.2) (isSmooth₂_of_discreteTopology _), ?_⟩
  rw [discreteSmoothH2Hom_smoothH2Mk]
  exact congrArg (fun z => Multiplicative.ofAdd (H2π _ z)) (Subtype.ext rfl)

/-- **The smooth second cohomology of a discrete group is the second cohomology of the additive
copy of the coefficients.** -/
noncomputable def discreteSmoothH2Equiv :
    SmoothH2 G M ≃* Multiplicative ↥(H2 (Rep.ofMulDistribMulAction G M)) :=
  MulEquiv.ofBijective (discreteSmoothH2Hom G M)
    ⟨discreteSmoothH2Hom_injective G M, discreteSmoothH2Hom_surjective G M⟩

variable {G M}

@[simp]
theorem discreteSmoothH2Equiv_smoothH2Mk {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hs : IsSmooth₂ a) :
    discreteSmoothH2Equiv G M (smoothH2Mk a ha hs)
      = Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ ha)) := rfl

end Two

end InverseGalois.CFT
