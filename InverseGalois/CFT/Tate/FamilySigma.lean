/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Family
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.PiSplit

/-!
# A family of modules over a disjoint union of invariant pieces

The places of a Galois extension of number fields are grouped by the place of the base field they
lie over, and the Galois group moves each group of places within itself.  The group of ideles is
therefore not one family of modules but a family of families, one for each place of the base, and
its group of sections is the product over the places of the base of the groups of sections of the
pieces.

This file records that splitting.  The index set is presented as a disjoint union of sets each
carrying an action of the group, a family of modules over it restricts to a family over each piece,
and the sections of the whole are the product of the sections of the pieces, compatibly with the
actions.  Two consequences follow at once from the corresponding statements for a product: over
finitely many pieces the Herbrand quotient of the sections is the product of the Herbrand quotients
of the pieces, and over arbitrarily many pieces the Tate groups of the sections vanish as soon as
they vanish for every piece.

## Main definitions

* `InverseGalois.CFT.FamilyAction.sigmaFiber`: the restriction of a family of modules over a
  disjoint union to one of its pieces.
* `InverseGalois.CFT.sigmaFamilyEquiv`: **the sections of a family over a disjoint union are the
  product over the pieces of the sections over each piece.**

## Main results

* `InverseGalois.CFT.sigmaFamilyEquiv_familyAut`: the splitting is compatible with the actions.
* `InverseGalois.CFT.herbrand_familyAut_sigma`: **over finitely many pieces the Herbrand quotient
  of the sections is the product of the Herbrand quotients of the pieces.**
* `InverseGalois.CFT.herbrand_familyAut_sigma_eq_one`: over arbitrarily many pieces with vanishing
  Tate groups the Herbrand quotient of the sections is one.
* `InverseGalois.CFT.herbrand_familyAut_sigma_split`: **the Herbrand quotient of the sections is the
  product over the finitely many named pieces**, as soon as the other pieces have vanishing Tate
  groups.

## Tags

Tate cohomology, Herbrand quotient, family of modules, disjoint union, idele
-/

namespace InverseGalois.CFT

variable {G Y : Type*} [Group G] {P : Y → Type*} [∀ y, MulAction G (P y)]
  {M : (Σ y, P y) → Type*} [∀ x, AddCommGroup (M x)]

/-! ### Reindexing a transport -/

/-- The transport of a reindexed family is the transport of the family along the corresponding
equality of indices. -/
theorem famCast_comp {X W : Type*} (N : X → Type*) [∀ x, AddCommGroup (N x)] (u : W → X)
    {a b : W} (h : a = b) (m : N (u a)) :
    famCast (fun w => N (u w)) h m = famCast N (congrArg u h) m := by
  subst h
  rfl

/-! ### The restriction to one piece -/

namespace FamilyAction

variable (F : FamilyAction M G)

/-- **The restriction of a family of modules over a disjoint union to one of its pieces.** -/
def sigmaFiber (y : Y) : FamilyAction (fun z : P y => M ⟨y, z⟩) G where
  map g z := F.map g ⟨y, z⟩
  map_one z a := (F.map_one ⟨y, z⟩ a).trans
    (famCast_comp M (fun w : P y => (⟨y, w⟩ : Σ y, P y)) (one_smul G z).symm a).symm
  map_mul g h z a := (F.map_mul g h ⟨y, z⟩ a).trans
    (famCast_comp M (fun w : P y => (⟨y, w⟩ : Σ y, P y)) (mul_smul g h z).symm _).symm

@[simp]
theorem sigmaFiber_map (y : Y) (g : G) (z : P y) :
    (F.sigmaFiber y).map g z = F.map g ⟨y, z⟩ := rfl

end FamilyAction

/-! ### The splitting of the sections -/

variable (F : FamilyAction M G)

/-- **The sections of a family over a disjoint union are the product over the pieces of the
sections over each piece.** -/
def sigmaFamilyEquiv : (∀ x : Σ y, P y, M x) ≃+ (∀ y : Y, ∀ z : P y, M ⟨y, z⟩) where
  toFun f y z := f ⟨y, z⟩
  invFun f := fun ⟨y, z⟩ => f y z
  left_inv _ := funext fun ⟨_, _⟩ => rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem sigmaFamilyEquiv_apply (f : ∀ x : Σ y, P y, M x) (y : Y) (z : P y) :
    sigmaFamilyEquiv f y z = f ⟨y, z⟩ := rfl

/-- **The splitting of the sections is compatible with the actions.** -/
theorem sigmaFamilyEquiv_familyAut (σ : G) (f : ∀ x : Σ y, P y, M x) :
    sigmaFamilyEquiv (F.familyAut σ f)
      = piAut (fun y : Y => (F.sigmaFiber y).familyAut σ) (sigmaFamilyEquiv (M := M) f) := by
  funext y z
  have hmk : σ • (⟨y, σ⁻¹ • z⟩ : Σ y, P y) = ⟨y, z⟩ := by
    rw [Sigma.smul_mk, smul_inv_smul]
  show F.familyAut σ f ⟨y, z⟩ = (F.sigmaFiber y).familyAut σ (fun w => f ⟨y, w⟩) z
  rw [F.familyAut_apply_eq_transport hmk f,
    (F.sigmaFiber y).familyAut_apply_eq_transport (smul_inv_smul σ z) (fun w => f ⟨y, w⟩),
    FamilyAction.transport_apply, FamilyAction.transport_apply, FamilyAction.sigmaFiber_map,
    famCast_comp M (fun w : P y => (⟨y, w⟩ : Σ y, P y)) (smul_inv_smul σ z)]
  rfl

/-! ### The Herbrand quotient -/

variable (σ : G) (n : ℕ)

/-- **Over finitely many pieces the Herbrand quotient of the sections of a family is the product of
the Herbrand quotients of the pieces.** -/
theorem herbrand_familyAut_sigma [Fintype Y] :
    herbrand (F.familyAut σ) n = ∏ y : Y, herbrand ((F.sigmaFiber y).familyAut σ) n := by
  rw [herbrand_congr (sigmaFamilyEquiv (M := M)) (sigmaFamilyEquiv_familyAut F σ) n]
  exact herbrand_piAut _ n

/-- The upper Tate group of the sections vanishes as soon as it vanishes for every piece. -/
theorem subsingleton_tateH0_familyAut_sigma
    (h : ∀ y : Y, Subsingleton (tateH0 ((F.sigmaFiber y).familyAut σ) n)) :
    Subsingleton (tateH0 (F.familyAut σ) n) := by
  haveI := subsingleton_tateH0_piAut (fun y : Y => (F.sigmaFiber y).familyAut σ) n h
  exact ⟨fun a b => (tateH0Congr (sigmaFamilyEquiv (M := M))
    (sigmaFamilyEquiv_familyAut F σ) n).injective (Subsingleton.elim _ _)⟩

/-- The lower Tate group of the sections vanishes as soon as it vanishes for every piece. -/
theorem subsingleton_tateHm1_familyAut_sigma
    (h : ∀ y : Y, Subsingleton (tateHm1 ((F.sigmaFiber y).familyAut σ) n)) :
    Subsingleton (tateHm1 (F.familyAut σ) n) := by
  haveI := subsingleton_tateHm1_piAut (fun y : Y => (F.sigmaFiber y).familyAut σ) n h
  exact ⟨fun a b => (tateHm1Congr (sigmaFamilyEquiv (M := M))
    (sigmaFamilyEquiv_familyAut F σ) n).injective (Subsingleton.elim _ _)⟩

/-- **Over arbitrarily many pieces with vanishing Tate groups the sections have Herbrand quotient
one.**  This is what the places outside a finite set contribute to the Herbrand quotient of the
group of ideles. -/
theorem herbrand_familyAut_sigma_eq_one
    (h0 : ∀ y : Y, Subsingleton (tateH0 ((F.sigmaFiber y).familyAut σ) n))
    (hm1 : ∀ y : Y, Subsingleton (tateHm1 ((F.sigmaFiber y).familyAut σ) n)) :
    herbrand (F.familyAut σ) n = 1 := by
  rw [herbrand_congr (sigmaFamilyEquiv (M := M)) (sigmaFamilyEquiv_familyAut F σ) n]
  exact herbrand_piAut_eq_one _ n h0 hm1

/-- **The Herbrand quotient of the sections of a family over a disjoint union is the product over
the finitely many named pieces**, as soon as the sections over the other pieces have vanishing Tate
groups.  This is the shape of the Herbrand quotient of the group of ideles: only the places in a
chosen finite set of the base field contribute. -/
theorem herbrand_familyAut_sigma_split (p : Y → Prop) [DecidablePred p] [Fintype {y // p y}]
    (h0 : ∀ y : {y // ¬ p y}, Subsingleton (tateH0 ((F.sigmaFiber (y : Y)).familyAut σ) n))
    (hm1 : ∀ y : {y // ¬ p y}, Subsingleton (tateHm1 ((F.sigmaFiber (y : Y)).familyAut σ) n)) :
    herbrand (F.familyAut σ) n
      = ∏ y : {y // p y}, herbrand ((F.sigmaFiber (y : Y)).familyAut σ) n := by
  rw [herbrand_congr (sigmaFamilyEquiv (M := M)) (sigmaFamilyEquiv_familyAut F σ) n]
  exact herbrand_piAut_split p _ n h0 hm1

end InverseGalois.CFT
