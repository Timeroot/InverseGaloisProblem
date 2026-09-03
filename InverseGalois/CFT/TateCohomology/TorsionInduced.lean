/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.TorsionShift

/-!
# The vectors killed by a number, and the shift

Taking the vectors killed by a natural number is a functor, and it carries a short complex of
representations to a short complex.  Exactness at the left and in the middle survives, because a
vector killed by the number that maps to zero comes from a vector that is killed by the number as
well; what can fail is surjectivity on the right, and that failure is the whole content of the
torsion of a short exact sequence.

For the sequence defining the shift there is no failure.  The record of all the translates of a
vector can be undone by reading off the value at the identity, so a function whose class in the
shift is killed by the number can be corrected by the record of its own value at the identity into
a function that is itself killed by the number.  The functions on the group with values in the
vectors killed by the number are the vectors killed by the number in the functions on the group, so
the middle term of the corrected sequence still has no complete cohomology, and **the complete
cohomology of the vectors killed by the number in the shift is that of the vectors killed by the
number in the representation, one degree higher.**

## Main definitions

* `InverseGalois.CFT.Tate.nsmulTorsionHom`: a map of representations, on the vectors killed by a
  natural number.
* `InverseGalois.CFT.Tate.nsmulTorsionSeqOf`: the vectors killed by a natural number in a short
  complex of representations.

## Main results

* `InverseGalois.CFT.Tate.indNsmulTorsionIso`: the functions on the group with values in the
  vectors killed by a number are the vectors killed by that number in the functions on the group.
* `InverseGalois.CFT.Tate.nsmulTorsion_shiftSeq_shortExact`: **the sequence defining the shift stays
  short exact on the vectors killed by a number.**
* `InverseGalois.CFT.Tate.shiftNsmulTorsionEquiv`,
  `InverseGalois.CFT.Tate.resShiftNsmulTorsionEquiv`: **the complete cohomology of the vectors
  killed by a number in the shift is the complete cohomology of the vectors killed by that number
  one degree higher**, over the group and over any of its subgroups.

## Tags

Tate cohomology, dimension shifting, torsion, induced representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Functoriality -/

section Functor

variable {A B : Rep k G} (m : ℕ)

omit [Finite G] in
/-- The image of a vector killed by a number is killed by that number. -/
theorem hom_mem_ker_nsmulLinear (φ : A ⟶ B) (v : ↥A.V)
    (hv : v ∈ LinearMap.ker (nsmulLinear k m ↥A.V)) :
    φ.hom.hom v ∈ LinearMap.ker (nsmulLinear k m ↥B.V) := by
  refine LinearMap.mem_ker.mpr ?_
  show m • φ.hom.hom v = 0
  rw [← map_nsmul, show m • v = (0 : ↥A.V) from LinearMap.mem_ker.mp hv, map_zero]

/-- **A map of representations, on the vectors killed by a natural number.** -/
def nsmulTorsionHom (φ : A ⟶ B) : nsmulTorsion A m ⟶ nsmulTorsion B m :=
  mkHom (φ.hom.hom.restrict (hom_mem_ker_nsmulLinear m φ))
    fun g => LinearMap.ext fun z => Subtype.ext (LinearMap.congr_fun (hom_equivariant φ g) z.1)

omit [Finite G] in
@[simp]
theorem nsmulTorsionHom_coe (φ : A ⟶ B) (z : ↥(nsmulTorsion A m).V) :
    ((nsmulTorsionHom m φ).hom.hom z).1 = φ.hom.hom z.1 := rfl

variable (X : ShortComplex (Rep k G))

/-- **The vectors killed by a natural number in a short complex of representations.** -/
def nsmulTorsionSeqOf : ShortComplex (Rep k G) where
  X₁ := nsmulTorsion X.X₁ m
  X₂ := nsmulTorsion X.X₂ m
  X₃ := nsmulTorsion X.X₃ m
  f := nsmulTorsionHom m X.f
  g := nsmulTorsionHom m X.g
  zero := by
    ext z
    refine Subtype.ext ?_
    exact congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom.hom z.1) X.zero

end Functor

section Exactness

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (m : ℕ)

include hX

omit [Finite G] in
/-- The vectors killed by a number in the left-hand term inject into those in the middle. -/
theorem injective_nsmulTorsionSeqOf_f :
    Function.Injective ((nsmulTorsionSeqOf m X).f).hom.hom :=
  fun _ _ h => Subtype.ext (shortExact_injective hX (congrArg Subtype.val h))

omit [Finite G] in
/-- A vector killed by a number that dies on the right comes from one killed by that number on the
left. -/
theorem exact_nsmulTorsionSeqOf (x : ↥(nsmulTorsion X.X₂ m).V)
    (hx : ((nsmulTorsionSeqOf m X).g).hom.hom x = 0) :
    ∃ y, ((nsmulTorsionSeqOf m X).f).hom.hom y = x := by
  have hker : x.1 ∈ LinearMap.ker X.g.hom.hom := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (shortExact_range_eq_ker hX ▸ hker : x.1 ∈ LinearMap.range X.f.hom.hom)
  refine ⟨⟨y, LinearMap.mem_ker.mpr (shortExact_injective hX ?_)⟩, Subtype.ext hy⟩
  show X.f.hom.hom (m • y) = X.f.hom.hom 0
  rw [map_nsmul, hy, map_zero]
  exact LinearMap.mem_ker.mp x.2

end Exactness

/-! ### The functions on the group -/

section Induced

variable (A : Rep k G) (m : ℕ)

/-- The functions on the group with values in the vectors killed by a number are the vectors killed
by that number in the functions on the group. -/
def indNsmulTorsionLinear :
    ↥(indObj (nsmulTorsion A m)).V ≃ₗ[k] ↥(nsmulTorsion (indObj A) m).V where
  toFun u := ⟨fun x => (u x).1, by
    refine LinearMap.mem_ker.mpr (funext fun x => ?_)
    exact LinearMap.mem_ker.mp (u x).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w x := ⟨w.1 x, by
    refine LinearMap.mem_ker.mpr ?_
    exact congrFun (LinearMap.mem_ker.mp w.2) x⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite G] in
theorem indNsmulTorsionLinear_equivariant (g : G) :
    (indNsmulTorsionLinear A m).toLinearMap ∘ₗ (indObj (nsmulTorsion A m)).ρ g
      = (nsmulTorsion (indObj A) m).ρ g ∘ₗ (indNsmulTorsionLinear A m).toLinearMap :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- **The functions on the group with values in the vectors killed by a number are the vectors
killed by that number in the functions on the group.** -/
def indNsmulTorsionIso : indObj (nsmulTorsion A m) ≅ nsmulTorsion (indObj A) m :=
  Action.mkIso (indNsmulTorsionLinear A m).toModuleIso fun g =>
    ModuleCat.hom_ext (indNsmulTorsionLinear_equivariant A m g)

/-- **The vectors killed by a number in the functions on the group have no complete cohomology.** -/
theorem isZero_tateModule_nsmulTorsion_indObj (n : ℤ) :
    Limits.IsZero (tateModule (nsmulTorsion (indObj A) m) n) :=
  isZero_tateModule_of_iso (indNsmulTorsionIso A m).symm n
    (isZero_tateModule_indObj (nsmulTorsion A m) n)

end Induced

/-! ### The sequence defining the shift -/

section Shift

variable (A : Rep k G) (m : ℕ)

omit [Finite G] in
/-- **A class of the shift killed by a number is the class of a function killed by that number.** -/
theorem surjective_nsmulTorsionSeqOf_shiftSeq_g :
    Function.Surjective ((nsmulTorsionSeqOf m (shiftSeq A)).g).hom.hom := by
  intro q
  obtain ⟨f, hf⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) q.1
  have hq : m • q.1 = 0 := LinearMap.mem_ker.mp q.2
  have hmf : (LinearMap.range (coindEmb A.ρ)).mkQ (m • f) = 0 := by
    rw [map_nsmul, hf, hq]
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmf
  have hv1 : v = m • f 1 := by
    have h1 : A.ρ 1 v = m • f 1 := congrFun hv 1
    rwa [map_one, Module.End.one_apply] at h1
  refine ⟨⟨f - coindEmb A.ρ (f 1), ?_⟩, Subtype.ext ?_⟩
  · refine LinearMap.mem_ker.mpr ?_
    show m • (f - coindEmb A.ρ (f 1)) = 0
    rw [smul_sub, ← map_nsmul, ← hv1, hv, sub_self]
  · have hz : (LinearMap.range (coindEmb A.ρ)).mkQ (coindEmb A.ρ (f 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ (f 1))
    show (LinearMap.range (coindEmb A.ρ)).mkQ (f - coindEmb A.ρ (f 1)) = q.1
    rw [map_sub, hf, hz, sub_zero]

omit [Finite G] in
/-- **The sequence defining the shift stays short exact on the vectors killed by a number.** -/
theorem nsmulTorsion_shiftSeq_shortExact : (nsmulTorsionSeqOf m (shiftSeq A)).ShortExact :=
  shortExact_of_linearMap (injective_nsmulTorsionSeqOf_f (shiftSeq_shortExact A) m)
    (surjective_nsmulTorsionSeqOf_shiftSeq_g A m)
    (exact_nsmulTorsionSeqOf (shiftSeq_shortExact A) m)

/-- **The complete cohomology of the vectors killed by a number in the shift is the complete
cohomology of the vectors killed by that number in the representation, one degree higher.** -/
def shiftNsmulTorsionEquiv (n : ℤ) :
    ↥(tateModule (nsmulTorsion (shiftObj A) m) n)
      ≃ₗ[k] ↥(tateModule (nsmulTorsion A m) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (nsmulTorsion_shiftSeq_shortExact A m) n).hom
    (bijective_tateδ (nsmulTorsion_shiftSeq_shortExact A m) n
      (isZero_tateModule_nsmulTorsion_indObj A m n)
      (isZero_tateModule_nsmulTorsion_indObj A m (n + 1)))

/-- **The vectors killed by a number in the shift have no complete cohomology in a degree in which
the vectors killed by that number have none one degree higher.** -/
theorem isZero_tateModule_nsmulTorsion_shiftObj (n : ℤ)
    (h : Limits.IsZero (tateModule (nsmulTorsion A m) (n + 1))) :
    Limits.IsZero (tateModule (nsmulTorsion (shiftObj A) m) n) :=
  isZero_of_forall_eq_zero fun x =>
    (shiftNsmulTorsionEquiv A m n).injective
      (by rw [map_zero]; exact eq_zero_of_isZero h _)

/-- **The vectors killed by a number have no complete cohomology one degree above a degree in which
the vectors killed by that number in the shift have none.** -/
theorem isZero_tateModule_nsmulTorsion_of_shiftObj (n : ℤ)
    (h : Limits.IsZero (tateModule (nsmulTorsion (shiftObj A) m) n)) :
    Limits.IsZero (tateModule (nsmulTorsion A m) (n + 1)) :=
  isZero_of_forall_eq_zero fun y => by
    obtain ⟨x, rfl⟩ := (shiftNsmulTorsionEquiv A m n).surjective y
    rw [eq_zero_of_isZero h x, map_zero]

end Shift

/-! ### Restriction to a subgroup -/

section Res

variable (A : Rep k G) (m : ℕ) (H : Subgroup G)

/-- Complete cohomology on a subgroup is unchanged by an isomorphism of representations of the
whole group. -/
theorem isZero_tateModule_resObj_of_iso {B C : Rep k G} (e : B ≅ C) (n : ℤ)
    (h : Limits.IsZero (tateModule (resObj H C) n)) :
    Limits.IsZero (tateModule (resObj H B) n) :=
  isZero_tateModule_of_iso ((Action.res (ModuleCat k) H.subtype).mapIso e) n h

/-- **The vectors killed by a number in the functions on the group still have no complete cohomology
after restriction to a subgroup.** -/
theorem isZero_tateModule_resObj_nsmulTorsion_indObj (n : ℤ) :
    Limits.IsZero (tateModule (resObj H (nsmulTorsion (indObj A) m)) n) :=
  isZero_tateModule_resObj_of_iso H (indNsmulTorsionIso A m).symm n
    (isZero_tateModule_resObj_indObj H (nsmulTorsion A m) n)

/-- **The complete cohomology of the vectors killed by a number in the shift, read on a subgroup, is
the complete cohomology of the vectors killed by that number, read on the subgroup, one degree
higher.** -/
def resShiftNsmulTorsionEquiv (n : ℤ) :
    ↥(tateModule (resObj H (nsmulTorsion (shiftObj A) m)) n)
      ≃ₗ[k] ↥(tateModule (resObj H (nsmulTorsion A m)) (n + 1)) :=
  LinearEquiv.ofBijective
    (tateδ (resSeq_shortExact (nsmulTorsion_shiftSeq_shortExact A m) H) n).hom
    (bijective_tateδ _ n (isZero_tateModule_resObj_nsmulTorsion_indObj A m H n)
      (isZero_tateModule_resObj_nsmulTorsion_indObj A m H (n + 1)))

/-- **The vectors killed by a number in the shift have no complete cohomology on a subgroup in a
degree in which the vectors killed by that number have none one degree higher.** -/
theorem isZero_tateModule_resObj_nsmulTorsion_shiftObj (n : ℤ)
    (h : Limits.IsZero (tateModule (resObj H (nsmulTorsion A m)) (n + 1))) :
    Limits.IsZero (tateModule (resObj H (nsmulTorsion (shiftObj A) m)) n) :=
  isZero_of_forall_eq_zero fun x =>
    (resShiftNsmulTorsionEquiv A m H n).injective
      (by rw [map_zero]; exact eq_zero_of_isZero h _)

end Res

end

end InverseGalois.CFT.Tate
