/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Duality
import InverseGalois.CFT.TateCohomology.PTorsionTrivial

/-!
# The duality of complete cohomology in every degree

The functionals on a representation with values in a fixed group of coefficients carry the
contragredient action, and in the two middle degrees the complete cohomology of the functionals is
the group of functionals on the complete cohomology of the representation.  The shift and the
coshift carry that statement to every pair of degrees adding to minus one.

The whole mechanism is one identification of modules with an action.  A function on the group with
values in the functionals is read as the functional which sums the values it takes on the values of
a function on the group, and that reading is a bijection which respects the action.  Under it the
summation map of the functionals becomes precomposition with the record of the translates, and the
record of the translates of the functionals becomes precomposition with the summation map.  So the
coshift of the functionals is the functionals on the shift, and the shift of the functionals is the
functionals on the coshift; only the second asks for something, namely that a functional defined on
the kernel of the summation map extend to the whole of the functions on the group, which is free
when the representation is killed by a prime.

Since the complete cohomology of a shift in a degree is the complete cohomology of the
representation one degree higher, the two identifications move the degree of the functionals up and
down at will, and the statement in the two middle degrees spreads to all of them.  For a
representation killed by a prime both moves are available, and every degree is reached from the
middle by an induction over the integers, in which the representation is replaced by its shift when
the degree descends and by its coshift when it climbs.

## Main definitions

* `InverseGalois.CFT.Tate.indDualMap`: the functions on the group with values in the functionals on
  a module, read as functionals on the functions on the group with values in the module.
* `InverseGalois.CFT.Tate.coeffDualShiftIso`, `InverseGalois.CFT.Tate.coeffDualCoshiftIso`: the
  coshift of the functionals is the functionals on the shift, and the shift of the functionals is
  the functionals on the coshift.

## Main results

* `InverseGalois.CFT.Tate.tateCoeffDualShiftEquiv`,
  `InverseGalois.CFT.Tate.tateCoeffDualCoshiftEquiv`: **the degree of the functionals moves up and
  down when the representation is replaced by its shift and by its coshift.**
* `InverseGalois.CFT.Tate.tateDualEquiv`: **the complete cohomology of the functionals on a
  representation killed by a prime, in any degree, is the group of functionals on the complete
  cohomology of the representation in the complementary degree.**

## Tags

Tate cohomology, duality, dimension shifting, dual representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

universe u

/-! ### Functionals on the functions on the group -/

section IndDual

variable (k : Type*) [CommRing k] (G : Type*) (V : Type*) [AddCommGroup V] [Module k V]
  (C : Type*) [AddCommGroup C] [Module k C]

/-- **The functions on the group with values in the functionals on a module, read as functionals on
the functions on the group with values in the module.**  A family of functionals is sent to the
functional summing the values its members take on the values of a function. -/
def indDualMap : (G → (V →ₗ[k] C)) →ₗ[k] ((G → V) →ₗ[k] C) :=
  ∑ᶠ x : G, (LinearMap.lcomp k C (LinearMap.proj x : (G → V) →ₗ[k] V)).comp
    (LinearMap.proj x : (G → (V →ₗ[k] C)) →ₗ[k] (V →ₗ[k] C))

theorem indDualMap_eq_sum [Fintype G] :
    indDualMap k G V C = ∑ x : G, (LinearMap.lcomp k C
        (LinearMap.proj x : (G → V) →ₗ[k] V)).comp
      (LinearMap.proj x : (G → (V →ₗ[k] C)) →ₗ[k] (V →ₗ[k] C)) :=
  finsum_eq_sum_of_fintype _

theorem indDualMap_apply [Fintype G] (φ : G → (V →ₗ[k] C)) (f : G → V) :
    indDualMap k G V C φ f = ∑ x : G, φ x (f x) := by
  simp [indDualMap_eq_sum, LinearMap.sum_apply]

theorem indDualMap_bijective [Finite G] : Function.Bijective (indDualMap k G V C) := by
  classical
  letI := Fintype.ofFinite G
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun φ hφ => funext fun y => LinearMap.ext fun v => ?_
    have h := LinearMap.congr_fun hφ (Pi.single y v)
    rw [indDualMap_apply, LinearMap.zero_apply,
      Finset.sum_eq_single y (fun x _ hx => by rw [Pi.single_eq_of_ne hx, map_zero])
        (fun hy => absurd (Finset.mem_univ y) hy), Pi.single_eq_same] at h
    exact h
  · intro Φ
    refine ⟨fun x => Φ.comp (LinearMap.single k (fun _ : G => V) x), LinearMap.ext fun f => ?_⟩
    rw [indDualMap_apply]
    have hsingle : ∀ x : G, (Φ.comp (LinearMap.single k (fun _ : G => V) x)) (f x)
        = Φ (Pi.single x (f x)) := fun _ => rfl
    simp_rw [hsingle]
    rw [← map_sum, Finset.univ_sum_single]

end IndDual

/-! ### The reading respects the action -/

section IndDualEquivariant

variable (k : Type*) [CommRing k] (G : Type*) [Group G] [Finite G] (V : Type*) [AddCommGroup V]
  [Module k V] (C : Type*) [AddCommGroup C] [Module k C]

/-- **Reading a family of functionals as a functional respects the action.** -/
theorem indDualMap_equivariant (g : G) :
    indDualMap k G V C ∘ₗ inducedRep k G (V →ₗ[k] C) g
      = coeffDual (inducedRep k G V) C g ∘ₗ indDualMap k G V C := by
  letI := Fintype.ofFinite G
  refine LinearMap.ext fun φ => LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, indDualMap_apply, coeffDual_apply,
    indDualMap_apply]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
  rw [Equiv.coe_mulRight, inducedRep_apply, inducedRep_apply, mul_inv_cancel_right]

end IndDualEquivariant

/-! ### The functionals on a shift and on a coshift -/

section ShiftDual

variable {k G V : Type*} [CommRing k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (C : Type*) [AddCommGroup C] [Module k C]

/-- **The summation map of the functionals is precomposition with the record of the
translates.** -/
theorem indDualMap_comp_coindEmb (φ : G → (V →ₗ[k] C)) :
    indDualMap k G V C φ ∘ₗ coindEmb ρ = augMap (coeffDual ρ C) φ := by
  letI := Fintype.ofFinite G
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, indDualMap_apply, augMap_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coindEmb_apply, coeffDual_apply, inv_inv]

/-- **The record of the translates of a functional is precomposition with the summation map.** -/
theorem indDualMap_coindEmb_coeffDual (ψ : V →ₗ[k] C) :
    indDualMap k G V C (coindEmb (coeffDual ρ C) ψ) = ψ ∘ₗ augMap ρ := by
  letI := Fintype.ofFinite G
  refine LinearMap.ext fun f => ?_
  rw [indDualMap_apply, LinearMap.comp_apply, augMap_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coindEmb_apply, coeffDual_apply]

/-- A family of functionals of vanishing sum is read as a functional killing the record of the
translates. -/
theorem range_coindEmb_le_ker_indDualMap (φ : ↥(LinearMap.ker (augMap (coeffDual ρ C)))) :
    LinearMap.range (coindEmb ρ)
      ≤ LinearMap.ker (indDualMap k G V C (φ : G → (V →ₗ[k] C))) := by
  rintro _ ⟨v, rfl⟩
  refine LinearMap.mem_ker.2 ?_
  rw [← LinearMap.comp_apply, indDualMap_comp_coindEmb, LinearMap.mem_ker.1 φ.2,
    LinearMap.zero_apply]

/-- **The coshift of the functionals lands in the functionals on the shift.** -/
def dualShiftMap : ↥(LinearMap.ker (augMap (coeffDual ρ C))) →ₗ[k]
    (((G → V) ⧸ LinearMap.range (coindEmb ρ)) →ₗ[k] C) where
  toFun φ := (LinearMap.range (coindEmb ρ)).liftQ (indDualMap k G V C (φ : G → (V →ₗ[k] C)))
    (range_coindEmb_le_ker_indDualMap ρ C φ)
  map_add' φ ψ := LinearMap.ext fun q => by
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb ρ)) q
    show indDualMap k G V C ((φ : G → (V →ₗ[k] C)) + (ψ : G → (V →ₗ[k] C))) f
      = indDualMap k G V C (φ : G → (V →ₗ[k] C)) f
        + indDualMap k G V C (ψ : G → (V →ₗ[k] C)) f
    rw [map_add, LinearMap.add_apply]
  map_smul' c φ := LinearMap.ext fun q => by
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb ρ)) q
    show indDualMap k G V C (c • (φ : G → (V →ₗ[k] C))) f
      = c • indDualMap k G V C (φ : G → (V →ₗ[k] C)) f
    rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem dualShiftMap_mkQ (φ : ↥(LinearMap.ker (augMap (coeffDual ρ C)))) (f : G → V) :
    dualShiftMap ρ C φ ((LinearMap.range (coindEmb ρ)).mkQ f)
      = indDualMap k G V C (φ : G → (V →ₗ[k] C)) f := rfl

theorem dualShiftMap_injective : Function.Injective (dualShiftMap ρ C) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ => Subtype.ext ?_
  refine (injective_iff_map_eq_zero _).1 (indDualMap_bijective k G V C).1 _
    (LinearMap.ext fun f => ?_)
  have h := LinearMap.congr_fun hφ ((LinearMap.range (coindEmb ρ)).mkQ f)
  rw [dualShiftMap_mkQ, LinearMap.zero_apply] at h
  rw [LinearMap.zero_apply]
  exact h

theorem dualShiftMap_surjective : Function.Surjective (dualShiftMap ρ C) := by
  intro F
  obtain ⟨φ, hφ⟩ := (indDualMap_bijective k G V C).2
    (F.comp (LinearMap.range (coindEmb ρ)).mkQ)
  have hker : φ ∈ LinearMap.ker (augMap (coeffDual ρ C)) := by
    refine LinearMap.mem_ker.2 ?_
    rw [← indDualMap_comp_coindEmb, hφ]
    refine LinearMap.ext fun v => ?_
    show F ((LinearMap.range (coindEmb ρ)).mkQ (coindEmb ρ v)) = 0
    rw [Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self (coindEmb ρ) v), map_zero]
  refine ⟨⟨φ, hker⟩, LinearMap.ext fun q => ?_⟩
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb ρ)) q
  show indDualMap k G V C φ f = F ((LinearMap.range (coindEmb ρ)).mkQ f)
  rw [hφ]
  rfl

/-- **The identification of the coshift of the functionals with the functionals on the shift
respects the action.** -/
theorem dualShiftMap_equivariant (g : G) :
    dualShiftMap ρ C ∘ₗ coshiftRep (coeffDual ρ C) g
      = coeffDual (shiftRep ρ) C g ∘ₗ dualShiftMap ρ C := by
  refine LinearMap.ext fun φ => LinearMap.ext fun q => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb ρ)) q
  show indDualMap k G V C (inducedRep k G (V →ₗ[k] C) g (φ : G → (V →ₗ[k] C))) f
    = indDualMap k G V C (φ : G → (V →ₗ[k] C)) (inducedRep k G V g⁻¹ f)
  exact LinearMap.congr_fun (LinearMap.congr_fun (indDualMap_equivariant k G V C g)
    (φ : G → (V →ₗ[k] C))) f

/-- **The shift of the functionals lands in the functionals on the coshift.** -/
def dualCoshiftMap : ((G → (V →ₗ[k] C)) ⧸ LinearMap.range (coindEmb (coeffDual ρ C)))
    →ₗ[k] (↥(LinearMap.ker (augMap ρ)) →ₗ[k] C) :=
  (LinearMap.range (coindEmb (coeffDual ρ C))).liftQ
    ((LinearMap.lcomp k C (LinearMap.ker (augMap ρ)).subtype).comp (indDualMap k G V C)) (by
      rintro _ ⟨ψ, rfl⟩
      refine LinearMap.mem_ker.2 (LinearMap.ext fun z => ?_)
      show indDualMap k G V C (coindEmb (coeffDual ρ C) ψ) (z : G → V) = 0
      rw [indDualMap_coindEmb_coeffDual, LinearMap.comp_apply, LinearMap.mem_ker.1 z.2, map_zero])

@[simp]
theorem dualCoshiftMap_mkQ (φ : G → (V →ₗ[k] C)) (z : ↥(LinearMap.ker (augMap ρ))) :
    dualCoshiftMap ρ C ((LinearMap.range (coindEmb (coeffDual ρ C))).mkQ φ) z
      = indDualMap k G V C φ (z : G → V) := rfl

theorem dualCoshiftMap_injective : Function.Injective (dualCoshiftMap ρ C) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb (coeffDual ρ C))) q
  have hle : LinearMap.ker (augMap ρ) ≤ LinearMap.ker (indDualMap k G V C φ) := by
    intro z hz
    refine LinearMap.mem_ker.2 ?_
    have h := LinearMap.congr_fun hq (⟨z, hz⟩ : ↥(LinearMap.ker (augMap ρ)))
    rwa [dualCoshiftMap_mkQ, LinearMap.zero_apply] at h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V →ₗ[k] C, ∀ f : G → V, ψ (augMap ρ f) = indDualMap k G V C φ f := by
    refine ⟨(Submodule.liftQ (LinearMap.ker (augMap ρ)) (indDualMap k G V C φ) hle).comp
      (LinearMap.quotKerEquivOfSurjective (augMap ρ) (augMap_surjective ρ)).symm.toLinearMap,
      fun f => ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨ψ, (indDualMap_bijective k G V C).1 ?_⟩
  rw [indDualMap_coindEmb_coeffDual]
  exact LinearMap.ext fun f => hψ f

theorem dualCoshiftMap_surjective (h : IsExtendableInto k C (LinearMap.ker (augMap ρ))) :
    Function.Surjective (dualCoshiftMap ρ C) := by
  intro F
  obtain ⟨F', hF'⟩ := h F
  obtain ⟨φ, hφ⟩ := (indDualMap_bijective k G V C).2 F'
  refine ⟨(LinearMap.range (coindEmb (coeffDual ρ C))).mkQ φ, LinearMap.ext fun z => ?_⟩
  rw [dualCoshiftMap_mkQ, hφ]
  exact hF' z

/-- **The identification of the shift of the functionals with the functionals on the coshift
respects the action.** -/
theorem dualCoshiftMap_equivariant (g : G) :
    dualCoshiftMap ρ C ∘ₗ shiftRep (coeffDual ρ C) g
      = coeffDual (coshiftRep ρ) C g ∘ₗ dualCoshiftMap ρ C := by
  refine LinearMap.ext fun q => LinearMap.ext fun z => ?_
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb (coeffDual ρ C))) q
  show indDualMap k G V C (inducedRep k G (V →ₗ[k] C) g φ) (z : G → V)
    = indDualMap k G V C φ (inducedRep k G V g⁻¹ (z : G → V))
  exact LinearMap.congr_fun (LinearMap.congr_fun (indDualMap_equivariant k G V C g) φ)
    (z : G → V)

end ShiftDual

/-! ### Moving the degree of the functionals -/

section Graded

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G) (C : Type u)
  [AddCommGroup C] [Module k C]

/-- **The coshift of the functionals on a representation is the functionals on its shift.** -/
def coeffDualShiftIso : coshiftObj (coeffDualObj A C) ≅ coeffDualObj (shiftObj A) C :=
  Action.mkIso (LinearEquiv.ofBijective (dualShiftMap A.ρ C)
      ⟨dualShiftMap_injective A.ρ C, dualShiftMap_surjective A.ρ C⟩).toModuleIso fun g =>
    ModuleCat.hom_ext (LinearMap.ext fun φ =>
      LinearMap.congr_fun (dualShiftMap_equivariant A.ρ C g) φ)

/-- **The shift of the functionals on a representation is the functionals on its coshift**, as soon
as the coefficients receive every functional defined on the kernel of the summation map. -/
def coeffDualCoshiftIso (h : IsExtendableInto k C (LinearMap.ker (augMap A.ρ))) :
    shiftObj (coeffDualObj A C) ≅ coeffDualObj (coshiftObj A) C :=
  Action.mkIso (LinearEquiv.ofBijective (dualCoshiftMap A.ρ C)
      ⟨dualCoshiftMap_injective A.ρ C, dualCoshiftMap_surjective A.ρ C h⟩).toModuleIso fun g =>
    ModuleCat.hom_ext (LinearMap.ext fun q =>
      LinearMap.congr_fun (dualCoshiftMap_equivariant A.ρ C g) q)

/-- **The complete cohomology of the functionals in a degree is the complete cohomology of the
functionals on the shift one degree higher.** -/
def tateCoeffDualShiftEquiv (n : ℤ) :
    ↥(tateModule (coeffDualObj A C) n)
      ≃ₗ[k] ↥(tateModule (coeffDualObj (shiftObj A) C) (n + 1)) :=
  (tateCoshiftEquiv (coeffDualObj A C) n).trans
    (tateMapIso (coeffDualShiftIso A C) (n + 1)).toLinearEquiv

/-- **The complete cohomology of the functionals on the coshift in a degree is the complete
cohomology of the functionals one degree higher.** -/
def tateCoeffDualCoshiftEquiv (h : IsExtendableInto k C (LinearMap.ker (augMap A.ρ))) (n : ℤ) :
    ↥(tateModule (coeffDualObj (coshiftObj A) C) n)
      ≃ₗ[k] ↥(tateModule (coeffDualObj A C) (n + 1)) :=
  (tateMapIso (coeffDualCoshiftIso A C h) n).symm.toLinearEquiv.trans
    (tateShiftEquiv (coeffDualObj A C) n)

end Graded

/-! ### Every degree, for coefficients killed by a prime -/

section Torsion

/-- **A functional on a submodule of a module killed by a prime extends to the whole module**, for
whichever action of the integers the ambient module carries. -/
theorem isExtendableInto_of_nsmul_eq_zero' {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C]
    [instC : Module ℤ C] {X : Type*} [AddCommGroup X] {instX : Module ℤ X}
    (N : @Submodule ℤ X _ _ instX) (hX : ∀ x : X, p • x = 0) :
    @IsExtendableInto ℤ _ C _ instC X _ instX N := by
  obtain rfl : instX = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  exact isExtendableInto_of_nsmul_eq_zero (p := p) N hX

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- **The complete cohomology of the functionals on a representation killed by a prime, in any
degree, is the group of functionals on the complete cohomology of the representation in the
complementary degree.** -/
theorem nonempty_tateDualEquiv (C : Type) [AddCommGroup C] (n : ℤ) :
    ∀ (A : Rep ℤ G), (∀ v : ↥A.V, p • v = 0) →
      Nonempty (↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ]
        (↥(tateModule A (-n - 1)) →ₗ[ℤ] C)) := by
  induction n using Int.induction_on with
  | zero =>
    intro A hA
    rw [show (-(0 : ℤ) - 1) = -1 from by norm_num]
    exact ⟨tateDualZeroEquivOfNsmul (p := p) A C hA⟩
  | succ i ih =>
    intro A hA
    obtain ⟨e⟩ := ih (coshiftObj A) (nsmul_coshiftObj_eq_zero A hA)
    have hs := tateCoshiftEquiv A (-(i : ℤ) - 2)
    rw [show (-(i : ℤ) - 2 + 1) = -(i : ℤ) - 1 from by ring] at hs
    rw [show (-((i : ℤ) + 1) - 1) = -(i : ℤ) - 2 from by ring]
    refine ⟨(tateCoeffDualCoshiftEquiv A C ?_ (i : ℤ)).symm.trans
      (e.trans (LinearEquiv.arrowCongr hs.symm (LinearEquiv.refl ℤ C)))⟩
    exact isExtendableInto_of_nsmul_eq_zero' (p := p) _ (nsmul_pi_eq_zero hA)
  | pred i ih =>
    intro A hA
    obtain ⟨e⟩ := ih (shiftObj A) (nsmul_shiftObj_eq_zero A hA)
    rw [show (-(-(i : ℤ)) - 1) = (i : ℤ) - 1 from by ring] at e
    have hs := tateShiftEquiv A ((i : ℤ) - 1)
    rw [show ((i : ℤ) - 1 + 1) = (i : ℤ) from by ring] at hs
    have hstep := tateCoeffDualShiftEquiv A C (-(i : ℤ) - 1)
    rw [show (-(i : ℤ) - 1 + 1) = -(i : ℤ) from by ring] at hstep
    rw [show (-(-(i : ℤ) - 1) - 1) = (i : ℤ) from by ring]
    exact ⟨hstep.trans (e.trans (LinearEquiv.arrowCongr hs (LinearEquiv.refl ℤ C)))⟩

/-- **The complete cohomology of the functionals on a representation killed by a prime, in any
degree, is the group of functionals on the complete cohomology of the representation in the
complementary degree.** -/
def tateDualEquiv (C : Type) [AddCommGroup C] (n : ℤ) (A : Rep ℤ G)
    (hA : ∀ v : ↥A.V, p • v = 0) :
    ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] C) :=
  (nonempty_tateDualEquiv (p := p) C n A hA).some

end Torsion

end

end InverseGalois.CFT.Tate
