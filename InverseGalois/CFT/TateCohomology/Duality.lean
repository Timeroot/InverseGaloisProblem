/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded
import InverseGalois.CFT.TateCohomology.TensorPExact

/-!
# The two middle complete cohomology groups are dual to each other

The functionals on a representation with values in a fixed module carry an action of the group
through the source, and the norm of such a functional is its composition with the norm of the
representation, because summing over the group is the same as summing over its inverses.  That one
identity is the whole of the duality in the two middle degrees.

Evaluation pairs an invariant functional with a class of the coinvariants killed by the norm: the
functional is constant on the orbits, so it only depends on the class, and it kills the norms, so
the pairing does not see the functionals that are themselves norms.  What comes out is a map from
the complete cohomology in degree zero of the functionals to the functionals on the complete
cohomology in degree minus one.

**That map is bijective as soon as the coefficients receive every functional defined on the norms
of the representation and every functional defined on its vectors of vanishing norm.**  Injectivity
is one extension: a functional killing the classes of vanishing norm factors through the norms, and
an extension of that factor to the whole representation has the given functional as its norm.
Surjectivity is the other: a functional read on the vectors of vanishing norm extends to the whole
representation, and the extension is already invariant, because the difference of a vector and one
of its translates has vanishing norm and trivial class.

Coefficients killed by a prime supply both extensions with nothing further, since a submodule of a
module killed by a prime is a direct summand.  This is the base case of the duality of complete
cohomology, the one from which the shift of degree propagates the statement to every pair of
degrees adding to minus one.

## Main definitions

* `InverseGalois.CFT.Tate.coeffDual`: the functionals on a representation with values in a fixed
  module, acted on by the group through the source.
* `InverseGalois.CFT.Tate.IsExtendableInto`: the property of a submodule that every functional on
  it with values in the coefficients extends to the ambient module.
* `InverseGalois.CFT.Tate.coeffDualPairing`: the evaluation pairing of the complete cohomology in
  degree zero of the functionals with the complete cohomology in degree minus one.

## Main results

* `InverseGalois.CFT.Tate.normMap_coeffDual`: **the norm of a functional is its composition with
  the norm of the representation.**
* `InverseGalois.CFT.Tate.coeffDualEquiv`: **the complete cohomology in degree zero of the
  functionals on a representation is the module of functionals on its complete cohomology in
  degree minus one.**
* `InverseGalois.CFT.Tate.isExtendableInto_of_nsmul_eq_zero`: **a functional on a submodule of a
  module killed by a prime extends to the whole module.**
* `InverseGalois.CFT.Tate.tateDualZeroEquiv`, `InverseGalois.CFT.Tate.tateDualZeroEquivOfNsmul`:
  the same statement written with the graded complete cohomology, and its form for a
  representation killed by a prime.

## Tags

Tate cohomology, duality, norm map, invariants, coinvariants, finite group
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

universe u

/-! ### Functionals on a representation -/

section CoeffDual

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (C : Type*) [AddCommGroup C] [Module k C]

/-- **The functionals on a representation with values in a fixed module**, acted on by the group
through the source. -/
def coeffDual : Representation k G (V →ₗ[k] C) := linHom ρ (trivial k G C)

@[simp]
theorem coeffDual_apply (g : G) (f : V →ₗ[k] C) (v : V) :
    coeffDual ρ C g f v = f (ρ g⁻¹ v) := rfl

/-- **A functional is invariant exactly when it is constant on the orbits.** -/
theorem mem_invariants_coeffDual_iff (f : V →ₗ[k] C) :
    f ∈ (coeffDual ρ C).invariants ↔ ∀ (g : G) (v : V), f (ρ g v) = f v := by
  rw [mem_invariants]
  constructor
  · intro h g v
    simpa using congrArg (fun F : V →ₗ[k] C => F v) (h g⁻¹)
  · intro h g
    exact LinearMap.ext fun v => h g⁻¹ v

end CoeffDual

/-! ### Extending a functional -/

section Extend

/-- **The coefficients receive every functional defined on a submodule**: every functional on the
submodule with values in the coefficients is the restriction of one on the ambient module. -/
def IsExtendableInto (k : Type*) [CommRing k] (C : Type*) [AddCommGroup C] [Module k C]
    {X : Type*} [AddCommGroup X] [Module k X] (N : Submodule k X) : Prop :=
  ∀ φ : ↥N →ₗ[k] C, ∃ F : X →ₗ[k] C, ∀ x : ↥N, F (x : X) = φ x

/-- **A functional on a submodule of a module killed by a prime extends to the whole module**,
because the submodule is a direct summand over the field with that many elements. -/
theorem isExtendableInto_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime] {C X : Type*} [AddCommGroup C]
    [instC : Module ℤ C] [AddCommGroup X] [instX : Module ℤ X] (N : Submodule ℤ X)
    (hX : ∀ x : X, p • x = 0) : IsExtendableInto ℤ C N := by
  obtain rfl : instC = AddCommGroup.toIntModule C := Subsingleton.elim _ _
  obtain rfl : instX = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  intro φ
  obtain ⟨r, hr⟩ := exists_addMonoidHom_leftInverse (p := p) N.subtype.toAddMonoidHom
    (fun _ _ hab => Subtype.ext hab) hX
  exact ⟨(φ.toAddMonoidHom.comp r).toIntLinearMap, fun x => congrArg φ (hr x)⟩

end Extend

/-! ### The pairing -/

section Pairing

variable {k G V : Type*} [CommRing k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (C : Type*) [AddCommGroup C] [Module k C]

/-- **The norm of a functional is its composition with the norm of the representation.**  Summing
the actions of the inverses is summing the actions. -/
theorem normMap_coeffDual (f : V →ₗ[k] C) : normMap (coeffDual ρ C) f = f ∘ₗ normMap ρ := by
  letI := Fintype.ofFinite G
  refine LinearMap.ext fun v => ?_
  rw [normMap_apply (coeffDual ρ C) f, LinearMap.sum_apply, LinearMap.comp_apply,
    normMap_apply ρ v, map_sum]
  exact Fintype.sum_bijective (fun g : G => g⁻¹) inv_involutive.bijective _ _ fun _ => rfl

/-- **A vector of vanishing norm, read as a class of vanishing norm.** -/
def kerNormToHm1 : ↥(LinearMap.ker (normMap ρ)) →ₗ[k] ↥(Hm1 ρ) where
  toFun z := Hm1mk ρ (z : V) (LinearMap.mem_ker.1 z.2)
  map_add' a b := Subtype.ext (map_add (Coinvariants.mk ρ) (a : V) (b : V))
  map_smul' c a := Subtype.ext (map_smul (Coinvariants.mk ρ) c (a : V))

@[simp]
theorem kerNormToHm1_apply (v : V) (hv : v ∈ LinearMap.ker (normMap ρ)) :
    kerNormToHm1 ρ ⟨v, hv⟩ = Hm1mk ρ v (LinearMap.mem_ker.1 hv) := rfl

/-- An invariant functional, read on the coinvariants. -/
def coeffDualDescend (f : ↥(coeffDual ρ C).invariants) : Coinvariants ρ →ₗ[k] C :=
  Coinvariants.lift ρ (f : V →ₗ[k] C)
    fun g => LinearMap.ext fun v => (mem_invariants_coeffDual_iff ρ C _).1 f.2 g v

omit [Finite G] in
@[simp]
theorem coeffDualDescend_mk (f : ↥(coeffDual ρ C).invariants) (v : V) :
    coeffDualDescend ρ C f (Coinvariants.mk ρ v) = (f : V →ₗ[k] C) v := rfl

/-- An invariant functional, restricted to the complete cohomology in degree minus one. -/
def coeffDualRestrict : ↥(coeffDual ρ C).invariants →ₗ[k] (↥(Hm1 ρ) →ₗ[k] C) where
  toFun f := (coeffDualDescend ρ C f).domRestrict (Hm1 ρ)
  map_add' f₁ f₂ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ y
    rfl
  map_smul' c f := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ y
    rfl

theorem coeffDualRestrict_apply (f : ↥(coeffDual ρ C).invariants) (v : V)
    (hv : normMap ρ v = 0) :
    coeffDualRestrict ρ C f (Hm1mk ρ v hv) = (f : V →ₗ[k] C) v := rfl

/-- A functional that is itself a norm kills the classes of vanishing norm. -/
theorem range_coinvariantsNorm_le_ker_coeffDualRestrict :
    LinearMap.range (coinvariantsNorm (coeffDual ρ C))
      ≤ LinearMap.ker (coeffDualRestrict ρ C) := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨f, rfl⟩ := Coinvariants.mk_surjective (coeffDual ρ C) c
  refine LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_)
  obtain ⟨v, hv, rfl⟩ := exists_Hm1mk ρ x
  rw [coeffDualRestrict_apply, LinearMap.zero_apply, coinvariantsNorm_mk, normMap_coeffDual,
    LinearMap.comp_apply, hv, map_zero]

/-- **The evaluation pairing of the complete cohomology in degree zero of the functionals on a
representation with its complete cohomology in degree minus one.** -/
def coeffDualPairing : H0 (coeffDual ρ C) →ₗ[k] (↥(Hm1 ρ) →ₗ[k] C) :=
  Submodule.liftQ _ (coeffDualRestrict ρ C) (range_coinvariantsNorm_le_ker_coeffDualRestrict ρ C)

@[simp]
theorem coeffDualPairing_H0mk (f : ↥(coeffDual ρ C).invariants) :
    coeffDualPairing ρ C (H0mk (coeffDual ρ C) f) = coeffDualRestrict ρ C f := rfl

/-- **The pairing is injective** as soon as the coefficients receive every functional defined on
the norms of the representation.  A functional killing the classes of vanishing norm factors
through the norms, and an extension of that factor has the given functional as its norm. -/
theorem injective_coeffDualPairing (h : IsExtendableInto k C (LinearMap.range (normMap ρ))) :
    Function.Injective (coeffDualPairing ρ C) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨f, rfl⟩ := H0mk_surjective (coeffDual ρ C) x
  have hx' : coeffDualRestrict ρ C f = 0 := hx
  have hle : LinearMap.ker (normMap ρ) ≤ LinearMap.ker (f : V →ₗ[k] C) := fun v hv =>
    LinearMap.mem_ker.2 (by
      rw [← coeffDualRestrict_apply ρ C f v (LinearMap.mem_ker.1 hv), hx', LinearMap.zero_apply])
  set φ : ↥(LinearMap.range (normMap ρ)) →ₗ[k] C :=
    (Submodule.liftQ (LinearMap.ker (normMap ρ)) (f : V →ₗ[k] C) hle).comp
      (LinearMap.quotKerEquivRange (normMap ρ)).symm.toLinearMap with hφdef
  have hφ : ∀ v : V, φ ⟨normMap ρ v, ⟨v, rfl⟩⟩ = (f : V →ₗ[k] C) v := fun v => by
    rw [hφdef]
    show (Submodule.liftQ (LinearMap.ker (normMap ρ)) (f : V →ₗ[k] C) hle)
      ((LinearMap.quotKerEquivRange (normMap ρ)).symm ⟨normMap ρ v, ⟨v, rfl⟩⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨F, hF⟩ := h φ
  refine (H0mk_eq_zero_iff (coeffDual ρ C) f).2 ⟨F, ?_⟩
  rw [normMap_coeffDual]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, hF ⟨normMap ρ v, ⟨v, rfl⟩⟩]
  exact hφ v

/-- **The pairing is surjective** as soon as the coefficients receive every functional defined on
the vectors of vanishing norm.  Such an extension is automatically invariant: the difference of a
vector and one of its translates has vanishing norm and trivial class, so the extension takes the
same value on both. -/
theorem surjective_coeffDualPairing (h : IsExtendableInto k C (LinearMap.ker (normMap ρ))) :
    Function.Surjective (coeffDualPairing ρ C) := by
  intro φ
  obtain ⟨F, hF⟩ := h (φ ∘ₗ kerNormToHm1 ρ)
  have hkey : ∀ (w : V) (hw : normMap ρ w = 0), F w = φ (Hm1mk ρ w hw) := fun w hw =>
    hF ⟨w, LinearMap.mem_ker.2 hw⟩
  have hinv : ∀ (g : G) (v : V), F (ρ g v) = F v := fun g v => by
    have hz : normMap ρ (ρ g v - v) = 0 := by rw [map_sub, normMap_smul_apply, sub_self]
    have h0 : Hm1mk ρ (ρ g v - v) hz = 0 := Subtype.ext (by
      show Coinvariants.mk ρ (ρ g v - v) = 0
      rw [map_sub, Coinvariants.mk_self_apply, sub_self])
    have h1 := hkey (ρ g v - v) hz
    rw [h0, map_zero, map_sub] at h1
    exact sub_eq_zero.1 h1
  refine ⟨H0mk (coeffDual ρ C) ⟨F, (mem_invariants_coeffDual_iff ρ C F).2 hinv⟩, ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, hv, rfl⟩ := exists_Hm1mk ρ x
  rw [coeffDualPairing_H0mk, coeffDualRestrict_apply]
  exact hkey v hv

/-- **The complete cohomology in degree zero of the functionals on a representation is the module
of functionals on its complete cohomology in degree minus one**, whenever the coefficients receive
the functionals defined on the norms and on the vectors of vanishing norm. -/
def coeffDualEquiv (h₁ : IsExtendableInto k C (LinearMap.range (normMap ρ)))
    (h₂ : IsExtendableInto k C (LinearMap.ker (normMap ρ))) :
    H0 (coeffDual ρ C) ≃ₗ[k] (↥(Hm1 ρ) →ₗ[k] C) :=
  LinearEquiv.ofBijective (coeffDualPairing ρ C)
    ⟨injective_coeffDualPairing ρ C h₁, surjective_coeffDualPairing ρ C h₂⟩

@[simp]
theorem coe_coeffDualEquiv (h₁ : IsExtendableInto k C (LinearMap.range (normMap ρ)))
    (h₂ : IsExtendableInto k C (LinearMap.ker (normMap ρ))) :
    ⇑(coeffDualEquiv ρ C h₁ h₂) = coeffDualPairing ρ C := rfl

end Pairing

/-! ### The statement for the graded complete cohomology -/

section Graded

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G) (C : Type u)
  [AddCommGroup C] [Module k C]

/-- **The functionals on a representation with values in a fixed module**, as a representation. -/
def coeffDualObj : Rep k G := Rep.of (coeffDual A.ρ C)

omit [Finite G] in
@[simp]
theorem coeffDualObj_ρ : (coeffDualObj A C).ρ = coeffDual A.ρ C := rfl

/-- **The complete cohomology in degree zero of the functionals on a representation is the module
of functionals on its complete cohomology in degree minus one.** -/
def tateDualZeroEquiv (h₁ : IsExtendableInto k C (LinearMap.range (normMap A.ρ)))
    (h₂ : IsExtendableInto k C (LinearMap.ker (normMap A.ρ))) :
    ↥(tateModule (coeffDualObj A C) 0) ≃ₗ[k] (↥(tateModule A (-1)) →ₗ[k] C) :=
  coeffDualEquiv A.ρ C h₁ h₂

end Graded

section GradedPTorsion

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] (A : Rep ℤ G) (C : Type)
  [AddCommGroup C]

/-- **For a representation killed by a prime the complete cohomology in degree zero of the
functionals is the module of functionals on the complete cohomology in degree minus one**, whatever
the coefficients are.  A submodule of a module killed by a prime is a direct summand, so both
extensions are available. -/
def tateDualZeroEquivOfNsmul (hA : ∀ v : ↥A.V, p • v = 0) :
    ↥(tateModule (coeffDualObj A C) 0) ≃ₗ[ℤ] (↥(tateModule A (-1)) →ₗ[ℤ] C) :=
  tateDualZeroEquiv A C
    (isExtendableInto_of_nsmul_eq_zero (p := p) (LinearMap.range (normMap A.ρ)) hA)
    (isExtendableInto_of_nsmul_eq_zero (p := p) (LinearMap.ker (normMap A.ρ)) hA)

end GradedPTorsion

end

end InverseGalois.CFT.Tate
