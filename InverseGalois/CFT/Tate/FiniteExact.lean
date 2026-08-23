/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Hexagon
import InverseGalois.CFT.Tate.Herbrand
import InverseGalois.CFT.Tate.Isogeny

/-!
# Finiteness of Tate groups travels along an isogeny

The Tate groups of a module over a cyclic group are almost never finite for the trivial reason
that the module is: the modules of interest are lattices, or rings of integers, which are infinite.
Finiteness of the Tate groups is instead a statement about the module modulo the operators
`x ↦ σ x - x` and the norm, and as such it is insensitive to a change of the module by something
finite.

That insensitivity is exactly what the Tate hexagon provides.  Three consecutive terms of an exact
sequence bound the middle one: if the outer two are finite so is the one between them, because the
middle term is an extension of a subgroup of the right-hand term by a quotient of the left-hand
one.  Applying this at the four corners of the hexagon that involve the two ends of a short exact
sequence with finite quotient term transports finiteness of the Tate groups in both directions,
from the subobject to the total object and back.

The consequence is that the invariance of the Herbrand quotient under an equivariant injection with
finite cokernel needs its finiteness hypotheses on one side only.  Whichever of the two modules is
under control supplies the finiteness of the Tate groups of the other, so the computation may be
transported to a lattice whose cohomology is known without first knowing that the answer is finite
on both sides.

## Main results

* `InverseGalois.CFT.finite_of_exact`: **the middle term of a three-term exact sequence with finite
  ends is finite.**
* `InverseGalois.CFT.TateSES.finite_tateH0_mid`, `InverseGalois.CFT.TateSES.finite_tateHm1_mid`,
  `InverseGalois.CFT.TateSES.finite_tateH0_sub`, `InverseGalois.CFT.TateSES.finite_tateHm1_sub`:
  **finiteness of the Tate groups transports across a short exact sequence with finite quotient
  term**, in both directions.
* `InverseGalois.CFT.TateSES.finite_tateH0_mid'` and its three companions: the same transport
  assuming only that the Tate groups of the quotient term are finite.
* `InverseGalois.CFT.finite_tateH0_of_injective` and its three companions: the same statements for
  an equivariant injection with finite cokernel.
* `InverseGalois.CFT.herbrand_eq_of_injective_of_finite_quotient_of_finite_source` and its three
  companions: **an equivariant injection with finite cokernel does not change the Herbrand
  quotient**, assuming finiteness of the Tate groups of only one of the two modules.

## Tags

Tate cohomology, Herbrand quotient, hexagon, exact sequence, finiteness
-/

namespace InverseGalois.CFT

/-! ### Finiteness in an exact sequence -/

/-- **The middle term of a three-term exact sequence with finite ends is finite.**  The middle term
is an extension of a subgroup of the right-hand term, namely the image of the second map, by the
kernel of that map, which is a quotient of the left-hand term. -/
theorem finite_of_exact {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (α : X →+ Y) (β : Y →+ Z) (h : α.range = β.ker) [Finite X] [Finite Z] : Finite Y := by
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype Z := Fintype.ofFinite Z
  haveI : Fintype Y := AddGroup.fintypeOfKerEqRange α β h.symm
  infer_instance

/-! ### Transport across a short exact sequence -/

namespace TateSES

variable {n : ℕ} {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (S : TateSES n A B C)

/-- The Tate group `Ĥ⁰` of the quotient term of a short exact sequence with finite quotient term is
finite, being a subquotient of a finite group. -/
theorem finite_tateH0_quot [Finite C] : Finite (tateH0 S.σC n) := inferInstance

/-- The Tate group `Ĥ⁻¹` of the quotient term of a short exact sequence with finite quotient term
is finite, being a subquotient of a finite group. -/
theorem finite_tateHm1_quot [Finite C] : Finite (tateHm1 S.σC n) := inferInstance

/-- **Finiteness of `Ĥ⁰` passes from the subobject to the total object** across a short exact
sequence whose quotient term is finite. -/
theorem finite_tateH0_mid [Finite C] [Finite (tateH0 S.σA n)] : Finite (tateH0 S.σB n) :=
  finite_of_exact S.alpha0 S.beta0 S.range_alpha0_eq_ker_beta0

/-- **Finiteness of `Ĥ⁻¹` passes from the subobject to the total object** across a short exact
sequence whose quotient term is finite. -/
theorem finite_tateHm1_mid [Finite C] [Finite (tateHm1 S.σA n)] : Finite (tateHm1 S.σB n) :=
  finite_of_exact S.alpha1 S.beta1 S.range_alpha1_eq_ker_beta1

/-- **Finiteness of `Ĥ⁰` passes from the total object to the subobject** across a short exact
sequence whose quotient term is finite. -/
theorem finite_tateH0_sub [Finite C] [Finite (tateH0 S.σB n)] : Finite (tateH0 S.σA n) :=
  finite_of_exact S.delta1 S.alpha0 S.range_delta1_eq_ker_alpha0

/-- **Finiteness of `Ĥ⁻¹` passes from the total object to the subobject** across a short exact
sequence whose quotient term is finite. -/
theorem finite_tateHm1_sub [Finite C] [Finite (tateHm1 S.σB n)] : Finite (tateHm1 S.σA n) :=
  finite_of_exact S.delta0 S.alpha1 S.range_delta0_eq_ker_alpha1

/-- **Finiteness of `Ĥ⁰` passes from the subobject to the total object** across a short exact
sequence whose quotient term has finite Tate groups. -/
theorem finite_tateH0_mid' [Finite (tateH0 S.σC n)] [Finite (tateH0 S.σA n)] :
    Finite (tateH0 S.σB n) :=
  finite_of_exact S.alpha0 S.beta0 S.range_alpha0_eq_ker_beta0

/-- **Finiteness of `Ĥ⁻¹` passes from the subobject to the total object** across a short exact
sequence whose quotient term has finite Tate groups. -/
theorem finite_tateHm1_mid' [Finite (tateHm1 S.σC n)] [Finite (tateHm1 S.σA n)] :
    Finite (tateHm1 S.σB n) :=
  finite_of_exact S.alpha1 S.beta1 S.range_alpha1_eq_ker_beta1

/-- **Finiteness of `Ĥ⁰` passes from the total object to the subobject** across a short exact
sequence whose quotient term has finite Tate groups. -/
theorem finite_tateH0_sub' [Finite (tateHm1 S.σC n)] [Finite (tateH0 S.σB n)] :
    Finite (tateH0 S.σA n) :=
  finite_of_exact S.delta1 S.alpha0 S.range_delta1_eq_ker_alpha0

/-- **Finiteness of `Ĥ⁻¹` passes from the total object to the subobject** across a short exact
sequence whose quotient term has finite Tate groups. -/
theorem finite_tateHm1_sub' [Finite (tateH0 S.σC n)] [Finite (tateHm1 S.σB n)] :
    Finite (tateHm1 S.σA n) :=
  finite_of_exact S.delta0 S.alpha1 S.range_delta0_eq_ker_alpha1

end TateSES

/-! ### Transport along an equivariant injection -/

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {σA : A ≃+ A} {σB : B ≃+ B} {n : ℕ}

/-- **An equivariant injection with finite cokernel carries finiteness of `Ĥ⁰` forwards.** -/
theorem finite_tateH0_of_injective (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (φ : A →+ B)
    (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ) [Finite (B ⧸ φ.range)]
    [Finite (tateH0 σA n)] [Finite (tateHm1 σA n)] : Finite (tateH0 σB n) := by
  haveI : Finite (tateH0 (tateSESOfInjective hσA hσB φ hφ hinj).σA n) :=
    inferInstanceAs (Finite (tateH0 σA n))
  exact (tateSESOfInjective hσA hσB φ hφ hinj).finite_tateH0_mid

/-- **An equivariant injection with finite cokernel carries finiteness of `Ĥ⁻¹` forwards.** -/
theorem finite_tateHm1_of_injective (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (φ : A →+ B)
    (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ) [Finite (B ⧸ φ.range)]
    [Finite (tateH0 σA n)] [Finite (tateHm1 σA n)] : Finite (tateHm1 σB n) := by
  haveI : Finite (tateHm1 (tateSESOfInjective hσA hσB φ hφ hinj).σA n) :=
    inferInstanceAs (Finite (tateHm1 σA n))
  exact (tateSESOfInjective hσA hσB φ hφ hinj).finite_tateHm1_mid

/-- **An equivariant injection with finite cokernel carries finiteness of `Ĥ⁰` backwards.** -/
theorem finite_tateH0_of_injective' (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (φ : A →+ B)
    (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ) [Finite (B ⧸ φ.range)]
    [Finite (tateH0 σB n)] [Finite (tateHm1 σB n)] : Finite (tateH0 σA n) := by
  haveI : Finite (tateH0 (tateSESOfInjective hσA hσB φ hφ hinj).σB n) :=
    inferInstanceAs (Finite (tateH0 σB n))
  exact (tateSESOfInjective hσA hσB φ hφ hinj).finite_tateH0_sub

/-- **An equivariant injection with finite cokernel carries finiteness of `Ĥ⁻¹` backwards.** -/
theorem finite_tateHm1_of_injective' (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (φ : A →+ B)
    (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ) [Finite (B ⧸ φ.range)]
    [Finite (tateH0 σB n)] [Finite (tateHm1 σB n)] : Finite (tateHm1 σA n) := by
  haveI : Finite (tateHm1 (tateSESOfInjective hσA hσB φ hφ hinj).σB n) :=
    inferInstanceAs (Finite (tateHm1 σB n))
  exact (tateSESOfInjective hσA hσB φ hφ hinj).finite_tateHm1_sub

/-! ### Invariance of the Herbrand quotient, with hypotheses on one side -/

/-- **An equivariant injection with finite cokernel does not change the Herbrand quotient**, the
finiteness of the Tate groups being assumed for the source only. -/
theorem herbrand_eq_of_injective_of_finite_quotient_of_finite_source (hσA : σA ^ n = 1)
    (hσB : σB ^ n = 1) (φ : A →+ B) (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ)
    [Finite (B ⧸ φ.range)] [Finite (tateH0 σA n)] [Finite (tateHm1 σA n)] :
    herbrand σA n = herbrand σB n := by
  haveI := finite_tateH0_of_injective hσA hσB φ hφ hinj
  haveI := finite_tateHm1_of_injective hσA hσB φ hφ hinj
  exact herbrand_eq_of_injective_of_finite_quotient hσA hσB φ hφ hinj

/-- **An equivariant injection with finite cokernel does not change the Herbrand quotient**, the
finiteness of the Tate groups being assumed for the target only. -/
theorem herbrand_eq_of_injective_of_finite_quotient_of_finite_target (hσA : σA ^ n = 1)
    (hσB : σB ^ n = 1) (φ : A →+ B) (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ)
    [Finite (B ⧸ φ.range)] [Finite (tateH0 σB n)] [Finite (tateHm1 σB n)] :
    herbrand σA n = herbrand σB n := by
  haveI := finite_tateH0_of_injective' hσA hσB φ hφ hinj
  haveI := finite_tateHm1_of_injective' hσA hσB φ hφ hinj
  exact herbrand_eq_of_injective_of_finite_quotient hσA hσB φ hφ hinj

/-- The image of the inclusion of a subgroup is that subgroup. -/
theorem range_subtype_eq (N : AddSubgroup B) : N.subtype.range = N := by
  ext b
  simp only [AddMonoidHom.mem_range, AddSubgroup.coe_subtype, Subtype.exists, exists_prop,
    exists_eq_right]

/-- **A stable subgroup of finite index has the Herbrand quotient of the whole module**, the
finiteness of the Tate groups being assumed for the subgroup only. -/
theorem herbrand_eq_of_finite_index_of_finite_source (hσB : σB ^ n = 1) (N : AddSubgroup B)
    (τ : N ≃+ N) (hτ : ∀ x : N, (τ x : B) = σB (x : B)) (hτn : τ ^ n = 1)
    [Finite (B ⧸ N)] [Finite (tateH0 τ n)] [Finite (tateHm1 τ n)] :
    herbrand τ n = herbrand σB n := by
  haveI : Finite (B ⧸ N.subtype.range) := by
    rw [range_subtype_eq]
    infer_instance
  exact herbrand_eq_of_injective_of_finite_quotient_of_finite_source hτn hσB N.subtype hτ
    Subtype.val_injective

/-- **A stable subgroup of finite index has the Herbrand quotient of the whole module**, the
finiteness of the Tate groups being assumed for the whole module only. -/
theorem herbrand_eq_of_finite_index_of_finite_target (hσB : σB ^ n = 1) (N : AddSubgroup B)
    (τ : N ≃+ N) (hτ : ∀ x : N, (τ x : B) = σB (x : B)) (hτn : τ ^ n = 1)
    [Finite (B ⧸ N)] [Finite (tateH0 σB n)] [Finite (tateHm1 σB n)] :
    herbrand τ n = herbrand σB n := by
  haveI : Finite (B ⧸ N.subtype.range) := by
    rw [range_subtype_eq]
    infer_instance
  exact herbrand_eq_of_injective_of_finite_quotient_of_finite_target hτn hσB N.subtype hτ
    Subtype.val_injective

end InverseGalois.CFT
