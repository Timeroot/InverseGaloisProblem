/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Hexagon
import InverseGalois.CFT.Tate.Herbrand

/-!
# The Herbrand quotient does not see a finite change

An equivariant injection with finite cokernel does not change the Herbrand quotient: the short
exact sequence it defines has a finite quotient term, whose Herbrand quotient is one, and the
quotient is multiplicative.

This is what makes the Herbrand quotient a usable invariant of a lattice.  A lattice acted on by a
cyclic group is rarely equal to a permutation lattice, but it frequently contains one with finite
index, or is contained in one with finite index, and that is enough to transport the computation.

## Main definitions

* `InverseGalois.CFT.quotAut`: the automorphism induced on the quotient by a stable subgroup.
* `InverseGalois.CFT.tateSESOfInjective`: the short exact sequence defined by an equivariant
  injection.

## Main results

* `InverseGalois.CFT.herbrand_eq_of_injective_of_finite_quotient`: **an equivariant injection with
  finite cokernel does not change the Herbrand quotient.**
* `InverseGalois.CFT.herbrand_eq_of_finite_index`: the same statement for a stable subgroup of
  finite index.

## Tags

Tate cohomology, Herbrand quotient, commensurable lattices
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}

/-! ### The automorphism induced on a quotient -/

variable (σ : B ≃+ B) (N : AddSubgroup B)

/-- **The automorphism induced on the quotient by a stable subgroup.** -/
def quotAut (hN : N.map (σ : B →+ B) = N) : (B ⧸ N) ≃+ (B ⧸ N) :=
  QuotientAddGroup.congr N N σ hN

@[simp]
theorem quotAut_mk (hN : N.map (σ : B →+ B) = N) (b : B) :
    quotAut σ N hN (QuotientAddGroup.mk b) = QuotientAddGroup.mk (σ b) := rfl

/-- Powers of the induced automorphism are induced by the powers. -/
theorem pow_quotAut_apply (hN : N.map (σ : B →+ B) = N) (k : ℕ) (b : B) :
    ((quotAut σ N hN) ^ k) (QuotientAddGroup.mk b) = QuotientAddGroup.mk ((σ ^ k) b) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, quotAut_mk, pow_succ_apply]

/-- The induced automorphism inherits the order. -/
theorem quotAut_pow_eq_one (hN : N.map (σ : B →+ B) = N) (hσ : σ ^ n = 1) :
    (quotAut σ N hN) ^ n = 1 := by
  refine AddEquiv.ext fun x => ?_
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [pow_quotAut_apply, hσ]
  rfl

/-! ### The sequence defined by an equivariant injection -/

variable {σ N}
variable {σA : A ≃+ A} {σB : B ≃+ B}

/-- The image of an equivariant homomorphism is stable. -/
theorem map_range_eq_range (φ : A →+ B) (hφ : ∀ a, φ (σA a) = σB (φ a)) :
    φ.range.map (σB : B →+ B) = φ.range := by
  ext b
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨σA a, hφ a⟩
  · rintro ⟨a, rfl⟩
    refine ⟨σA.symm a, ?_⟩
    have h := hφ (σA.symm a)
    rw [σA.apply_symm_apply] at h
    exact h.symm

/-- **The short exact sequence defined by an equivariant injection**, with the cokernel as its
third term. -/
abbrev tateSESOfInjective (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (φ : A →+ B)
    (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ) :
    TateSES n A B (B ⧸ φ.range) where
  σA := σA
  σB := σB
  σC := quotAut σB φ.range (map_range_eq_range φ hφ)
  hσA := hσA
  hσB := hσB
  hσC := quotAut_pow_eq_one _ _ _ hσB
  f := φ
  g := QuotientAddGroup.mk' φ.range
  hf := hφ
  hg _ := rfl
  finj := hinj
  gsurj := QuotientAddGroup.mk'_surjective _
  range_eq_ker := (QuotientAddGroup.ker_mk' _).symm

/-! ### Invariance of the Herbrand quotient -/

/-- **An equivariant injection with finite cokernel does not change the Herbrand quotient.** -/
theorem herbrand_eq_of_injective_of_finite_quotient (hσA : σA ^ n = 1) (hσB : σB ^ n = 1)
    (φ : A →+ B) (hφ : ∀ a, φ (σA a) = σB (φ a)) (hinj : Function.Injective φ)
    [Finite (B ⧸ φ.range)]
    [Finite (tateH0 σA n)] [Finite (tateH0 σB n)]
    [Finite (tateHm1 σA n)] [Finite (tateHm1 σB n)] :
    herbrand σA n = herbrand σB n := by
  haveI : Finite (tateH0 (tateSESOfInjective hσA hσB φ hφ hinj).σA n) :=
    inferInstanceAs (Finite (tateH0 σA n))
  haveI : Finite (tateH0 (tateSESOfInjective hσA hσB φ hφ hinj).σB n) :=
    inferInstanceAs (Finite (tateH0 σB n))
  haveI : Finite (tateHm1 (tateSESOfInjective hσA hσB φ hφ hinj).σA n) :=
    inferInstanceAs (Finite (tateHm1 σA n))
  haveI : Finite (tateHm1 (tateSESOfInjective hσA hσB φ hφ hinj).σB n) :=
    inferInstanceAs (Finite (tateHm1 σB n))
  exact ((tateSESOfInjective hσA hσB φ hφ hinj).herbrand_eq_of_finite_quotient).symm

/-- **A stable subgroup of finite index has the Herbrand quotient of the whole module.** -/
theorem herbrand_eq_of_finite_index (hσB : σB ^ n = 1) (N : AddSubgroup B) (τ : N ≃+ N)
    (hτ : ∀ x : N, (τ x : B) = σB (x : B)) (hτn : τ ^ n = 1)
    [Finite (B ⧸ N)] [Finite (tateH0 τ n)] [Finite (tateH0 σB n)]
    [Finite (tateHm1 τ n)] [Finite (tateHm1 σB n)] :
    herbrand τ n = herbrand σB n := by
  have hrange : N.subtype.range = N := by
    ext b
    simp only [AddMonoidHom.mem_range, AddSubgroup.coe_subtype, Subtype.exists, exists_prop,
      exists_eq_right]
  haveI : Finite (B ⧸ N.subtype.range) := by
    rw [hrange]
    infer_instance
  exact herbrand_eq_of_injective_of_finite_quotient hτn hσB N.subtype hτ Subtype.val_injective

end InverseGalois.CFT
