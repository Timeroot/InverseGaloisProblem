/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.FiniteExact
import InverseGalois.CFT.Tate.Shapiro

/-!
# A module containing an induced lattice of finite index

Over the trivial group both Tate groups vanish: the norm is the identity, so every fixed point is a
norm, and only zero has norm zero.  Shapiro's lemma then makes both Tate groups of a module induced
from the trivial group vanish, so its Herbrand quotient is one.  A module carrying an equivariant
copy of such an induced module with finite cokernel therefore has Herbrand quotient one as well.

## Main results

* `InverseGalois.CFT.subsingleton_tateH0_one`, `InverseGalois.CFT.subsingleton_tateHm1_one`: both
  Tate groups over the trivial group are trivial.
* `InverseGalois.CFT.herbrand_one`: the Herbrand quotient over the trivial group is one.
* `InverseGalois.CFT.herbrand_indAut_one`: **the Herbrand quotient of a module induced from the
  trivial action is one.**
* `InverseGalois.CFT.subsingleton_tateH0_of_indAutEquiv`,
  `InverseGalois.CFT.subsingleton_tateHm1_of_indAutEquiv`: both Tate groups of a module isomorphic
  to one induced from the trivial action vanish.
* `InverseGalois.CFT.finite_tate_of_indAut`: such a module has finite Tate groups.
* `InverseGalois.CFT.herbrand_eq_one_of_indAut`: **a module containing an equivariant induced
  module with finite cokernel has Herbrand quotient one.**

## Tags

Tate cohomology, Herbrand quotient, induced module, Shapiro's lemma, lattice
-/

namespace InverseGalois.CFT

variable {C : Type*} [AddCommGroup C]

/-! ### The trivial group -/

/-- **The norm over the trivial group is the identity.** -/
theorem normHom_apply_one (σ : C ≃+ C) (x : C) : normHom σ 1 x = x := by
  rw [normHom_apply, Finset.sum_range_one, pow_zero]
  rfl

/-- **The upper Tate group over the trivial group is trivial**, because every fixed point is its
own norm. -/
theorem subsingleton_tateH0_one (σ : C ≃+ C) : Subsingleton (tateH0 σ 1) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective a
  obtain ⟨y, hy, rfl⟩ := tateH0.mk_surjective b
  rw [← sub_eq_zero, tateH0.mk_sub, tateH0.mk_eq_zero_iff]
  exact ⟨x - y, normHom_apply_one σ (x - y)⟩

/-- **The lower Tate group over the trivial group is trivial**, because only zero has norm zero. -/
theorem subsingleton_tateHm1_one (σ : C ≃+ C) : Subsingleton (tateHm1 σ 1) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx, rfl⟩ := tateHm1.mk_surjective a
  obtain ⟨y, hy, rfl⟩ := tateHm1.mk_surjective b
  rw [normHom_apply_one] at hx hy
  subst hx
  subst hy
  rfl

/-- The upper Tate group over the trivial group is finite. -/
theorem finite_tateH0_one (σ : C ≃+ C) : Finite (tateH0 σ 1) :=
  haveI := subsingleton_tateH0_one σ
  Finite.of_subsingleton

/-- The lower Tate group over the trivial group is finite. -/
theorem finite_tateHm1_one (σ : C ≃+ C) : Finite (tateHm1 σ 1) :=
  haveI := subsingleton_tateHm1_one σ
  Finite.of_subsingleton

/-- **The Herbrand quotient over the trivial group is one.** -/
theorem herbrand_one (σ : C ≃+ C) : herbrand σ 1 = 1 := by
  haveI := subsingleton_tateH0_one σ
  haveI := subsingleton_tateHm1_one σ
  rw [herbrand, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩,
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
  norm_num

/-! ### An induced module -/

variable (C) in
/-- The automorphism of a module induced from the trivial action has order dividing the number of
coordinates. -/
theorem indAut_one_pow_eq_one (d : ℕ) [NeZero d] : (indAut (1 : C ≃+ C) d) ^ d = 1 := by
  have h := indAut_pow_eq_one (1 : C ≃+ C) (d := d) (m := 1) (one_pow 1)
  rwa [mul_one] at h

variable (C) in
/-- **The upper Tate group of a module induced from the trivial action vanishes.** -/
theorem subsingleton_tateH0_indAut_one (d : ℕ) [NeZero d] :
    Subsingleton (tateH0 (indAut (1 : C ≃+ C) d) d) := by
  haveI := subsingleton_tateH0_one (1 : C ≃+ C)
  have e := tateH0IndEquiv (1 : C ≃+ C) (d := d) 1 (one_pow 1)
  rw [mul_one] at e
  exact e.injective.subsingleton

variable (C) in
/-- **The lower Tate group of a module induced from the trivial action vanishes.** -/
theorem subsingleton_tateHm1_indAut_one (d : ℕ) [NeZero d] :
    Subsingleton (tateHm1 (indAut (1 : C ≃+ C) d) d) := by
  haveI := subsingleton_tateHm1_one (1 : C ≃+ C)
  have e := tateHm1IndEquiv (1 : C ≃+ C) (d := d) 1 (one_pow 1)
  rw [mul_one] at e
  exact e.injective.subsingleton

variable (C) in
/-- The upper Tate group of a module induced from the trivial action is finite. -/
theorem finite_tateH0_indAut_one (d : ℕ) [NeZero d] :
    Finite (tateH0 (indAut (1 : C ≃+ C) d) d) :=
  haveI := subsingleton_tateH0_indAut_one C d
  Finite.of_subsingleton

variable (C) in
/-- The lower Tate group of a module induced from the trivial action is finite. -/
theorem finite_tateHm1_indAut_one (d : ℕ) [NeZero d] :
    Finite (tateHm1 (indAut (1 : C ≃+ C) d) d) :=
  haveI := subsingleton_tateHm1_indAut_one C d
  Finite.of_subsingleton

variable (C) in
/-- **The Herbrand quotient of a module induced from the trivial action is one.** -/
theorem herbrand_indAut_one (d : ℕ) [NeZero d] : herbrand (indAut (1 : C ≃+ C) d) d = 1 := by
  have h := herbrand_indAut (1 : C ≃+ C) (d := d) 1 (one_pow 1)
  rw [mul_one] at h
  rw [h, herbrand_one]

/-! ### A module isomorphic to an induced module -/

variable {B : Type*} [AddCommGroup B] {d : ℕ} [NeZero d] {σB : B ≃+ B}

/-- **The upper Tate group of a module isomorphic to one induced from the trivial action
vanishes.** -/
theorem subsingleton_tateH0_of_indAutEquiv (Φ : (ZMod d → C) ≃+ B)
    (hΦ : ∀ f, Φ (indAut (1 : C ≃+ C) d f) = σB (Φ f)) : Subsingleton (tateH0 σB d) := by
  haveI := subsingleton_tateH0_indAut_one C d
  exact (tateH0Congr Φ hΦ d).symm.injective.subsingleton

/-- **The lower Tate group of a module isomorphic to one induced from the trivial action
vanishes.** -/
theorem subsingleton_tateHm1_of_indAutEquiv (Φ : (ZMod d → C) ≃+ B)
    (hΦ : ∀ f, Φ (indAut (1 : C ≃+ C) d f) = σB (Φ f)) : Subsingleton (tateHm1 σB d) := by
  haveI := subsingleton_tateHm1_indAut_one C d
  exact (tateHm1Congr Φ hΦ d).symm.injective.subsingleton

/-! ### A module containing an induced lattice -/

/-- Both Tate groups of a module containing an equivariant induced module with finite cokernel are
finite. -/
theorem finite_tate_of_indAut (hσB : σB ^ d = 1) (Φ : (ZMod d → C) →+ B)
    (hΦ : ∀ f, Φ (indAut (1 : C ≃+ C) d f) = σB (Φ f)) (hinj : Function.Injective Φ)
    [Finite (B ⧸ Φ.range)] : Finite (tateH0 σB d) ∧ Finite (tateHm1 σB d) := by
  haveI := finite_tateH0_indAut_one C d
  haveI := finite_tateHm1_indAut_one C d
  exact ⟨finite_tateH0_of_injective (indAut_one_pow_eq_one C d) hσB Φ hΦ hinj,
    finite_tateHm1_of_injective (indAut_one_pow_eq_one C d) hσB Φ hΦ hinj⟩

/-- **A module containing an equivariant induced module with finite cokernel has Herbrand quotient
one.** -/
theorem herbrand_eq_one_of_indAut (hσB : σB ^ d = 1) (Φ : (ZMod d → C) →+ B)
    (hΦ : ∀ f, Φ (indAut (1 : C ≃+ C) d f) = σB (Φ f)) (hinj : Function.Injective Φ)
    [Finite (B ⧸ Φ.range)] : herbrand σB d = 1 := by
  haveI := finite_tateH0_indAut_one C d
  haveI := finite_tateHm1_indAut_one C d
  rw [← herbrand_eq_of_injective_of_finite_quotient_of_finite_source
    (indAut_one_pow_eq_one C d) hσB Φ hΦ hinj, herbrand_indAut_one]

end InverseGalois.CFT
