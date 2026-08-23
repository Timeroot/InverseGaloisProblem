/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# The Tate groups of a finite product

A finite family of modules over the same cyclic group may be combined into their product, the
automorphism acting on each factor separately.  Both operators of the Tate formalism are then
computed coordinatewise: the difference of a family is the family of differences and the norm of a
family is the family of norms.  Consequently the fixed points, the norm kernels, the norm images
and the difference images are all products, and so are the two Tate groups.

Counting, the orders of the Tate groups multiply over the index, and hence so do the Herbrand
quotients.  The description of the Tate groups as products needs no finiteness at all, so a product
of arbitrarily many factors with vanishing Tate groups has vanishing Tate groups and Herbrand
quotient one.  Together with the description of a module induced from a subgroup, this is the shape
of the decomposition of the group of ideles of a Galois extension: the places above a fixed place of
the base form a single orbit and contribute an induced module, and the finitely many places of the
base that are allowed to contribute at all are combined by the product formula proved here.

## Main definitions

* `InverseGalois.CFT.piAut`: the automorphism of a finite product acting on each factor separately.
* `InverseGalois.CFT.tateH0PiEquiv`, `InverseGalois.CFT.tateHm1PiEquiv`: the Tate groups of a
  finite product are the products of the Tate groups.

## Main results

* `InverseGalois.CFT.normHom_piAut`: the norm of a family is computed coordinatewise.
* `InverseGalois.CFT.card_tateH0_piAut`, `InverseGalois.CFT.card_tateHm1_piAut`: the orders
  multiply over the index.
* `InverseGalois.CFT.herbrand_piAut`: **the Herbrand quotient of a finite product is the product of
  the Herbrand quotients.**
* `InverseGalois.CFT.subsingleton_tateH0_piAut`,
  `InverseGalois.CFT.subsingleton_tateHm1_piAut`: the Tate groups of a product of arbitrarily many
  factors vanish as soon as they vanish in every factor.
* `InverseGalois.CFT.herbrand_piAut_eq_one`: such a product has Herbrand quotient one.

## Tags

Tate cohomology, product, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]

/-! ### The automorphism of a product -/

/-- **The automorphism of a finite product** acting on each factor separately. -/
def piAut (σ : ∀ i, M i ≃+ M i) : (∀ i, M i) ≃+ (∀ i, M i) where
  toFun x i := σ i (x i)
  invFun x i := (σ i).symm (x i)
  left_inv _ := funext fun i => (σ i).symm_apply_apply _
  right_inv _ := funext fun i => (σ i).apply_symm_apply _
  map_add' _ _ := funext fun i => map_add (σ i) _ _

@[simp]
theorem piAut_apply (σ : ∀ i, M i ≃+ M i) (x : ∀ i, M i) (i : ι) : piAut σ x i = σ i (x i) := rfl

/-- Powers of the automorphism of a product act on each factor separately. -/
theorem pow_piAut_apply (σ : ∀ i, M i ≃+ M i) (k : ℕ) (x : ∀ i, M i) (i : ι) :
    ((piAut σ) ^ k) x i = ((σ i) ^ k) (x i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, piAut_apply, ih, pow_succ_apply]

/-- The automorphism of a product has the order given by the factors. -/
theorem piAut_pow_eq_one {σ : ∀ i, M i ≃+ M i} {n : ℕ} (hσ : ∀ i, (σ i) ^ n = 1) :
    (piAut σ) ^ n = 1 := by
  refine AddEquiv.ext fun x => funext fun i => ?_
  show ((piAut σ) ^ n) x i = x i
  rw [pow_piAut_apply, hσ i]
  rfl

/-! ### The two operators -/

/-- The difference operator of a product is computed coordinatewise. -/
theorem sigmaSubOne_piAut (σ : ∀ i, M i ≃+ M i) (x : ∀ i, M i) (i : ι) :
    sigmaSubOne (piAut σ) x i = sigmaSubOne (σ i) (x i) := rfl

/-- **The norm of a family is computed coordinatewise.** -/
theorem normHom_piAut (σ : ∀ i, M i ≃+ M i) (n : ℕ) (x : ∀ i, M i) (i : ι) :
    normHom (piAut σ) n x i = normHom (σ i) n (x i) := by
  rw [normHom_apply, normHom_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => pow_piAut_apply σ k x i

/-! ### The upper Tate group -/

variable (σ : ∀ i, M i ≃+ M i) (n : ℕ)

/-- Every coordinate of a fixed point of a product is fixed. -/
theorem fixed_apply_of_piAut {x : ∀ i, M i} (hx : piAut σ x = x) (i : ι) : σ i (x i) = x i :=
  congrFun hx i

/-- Every coordinate of an element of a product of norm zero has norm zero. -/
theorem normHom_apply_of_piAut {x : ∀ i, M i} (hx : normHom (piAut σ) n x = 0) (i : ι) :
    normHom (σ i) n (x i) = 0 := by
  rw [← normHom_piAut, hx]
  rfl

/-- **The comparison map from the upper Tate group of a product** to the product of the upper Tate
groups, induced by the projections. -/
def tateH0PiHom : tateH0 (piAut σ) n →+ ∀ i, tateH0 (σ i) n :=
  Pi.addMonoidHom fun i => tateH0.map n (Pi.evalAddMonoidHom M i) fun _ => rfl

theorem tateH0PiHom_mk (x : ∀ i, M i) (hx : piAut σ x = x) (i : ι) :
    tateH0PiHom σ n (tateH0.mk (piAut σ) n x hx) i
      = tateH0.mk (σ i) n (x i) (fixed_apply_of_piAut σ hx i) := rfl

theorem tateH0PiHom_surjective : Function.Surjective (tateH0PiHom σ n) := by
  intro c
  choose x hx hmk using fun i => tateH0.mk_surjective (c i)
  exact ⟨tateH0.mk (piAut σ) n x (funext hx), funext hmk⟩

theorem tateH0PiHom_injective : Function.Injective (tateH0PiHom σ n) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective c
  have hzero : ∀ i, tateH0.mk (σ i) n (x i) (fixed_apply_of_piAut σ hx i) = 0 := fun i => by
    rw [← tateH0PiHom_mk σ n x hx i, hc]
    rfl
  choose y hy using fun i => (tateH0.mk_eq_zero_iff _ _).mp (hzero i)
  refine (tateH0.mk_eq_zero_iff _ _).mpr ⟨y, funext fun i => ?_⟩
  rw [normHom_piAut]
  exact hy i

/-- **The upper Tate group of a finite product is the product of the upper Tate groups.** -/
noncomputable def tateH0PiEquiv : tateH0 (piAut σ) n ≃+ ∀ i, tateH0 (σ i) n :=
  AddEquiv.ofBijective _ ⟨tateH0PiHom_injective σ n, tateH0PiHom_surjective σ n⟩

/-- **The upper Tate group of a product vanishes as soon as it vanishes in every factor**, the
index being arbitrary. -/
theorem subsingleton_tateH0_piAut (h : ∀ i, Subsingleton (tateH0 (σ i) n)) :
    Subsingleton (tateH0 (piAut σ) n) :=
  ⟨fun _ _ => (tateH0PiEquiv σ n).injective (funext fun i => (h i).elim _ _)⟩

/-- The order of the upper Tate group of a product is the product of the orders. -/
theorem card_tateH0_piAut [Fintype ι] :
    Nat.card (tateH0 (piAut σ) n) = ∏ i, Nat.card (tateH0 (σ i) n) := by
  rw [Nat.card_congr (tateH0PiEquiv σ n).toEquiv, Nat.card_pi]

/-! ### The lower Tate group -/

/-- **The comparison map from the lower Tate group of a product** to the product of the lower Tate
groups, induced by the projections. -/
noncomputable def tateHm1PiHom : tateHm1 (piAut σ) n →+ ∀ i, tateHm1 (σ i) n :=
  Pi.addMonoidHom fun i => tateHm1.map n (Pi.evalAddMonoidHom M i) fun _ => rfl

theorem tateHm1PiHom_mk (x : ∀ i, M i) (hx : normHom (piAut σ) n x = 0) (i : ι) :
    tateHm1PiHom σ n (tateHm1.mk (piAut σ) n x hx) i
      = tateHm1.mk (σ i) n (x i) (normHom_apply_of_piAut σ n hx i) := rfl

theorem tateHm1PiHom_surjective : Function.Surjective (tateHm1PiHom σ n) := by
  intro c
  choose x hx hmk using fun i => tateHm1.mk_surjective (c i)
  refine ⟨tateHm1.mk (piAut σ) n x (funext fun i => ?_), funext hmk⟩
  rw [normHom_piAut]
  exact hx i

theorem tateHm1PiHom_injective : Function.Injective (tateHm1PiHom σ n) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := tateHm1.mk_surjective c
  have hzero : ∀ i, tateHm1.mk (σ i) n (x i) (normHom_apply_of_piAut σ n hx i) = 0 := fun i => by
    rw [← tateHm1PiHom_mk σ n x hx i, hc]
    rfl
  choose y hy using fun i => (tateHm1.mk_eq_zero_iff _ _).mp (hzero i)
  exact (tateHm1.mk_eq_zero_iff _ _).mpr ⟨y, funext hy⟩

/-- **The lower Tate group of a finite product is the product of the lower Tate groups.** -/
noncomputable def tateHm1PiEquiv : tateHm1 (piAut σ) n ≃+ ∀ i, tateHm1 (σ i) n :=
  AddEquiv.ofBijective _ ⟨tateHm1PiHom_injective σ n, tateHm1PiHom_surjective σ n⟩

/-- **The lower Tate group of a product vanishes as soon as it vanishes in every factor**, the
index being arbitrary. -/
theorem subsingleton_tateHm1_piAut (h : ∀ i, Subsingleton (tateHm1 (σ i) n)) :
    Subsingleton (tateHm1 (piAut σ) n) :=
  ⟨fun _ _ => (tateHm1PiEquiv σ n).injective (funext fun i => (h i).elim _ _)⟩

/-- The order of the lower Tate group of a product is the product of the orders. -/
theorem card_tateHm1_piAut [Fintype ι] :
    Nat.card (tateHm1 (piAut σ) n) = ∏ i, Nat.card (tateHm1 (σ i) n) := by
  rw [Nat.card_congr (tateHm1PiEquiv σ n).toEquiv, Nat.card_pi]

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of a finite product is the product of the Herbrand quotients.** -/
theorem herbrand_piAut [Fintype ι] : herbrand (piAut σ) n = ∏ i, herbrand (σ i) n := by
  simp only [herbrand]
  rw [card_tateH0_piAut, card_tateHm1_piAut, Nat.cast_prod, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- **A product of arbitrarily many modules with vanishing Tate groups has Herbrand quotient
one.**  This is what the places outside a finite set contribute to the Herbrand quotient of the
group of ideles. -/
theorem herbrand_piAut_eq_one (h0 : ∀ i, Subsingleton (tateH0 (σ i) n))
    (hm1 : ∀ i, Subsingleton (tateHm1 (σ i) n)) : herbrand (piAut σ) n = 1 := by
  haveI := subsingleton_tateH0_piAut σ n h0
  haveI := subsingleton_tateHm1_piAut σ n hm1
  rw [herbrand, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩]
  norm_num

end InverseGalois.CFT
