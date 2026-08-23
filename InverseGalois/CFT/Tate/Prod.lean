/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# The Tate groups of a product

A pair of modules over the same cyclic group may be combined into their product, the automorphism
acting on each factor separately.  Both operators of the Tate formalism are then computed
coordinatewise: the difference of a pair is the pair of differences and the norm of a pair is the
pair of norms.  Consequently the fixed points, the norm kernels, the norm images and the difference
images are all products, and so are the two Tate groups.

Counting, the orders of the Tate groups multiply, and hence so do the Herbrand quotients.  This is
the finite shadow of the decomposition of the group of ideles into local factors, where a Herbrand
quotient is computed one place at a time and the answers are multiplied.

## Main definitions

* `InverseGalois.CFT.prodAut`: the automorphism of a product acting on each factor separately.
* `InverseGalois.CFT.tateH0ProdEquiv`, `InverseGalois.CFT.tateHm1ProdEquiv`: the Tate groups of a
  product are the products of the Tate groups.

## Main results

* `InverseGalois.CFT.normHom_prodAut`: the norm of a product is computed coordinatewise.
* `InverseGalois.CFT.card_tateH0_prodAut`, `InverseGalois.CFT.card_tateHm1_prodAut`: the orders
  multiply.
* `InverseGalois.CFT.herbrand_prodAut`: **the Herbrand quotient is multiplicative in products.**

## Tags

Tate cohomology, product, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-! ### The automorphism of a product -/

/-- **The automorphism of a product** acting on each factor separately. -/
def prodAut (σ : A ≃+ A) (τ : B ≃+ B) : A × B ≃+ A × B where
  toFun z := (σ z.1, τ z.2)
  invFun z := (σ.symm z.1, τ.symm z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' _ _ := by simp

@[simp]
theorem prodAut_apply (σ : A ≃+ A) (τ : B ≃+ B) (z : A × B) :
    prodAut σ τ z = (σ z.1, τ z.2) := rfl

/-- Powers of the automorphism of a product act on each factor separately. -/
theorem pow_prodAut_apply (σ : A ≃+ A) (τ : B ≃+ B) (i : ℕ) (z : A × B) :
    ((prodAut σ τ) ^ i) z = ((σ ^ i) z.1, (τ ^ i) z.2) := by
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, prodAut_apply, pow_succ_apply, pow_succ_apply]

/-- The automorphism of a product has the order given by the two factors. -/
theorem prodAut_pow_eq_one {σ : A ≃+ A} {τ : B ≃+ B} {n : ℕ} (hσ : σ ^ n = 1) (hτ : τ ^ n = 1) :
    (prodAut σ τ) ^ n = 1 := by
  refine AddEquiv.ext fun z => ?_
  rw [pow_prodAut_apply]
  have h1 : (σ ^ n) z.1 = z.1 := by rw [hσ]; rfl
  have h2 : (τ ^ n) z.2 = z.2 := by rw [hτ]; rfl
  rw [h1, h2]
  rfl

/-! ### The two operators -/

/-- The difference operator of a product is computed coordinatewise. -/
theorem sigmaSubOne_prodAut (σ : A ≃+ A) (τ : B ≃+ B) (z : A × B) :
    sigmaSubOne (prodAut σ τ) z = (sigmaSubOne σ z.1, sigmaSubOne τ z.2) := rfl

/-- **The norm of a product is computed coordinatewise.** -/
theorem normHom_prodAut (σ : A ≃+ A) (τ : B ≃+ B) (n : ℕ) (z : A × B) :
    normHom (prodAut σ τ) n z = (normHom σ n z.1, normHom τ n z.2) := by
  rw [normHom_apply, normHom_apply, normHom_apply]
  induction n with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]
      rfl
  | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        pow_prodAut_apply]
      rfl

/-! ### The upper Tate group -/

variable (σ : A ≃+ A) (τ : B ≃+ B) (n : ℕ)

/-- The first coordinate of a fixed point of a product is fixed. -/
theorem fixed_fst_of_prodAut {z : A × B} (hz : prodAut σ τ z = z) : σ z.1 = z.1 :=
  congrArg Prod.fst hz

/-- The second coordinate of a fixed point of a product is fixed. -/
theorem fixed_snd_of_prodAut {z : A × B} (hz : prodAut σ τ z = z) : τ z.2 = z.2 :=
  congrArg Prod.snd hz

/-- The first coordinate of an element of a product of norm zero has norm zero. -/
theorem normHom_fst_of_prodAut {z : A × B} (hz : normHom (prodAut σ τ) n z = 0) :
    normHom σ n z.1 = 0 := by
  rw [normHom_prodAut] at hz
  exact congrArg Prod.fst hz

/-- The second coordinate of an element of a product of norm zero has norm zero. -/
theorem normHom_snd_of_prodAut {z : A × B} (hz : normHom (prodAut σ τ) n z = 0) :
    normHom τ n z.2 = 0 := by
  rw [normHom_prodAut] at hz
  exact congrArg Prod.snd hz

/-- **The comparison map from the upper Tate group of a product** to the product of the upper Tate
groups, induced by the two projections. -/
def tateH0ProdHom : tateH0 (prodAut σ τ) n →+ tateH0 σ n × tateH0 τ n :=
  (tateH0.map n (AddMonoidHom.fst A B) fun _ => rfl).prod
    (tateH0.map n (AddMonoidHom.snd A B) fun _ => rfl)

theorem tateH0ProdHom_mk (z : A × B) (hz : prodAut σ τ z = z) :
    tateH0ProdHom σ τ n (tateH0.mk (prodAut σ τ) n z hz)
      = (tateH0.mk σ n z.1 (fixed_fst_of_prodAut σ τ hz),
        tateH0.mk τ n z.2 (fixed_snd_of_prodAut σ τ hz)) := rfl

theorem tateH0ProdHom_surjective : Function.Surjective (tateH0ProdHom σ τ n) := by
  rintro ⟨c, d⟩
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective c
  obtain ⟨y, hy, rfl⟩ := tateH0.mk_surjective d
  refine ⟨tateH0.mk (prodAut σ τ) n (x, y) ?_, rfl⟩
  show (σ x, τ y) = (x, y)
  rw [hx, hy]

theorem tateH0ProdHom_injective : Function.Injective (tateH0ProdHom σ τ n) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, hz, rfl⟩ := tateH0.mk_surjective c
  rw [tateH0ProdHom_mk] at hc
  have h1 : tateH0.mk σ n z.1 (fixed_fst_of_prodAut σ τ hz) = 0 := congrArg Prod.fst hc
  have h2 : tateH0.mk τ n z.2 (fixed_snd_of_prodAut σ τ hz) = 0 := congrArg Prod.snd hc
  obtain ⟨a, ha⟩ := (tateH0.mk_eq_zero_iff _ _).mp h1
  obtain ⟨b, hb⟩ := (tateH0.mk_eq_zero_iff _ _).mp h2
  refine (tateH0.mk_eq_zero_iff _ _).mpr ⟨(a, b), ?_⟩
  rw [normHom_prodAut]
  exact Prod.ext ha hb

/-- **The upper Tate group of a product is the product of the upper Tate groups.** -/
noncomputable def tateH0ProdEquiv : tateH0 (prodAut σ τ) n ≃+ tateH0 σ n × tateH0 τ n :=
  AddEquiv.ofBijective _ ⟨tateH0ProdHom_injective σ τ n, tateH0ProdHom_surjective σ τ n⟩

/-- The order of the upper Tate group of a product is the product of the orders. -/
theorem card_tateH0_prodAut :
    Nat.card (tateH0 (prodAut σ τ) n) = Nat.card (tateH0 σ n) * Nat.card (tateH0 τ n) := by
  rw [Nat.card_congr (tateH0ProdEquiv σ τ n).toEquiv, Nat.card_prod]

/-! ### The lower Tate group -/

/-- **The comparison map from the lower Tate group of a product** to the product of the lower Tate
groups, induced by the two projections. -/
noncomputable def tateHm1ProdHom : tateHm1 (prodAut σ τ) n →+ tateHm1 σ n × tateHm1 τ n :=
  (tateHm1.map n (AddMonoidHom.fst A B) fun _ => rfl).prod
    (tateHm1.map n (AddMonoidHom.snd A B) fun _ => rfl)

theorem tateHm1ProdHom_mk (z : A × B) (hz : normHom (prodAut σ τ) n z = 0) :
    tateHm1ProdHom σ τ n (tateHm1.mk (prodAut σ τ) n z hz)
      = (tateHm1.mk σ n z.1 (normHom_fst_of_prodAut σ τ n hz),
        tateHm1.mk τ n z.2 (normHom_snd_of_prodAut σ τ n hz)) := rfl

theorem tateHm1ProdHom_surjective : Function.Surjective (tateHm1ProdHom σ τ n) := by
  rintro ⟨c, d⟩
  obtain ⟨x, hx, rfl⟩ := tateHm1.mk_surjective c
  obtain ⟨y, hy, rfl⟩ := tateHm1.mk_surjective d
  refine ⟨tateHm1.mk (prodAut σ τ) n (x, y) ?_, rfl⟩
  rw [normHom_prodAut, hx, hy]
  rfl

theorem tateHm1ProdHom_injective : Function.Injective (tateHm1ProdHom σ τ n) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, hz, rfl⟩ := tateHm1.mk_surjective c
  rw [tateHm1ProdHom_mk] at hc
  have h1 : tateHm1.mk σ n z.1 (normHom_fst_of_prodAut σ τ n hz) = 0 := congrArg Prod.fst hc
  have h2 : tateHm1.mk τ n z.2 (normHom_snd_of_prodAut σ τ n hz) = 0 := congrArg Prod.snd hc
  obtain ⟨a, ha⟩ := (tateHm1.mk_eq_zero_iff _ _).mp h1
  obtain ⟨b, hb⟩ := (tateHm1.mk_eq_zero_iff _ _).mp h2
  exact (tateHm1.mk_eq_zero_iff _ _).mpr ⟨(a, b), Prod.ext ha hb⟩

/-- **The lower Tate group of a product is the product of the lower Tate groups.** -/
noncomputable def tateHm1ProdEquiv : tateHm1 (prodAut σ τ) n ≃+ tateHm1 σ n × tateHm1 τ n :=
  AddEquiv.ofBijective _ ⟨tateHm1ProdHom_injective σ τ n, tateHm1ProdHom_surjective σ τ n⟩

/-- The order of the lower Tate group of a product is the product of the orders. -/
theorem card_tateHm1_prodAut :
    Nat.card (tateHm1 (prodAut σ τ) n) = Nat.card (tateHm1 σ n) * Nat.card (tateHm1 τ n) := by
  rw [Nat.card_congr (tateHm1ProdEquiv σ τ n).toEquiv, Nat.card_prod]

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient is multiplicative in products.** -/
theorem herbrand_prodAut : herbrand (prodAut σ τ) n = herbrand σ n * herbrand τ n := by
  rw [herbrand, herbrand, herbrand, card_tateH0_prodAut, card_tateHm1_prodAut, Nat.cast_mul,
    Nat.cast_mul, div_mul_div_comm]

end InverseGalois.CFT
