/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Mul

/-!
# The Tate groups of the units of a cyclic extension

For a finite cyclic Galois extension `L / K` with a chosen generator `g` of the Galois group, the
unit group `Lˣ` is a module over that cyclic group.  Two computations identify its Tate groups.

The norm operator of the Tate formalism, the product of the conjugates `x ↦ ∏ i < n, g ^ i x`, is
the field norm: enumerating a cyclic group by the powers of a generator turns the product over the
exponents into the product over the Galois group, which is the norm of the extension.  Hilbert's
theorem 90 then says exactly that `Ĥ⁻¹(Lˣ)` is trivial: an element whose conjugates multiply to one
is a quotient `g y / y`.

In the other degree, the fixed points of `g` in `Lˣ` are the units of the base field, because a
generator fixes only what the whole Galois group fixes, and for a Galois extension that is the base
field.  So `Ĥ⁰(Lˣ)` is the units of the base field modulo the norms from `L`.

## Main results

* `InverseGalois.CFT.coe_prod_range_unitsAut`: the product of the conjugates is the field norm.
* `InverseGalois.CFT.tateHm1_unitsAut_eq_zero`: **Hilbert's theorem 90**, that `Ĥ⁻¹(Lˣ)` is
  trivial.
* `InverseGalois.CFT.exists_algebraMap_of_unitsAut_eq`: a unit fixed by a generator lies in the
  base field.
* `InverseGalois.CFT.tateH0_unitsAut_mk_eq_zero_iff`: a unit of the base field is trivial in
  `Ĥ⁰(Lˣ)` exactly when it is a norm.

## Tags

Tate cohomology, Hilbert theorem 90, cyclic extension, norm
-/

namespace InverseGalois.CFT

/-- **Enumerating a finite cyclic group by the powers of a generator.**  The powers `a ^ i` for
`i` below the order of the group run through the group exactly once, so a product over the group
may be rewritten as a product over that range of exponents. -/
theorem prod_range_card_pow {α : Type*} [Group α] [Fintype α] {a : α}
    (ha : ∀ x : α, x ∈ Subgroup.zpowers a) {H : Type*} [CommMonoid H] (f : α → H) :
    ∏ i ∈ Finset.range (Nat.card α), f (a ^ i) = ∏ x : α, f x := by
  classical
  have horder : orderOf a = Nat.card α := orderOf_eq_card_of_forall_mem_zpowers ha
  have hinj : Set.InjOn (fun i => a ^ i) (Finset.range (Nat.card α) : Finset ℕ) := by
    intro i hi j hj hij
    refine pow_injOn_Iio_orderOf (x := a) ?_ ?_ hij
    · simpa [horder] using Finset.mem_range.mp hi
    · simpa [horder] using Finset.mem_range.mp hj
  rw [← IsCyclic.image_range_card ha, Finset.prod_image hinj]

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The automorphism of the unit group induced by a field automorphism.** -/
def unitsAut (g : L ≃ₐ[K] L) : Lˣ ≃* Lˣ := Units.mapEquiv g.toRingEquiv.toMulEquiv

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem coe_unitsAut (g : L ≃ₐ[K] L) (x : Lˣ) : ((unitsAut g x : Lˣ) : L) = g (x : L) := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Applying a successor power of a field automorphism means applying it last. -/
theorem algEquiv_pow_succ_apply (g : L ≃ₐ[K] L) (i : ℕ) (y : L) :
    (g ^ (i + 1)) y = g ((g ^ i) y) := by
  rw [pow_succ']
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Powers of the induced automorphism of the unit group are induced by powers. -/
theorem coe_unitsAut_pow (g : L ≃ₐ[K] L) (i : ℕ) (x : Lˣ) :
    ((((unitsAut g) ^ i) x : Lˣ) : L) = (g ^ i) (x : L) := by
  induction i with
  | zero => rfl
  | succ k ih => rw [mulPow_succ_apply, coe_unitsAut, ih, algEquiv_pow_succ_apply]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The induced automorphism of the unit group has order dividing the order of the Galois group. -/
theorem unitsAut_pow_card_eq_one (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    (unitsAut g) ^ (Nat.card (L ≃ₐ[K] L)) = 1 := by
  refine MulEquiv.ext fun x => Units.ext ?_
  rw [coe_unitsAut_pow, ← orderOf_eq_card_of_forall_mem_zpowers hg, pow_orderOf_eq_one]
  rfl

/-- **The product of the conjugates is the field norm.** -/
theorem coe_prod_range_unitsAut (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g)
    (x : Lˣ) :
    ((∏ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), ((unitsAut g) ^ i) x : Lˣ) : L)
      = algebraMap K L (Algebra.norm K (x : L)) := by
  have hval : ((∏ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), ((unitsAut g) ^ i) x : Lˣ) : L)
      = ∏ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), ((((unitsAut g) ^ i) x : Lˣ) : L) :=
    map_prod (Units.coeHom L) _ _
  rw [hval, Algebra.norm_eq_prod_automorphisms, ← prod_range_card_pow hg fun φ => φ (x : L)]
  exact Finset.prod_congr rfl fun i _ => coe_unitsAut_pow g i x

/-- **Hilbert's theorem 90 in Tate form.**  For a finite cyclic Galois extension the Tate group
`Ĥ⁻¹` of the unit group is trivial: an element whose conjugates multiply to one is a quotient
`g y / y`. -/
theorem tateHm1_unitsAut_eq_zero (g : L ≃ₐ[K] L)
    (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g)
    (c : tateHm1 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L))) : c = 0 := by
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨g, hg⟩⟩
  refine tateHm1_eq_zero (unitsAut g) _ (fun x hx => ?_) c
  have hnorm : Algebra.norm K (x : L) = 1 := by
    refine FaithfulSMul.algebraMap_injective K L ?_
    rw [← coe_prod_range_unitsAut g hg x, hx, Units.val_one, map_one]
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (K := K) (g := g) hg hnorm
  refine ⟨y⁻¹, Units.ext ?_⟩
  simp only [Units.val_div_eq_div_val, coe_unitsAut, Units.val_inv_eq_inv_val, map_inv₀,
    inv_div_inv]
  exact hy

/-- **A unit fixed by a generator lies in the base field.**  A generator fixes only what the whole
Galois group fixes, and for a Galois extension that is the base field. -/
theorem exists_algebraMap_of_unitsAut_eq (g : L ≃ₐ[K] L)
    (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) {x : Lˣ} (hx : unitsAut g x = x) :
    ∃ k : Kˣ, algebraMap K L (k : K) = (x : L) := by
  have hgx : g ∈ MulAction.stabilizer (L ≃ₐ[K] L) (x : L) := congrArg Units.val hx
  have hall : ∀ φ : L ≃ₐ[K] L, φ (x : L) = (x : L) := fun φ =>
    (Subgroup.zpowers_le.mpr hgx) (hg φ)
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x : L)).mpr hall
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hk, map_zero])
  exact ⟨Units.mk0 k hk0, hk⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- **A unit of the base field is trivial in `Ĥ⁰` of the unit group exactly when it is a norm.** -/
theorem tateH0_unitsAut_mk_eq_zero_iff (g : L ≃ₐ[K] L) (x : Lˣ)
    (hx : addAut (unitsAut g) (Additive.ofMul x) = Additive.ofMul x) :
    tateH0.mk (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L)) (Additive.ofMul x) hx = 0
      ↔ ∃ y : Lˣ, ∏ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), ((unitsAut g) ^ i) y = x :=
  tateH0_mk_eq_zero_iff (unitsAut g) _ x hx

end InverseGalois.CFT
