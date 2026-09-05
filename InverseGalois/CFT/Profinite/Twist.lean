/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Pi

/-!
# Twisting a class with cyclic coefficients by a finite module

Kummer theory describes the first cohomology of a Galois group with coefficients in a group `M` of
roots of unity: the classes are the elements of a group `A` — for a field, its multiplicative
group — taken modulo the subgroup of `p`-th powers.  The coefficients that occur in a lifting
problem are not `M` itself but a finite module `E` killed by `p`, on which the Galois group of the
base field acts; and such an `E`, as an abstract group, is a product of finitely many copies of `M`.

A homomorphism `w : M →* E` carries a class with coefficients in `M` to one with coefficients in
`E`, and the class so obtained is multiplicative both in the element of `A` and in `w`.  So the
construction is a map out of the tensor product of `A` with the group of homomorphisms `M →* E`,
both written additively, and **that map is an isomorphism onto the first cohomology with
coefficients in `E`**.

The proof is a coordinate computation, and needs nothing of the group or of the field.  Choose an
isomorphism of `E` with a product of copies of `M`; the first cohomology of a finite product is the
product of the first cohomologies, so a class with coefficients in `E` becomes a family of classes
with coefficients in `M`, one for each factor.  Each member of the family comes from an element of
`A`, well defined up to a `p`-th power — and a `p`-th power dies in the tensor product, because the
group of homomorphisms `M →* E` is killed by `p`.  This builds a candidate inverse.  That it is an
inverse on one side is the observation that the coordinates of the class attached to `a` and to the
inclusion of the `i`-th factor are the class of `a` in the `i`-th place and trivial elsewhere; on
the other side it is the observation that an endomorphism of a cyclic group is a power map, so each
coordinate of the class attached to `a` and to `w` is a power of the class of `a`, and those powers
reassemble `w`.

## Main definitions

* `InverseGalois.CFT.twistClass`: the class with coefficients in `E` obtained from an element of
  `A` and a homomorphism `M →* E`.
* `InverseGalois.CFT.twistMap`: the map it induces out of the tensor product.
* `InverseGalois.CFT.twistCoord`: the coordinates of a class with coefficients in `E`.

## Main results

* `InverseGalois.CFT.exists_zpow_of_isCyclic`: an endomorphism of a cyclic group is a power map.
* `InverseGalois.CFT.twistMap_bijective`, `InverseGalois.CFT.twistEquiv`: **the first cohomology
  with coefficients in a finite product of copies of a cyclic group is the tensor product of the
  first cohomology with cyclic coefficients and the group of homomorphisms of the coefficients.**

## Tags

Galois cohomology, Kummer theory, tensor product, cyclic group, twist
-/

namespace InverseGalois.CFT

open groupCohomology TensorProduct

/-! ### Endomorphisms of a cyclic group -/

section Cyclic

variable {M : Type*} [CommGroup M]

/-- **An endomorphism of a cyclic group is a power map.** -/
theorem exists_zpow_of_isCyclic [IsCyclic M] (c : M →* M) : ∃ n : ℤ, ∀ m : M, c m = m ^ n := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := M)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hζ (c ζ))
  refine ⟨n, fun m => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hζ m)
  rw [← hk, map_zpow, ← hn, ← zpow_mul, ← zpow_mul, mul_comm]

end Cyclic

/-! ### Homomorphisms between trivially acted on coefficients -/

section Trivial

variable {G : Type*} [Group G] {M N : Type*} [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N]
variable (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivN : ∀ (g : G) (n : N), g • n = n)

include htrivM htrivN in
/-- A homomorphism between trivially acted on coefficient groups is equivariant. -/
theorem smul_eq_of_trivial (w : M →* N) (g : G) (m : M) : w (g • m) = g • w m := by
  rw [htrivM, htrivN]

include htrivM in
/-- A product of trivially acted on coefficient groups is trivially acted on. -/
theorem smul_pi_eq_of_trivial {ι : Type*} (g : G) (x : ι → M) : g • x = x :=
  funext fun i => htrivM g (x i)

end Trivial

/-! ### A `p`-th power dies in the tensor product -/

section Torsion

variable {M E A : Type*} [CommGroup M] [CommGroup E] [CommGroup A] {p : ℕ}

/-- **The tensor product of a group with a group of homomorphisms killed by `p` kills `p`-th
powers.** -/
theorem tmul_pow_eq_zero (hEp : ∀ e : E, e ^ p = 1) (b : A) (w : M →* E) :
    (Additive.ofMul (b ^ p) ⊗ₜ[ℤ] Additive.ofMul w
      : Additive A ⊗[ℤ] Additive (M →* E)) = 0 := by
  have hw : (w ^ (p : ℤ) : M →* E) = 1 :=
    MonoidHom.ext fun m => by rw [MonoidHom.zpow_apply, zpow_natCast, hEp]; rfl
  have h0 : ((p : ℤ) • Additive.ofMul w : Additive (M →* E)) = 0 := by
    rw [← ofMul_zpow, hw]; rfl
  have hb : Additive.ofMul (b ^ p) = ((p : ℤ) • Additive.ofMul b : Additive A) := by
    rw [← zpow_natCast, ofMul_zpow]
  rw [hb, TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]

end Torsion

/-! ### The twisting map -/

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M E A : Type*} [CommGroup M] [CommGroup E] [CommGroup A]
variable [MulDistribMulAction G M] [MulDistribMulAction G E]
variable (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivE : ∀ (g : G) (e : E), g • e = e)
variable (κ : A →* SmoothH1 G M) {p : ℕ}

/-- **The class with coefficients in `E` attached to an element of `A` and a homomorphism of the
coefficients.** -/
def twistClass (a : A) (w : M →* E) : SmoothH1 G E :=
  coeffH1 w (smul_eq_of_trivial htrivM htrivE w) (κ a)

theorem twistClass_mul_left (a b : A) (w : M →* E) :
    twistClass htrivM htrivE κ (a * b) w
      = twistClass htrivM htrivE κ a w * twistClass htrivM htrivE κ b w := by
  simp only [twistClass, map_mul]

theorem twistClass_mul_right (a : A) (w v : M →* E) :
    twistClass htrivM htrivE κ a (w * v)
      = twistClass htrivM htrivE κ a w * twistClass htrivM htrivE κ a v :=
  coeffH1_mul w v _ _ _ (κ a)

theorem twistClass_one_left (w : M →* E) : twistClass htrivM htrivE κ 1 w = 1 := by
  simp only [twistClass, map_one]

theorem twistClass_one_right (a : A) : twistClass htrivM htrivE κ a 1 = 1 :=
  coeffH1_one _ (κ a)

/-- The twisting construction, additive in each of its two variables. -/
def twistAddHom : Additive A →+ Additive (M →* E) →+ Additive (SmoothH1 G E) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun w => Additive.ofMul (twistClass htrivM htrivE κ a.toMul w.toMul))
      (fun w v => by exact twistClass_mul_right htrivM htrivE κ _ _ _))
    (fun a b => AddMonoidHom.ext fun w => by
      exact twistClass_mul_left htrivM htrivE κ _ _ _)

/-- **The twisting map out of the tensor product.** -/
def twistMap : Additive A ⊗[ℤ] Additive (M →* E) →+ Additive (SmoothH1 G E) :=
  TensorProduct.liftAddHom (twistAddHom htrivM htrivE κ) fun r a w => by
    rw [map_zsmul (twistAddHom htrivM htrivE κ) r a,
      map_zsmul (twistAddHom htrivM htrivE κ a) r w]
    rfl

@[simp]
theorem twistMap_tmul (a : A) (w : M →* E) :
    twistMap htrivM htrivE κ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul (twistClass htrivM htrivE κ a w) := rfl

omit [MulDistribMulAction G E] in
/-- Two elements of `A` with the same class give the same element of the tensor product, because
they differ by a `p`-th power. -/
theorem tmul_eq_of_map_eq (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) {a b : A} (h : κ a = κ b) (w : M →* E) :
    (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w : Additive A ⊗[ℤ] Additive (M →* E))
      = Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul w := by
  obtain ⟨c, hc⟩ := hker (show a * b⁻¹ ∈ κ.ker by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel])
  have hc' : c ^ p = a * b⁻¹ := hc
  have hab : a = b * c ^ p := by
    rw [hc', mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hab, ofMul_mul, TensorProduct.add_tmul, tmul_pow_eq_zero hEp c w, add_zero]

/-! ### Coordinates -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (α : E ≃* (ι → M))

omit [Fintype ι] [DecidableEq ι] in
/-- The `i`-th coordinate of the chosen decomposition of `E`, as a map of the coefficients. -/
def twistProj (i : ι) : E →* M :=
  (Pi.evalMonoidHom (fun _ : ι => M) i).comp (α : E →* (ι → M))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem twistProj_apply (i : ι) (e : E) : twistProj α i e = α e i := rfl

omit [Fintype ι] in
/-- The inclusion of the cyclic group as the `i`-th factor of `E`. -/
def twistIncl (i : ι) : M →* E :=
  (α.symm : (ι → M) →* E).comp (MonoidHom.mulSingle (fun _ : ι => M) i)

omit [Fintype ι] in
@[simp]
theorem twistIncl_apply (i : ι) (m : M) : twistIncl α i m = α.symm (Pi.mulSingle i m) := rfl

/-- **The coordinates of a class with coefficients in `E`**, one for each factor of the chosen
decomposition of `E` into copies of the cyclic group. -/
noncomputable def twistCoord : SmoothH1 G E ≃* (ι → SmoothH1 G M) :=
  (coeffH1Equiv α (fun g e => by
      rw [htrivE, smul_pi_eq_of_trivial htrivM g (α e)])).trans
    (smoothH1PiEquiv G fun _ : ι => M)

omit [DecidableEq ι] in
theorem twistCoord_apply (f : SmoothH1 G E) (i : ι) :
    twistCoord htrivM htrivE α f i
      = coeffH1 (twistProj α i) (smul_eq_of_trivial htrivE htrivM (twistProj α i)) f :=
  coeffH1_comp _ _ _ _ _ f

omit [DecidableEq ι] in
/-- The `i`-th coordinate of a twisted class is a power of the class one started from, the exponent
being the one which describes the `i`-th coordinate of the twisting homomorphism. -/
theorem twistCoord_twistClass (a : A) (w : M →* E) (i : ι) (n : ℤ)
    (hn : ∀ m : M, α (w m) i = m ^ n) :
    twistCoord htrivM htrivE α (twistClass htrivM htrivE κ a w) i = κ a ^ n := by
  rw [twistCoord_apply, twistClass,
    coeffH1_comp w (smul_eq_of_trivial htrivM htrivE w) (twistProj α i)
      (smul_eq_of_trivial htrivE htrivM (twistProj α i))
      (smul_eq_of_trivial htrivM htrivM ((twistProj α i).comp w)) (κ a)]
  exact coeffH1_zpow htrivM n _ hn _ (κ a)

/-- The coordinates of the class attached to an element of `A` and to the inclusion of the `i`-th
factor: the class of that element in the `i`-th place, and trivial elsewhere. -/
theorem twistCoord_twistClass_incl (a : A) (i j : ι) :
    twistCoord htrivM htrivE α (twistClass htrivM htrivE κ a (twistIncl α i)) j
      = if j = i then κ a else 1 := by
  by_cases h : j = i
  · subst h
    rw [twistCoord_twistClass htrivM htrivE κ α a (twistIncl α j) j 1 (fun m => by
      rw [twistIncl_apply, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, zpow_one]),
      if_pos rfl, zpow_one]
  · rw [twistCoord_twistClass htrivM htrivE κ α a (twistIncl α i) j 0 (fun m => by
      rw [twistIncl_apply, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne h, zpow_zero]),
      if_neg h, zpow_zero]

/-! ### The inverse -/

variable (hsurj : Function.Surjective κ)

include hsurj

/-- A chosen element of `A` whose class is a given one. -/
noncomputable def twistSec (y : SmoothH1 G M) : A := (hsurj y).choose

@[simp]
theorem twistSec_spec (y : SmoothH1 G M) : κ (twistSec κ hsurj y) = y := (hsurj y).choose_spec

/-- The element of the tensor product assembled from the coordinates of a class. -/
noncomputable def twistInv (f : SmoothH1 G E) : Additive A ⊗[ℤ] Additive (M →* E) :=
  ∑ i : ι, Additive.ofMul (twistSec κ hsurj (twistCoord htrivM htrivE α f i)) ⊗ₜ[ℤ]
    Additive.ofMul (twistIncl α i)

theorem twistInv_mul (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) (f f' : SmoothH1 G E) :
    twistInv htrivM htrivE κ α hsurj (f * f')
      = twistInv htrivM htrivE κ α hsurj f + twistInv htrivM htrivE κ α hsurj f' := by
  rw [twistInv, twistInv, twistInv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← TensorProduct.add_tmul, ← ofMul_mul]
  refine tmul_eq_of_map_eq κ hEp hker ?_ _
  simp only [map_mul, twistSec_spec, Pi.mul_apply]

/-- The candidate inverse of the twisting map. -/
noncomputable def twistInvHom (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) :
    Additive (SmoothH1 G E) →+ Additive A ⊗[ℤ] Additive (M →* E) :=
  AddMonoidHom.mk' (fun f => twistInv htrivM htrivE κ α hsurj f.toMul)
    (fun f f' => twistInv_mul htrivM htrivE κ α hsurj hEp hker f.toMul f'.toMul)

@[simp]
theorem twistInvHom_apply (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) (f : SmoothH1 G E) :
    twistInvHom htrivM htrivE κ α hsurj hEp hker (Additive.ofMul f)
      = twistInv htrivM htrivE κ α hsurj f := rfl

/-- **The candidate inverse is a right inverse.** -/
theorem twistMap_twistInv (f : SmoothH1 G E) :
    twistMap htrivM htrivE κ (twistInv htrivM htrivE κ α hsurj f) = Additive.ofMul f := by
  have key : ∏ i : ι, twistClass htrivM htrivE κ
      (twistSec κ hsurj (twistCoord htrivM htrivE α f i)) (twistIncl α i) = f := by
    refine (twistCoord htrivM htrivE α).injective (funext fun j => ?_)
    have hterm : ∀ i : ι, twistCoord htrivM htrivE α (twistClass htrivM htrivE κ
        (twistSec κ hsurj (twistCoord htrivM htrivE α f i)) (twistIncl α i)) j
        = if j = i then twistCoord htrivM htrivE α f i else 1 := by
      intro i
      rw [twistCoord_twistClass_incl]
      by_cases h : j = i
      · rw [if_pos h, if_pos h, twistSec_spec]
      · rw [if_neg h, if_neg h]
    rw [map_prod, Finset.prod_apply]
    rw [Finset.prod_eq_single j]
    · rw [hterm j, if_pos rfl]
    · intro i _ hij
      rw [hterm i, if_neg (Ne.symm hij)]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [twistInv, map_sum]
  simp only [twistMap_tmul]
  rw [← ofMul_prod, key]

/-- **The candidate inverse undoes the twisting construction on a pure tensor.** -/
theorem twistInv_twistClass [IsCyclic M] (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) (a : A) (w : M →* E) :
    twistInv htrivM htrivE κ α hsurj (twistClass htrivM htrivE κ a w)
      = Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w := by
  obtain ⟨n, hn⟩ : ∃ n : ι → ℤ, ∀ (i : ι) (m : M), α (w m) i = m ^ n i := by
    have h : ∀ i : ι, ∃ nn : ℤ, ∀ m : M, α (w m) i = m ^ nn := fun i =>
      exists_zpow_of_isCyclic ((twistProj α i).comp w)
    choose n hn using h
    exact ⟨n, hn⟩
  have hD : ∀ i : ι,
      twistCoord htrivM htrivE α (twistClass htrivM htrivE κ a w) i = κ a ^ n i :=
    fun i => twistCoord_twistClass htrivM htrivE κ α a w i (n i) (hn i)
  have hterm : ∀ i : ι,
      (Additive.ofMul (twistSec κ hsurj (twistCoord htrivM htrivE α
          (twistClass htrivM htrivE κ a w) i)) ⊗ₜ[ℤ] Additive.ofMul (twistIncl α i)
        : Additive A ⊗[ℤ] Additive (M →* E))
        = Additive.ofMul a ⊗ₜ[ℤ] (n i • Additive.ofMul (twistIncl α i)) := by
    intro i
    rw [tmul_eq_of_map_eq κ hEp hker (w := twistIncl α i) (b := a ^ n i)
      (by rw [twistSec_spec, hD i, map_zpow]), ofMul_zpow, TensorProduct.smul_tmul]
  have hprod : (∏ i : ι, twistIncl α i ^ n i) = w := by
    refine MonoidHom.ext fun m => ?_
    have h1 : ∀ i : ι, (twistIncl α i ^ n i) m = α.symm (Pi.mulSingle i (m ^ n i)) := by
      intro i
      rw [MonoidHom.zpow_apply, twistIncl_apply, ← map_zpow, Pi.mulSingle_zpow]
    rw [MonoidHom.finset_prod_apply]
    simp only [h1]
    rw [← map_prod, Finset.univ_prod_mulSingle,
      show (fun i => m ^ n i) = α (w m) from funext fun i => (hn i m).symm,
      MulEquiv.symm_apply_apply]
  have hsum : ∑ i : ι, n i • Additive.ofMul (twistIncl α i)
      = ∑ i : ι, Additive.ofMul (twistIncl α i ^ n i) :=
    Finset.sum_congr rfl fun i _ => (ofMul_zpow (n i) (twistIncl α i)).symm
  rw [twistInv]
  simp only [hterm]
  rw [← TensorProduct.tmul_sum, hsum, ← ofMul_prod, hprod]

/-- **The candidate inverse is a left inverse.** -/
theorem twistInv_twistMap [IsCyclic M] (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range)
    (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    twistInvHom htrivM htrivE κ α hsurj hEp hker (twistMap htrivM htrivE κ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  | tmul x y =>
    exact twistInv_twistClass htrivM htrivE κ α hsurj hEp hker x.toMul y.toMul

include α in
/-- **The twisting map is bijective.** -/
theorem twistMap_bijective [IsCyclic M] (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) :
    Function.Bijective (twistMap htrivM htrivE κ : Additive A ⊗[ℤ] Additive (M →* E) →
      Additive (SmoothH1 G E)) := by
  constructor
  · intro z z' h
    rw [← twistInv_twistMap htrivM htrivE κ α hsurj hEp hker z,
      ← twistInv_twistMap htrivM htrivE κ α hsurj hEp hker z', h]
  · intro f
    exact ⟨twistInv htrivM htrivE κ α hsurj f.toMul, twistMap_twistInv htrivM htrivE κ α hsurj _⟩

/-- **The first cohomology with coefficients in a finite product of copies of a cyclic group is
the tensor product of the first cohomology with cyclic coefficients and the group of homomorphisms
of the coefficients.** -/
noncomputable def twistEquiv [IsCyclic M] (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) :
    Additive A ⊗[ℤ] Additive (M →* E) ≃+ Additive (SmoothH1 G E) :=
  AddEquiv.ofBijective (twistMap htrivM htrivE κ)
    (twistMap_bijective htrivM htrivE κ α hsurj hEp hker)

@[simp]
theorem twistEquiv_tmul [IsCyclic M] (hEp : ∀ e : E, e ^ p = 1)
    (hker : κ.ker ≤ (powMonoidHom p : A →* A).range) (a : A) (w : M →* E) :
    twistEquiv htrivM htrivE κ α hsurj hEp hker (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul (twistClass htrivM htrivE κ a w) := rfl

end Twist

end InverseGalois.CFT
