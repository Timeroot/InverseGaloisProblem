/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Herbrand

/-!
# The Tate groups of a module over a cyclic group

A module over a cyclic group of order dividing `n` is presented, as in
`InverseGalois.CFT.Herbrand`, by a single additive automorphism `σ` of an abelian group `M` with
`σ ^ n = 1`.  The two operators `x ↦ σ x - x` and `x ↦ ∑ i < n, σ ^ i x` form a two-periodic
complex, and its two cohomology groups are the Tate groups

`Ĥ⁰ = ker (σ - 1) / im N`  and  `Ĥ⁻¹ = ker N / im (σ - 1)`,

the fixed points modulo the norms and the norm-zero elements modulo the differences.  This file
names them, gives the interface for building and recognising their elements, and makes them
functorial: an equivariant homomorphism of modules induces homomorphisms of both Tate groups.

## Main definitions

* `InverseGalois.CFT.tateH0`, `InverseGalois.CFT.tateHm1`: the two Tate groups.
* `InverseGalois.CFT.tateH0.mk`, `InverseGalois.CFT.tateHm1.mk`: the classes of an element.
* `InverseGalois.CFT.tateH0.map`, `InverseGalois.CFT.tateHm1.map`: the induced homomorphisms.

## Main results

* `InverseGalois.CFT.tateH0.mk_surjective`, `InverseGalois.CFT.tateHm1.mk_surjective`: every
  element of a Tate group is the class of an element of the module.
* `InverseGalois.CFT.tateH0.mk_eq_zero_iff`: a fixed point has trivial class exactly when it is a
  norm.
* `InverseGalois.CFT.tateHm1.mk_eq_zero_iff`: an element of norm zero has trivial class exactly
  when it is a difference `σ y - y`.

## Tags

Tate cohomology, cyclic group, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-! ### Equivariant homomorphisms -/

section Equivariant

variable {σA : A ≃+ A} {σB : B ≃+ B}

/-- An equivariant homomorphism commutes with every power of the automorphism. -/
theorem map_pow_apply (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a)) (i : ℕ) (a : A) :
    f ((σA ^ i) a) = (σB ^ i) (f a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ_apply σA i a, hf, ih, ← pow_succ_apply σB i (f a)]

/-- An equivariant homomorphism commutes with the operator `x ↦ σ x - x`. -/
theorem map_sigmaSubOne (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a)) (a : A) :
    f (sigmaSubOne σA a) = sigmaSubOne σB (f a) := by
  rw [sigmaSubOne_apply, sigmaSubOne_apply, map_sub, hf]

/-- An equivariant homomorphism commutes with the norm operator. -/
theorem map_normHom (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a)) (n : ℕ) (a : A) :
    f (normHom σA n a) = normHom σB n (f a) := by
  rw [normHom_apply, normHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_pow_apply f hf i a

/-- An equivariant homomorphism carries fixed points to fixed points. -/
theorem mapsTo_ker_sigmaSubOne (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a))
    {a : A} (ha : a ∈ (sigmaSubOne σA).ker) : f a ∈ (sigmaSubOne σB).ker := by
  rw [AddMonoidHom.mem_ker, ← map_sigmaSubOne f hf, AddMonoidHom.mem_ker.mp ha, map_zero]

/-- An equivariant homomorphism carries elements of norm zero to elements of norm zero. -/
theorem mapsTo_ker_normHom (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a)) (n : ℕ)
    {a : A} (ha : a ∈ (normHom σA n).ker) : f a ∈ (normHom σB n).ker := by
  rw [AddMonoidHom.mem_ker, ← map_normHom f hf, AddMonoidHom.mem_ker.mp ha, map_zero]

/-- An equivariant homomorphism carries norms to norms. -/
theorem mapsTo_range_normHom (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a)) (n : ℕ)
    {a : A} (ha : a ∈ (normHom σA n).range) : f a ∈ (normHom σB n).range := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨f y, (map_normHom f hf n y).symm⟩

/-- An equivariant homomorphism carries differences to differences. -/
theorem mapsTo_range_sigmaSubOne (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a))
    {a : A} (ha : a ∈ (sigmaSubOne σA).range) : f a ∈ (sigmaSubOne σB).range := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨f y, (map_sigmaSubOne f hf y).symm⟩

end Equivariant

/-! ### The Tate groups -/

/-- The Tate group `Ĥ⁰`: the fixed points of `σ` modulo the image of the norm. -/
abbrev tateH0 (σ : A ≃+ A) (n : ℕ) : Type _ :=
  (sigmaSubOne σ).ker ⧸ (normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker

/-- The Tate group `Ĥ⁻¹`: the elements of norm zero modulo the differences `σ y - y`. -/
abbrev tateHm1 (σ : A ≃+ A) (n : ℕ) : Type _ :=
  (normHom σ n).ker ⧸ (sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker

namespace tateH0

variable {σ : A ≃+ A} {n : ℕ}

/-- The class in `Ĥ⁰` of a fixed point of `σ`. -/
def mk (σ : A ≃+ A) (n : ℕ) (x : A) (hx : σ x = x) : tateH0 σ n :=
  QuotientAddGroup.mk ⟨x, (mem_ker_sigmaSubOne_iff σ x).mpr hx⟩

/-- Every element of `Ĥ⁰` is the class of a fixed point. -/
theorem mk_surjective (c : tateH0 σ n) : ∃ (x : A) (hx : σ x = x), mk σ n x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact ⟨x, (mem_ker_sigmaSubOne_iff σ x).mp hx, rfl⟩

/-- The class of a fixed point vanishes exactly when the point is a norm. -/
theorem mk_eq_zero_iff (x : A) (hx : σ x = x) :
    mk σ n x hx = 0 ↔ ∃ y, normHom σ n y = x := by
  rw [mk, QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

/-- The class map is additive. -/
theorem mk_add (x y : A) (hx : σ x = x) (hy : σ y = y) :
    mk σ n (x + y) (by rw [map_add, hx, hy]) = mk σ n x hx + mk σ n y hy := rfl

/-- The class map turns subtraction into subtraction. -/
theorem mk_sub (x y : A) (hx : σ x = x) (hy : σ y = y) :
    mk σ n x hx - mk σ n y hy = mk σ n (x - y) (by rw [map_sub, hx, hy]) := rfl

/-- Two fixed points have the same class exactly when they differ by a norm. -/
theorem mk_eq_mk_iff (x y : A) (hx : σ x = x) (hy : σ y = y) :
    mk σ n x hx = mk σ n y hy ↔ ∃ z, normHom σ n z = x - y := by
  rw [← sub_eq_zero, mk_sub, mk_eq_zero_iff]

/-- The class of a norm vanishes. -/
theorem mk_normHom (y : A) (hσ : σ ^ n = 1) :
    mk σ n (normHom σ n y)
      ((mem_ker_sigmaSubOne_iff σ _).mp (range_normHom_le_ker_sigmaSubOne σ hσ ⟨y, rfl⟩)) = 0 :=
  (mk_eq_zero_iff _ _).mpr ⟨y, rfl⟩

end tateH0

namespace tateHm1

variable {σ : A ≃+ A} {n : ℕ}

/-- The class in `Ĥ⁻¹` of an element of norm zero. -/
def mk (σ : A ≃+ A) (n : ℕ) (x : A) (hx : normHom σ n x = 0) : tateHm1 σ n :=
  QuotientAddGroup.mk ⟨x, hx⟩

/-- Every element of `Ĥ⁻¹` is the class of an element of norm zero. -/
theorem mk_surjective (c : tateHm1 σ n) :
    ∃ (x : A) (hx : normHom σ n x = 0), mk σ n x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact ⟨x, hx, rfl⟩

/-- The class of an element of norm zero vanishes exactly when it is a difference `σ y - y`. -/
theorem mk_eq_zero_iff (x : A) (hx : normHom σ n x = 0) :
    mk σ n x hx = 0 ↔ ∃ y, σ y - y = x := by
  rw [mk, QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

/-- The class map is additive. -/
theorem mk_add (x y : A) (hx : normHom σ n x = 0) (hy : normHom σ n y = 0) :
    mk σ n (x + y) (by rw [map_add, hx, hy, add_zero]) = mk σ n x hx + mk σ n y hy := rfl

/-- The class map turns subtraction into subtraction. -/
theorem mk_sub (x y : A) (hx : normHom σ n x = 0) (hy : normHom σ n y = 0) :
    mk σ n x hx - mk σ n y hy = mk σ n (x - y) (by rw [map_sub, hx, hy, sub_zero]) := rfl

/-- Two elements of norm zero have the same class exactly when they differ by a difference. -/
theorem mk_eq_mk_iff (x y : A) (hx : normHom σ n x = 0) (hy : normHom σ n y = 0) :
    mk σ n x hx = mk σ n y hy ↔ ∃ z, σ z - z = x - y := by
  rw [← sub_eq_zero, mk_sub, mk_eq_zero_iff]

/-- The class of a difference vanishes. -/
theorem mk_sigmaSubOne (y : A) (hσ : σ ^ n = 1) :
    mk σ n (σ y - y)
      (AddMonoidHom.mem_ker.mp (range_sigmaSubOne_le_ker_normHom σ hσ ⟨y, rfl⟩)) = 0 :=
  (mk_eq_zero_iff _ _).mpr ⟨y, rfl⟩

end tateHm1

/-! ### Functoriality -/

section Functoriality

variable {σA : A ≃+ A} {σB : B ≃+ B} (n : ℕ) (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a))

/-- An equivariant homomorphism restricted to the fixed points. -/
def kerSigmaSubOneRestrict : (sigmaSubOne σA).ker →+ (sigmaSubOne σB).ker :=
  AddMonoidHom.codRestrict (f.comp (sigmaSubOne σA).ker.subtype) _
    fun x => mapsTo_ker_sigmaSubOne f hf x.2

/-- An equivariant homomorphism restricted to the elements of norm zero. -/
noncomputable def kerNormHomRestrict : (normHom σA n).ker →+ (normHom σB n).ker :=
  AddMonoidHom.codRestrict (f.comp (normHom σA n).ker.subtype) _
    fun x => mapsTo_ker_normHom f hf n x.2

/-- The homomorphism induced on `Ĥ⁰` by an equivariant homomorphism. -/
def tateH0.map : tateH0 σA n →+ tateH0 σB n :=
  QuotientAddGroup.map _ _ (kerSigmaSubOneRestrict f hf) <| by
    rintro ⟨x, hx⟩ hmem
    exact mapsTo_range_normHom f hf n hmem

/-- The homomorphism induced on `Ĥ⁻¹` by an equivariant homomorphism. -/
noncomputable def tateHm1.map : tateHm1 σA n →+ tateHm1 σB n :=
  QuotientAddGroup.map _ _ (kerNormHomRestrict n f hf) <| by
    rintro ⟨x, hx⟩ hmem
    exact mapsTo_range_sigmaSubOne f hf hmem

variable {n f hf}

/-- The induced map on `Ĥ⁰` sends the class of `x` to the class of `f x`. -/
@[simp]
theorem tateH0.map_mk (x : A) (hx : σA x = x) :
    tateH0.map n f hf (tateH0.mk σA n x hx) =
      tateH0.mk σB n (f x) (by rw [← hf, hx]) := rfl

/-- The induced map on `Ĥ⁻¹` sends the class of `x` to the class of `f x`. -/
@[simp]
theorem tateHm1.map_mk (x : A) (hx : normHom σA n x = 0) :
    tateHm1.map n f hf (tateHm1.mk σA n x hx) =
      tateHm1.mk σB n (f x) (by rw [← map_normHom f hf, hx, map_zero]) := rfl

end Functoriality

end InverseGalois.CFT
