/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.SUnit

/-!
# The orders of a unit at the primes outside a finite set

Fix a finite set of primes of a number field, stable under the Galois group.  Reading off the order
of an element at each of the remaining primes gives a homomorphism from the multiplicative group of
the field to the free abelian group on those primes, finitely supported because an element has a
zero or a pole at only finitely many places.  Its kernel is exactly the group of units for the
chosen set, and — as soon as the set is large enough to meet every ideal class — it is onto: every
prescribed system of orders away from the set is realised.

The primes outside a stable set carry the Galois action, so the free abelian group on them is a
permutation module and the homomorphism is equivariant.  This is the presentation of the units of a
number field as an extension of a permutation module by a finitely generated group, which is what
makes a cohomology class with coefficients in the units computable place by place.

## Main definitions

* `InverseGalois.CFT.IsGaloisStablePlaces`: a set of primes carried into itself by the Galois
  group.
* `InverseGalois.CFT.ordFinsupp`: **the finitely supported vector of orders at the primes outside
  the set.**

## Main results

* `InverseGalois.CFT.ordFinsupp_globalUnitsAut`: **the order vector is equivariant**, the Galois
  group acting on the primes outside the set by permutation.
* `InverseGalois.CFT.mem_ker_ordFinsupp`: **the kernel of the order vector is the group of units
  for the set.**
* `InverseGalois.CFT.ordFinsupp_surjective`: the order vector is onto when the set meets every
  ideal class.
* `InverseGalois.CFT.exists_finite_stable_ordFinsupp_surjective`: **such a set exists**, finite and
  stable under the Galois group.

## Tags

number field, height one prime, order, S-unit, permutation module, Galois action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### A set of primes stable under the Galois group -/

/-- **A set of primes carried into itself by every automorphism of the extension.** -/
class IsGaloisStablePlaces (k K : Type*) [Field k] [Field K] [Algebra k K] [NumberField K]
    (T : Set (HeightOneSpectrum (𝓞 K))) : Prop where
  /-- An automorphism carries a prime of the set to a prime of the set, and conversely. -/
  smul_mem_iff (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) : σ • v ∈ T ↔ v ∈ T

section Places

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (T : Set (HeightOneSpectrum (𝓞 K)))

/-- **The Galois action on the primes outside a stable set.** -/
instance mulActionOutsidePlaces [IsGaloisStablePlaces k K T] :
    MulAction Gal(K/k) {v : HeightOneSpectrum (𝓞 K) // v ∉ T} where
  smul σ y := ⟨σ • (y : HeightOneSpectrum (𝓞 K)),
    fun h => y.2 ((IsGaloisStablePlaces.smul_mem_iff (k := k) σ (y : _)).1 h)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

@[simp]
theorem coe_smul_outsidePlaces [IsGaloisStablePlaces k K T] (σ : Gal(K/k))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ((σ • y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) : HeightOneSpectrum (𝓞 K))
      = σ • (y : HeightOneSpectrum (𝓞 K)) := rfl

/-! ### The vector of orders outside the set -/

/-- An element has a zero or a pole at only finitely many of the primes outside the set. -/
theorem finite_support_ord (x : K) :
    (Function.support fun y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ord K (y : HeightOneSpectrum (𝓞 K)) x).Finite :=
  Set.Finite.preimage (f := fun y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      (y : HeightOneSpectrum (𝓞 K))) Subtype.val_injective.injOn
    (Filter.eventually_cofinite.1 (ord_finite (R := 𝓞 K) (K := K) x))

/-- **The finitely supported vector of orders at the primes outside the set.** -/
noncomputable def ordFinsupp :
    Additive Kˣ →+ ({v : HeightOneSpectrum (𝓞 K) // v ∉ T} →₀ ℤ) where
  toFun u := Finsupp.ofSupportFinite
    (fun y => ord K (y : HeightOneSpectrum (𝓞 K)) ((u.toMul : Kˣ) : K)) (finite_support_ord T _)
  map_zero' := by
    refine Finsupp.ext fun y => ?_
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    show ord K (y : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  map_add' u w := by
    refine Finsupp.ext fun y => ?_
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_add, Pi.add_apply]
    show ord K (y : HeightOneSpectrum (𝓞 K)) (((u.toMul * w.toMul : Kˣ) : K)) = _
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _)]

@[simp]
theorem ordFinsupp_apply (u : Additive Kˣ) (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ordFinsupp T u y = ord K (y : HeightOneSpectrum (𝓞 K)) ((u.toMul : Kˣ) : K) := rfl

/-- **The order vector is equivariant**: an automorphism moves the orders of an element along the
permutation it induces on the primes outside the set. -/
theorem ordFinsupp_globalUnitsAut [IsGaloisStablePlaces k K T] (σ : Gal(K/k)) (u : Additive Kˣ)
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ordFinsupp T (globalUnitsAut σ u) y = ordFinsupp T u (σ⁻¹ • y) := by
  rw [ordFinsupp_apply, ordFinsupp_apply, coe_globalUnitsAut_apply, coe_smul_outsidePlaces]
  have h := ord_galSmul σ (σ⁻¹ • (y : HeightOneSpectrum (𝓞 K))) ((u.toMul : Kˣ) : K)
  rwa [smul_inv_smul] at h

/-- **The kernel of the order vector is the group of units for the set.** -/
theorem mem_ker_ordFinsupp {u : Additive Kˣ} :
    u ∈ (ordFinsupp T).ker ↔ (u.toMul : Kˣ) ∈ sUnits K T := by
  rw [AddMonoidHom.mem_ker]
  refine ⟨fun h => mem_sUnits.2 fun v hv => ?_, fun h => Finsupp.ext fun y => ?_⟩
  · have h2 := congrArg (fun z : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} →₀ ℤ => z ⟨v, hv⟩) h
    simpa using h2
  · simpa using mem_sUnits.1 h (y : HeightOneSpectrum (𝓞 K)) y.2

/-- The order vector is onto when every prescribed system of orders away from the set is realised
by an element of the field. -/
theorem ordFinsupp_surjective
    (hrepr : ∀ n : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0) →
      ∃ a : Kˣ, ∀ v ∉ T, ord K v ((a : Kˣ) : K) = n v) :
    Function.Surjective (ordFinsupp T) := by
  classical
  intro b
  refine ?_
  set n : HeightOneSpectrum (𝓞 K) → ℤ := fun v => if h : v ∈ T then 0 else b ⟨v, h⟩ with hn
  have hcof : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0 := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (b.finite_support.image
      fun y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => (y : HeightOneSpectrum (𝓞 K))) ?_
    intro v hv
    have hvT : v ∉ T := by
      intro hvT
      exact hv (by rw [hn]; simp [hvT])
    refine ⟨⟨v, hvT⟩, ?_, rfl⟩
    have : n v = b ⟨v, hvT⟩ := by rw [hn]; simp [hvT]
    exact fun hb => hv (by rw [this, hb])
  obtain ⟨a, ha⟩ := hrepr n hcof
  refine ⟨Additive.ofMul a, Finsupp.ext fun y => ?_⟩
  rw [ordFinsupp_apply]
  have hy := ha (y : HeightOneSpectrum (𝓞 K)) y.2
  rw [show ((Additive.ofMul a).toMul : Kˣ) = a from rfl, hy, hn]
  simp [y.2]

end Places

/-! ### A stable set for which the order vector is onto -/

section Stable

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]

/-- **There is a finite set of primes, stable under the Galois group, for which the vector of
orders at the remaining primes is onto.**  Take the set attached to the ideal classes and replace
it by the union of its translates. -/
theorem exists_finite_stable_ordFinsupp_surjective :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ IsGaloisStablePlaces k K T ∧
      Function.Surjective (ordFinsupp T) := by
  obtain ⟨T, hTfin, hTstab, hTrepr⟩ := exists_finite_stable_ord_repr (k := k) (K := K)
  exact ⟨T, hTfin, ⟨hTstab⟩, ordFinsupp_surjective T hTrepr⟩

end Stable

end InverseGalois.CFT
