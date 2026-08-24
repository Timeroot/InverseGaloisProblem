/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.Denominator
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Radical extensions are unramified away from the exponent and the radicands

Adjoining `p`-th roots of elements of a number field containing the `p`-th roots of unity produces
an extension which is ramified only at the places dividing `p` and at the places where one of the
radicands fails to be a unit.  This is what makes Kummer theory usable in the algebraic proof of
the second inequality of class field theory: the finite set of bad places can be read off from the
radicands, and everywhere else the local extension is unramified, so local units are norms.

The argument is with the inertia group.  Let `w` be a place of the top field lying over a place at
which all the radicands are units, and let `σ` be in the inertia group at `w`.  A radical `α` need
not be an algebraic integer, but its radicand can be scaled into the ring of integers by a factor
which is a unit at the place below, and the scaled radical `β` is then an algebraic integer which
is a unit at `w`.  Since `σ` fixes the radicand, it multiplies `β` by a `p`-th root of unity, so
the difference `σ β - β` is `β` times `ζ ^ j - 1`, and that difference lies in `w`.  As `β` is a
unit at `w`, the factor `ζ ^ j - 1` lies in `w`; but it divides `p`, which does not lie in `w`
unless `j` is zero.  So `σ` fixes every radical, and the radicals generate.

## Main results

* `InverseGalois.CFT.sub_one_dvd_natCast_of_isPrimitiveRoot`: a primitive `p`-th root of unity is
  congruent to one modulo `p`.
* `InverseGalois.CFT.eq_of_mem_inertia_of_radical`: an element of the inertia group fixes a radical
  whose radicand is a unit below.
* `InverseGalois.CFT.isUnramifiedAt_of_radicals`: **a radical extension is unramified at every
  place away from the exponent at which all the radicands are units.**

## Tags

number field, Kummer theory, radical, inertia, unramified, root of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section Dvd

/-- **A primitive `p`-th root of unity is congruent to one modulo `p`**: the sum of the powers of
the root vanishes, so `p` is the sum of the differences `1 - ξ ^ i`, each of which is divisible by
`1 - ξ`. -/
theorem sub_one_dvd_natCast_of_isPrimitiveRoot {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (hp : 1 < p) {ξ : R} (hξ : IsPrimitiveRoot ξ p) : ξ - 1 ∣ (p : R) := by
  have hsum : ∑ i ∈ Finset.range p, ξ ^ i = 0 := hξ.geom_sum_eq_zero hp
  have hcast : (p : R) = ∑ i ∈ Finset.range p, ((1 : R) - ξ ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
  have hdvd : (1 : R) - ξ ∣ (p : R) := by
    rw [hcast]
    refine Finset.dvd_sum fun i _ => ?_
    simpa using sub_dvd_pow_sub_pow (1 : R) ξ i
  rw [show ξ - 1 = -((1 : R) - ξ) by ring]
  exact neg_dvd.mpr hdvd

end Dvd

section Radical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {p : ℕ}

omit [IsGalois K L] in
/-- **An element of the inertia group at a place away from the exponent fixes every radical whose
radicand is a unit at the place below.**  The automorphism scales the radical by a `p`-th root of
unity, and the difference lies in the place; scaling the radical into the ring of integers by a
factor which is a unit below keeps it a unit at the place, so the root of unity is congruent to one
there, and a nontrivial one is not. -/
theorem eq_of_mem_inertia_of_radical (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {w : HeightOneSpectrum (𝓞 L)} (hpw : (p : 𝓞 L) ∉ w.asIdeal)
    {σ : Gal(L/K)} (hσ : σ ∈ Ideal.inertia Gal(L/K) w.asIdeal)
    {α : L} {a : K} (hav : (primeUnder (𝓞 K) w).valuation K a = 1)
    (hpow : α ^ p = algebraMap K L a) : σ α = α := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set v : HeightOneSpectrum (𝓞 K) := primeUnder (𝓞 K) w with hv
  obtain ⟨t, htv, c, htc⟩ := exists_notMem_smul_mem v (le_of_eq hav)
  have hane : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hav
    exact zero_ne_one hav
  have haL : algebraMap K L a ≠ 0 := fun h => hane ((map_eq_zero _).mp h)
  have hαne : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hpow
    exact haL hpow.symm
  -- the radicand becomes integral after scaling by an element which is a unit at the place
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 K, algebraMap (𝓞 K) K t ^ p * a = algebraMap (𝓞 K) K y := by
    refine ⟨t ^ (p - 1) * c, ?_⟩
    have hpe : algebraMap (𝓞 K) K t ^ p
        = algebraMap (𝓞 K) K t ^ (p - 1) * algebraMap (𝓞 K) K t := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
    rw [map_mul, map_pow, ← htc, ← mul_assoc, hpe]
  set β : L := algebraMap K L (algebraMap (𝓞 K) K t) * α with hβdef
  have hβpow : β ^ p = algebraMap K L (algebraMap (𝓞 K) K y) := by
    rw [hβdef, mul_pow, ← map_pow, hpow, ← map_mul, hy]
  have hint : IsIntegral (𝓞 K) β := by
    refine ⟨Polynomial.X ^ p - Polynomial.C y, Polynomial.monic_X_pow_sub_C y hp.ne_zero, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    rw [hβpow, ← IsScalarTower.algebraMap_apply, sub_self]
  obtain ⟨β₀, hβ₀⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 L) |>.mp hint
  -- the scaled radical is a unit at the place
  have hteq : v.valuation K (algebraMap (𝓞 K) K t) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (HeightOneSpectrum.intValuation_le_one v t) (not_lt.mp ?_)
    exact fun h => htv ((HeightOneSpectrum.intValuation_lt_one_iff_mem v t).mp h)
  have hyv : y ∉ v.asIdeal := by
    have heq : v.valuation K (algebraMap (𝓞 K) K y) = 1 := by
      rw [← hy, map_mul, map_pow, hteq, hav, one_pow, one_mul]
    rw [HeightOneSpectrum.valuation_of_algebraMap] at heq
    exact fun hc => absurd heq ((HeightOneSpectrum.intValuation_lt_one_iff_mem v y).mpr hc).ne
  have hpow' : β₀ ^ p = algebraMap (𝓞 K) (𝓞 L) y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hβ₀, hβpow, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hβ₀w : β₀ ∉ w.asIdeal := by
    intro hmem
    have hmemy : algebraMap (𝓞 K) (𝓞 L) y ∈ w.asIdeal := by
      rw [← hpow']
      exact Ideal.pow_mem_of_mem _ hmem _ (Nat.pos_of_ne_zero hp.ne_zero)
    exact hyv hmemy
  -- the automorphism scales the radical by a root of unity
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p := hζ.map_of_injective (algebraMap K L).injective
  have hone : (σ α / α) ^ p = 1 := by
    rw [div_pow, ← map_pow, hpow, AlgEquiv.commutes, div_self haL]
  obtain ⟨j, hjlt, hj⟩ := hζL.eq_pow_of_pow_eq_one hone
  have hσα : σ α = algebraMap K L ζ ^ j * α := by rw [hj, div_mul_cancel₀ _ hαne]
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hσα)
  have hζint : IsIntegral ℤ (algebraMap K L ζ) := hζL.isIntegral (Nat.pos_of_ne_zero hp.ne_zero)
  set ζ₀ : 𝓞 L := ⟨algebraMap K L ζ, hζint⟩ with hζ₀
  have hζ₀prim : IsPrimitiveRoot ζ₀ p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζL
      (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  have hcop : Nat.Coprime j p :=
    (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (Nat.pos_of_ne_zero hj0) hjlt)))
  have hdvd : ζ₀ ^ j - 1 ∣ (p : 𝓞 L) :=
    sub_one_dvd_natCast_of_isPrimitiveRoot hp.one_lt (hζ₀prim.pow_of_coprime j hcop)
  -- the difference of the radical and its image is the radical times a nonunit
  have hσβ : σ β = algebraMap K L ζ ^ j * β := by
    rw [hβdef, map_mul, AlgEquiv.commutes, hσα]
    ring
  have hsmul : σ • β₀ - β₀ = (ζ₀ ^ j - 1) * β₀ := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_sub, map_mul, map_sub, map_pow, map_one]
    show σ (algebraMap (𝓞 L) L β₀) - _ = (algebraMap K L ζ ^ j - 1) * _
    rw [hβ₀, hσβ]
    ring
  have hmem : σ • β₀ - β₀ ∈ w.asIdeal := AddSubgroup.mem_inertia.mp hσ β₀
  rw [hsmul] at hmem
  have hfac : ζ₀ ^ j - 1 ∈ w.asIdeal :=
    (w.isPrime.mul_mem_iff_mem_or_mem.mp hmem).resolve_right hβ₀w
  obtain ⟨z, hz⟩ := hdvd
  exact hpw (by rw [hz]; exact Ideal.mul_mem_right _ _ hfac)

omit [IsGalois K L] in
/-- The inertia group of a radical extension is trivial at a place away from the exponent at which
all the radicands are units. -/
theorem inertia_eq_bot_of_radicals (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {ι : Type*}
    {α : ι → L} {a : ι → K} (hpow : ∀ i, α i ^ p = algebraMap K L (a i))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤)
    {w : HeightOneSpectrum (𝓞 L)} (hpw : (p : 𝓞 L) ∉ w.asIdeal)
    (hav : ∀ i, (primeUnder (𝓞 K) w).valuation K (a i) = 1) :
    Ideal.inertia Gal(L/K) w.asIdeal = ⊥ := by
  refine Subgroup.eq_bot_iff_forall _ |>.mpr fun σ hσ => ?_
  have hzs : ∀ i, Subgroup.zpowers σ ≤ stabilizer Gal(L/K) (α i) := fun i => by
    rw [Subgroup.zpowers_le]
    exact eq_of_mem_inertia_of_radical hp hζ hpw hσ (hav i) (hpow i)
  have hle : Subgroup.zpowers σ ≤ (⊤ : IntermediateField K L).fixingSubgroup := by
    rw [← IntermediateField.le_iff_le, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact fun τ => hzs i τ.2
  refine AlgEquiv.ext fun x => ?_
  exact hle (Subgroup.mem_zpowers σ) ⟨x, IntermediateField.mem_top⟩

/-- **A radical extension of number fields is unramified at every place away from the exponent at
which all the radicands are units.**  An element of the inertia group multiplies each radical by a
root of unity, and that root of unity is congruent to one at the place, since the exponent is; but
the radicals generate, so the element is the identity. -/
theorem isUnramifiedAt_of_radicals (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {ι : Type*}
    {α : ι → L} {a : ι → K} (hpow : ∀ i, α i ^ p = algebraMap K L (a i))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤)
    {w : HeightOneSpectrum (𝓞 L)} (hpw : (p : 𝓞 L) ∉ w.asIdeal)
    (hav : ∀ i, (primeUnder (𝓞 K) w).valuation K (a i) = 1) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  exact (inertia_eq_bot_iff_isUnramifiedAt_base w.asIdeal w.ne_bot).mp
    (inertia_eq_bot_of_radicals hp hζ hpow hgen hpw hav)

end Radical

end InverseGalois.CFT
