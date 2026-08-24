/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.Pairing
import InverseGalois.CFT.Units.SplitPlaces

/-!
# From local `p`-th powers to a global one

Let `K` be a number field containing a primitive `p`-th root of unity and let `B` be a subgroup of
`Kˣ` equipped with a power basis, so that the radical extension `M` attached to the basis is a
Kummer extension of `K` of exponent `p`.  Fix `a ∈ B` together with a `p`-th root `wa` of `a` in
`M`.

The statement proved here is the global step of the second inequality: if an element `x` of `B`
becomes a `p`-th power in the completion at every place that splits completely in the field cut out
by `wa`, then `x` is already of the form `a ^ l * y ^ p` in `Kˣ`.  Two ingredients combine.  The
local input is turned into the statement that every automorphism lying in the decomposition group at
such a place fixes a chosen `p`-th root of `x`; that is the content of the Kummer descent for
completions.  The decomposition groups at those places generate the whole subgroup of automorphisms
fixing `wa`, because that subgroup is the group of the extension over an intermediate field and the
Galois group here is abelian of exponent `p`.  Comparing exponent vectors then produces the
exponent `l`.

## Main results

* `InverseGalois.CFT.PowBasis.pow_eq_one_gal`: the Galois group of the radical extension has
  exponent `p`.
* `InverseGalois.CFT.PowBasis.isSolvable_gal`: it is abelian, hence solvable.
* `InverseGalois.CFT.PowBasis.exists_zpow_mul_pow_of_forall_local`: an element fixed by the
  decomposition groups at a generating set of places is a power of `a` times a `p`-th power.
* `InverseGalois.CFT.PowBasis.exists_zpow_mul_pow_of_forall_split`: **an element that is a local
  `p`-th power at every place splitting completely in the field cut out by `wa` is a power of `a`
  times a `p`-th power.**

## Tags

Kummer theory, class field theory, second inequality, local-global, power basis
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-- A radical extension of a number field is a number field. -/
instance numberField_radExt {E : Type*} [Field E] [NumberField E] {ι : Type*} [Fintype ι]
    (n : ℕ) (g : ι → E) : NumberField (Kummer.RadExt n g) :=
  NumberField.of_module_finite E _

namespace PowBasis

variable {K : Type*} [Field K] [NumberField K] {p s : ℕ} [NeZero p] {ζ : K} {B : Subgroup Kˣ}
  (P : PowBasis B p s)

/-- **The Galois group of the radical extension has exponent `p`.** -/
theorem pow_eq_one_gal (hζ : IsPrimitiveRoot ζ p) (σ : Gal(P.ext/K)) : σ ^ p = 1 := by
  refine (P.setup hζ).galEquiv.injective ?_
  rw [map_pow, map_one]
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity p _).mp ((P.setup hζ).galEquiv σ i).2

/-- The Galois group of the radical extension is abelian. -/
theorem mul_comm_gal (hζ : IsPrimitiveRoot ζ p) (σ τ : Gal(P.ext/K)) : σ * τ = τ * σ := by
  refine (P.setup hζ).galEquiv.injective ?_
  rw [map_mul, map_mul, mul_comm]

/-- **The Galois group of the radical extension is solvable.** -/
theorem isSolvable_gal (hζ : IsPrimitiveRoot ζ p) : IsSolvable Gal(P.ext/K) :=
  isSolvable_of_comm (P.mul_comm_gal hζ)

/-- An element of the subgroup which is a `p`-th power in the completion at each place of a family
whose decomposition groups generate the automorphisms fixing a `p`-th root of `a` differs from a
power of `a` by a `p`-th power. -/
theorem exists_zpow_mul_pow_of_forall_local (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {a x : Kˣ} (ha : a ∈ B) (hx : x ∈ B)
    {wa : P.ext} (hwa : wa ^ p = algebraMap K P.ext (a : K))
    {W : Set (HeightOneSpectrum (𝓞 P.ext))}
    (hW : ∀ w ∈ W, ∃ c : (primeUnder (𝓞 K) w).adicCompletion K,
      c ^ p = algebraMap K ((primeUnder (𝓞 K) w).adicCompletion K) (x : K))
    (hgen : ∀ σ : Gal(P.ext/K), σ wa = wa →
      σ ∈ Subgroup.closure (⋃ w ∈ W, (stabilizer Gal(P.ext/K) w : Set Gal(P.ext/K)))) :
    ∃ (l : ℤ) (y : Kˣ), x = a ^ l * y ^ p := by
  haveI : IsGalois K P.ext := P.isGalois_ext hζ
  obtain ⟨wx, hwx⟩ := P.exists_root hx
  refine P.exists_zpow_mul_pow_of_forall_fix hp hζ ha hx hwa hwx fun σ hσ => ?_
  exact smul_eq_self_of_mem_closure_stabilizer hζ hp.ne_zero hwx.symm hW (hgen σ hσ)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An element of the subgroup which is a `p`-th power in the completion at every place splitting
completely in the field cut out by a `p`-th root of `a` differs from a power of `a` by a `p`-th
power.**  The places in question are exactly those, away from a prescribed finite set of places of
the base outside which the extension is unramified, whose decomposition group fixes the chosen
root. -/
theorem exists_zpow_mul_pow_of_forall_split (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {a x : Kˣ} (ha : a ∈ B) (hx : x ∈ B)
    {wa : P.ext} (hwa : wa ^ p = algebraMap K P.ext (a : K))
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 P.ext), primeUnder (𝓞 K) w ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 P.ext), primeUnder (𝓞 K) w ∉ S →
      (∀ σ : Gal(P.ext/K), σ • w = w → σ wa = wa) →
      ∃ c : (primeUnder (𝓞 K) w).adicCompletion K,
        c ^ p = algebraMap K ((primeUnder (𝓞 K) w).adicCompletion K) (x : K)) :
    ∃ (l : ℤ) (y : Kˣ), x = a ^ l * y ^ p := by
  haveI : IsGalois K P.ext := P.isGalois_ext hζ
  haveI : IsSolvable Gal(P.ext/K) := P.isSolvable_gal hζ
  set L : IntermediateField K P.ext :=
    IntermediateField.fixedField (stabilizer Gal(P.ext/K) wa) with hLdef
  haveI : IsSolvable Gal(P.ext/↥L) := isSolvable_gal_intermediate L
  have hfix : L.fixingSubgroup = stabilizer Gal(P.ext/K) wa :=
    IntermediateField.fixingSubgroup_fixedField _
  refine P.exists_zpow_mul_pow_of_forall_local hp hζ ha hx hwa (W := splitPlaces L S) ?_ ?_
  · rintro w ⟨hwS, hwle⟩
    refine hloc w hwS fun σ hσ => ?_
    have hmem := hwle (mem_stabilizer_iff.mpr hσ)
    rw [hfix] at hmem
    exact hmem
  · intro σ hσ
    rw [closure_stabilizer_splitPlaces hp (P.pow_eq_one_gal hζ) hS hunr, hfix]
    exact hσ

end PowBasis

end InverseGalois.CFT
