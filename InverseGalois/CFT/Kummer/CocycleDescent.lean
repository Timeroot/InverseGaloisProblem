/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InflationRootsOfUnity
import InverseGalois.CFT.Kummer.RadicalClosure
import InverseGalois.CFT.Kummer.RootsInBase

/-!
# Splitting a cocycle of roots of unity over a radical extension

Let `k` be a number field containing a primitive `n`-th root of unity, let `K/k` be finite Galois,
and let `a` be a `μ_n`-valued `2`-cocycle on `Gal(K/k)` which becomes a coboundary in `Kˣ`, say
`a = ∂b`.  Hilbert 90 turns the failure of `b` to take values in `μ_n` into a single element
`β ∈ Kˣ`, and adjoining an `n`-th root of `β` produces a finite Galois extension `M/k` over which
the cochain can be rescaled to take values in `μ_n`.  Since `k` already contains all `n`-th roots of
unity, those values descend to `kˣ`, so the inflation of `a` to `Gal(M/k)` is the coboundary of an
explicit `kˣ`-valued cochain of `n`-th roots of unity.

This is the field-theoretic half of the solution of a central embedding problem with kernel of order
`n`: the cochain produced here is exactly the datum that trivialises the factor set of a central
extension.

## Main results

* `InverseGalois.CFT.exists_intermediateField_cochain_of_isMulCoboundary`: **a cocycle of `n`-th
  roots of unity that is a coboundary in the big field becomes, after a radical extension, the
  coboundary of a cochain of `n`-th roots of unity of the base field.**  The radical extension
  contains the given one, and the map of Galois groups is the restriction of automorphisms.

## Tags

Kummer theory, roots of unity, group cohomology, coboundary, embedding problem
-/

namespace InverseGalois.CFT

open IntermediateField

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A cocycle of `n`-th roots of unity of the base field which is a coboundary in the units of a
finite Galois extension `K/k` becomes, after a further radical extension `M/K`, the coboundary of a
cochain valued in the `n`-th roots of unity of `k` itself.**

Hilbert 90 converts the coboundary datum `b` into an element `β` of `Kˣ` with `σ β / β = (b σ) ^ n`;
adjoining an `n`-th root of `β` and taking the Galois closure gives `M`, over which `b` may be
rescaled to take values in `μ_n`.  As `k` contains a primitive `n`-th root of unity, `μ_n` already
lies in `k`, giving the `kˣ`-valued cochain `c`.  The extension `M` contains `K`, and the
homomorphism relating their Galois groups is the restriction of automorphisms. -/
theorem exists_intermediateField_cochain_of_isMulCoboundary
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {a : Gal(↥K/k) → Gal(↥K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    {b : Gal(↥K/k) → (↥K)ˣ}
    (hb : ∀ g h : Gal(↥K/k), g • b h / b (g * h) * b g =
      Units.map (algebraMap k ↥K : k →* ↥K) (a g h)) :
    ∃ M : IntermediateField k Ω, K ≤ M ∧ NumberField ↥M ∧ IsGalois k ↥M ∧
      ∃ ρ : Gal(↥M/k) →* Gal(↥K/k), Function.Surjective ρ ∧
        (∀ (g : Gal(↥M/k)) (x : Ω) (hx : x ∈ K) (hx' : x ∈ M),
          ((ρ g ⟨x, hx⟩ : ↥K) : Ω) = ((g ⟨x, hx'⟩ : ↥M) : Ω)) ∧
        ∃ c : Gal(↥M/k) → kˣ, (∀ g, c g ^ n = 1) ∧
          ∀ g h, a (ρ g) (ρ h) = c g * c h * (c (g * h))⁻¹ := by
  classical
  obtain ⟨β, hβ⟩ := exists_pow_eq_of_isMulCoboundary₂ (n := n)
    (a := fun p => Units.map (algebraMap k ↥K : k →* ↥K) (a p.1 p.2))
    (fun p => by rw [← map_pow, hpow, map_one]) hb
  obtain ⟨M, hKM, hMfin, hMgal, hroot⟩ :=
    exists_isGalois_intermediateField_forall_pow_eq (k := k) (Ω := Ω) K
      (fun _ : Unit => ((β : ↥K) : Ω)) (NeZero.ne n)
  haveI : Module.Finite k ↥M := hMfin
  haveI : NumberField ↥M := NumberField.of_module_finite k ↥M
  haveI := hMgal
  letI : Algebra ↥K ↥M := RingHom.toAlgebra (IntermediateField.inclusion hKM).toRingHom
  haveI : IsScalarTower k ↥K ↥M :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := ↥K) (A := ↥M) (fun x => rfl)
  obtain ⟨α, hαM, hαpow⟩ := hroot ()
  set αM : ↥M := ⟨α, hαM⟩ with hαM'
  have hαne : αM ≠ 0 := by
    intro h
    have h0 : α = 0 := congrArg Subtype.val h
    rw [h0, zero_pow (NeZero.ne n)] at hαpow
    exact (Units.ne_zero β) (Subtype.ext hαpow.symm)
  set αU : (↥M)ˣ := Units.mk0 αM hαne with hαU
  have hαUpow : αU ^ n = Units.map (algebraMap ↥K ↥M : ↥K →* ↥M) β := by
    refine Units.ext (Subtype.ext ?_)
    show (αM : Ω) ^ n = ((β : ↥K) : Ω)
    exact hαpow
  obtain ⟨b', hb'pow, hb'⟩ := exists_cochain_pow_eq_one (k := k) (K := ↥K) (M := ↥M) (n := n)
    (a := fun p => Units.map (algebraMap k ↥K : k →* ↥K) (a p.1 p.2)) hb hβ αU hαUpow
  choose c hcpow hcmap using fun g : Gal(↥M/k) =>
    exists_units_algebraMap_eq_of_pow_eq_one (k := k) (M := ↥M) hζ (hb'pow g)
  have hres : ∀ (g : Gal(↥M/k)) (x : Ω) (hx : x ∈ K) (hx' : x ∈ M),
      ((AlgEquiv.restrictNormalHom ↥K g ⟨x, hx⟩ : ↥K) : Ω) = ((g ⟨x, hx'⟩ : ↥M) : Ω) := by
    intro g x hx hx'
    exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes (E := ↥K) g (⟨x, hx⟩ : ↥K))
  refine ⟨M, hKM, inferInstance, inferInstance, AlgEquiv.restrictNormalHom ↥K,
    AlgEquiv.restrictNormalHom_surjective ↥M, hres, c, hcpow, fun g h => ?_⟩
  have hinj : Function.Injective (Units.map (algebraMap k ↥M : k →* ↥M)) :=
    Units.map_injective (algebraMap k ↥M).injective
  refine hinj ?_
  have hmap : ∀ x : kˣ, Units.map (algebraMap ↥K ↥M : ↥K →* ↥M)
      (Units.map (algebraMap k ↥K : k →* ↥K) x) = Units.map (algebraMap k ↥M : k →* ↥M) x := by
    intro x
    refine Units.ext ?_
    simp [← IsScalarTower.algebraMap_apply k ↥K ↥M]
  have hcomm : c g * c h * (c (g * h))⁻¹ = c h / c (g * h) * c g := by
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  have hkey := hb' g h
  rw [smul_eq_self_of_pow_eq_one hζ g (hb'pow h)] at hkey
  rw [← hcmap g, ← hcmap h, ← hcmap (g * h)] at hkey
  rw [hcomm, map_mul, map_div, hkey, hmap]

end InverseGalois.CFT
