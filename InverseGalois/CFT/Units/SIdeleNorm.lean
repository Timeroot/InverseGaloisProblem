/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteNormIndex
import InverseGalois.CFT.Local.NormIndex
import InverseGalois.CFT.Units.SIdeleHerbrand

/-!
# Recognising a norm among the ideles that are units outside a finite set of places

An idele that is a unit outside a finite invariant set of places has an archimedean part and a
finite part, and the two have been treated separately: over each orbit of places the sections are
the module induced from the decomposition group of any one of them, so a section is a norm as soon
as its value at one place of each orbit is a local norm.  At a finite place outside the set nothing
has to be assumed, because there the local subgroup is the units of the valuation ring and the
decomposition group fixes a uniformizer.

Putting the two halves together gives the local-to-global criterion that the algebraic proof of the
second inequality of class field theory rests on: an idele of the base field that is a local norm at
one place above each place is a global norm of an idele of the extension.

## Main results

* `InverseGalois.CFT.exists_normHom_sIdeleAut`: **an idele that is a unit outside the chosen places
  is a norm as soon as it is a local norm at one place above each infinite place and above each
  chosen finite place.**

## Tags

number field, idele, norm, decomposition group, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### Multiples of the local degree are local norms -/

section LocalPower

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Finite Gal(K/k)] {σ : Gal(K/k)}
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hgen

/-- **A multiple of the order of the decomposition group of a finite place is a local norm there**,
for the full turn of the orbit of that place.  The norm index at a place is the order of its
decomposition group, so that order annihilates the local zeroth Tate group. -/
theorem exists_normHom_orbitTurn_adicUnits [NumberField K]
    {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit) [Fintype ω.orbit]
    (hH : ∀ g : Gal(K/k), g • v₀ = v₀ → g ∈ stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))
    {m : ℕ} (hm : Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) ∣ m)
    (x : Additive ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
    (hx : smulUnitsAut (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)
      (orbitTurn σ v₀ hH) x = x) :
    ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
        (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) (orbitTurn σ v₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) b = m • x := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  haveI : NeZero (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) :=
    ⟨Nat.card_pos.ne'⟩
  exact exists_normHom_adicUnits_eq_nsmul (k := k) (v₀ : HeightOneSpectrum (𝓞 K))
    (mem_zpowers_orbitTurn v₀ hH hgen (smul_orbit_of_mem_stabilizer v₀))
    (orbitTurn_pow_card v₀ hH rfl) rfl x hx hm

/-- **A multiple of the order of the decomposition group of an infinite place is a local norm
there**, for the full turn of the orbit of that place. -/
theorem exists_normHom_orbitTurn_infiniteUnits [IsGalois k K]
    {ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K)} (w₀ : ω.orbit) [Fintype ω.orbit]
    (hH : ∀ g : Gal(K/k), g • w₀ = w₀ → g ∈ stabilizer Gal(K/k) (w₀ : InfinitePlace K))
    {m : ℕ} (hm : Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) ∣ m)
    (x : Additive (w₀ : InfinitePlace K).Completionˣ)
    (hx : smulUnitsAut (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH) x = x) :
    ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
        (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K))) b = m • x :=
  exists_normHom_infiniteUnits_eq_nsmul (k := k) (w₀ : InfinitePlace K)
    (mem_zpowers_orbitTurn w₀ hH hgen (smul_orbit_of_mem_stabilizer_infinite w₀)) rfl x hx hm

end LocalPower

section SIdeleNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]
  {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
  (hn : Nat.card Gal(K/k) = n)

include hι hgen hn

/-- **An idele that is a unit outside the chosen places is a norm as soon as it is a local norm at
one place above each infinite place and above each chosen finite place.**  Above a finite place
outside the chosen ones the condition is automatic, the local subgroup there being the units of the
valuation ring at an unramified place. -/
theorem exists_normHom_sIdeleAut
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {f : (∀ w : InfinitePlace K, Additive w.Completionˣ)
      × (∀ v : HeightOneSpectrum (𝓞 K), ↥(adicSUnits (Set.range ι) v))}
    (hf : sIdeleAut hι σ f = f)
    (hinf : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ∃ b,
      normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) ω.out)) (R := (ω.out).Completion)
          (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))))
        (Nat.card ↥(stabilizer Gal(K/k) ω.out)) b = f.1 ω.out)
    (hfin : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ω.out ∈ Set.range ι → ∃ b,
        normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) ω.out))
            (R := (ω.out).adicCompletion K)
            (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))))
          (Nat.card ↥(stabilizer Gal(K/k) ω.out)) b
        = ((f.2 ω.out : ↥(adicSUnits (Set.range ι) ω.out)) :
            Additive ((ω.out).adicCompletion K)ˣ)) :
    ∃ u, normHom (sIdeleAut hι σ) n u = f := by
  haveI : Module.Finite k K := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [sIdeleAut_eq]
  exact exists_normHom_prodAut _ _ n
    (exists_normHom_infiniteUnitsFamily hgen hn (congrArg Prod.fst hf) hinf)
    (exists_normHom_adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι) hgen hn hunram
      (congrArg Prod.snd hf) hfin)

end SIdeleNorm

/-! ### Local powers are global norms -/

section SIdelePower

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]
  {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
  (hn : Nat.card Gal(K/k) = n)

include hι hgen hn

/-- **An idele that is a unit outside the chosen places and is locally a multiple of the local
degree above each of them is a norm.**  At every place the norm index is the order of the
decomposition group, so a multiple of that order is a local norm, and the local norms at one place
above each place of the base field assemble into a global one. -/
theorem exists_normHom_sIdeleAut_of_nsmul
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {f : (∀ w : InfinitePlace K, Additive w.Completionˣ)
      × (∀ v : HeightOneSpectrum (𝓞 K), ↥(adicSUnits (Set.range ι) v))}
    (hf : sIdeleAut hι σ f = f)
    (hinf : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      ∃ (m : ℕ) (x : Additive ((orbitOut ω : ω.orbit) : InfinitePlace K).Completionˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : InfinitePlace K)) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))) x = x
          ∧ f.1 ((orbitOut ω : ω.orbit) : InfinitePlace K) = m • x)
    (hfin : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.out ∈ Set.range ι →
      ∃ (m : ℕ) (x : Additive
          (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))) x = x
          ∧ ((f.2 ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) :
                ↥(adicSUnits (Set.range ι) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) :
              Additive (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
            = m • x) :
    ∃ u, normHom (sIdeleAut hι σ) n u = f := by
  haveI : Module.Finite k K := Module.Finite.of_restrictScalars_finite ℚ k K
  refine exists_normHom_sIdeleAut hι hgen hn hunram hf (fun ω => ?_) (fun ω hω => ?_)
  · haveI : Fintype ω.orbit := Fintype.ofFinite _
    obtain ⟨m, x, hm, hx, hfx⟩ := hinf ω
    obtain ⟨b, hb⟩ := exists_normHom_orbitTurn_infiniteUnits hgen (orbitOut ω)
      (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω)) hm x hx
    exact ⟨b, hb.trans hfx.symm⟩
  · haveI : Fintype ω.orbit := Fintype.ofFinite _
    obtain ⟨m, x, hm, hx, hfx⟩ := hfin ω hω
    obtain ⟨b, hb⟩ := exists_normHom_orbitTurn_adicUnits hgen (orbitOut ω)
      (mem_stabilizer_of_smul_orbit (orbitOut ω)) hm x hx
    exact ⟨b, hb.trans hfx.symm⟩

end SIdelePower

end InverseGalois.CFT
