/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InfinitePlaceCrossedProduct
import InverseGalois.CFT.Brauer.PlaceCoboundary
import InverseGalois.CFT.Brauer.SmoothBrauer
import InverseGalois.CFT.Units.ABHN

/-!
# The Albert-Brauer-Hasse-Noether theorem

A central simple algebra over a number field which splits over every completion is already split.
Equivalently, the Brauer group of a number field injects into the product of the Brauer groups of
its completions.

The proof puts together three things.  A Brauer class over a number field is split by some finite
Galois extension, and a class split by a finite Galois extension is the class of a crossed product
of that extension, so every class is the class of a crossed product of a Galois extension of number
fields.  Extending scalars to a completion of the base turns that crossed product into the crossed
product of the cocycle restricted to the decomposition group at a place above, so the hypothesis
that the class is locally trivial says exactly that the cocycle is locally a coboundary.  And a
cocycle of a Galois extension of number fields which is a coboundary at every place is a
coboundary, which is the theorem on the units proved from the cohomology of the ideles.

## Main results

* `InverseGalois.CFT.eq_one_of_forall_mem_relative`: **a Brauer class over a number field which is
  split by every completion is trivial.**
* `InverseGalois.CFT.eq_one_of_forall_placeInvariant_eq_one`: the same, with the finite places
  phrased through the local invariant.
* `InverseGalois.CFT.brauerToCompletions_injective`: **the Brauer group of a number field injects
  into the product of the Brauer groups of its completions.**

## Tags

Brauer group, number field, completion, crossed product, Albert-Brauer-Hasse-Noether,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section HasseNoether

variable {k : Type} [Field k] [NumberField k]

/-- **The Albert-Brauer-Hasse-Noether theorem.**  A Brauer class over a number field which is split
by every completion, finite or infinite, is trivial. -/
theorem eq_one_of_forall_mem_relative (x : BrauerGroup k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), x ∈ BrauerGroup.relative k (v.adicCompletion k))
    (hinf : ∀ u : InfinitePlace k, x ∈ BrauerGroup.relative k u.Completion) :
    x = 1 := by
  obtain ⟨L, hfd, hgal, hx⟩ := exists_isGalois_mem_relative x
  haveI : FiniteDimensional k ↥L := hfd
  haveI : IsGalois k ↥L := hgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  obtain ⟨f, hf, rfl⟩ := exists_mk_csa_eq_of_mem_relative (L := ↥L) x hx
  refine (CrossedProduct.mk_csa_eq_one_iff hf).mpr ?_
  have hga : ∀ (σ : Gal(↥L/k)) (u : Additive (↥L)ˣ),
      Additive.toMul (globalUnitsAut σ u) = σ • Additive.toMul u := fun _ _ => Units.ext rfl
  have ha : ∀ x y z : Gal(↥L/k),
      globalUnitsAut x (Additive.ofMul (f (y, z))) + Additive.ofMul (f (x, y * z))
        = Additive.ofMul (f (x * y, z)) + Additive.ofMul (f (x, y)) := by
    intro x y z
    refine Additive.toMul.injective ?_
    simp only [toMul_add, hga, toMul_ofMul]
    exact (hf x y z).symm
  have hinfL : ∀ w : InfinitePlace ↥L,
      ∃ c : ↥(stabilizer Gal(↥L/k) w) → Additive w.Completionˣ,
        ∀ s t : ↥(stabilizer Gal(↥L/k) w),
          Additive.ofMul (infiniteUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s := fun w =>
    (mem_relative_mk_csa_infiniteCompletion_iff_exists k w hf).mp
      (hinf (w.comap (algebraMap k ↥L)))
  have hfinL : ∀ v : HeightOneSpectrum (𝓞 ↥L),
      ∃ c : ↥(stabilizer Gal(↥L/k) v) → Additive (v.adicCompletion ↥L)ˣ,
        ∀ s t : ↥(stabilizer Gal(↥L/k) v),
          Additive.ofMul (adicUnitHom v (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s := fun v =>
    (mem_relative_mk_csa_adicCompletion_iff_exists k v hf).mp (hfin (primeUnder (𝓞 k) v))
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits
    (a := fun σ τ : Gal(↥L/k) => Additive.ofMul (f (σ, τ))) ha hinfL hfinL
  refine ⟨fun σ => Additive.toMul (b σ), fun g₁ g₂ => ?_⟩
  have heq := congrArg Additive.toMul (hb g₁ g₂)
  rw [toMul_ofMul, toMul_add, toMul_sub, hga] at heq
  exact heq.symm

/-- **A Brauer class over a number field with trivial invariant at every finite place and split by
every infinite completion is trivial.** -/
theorem eq_one_of_forall_placeInvariant_eq_one (x : BrauerGroup k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x = 1)
    (hinf : ∀ u : InfinitePlace k, x ∈ BrauerGroup.relative k u.Completion) :
    x = 1 :=
  eq_one_of_forall_mem_relative x
    (fun v => (placeInvariant_eq_one_iff v x).mp (hfin v)) hinf

variable (k) in
/-- **The Brauer group of a number field maps to the product of the Brauer groups of its
completions.** -/
noncomputable def brauerToCompletions :
    BrauerGroup k →*
      ((v : HeightOneSpectrum (𝓞 k)) → BrauerGroup (v.adicCompletion k)) ×
        ((u : InfinitePlace k) → BrauerGroup u.Completion) :=
  (Pi.monoidHom fun v : HeightOneSpectrum (𝓞 k) =>
      BrauerGroup.baseChangeHom (v.adicCompletion k)).prod
    (Pi.monoidHom fun u : InfinitePlace k => BrauerGroup.baseChangeHom u.Completion)

variable (k) in
@[simp]
theorem brauerToCompletions_apply (x : BrauerGroup k) :
    brauerToCompletions k x
      = (fun v : HeightOneSpectrum (𝓞 k) => BrauerGroup.baseChangeHom (v.adicCompletion k) x,
          fun u : InfinitePlace k => BrauerGroup.baseChangeHom u.Completion x) := rfl

variable (k) in
/-- **The Brauer group of a number field injects into the product of the Brauer groups of its
completions.** -/
theorem brauerToCompletions_injective : Function.Injective (brauerToCompletions k) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  refine eq_one_of_forall_mem_relative x (fun v => MonoidHom.mem_ker.mpr ?_)
    (fun u => MonoidHom.mem_ker.mpr ?_)
  · simpa using congrFun (congrArg Prod.fst hx) v
  · simpa using congrFun (congrArg Prod.snd hx) u

end HasseNoether

end InverseGalois.CFT
