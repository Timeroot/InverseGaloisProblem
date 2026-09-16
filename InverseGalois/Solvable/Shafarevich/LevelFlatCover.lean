/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.GenericHomology
import InverseGalois.Solvable.Shafarevich.LevelFlatKernel

/-!
# The flat prescription covered by the homology of the level

The flat prescription asks for a homomorphism of the kernel of the base realization into a layer
taking prescribed values along the inertia of finitely many named primes.  Over a number field that
demand is not met outright: the prescribed divisor has an obstruction to being corrected to an
invariant one, and the obstruction is a genuine class, killed only by enlarging the level.  What the
arithmetic supplies is therefore not an answer but a cover: a single class of the first homology of
the level whose death under a shrinking makes the prescription answerable at the shrunk level.

That is the same packaging the everywhere locally trivial classes of the second cohomology arrive
in, and it is consumed the same way.  The count on first homology asks only for the operator group,
the number of letters the answer is wanted at, the layer and the twist, so the number of letters to
start from is fixed before any lift, any named prime and hence any class is known.  At that number
the cover turns the data into one homology class, the count kills it by a surjective equivariant
homomorphism, and the prescription is answered at the intermediate number of letters.  The two
shrinkings compose: the one that kills the class first and the one the answer spends second.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatKernelCover` — **the data the flat prescription is read on names
  a class of the first homology of the level whose death under a shrinking makes the prescription
  answerable at the shrunk level.**

## Main results

* `InverseGalois.Shafarevich.hasFlatKernelPrescription_of_hasFlatKernelCover` — **a covered
  prescription is a prescription**, the count on first homology paying for the shrinking.

## Tags

Shafarevich's theorem, embedding problem, group homology, p-central series, ramification,
decomposition group
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT MulAction NumberField

open scoped Pointwise

attribute [local instance] genericQuotAction

/-! ### The covering the arithmetic supplies -/

section Cover

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))

/-- **The data the flat prescription is read on names a class of the first homology of the level
whose death under a shrinking makes the prescription answerable at the shrunk level.**

The homology is that of the semidirect product of the generic operator group with the operator
group, with coefficients in the layer tensored with a fixed module; over a number field the fixed
module is the twist by the roots of unity, and the covering is global duality read against the
level, the obstruction to correcting the prescribed divisor to an invariant one being traded by the
duality for a class of the level.

What is asked of the covering is the naturality of that reading: a shrinking which kills the
homology class leaves a prescription which can be answered, the data being carried across the
shrinking by the map of layers.  The number of letters the answer is wanted at is fixed in advance,
and so is the intermediate number the class is killed down to. -/
def HasFlatKernelCover (R N : ℕ) (W : Rep (ZMod ℓ) U) : Prop :=
  ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Finite ι]
      (Q : ι → Ideal (𝓞 Ω)) (A : ι → Subgroup Gal(Ω/k))
      (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
    Function.Surjective F → IsSmoothHom F →
    (∀ x, SemidirectProduct.rightHom (F x) = φ x) →
    (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) → (∀ μ, (ℓ : 𝓞 Ω) ∉ Q μ) →
    (∀ μ ν : ι, μ ≠ ν → ∀ ρ : Gal(Ω/k), Q ν ≠ ρ • Q μ) →
    (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
    (∀ μ, A μ = Ideal.inertia Gal(Ω/k) (Q μ) ⊓ φ.ker) →
    (∀ μ, Ideal.inertia Gal(Ω/k) (Q μ) ≤ φ.ker) →
    (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)) :
      ↥(A μ) → ↥(layerSub ℓ (Generic U N S) j))) →
    (∀ (μ : ι) (g : Gal(Ω/k)) (x : ↥(A μ)) (hx : g * (x : Gal(Ω/k)) * g⁻¹ ∈ A μ),
      a μ ⟨g * (x : Gal(Ω/k)) * g⁻¹, hx⟩ = φ g • a μ x) →
    (∀ (μ : ι) (ν : Fin t) (ρ : Gal(Ω/k)),
      ∃ y ∈ stabilizer Gal(Ω/k) (Q μ), ρ * y * ρ⁻¹ ∉ D ν) →
      ∃ x : groupHomology.H1 (genericInflate U N S ℓ j W),
        ∀ (γ : Generic U N S →* Generic U R S) (hγ : IsOperatorHom γ), Function.Surjective γ →
          groupHomology.map (operatorSemidirect hγ) (operatorInflateRep hγ ℓ j W) 1 x = 0 →
            FlatKernelAnswer ℓ U n S j φ D R ((layerSemidirectMap ℓ hγ (j + 1)).comp F) ι Q A
              fun μ => (layerSubMap ℓ γ j).comp (a μ)

end Cover

/-! ### A covered prescription is a prescription -/

section Consume

variable {ℓ : ℕ} [Fact ℓ.Prime] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type} [Group S]
  [Finite S] {j : ℕ} {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

omit [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **A covered prescription is a prescription.**

The number of letters to start from is settled by the count on first homology, which asks only for
the operator group, the intermediate number of letters, the layer and the twist; so it is fixed
before any lift, and hence any class, is chosen.  At that number the covering turns the data into a
single homology class, the count kills that class by a surjective equivariant homomorphism onto the
intermediate number, and the prescription is answered there.

The two shrinkings compose.  The map of layers is functorial, so the prescribed values carried
across the composite are the values carried across the first and then the second; and the morphism
of extensions is functorial too, so the given lift carried down along the composite is the lift
carried down along the first and then the second, which is what the clause confining the new
ramification is read against. -/
theorem hasFlatKernelPrescription_of_hasFlatKernelCover (hS : IsPGroup ℓ S) (R : ℕ)
    (W : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) W]
    (hcov : ∀ N : ℕ, HasFlatKernelCover ℓ U n S j φ D R N W) :
    HasFlatKernelPrescription ℓ U n S j φ D := by
  obtain ⟨N, hN⟩ := exists_operatorHom_h1_eq_zero U R S hS (j := j) (t := 1) W
  refine ⟨N, ?_⟩
  intro F ι _ Q A a hFsurj hFsm hFright hQp hQbot hQℓ hQconj hAstab hAker hAeq hAunr hasm haequiv
    hesc
  obtain ⟨x, hx⟩ := hcov N F ι Q A a hFsurj hFsm hFright hQp hQbot hQℓ hQconj hAstab hAker hAeq
    hAunr hasm haequiv hesc
  obtain ⟨γ, hγ, hγsurj, hkill⟩ := hN fun _ : Fin 1 => x
  obtain ⟨β, hβ, hβsurj, u, hsm, hueq, huD, hua, huram⟩ := hx γ hγ hγsurj (hkill 0)
  refine ⟨β.comp γ, hβ.comp hγ, hβsurj.comp hγsurj, u, hsm, hueq, huD, fun μ y hy => ?_,
    fun P hP hPbot hram => ?_⟩
  · simp only [hua μ y hy, layerSubMap_comp, MonoidHom.comp_apply]
  · refine (huram P hP hPbot hram).imp id fun h g hg => ?_
    exact (layerSemidirectMap_comp ℓ hγ hβ (hβ.comp hγ) (j + 1) (F g)).symm.trans (h g hg)

end Consume

end InverseGalois.Shafarevich
