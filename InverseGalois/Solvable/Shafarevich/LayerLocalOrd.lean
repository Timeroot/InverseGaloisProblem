/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalOrdOutside
import InverseGalois.Solvable.ElementaryAbelian
import InverseGalois.Solvable.Shafarevich.LayerKummerShrink

/-!
# The local dictionary of a layer, from the orders outside a stable set

The ladder which climbs a generic operator group one layer at a time asks for a local dictionary at
every number of letters: the reading of a class in the units of a finite Galois subextension has to
be an order at each place away from a finite set.  With the places taken to be the primes of the
subextension outside a set carried into itself by the Galois group, and the reading taken to be the
vector of orders at them, the dictionary at a place already says everything, so all that is left is
to feed it the coefficients.

Those coefficients are the homomorphisms of the roots of unity into the layer.  Both groups are
finite and the layer is killed by the prime, so the homomorphisms form a finite abelian group killed
by the prime, hence a coordinate space over the field with that many elements — which is exactly the
shape the dictionary at a place wants.  Since the coefficients are produced afresh at each number of
letters, **the local dictionary of a layer holds at every number of letters at once.**

## Main results

* `InverseGalois.Shafarevich.exists_addEquiv_hom_layerSub`: the homomorphisms of the roots of unity
  into a layer form a coordinate space over the field with `ℓ` elements.
* `InverseGalois.Shafarevich.hasLayerLocalOrdHom_ordFinsupp`: **the vector of orders outside a
  stable set of places is the local dictionary of a layer**, at every number of letters.

## Tags

Shafarevich's theorem, Kummer theory, layer, decomposition group, order, elementary abelian group
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain NumberField

section Layer

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (S : Type) [Group S] [Finite S]
  (j : ℕ)
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [NumberField ↥K] [IsGalois k ↥K]
variable {M : Type} [CommGroup M] [Finite M] [IsCyclic M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ι : M →* (↥K)ˣ}
variable (φ : Gal(Ω/k) →* U)
variable (T : Set (HeightOneSpectrum (𝓞 ↥K))) [IsGaloisStablePlaces k ↥K T]
variable [DecidableEq {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}]

omit [Group U] [NumberField k] [IsGalois k Ω] [NumberField ↥K] [IsGalois k ↥K] [IsCyclic M]
  [MulDistribMulAction Gal(Ω/↥K) M] [MulDistribMulAction Gal(Ω/k) M]
  [IsGaloisStablePlaces k ↥K T] [DecidableEq {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}] in
/-- **The homomorphisms of the roots of unity into a layer form a coordinate space over the field
with as many elements as the prime.**  There are finitely many of them because both groups are
finite, and the prime kills them because it kills the layer. -/
theorem exists_addEquiv_hom_layerSub (m : ℕ) :
    ∃ d : ℕ, Nonempty (Additive (M →* ↥(layerSub ℓ (Generic U m S) j)) ≃+ (Fin d → ZMod ℓ)) := by
  haveI : Finite (M →* ↥(layerSub ℓ (Generic U m S) j)) :=
    Finite.of_injective (fun w => (w : M → ↥(layerSub ℓ (Generic U m S) j)))
      DFunLike.coe_injective
  refine exists_rank_addEquiv_of_forall_nsmul_eq_zero fun w => ?_
  have hpow : ℓ • w = Additive.ofMul (Additive.toMul w ^ ℓ) :=
    (_root_.ofMul_pow ℓ (Additive.toMul w)).symm
  have hone : (Additive.toMul w : M →* ↥(layerSub ℓ (Generic U m S) j)) ^ ℓ = 1 := by
    refine MonoidHom.ext fun t => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    exact layerSub_pow_eq_one ℓ (Generic U m S) j _
  rw [hpow, hone, _root_.ofMul_one]

/-- **The vector of orders at the primes outside a stable set of places is the local dictionary a
layer asks for**, at every number of letters at once: at each number of letters the homomorphisms of
the roots of unity into the layer are a coordinate space over the field with as many elements as the
prime, and every prime outside the set carries the dictionary at its own place. -/
theorem hasLayerLocalOrdHom_ordFinsupp {D : Set (Subgroup Gal(Ω/k))}
    (hD : finiteDecompositionSubgroups k Ω ⊆ D) (hker : K.fixingSubgroup ≤ φ.ker)
    (h : IsKummerData ↥K Ω M ι ℓ) (htriv : ∀ (σ : Gal(Ω/k)) (n : M), σ • n = n)
    (hM : Nat.card M = ℓ)
    (hfix : ∀ (σ : Gal(Ω/k)) (n : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι n)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι n))
    (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ ℓ = y) :
    HasLayerLocalOrdHom ℓ U S j K φ hker h htriv hM (ordFinsupp T) D := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  intro m
  letI := galLayerAction ℓ U m S j φ
  letI := actsTrivially_hom_layerSub ℓ U S j K φ m hker htriv
  intro x
  obtain ⟨d, ⟨eM⟩⟩ := exists_addEquiv_hom_layerSub ℓ U S j (M := M) m
  exact hasLocalOrdHom_ordFinsupp h htriv _ _ _ hfix T eM hroot hD x

end Layer

end InverseGalois.Shafarevich
