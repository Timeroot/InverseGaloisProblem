/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.PlaceTower

/-!
# Moving a place of a tower by an automorphism of the top field

An automorphism of the top field of a tower whose middle field is normal over the bottom restricts
to an automorphism of the middle field, and the two automorphisms are compatible with passing to
the place below: the place of the middle field below the image of a place is the image, under the
restricted automorphism, of the place below.

The same compatibility holds one level up, between the completions.  The isomorphism of completions
attached to the automorphism of the top field carries the image of the completion of the middle
field onto the image of the completion at the moved place, and there it agrees with the isomorphism
attached to the restricted automorphism; both sides are continuous and agree on the dense image of
the middle field, where the statement is the defining property of the restriction.

Taking unit groups gives the statement in the form the ideles need.  When the middle field is the
bottom field the restricted automorphism is the identity and these are the compatibilities already
recorded for the fixed ideles.

## Main results

* `InverseGalois.CFT.primeUnder_smul`: **the prime of the middle field below a moved prime is the
  moved prime below.**
* `InverseGalois.CFT.comap_smul_algebraMap`: **the place of the middle field below a moved place is
  the moved place below.**
* `InverseGalois.CFT.adicCompletionGalEquiv_adicCompletionComap_restrict`,
  `InverseGalois.CFT.infiniteCompletionGalEquiv_infiniteCompletionComap_restrict`: **the
  isomorphisms of completions attached to an automorphism and to its restriction agree on the
  completion of the middle field.**
* `InverseGalois.CFT.unitsFamily_map_adicUnitsComap_restrict`,
  `InverseGalois.CFT.unitsFamily_map_infiniteUnitsComap_restrict`: the same for the local unit
  groups.

## Tags

number field, tower, place, completion, Galois action, restriction
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField NumberField.InfinitePlace

section PlaceRestrict

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F]

/-! ### The restriction of an automorphism to the middle field -/

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The restriction of an automorphism to the middle field commutes with the inclusion of the
middle field.** -/
theorem algebraMap_restrictNormalHom (σ : Gal(K/k)) (y : F) :
    algebraMap F K (AlgEquiv.restrictNormalHom F σ y) = σ (algebraMap F K y) :=
  AlgEquiv.restrictNormal_commutes σ F y

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k F] in
/-- The inclusion of the integers of the middle field into the integers of the top field is the
inclusion of the middle field. -/
theorem coe_algebraMap_ringOfIntegers (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = algebraMap F K (a : F) := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F K, RingOfIntegers.coe_eq_algebraMap]

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The restriction of an automorphism to the middle field commutes with the inclusion of the
integers of the middle field.** -/
theorem algebraMap_smul_ringOfIntegers (σ : Gal(K/k)) (a : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 K) (AlgEquiv.restrictNormalHom F σ • a) = σ • algebraMap (𝓞 F) (𝓞 K) a :=
  RingOfIntegers.ext (by
    rw [coe_algebraMap_ringOfIntegers F]
    exact algebraMap_restrictNormalHom F σ (a : F))

/-! ### The finite places -/

variable (F) in
omit [NumberField k] [NumberField F] in
/-- **The prime of the middle field below a moved prime is the moved prime below**: the two sides
have the same elements, an element of the middle field lying in one exactly when the automorphism
carries it into the prime of the top field. -/
theorem primeUnder_smul (σ : Gal(K/k)) (w : HeightOneSpectrum (𝓞 K)) :
    primeUnder (𝓞 F) (σ • w) = AlgEquiv.restrictNormalHom F σ • primeUnder (𝓞 F) w := by
  refine HeightOneSpectrum.ext ?_
  ext a
  rw [primeUnder_asIdeal, asIdeal_smul, asIdeal_smul, primeUnder_asIdeal, Ideal.under_def,
    Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap,
    ← map_inv (AlgEquiv.restrictNormalHom F) σ, algebraMap_smul_ringOfIntegers F]

variable (F) in
omit [NumberField k] in
/-- **The isomorphisms of completions at the finite places attached to an automorphism and to its
restriction to the middle field agree on the completion of the middle field**: both sides are
continuous and agree on the dense image of the middle field. -/
theorem adicCompletionGalEquiv_adicCompletionComap_restrict (w : HeightOneSpectrum (𝓞 K))
    (σ : Gal(K/k)) (c : (primeUnder (𝓞 F) w).adicCompletion F) :
    adicCompletionGalEquiv w σ (adicCompletionComap (𝓞 F) (k := F) (K := K) w c)
      = adicCompletionComap (𝓞 F) (k := F) (K := K) (σ • w)
          (ringCast (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletion F)
            (primeUnder_smul F σ w).symm
            (adicCompletionGalEquiv (primeUnder (𝓞 F) w)
              (AlgEquiv.restrictNormalHom F σ) c)) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_adicCompletionGalEquiv w σ).comp
        (continuous_adicCompletionComap (𝓞 F) (k := F) (K := K) w))
      ((continuous_adicCompletionComap (𝓞 F) (k := F) (K := K) (σ • w)).comp
        ((continuous_ringCast _ _).comp
          (continuous_adicCompletionGalEquiv (primeUnder (𝓞 F) w)
            (AlgEquiv.restrictNormalHom F σ))))
  · intro x
    set y : F := WithVal.equiv ((primeUnder (𝓞 F) w).valuation F) x with hy
    have h1 : adicCompletionComap (𝓞 F) (k := F) (K := K) w (adicCoe y (primeUnder (𝓞 F) w))
        = adicCoe (algebraMap F K y) w := adicCompletionComap_coe (𝓞 F) w y
    have h2 : adicCompletionComap (𝓞 F) (k := F) (K := K) (σ • w)
          (adicCoe (AlgEquiv.restrictNormalHom F σ y) (primeUnder (𝓞 F) (σ • w)))
        = adicCoe (algebraMap F K (AlgEquiv.restrictNormalHom F σ y)) (σ • w) :=
      adicCompletionComap_coe (𝓞 F) (σ • w) _
    show adicCompletionGalEquiv w σ
        (adicCompletionComap (𝓞 F) (k := F) (K := K) w (adicCoe y (primeUnder (𝓞 F) w)))
      = adicCompletionComap (𝓞 F) (k := F) (K := K) (σ • w)
          (ringCast _ (primeUnder_smul F σ w).symm
            (adicCompletionGalEquiv (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
              (adicCoe y (primeUnder (𝓞 F) w))))
    rw [h1, adicCompletionGalEquiv_adicCoe, adicCompletionGalEquiv_adicCoe, ringCast_adicCoe, h2,
      algebraMap_restrictNormalHom F]

variable (F) in
omit [NumberField k] in
/-- **The transports of the local units at the finite places attached to an automorphism and to its
restriction to the middle field agree on the local units of the middle field.** -/
theorem unitsFamily_map_adicUnitsComap_restrict (w : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (c : Additive ((primeUnder (𝓞 F) w).adicCompletion F)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.map σ w (adicUnitsComap F w c)
      = adicUnitsComap F (σ • w)
          (famCast (fun p : HeightOneSpectrum (𝓞 F) => Additive (p.adicCompletion F)ˣ)
            (primeUnder_smul F σ w).symm
            ((adicRingFamily (k := k) (K := F)).unitsFamily.map
              (AlgEquiv.restrictNormalHom F σ) (primeUnder (𝓞 F) w) c)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_adicUnitsComap]
  show adicCompletionGalEquiv w σ
      ((Additive.toMul (adicUnitsComap F w c) : (w.adicCompletion K)ˣ) : w.adicCompletion K)
    = algebraMap ((primeUnder (𝓞 F) (σ • w)).adicCompletion F) ((σ • w).adicCompletion K)
        (ringCast (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletion F)
          (primeUnder_smul F σ w).symm
          (adicCompletionGalEquiv (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
            ((Additive.toMul c : ((primeUnder (𝓞 F) w).adicCompletion F)ˣ) :
              (primeUnder (𝓞 F) w).adicCompletion F)))
  rw [coe_adicUnitsComap, algebraMap_adicCompletion F w, algebraMap_adicCompletion F (σ • w)]
  exact adicCompletionGalEquiv_adicCompletionComap_restrict F w σ _

/-! ### The infinite places -/

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The place of the middle field below a moved place is the moved place below**: moving a place
and restricting it is restricting it and moving it by the restricted automorphism. -/
theorem comap_smul_algebraMap (σ : Gal(K/k)) (w : InfinitePlace K) :
    (σ • w).comap (algebraMap F K)
      = AlgEquiv.restrictNormalHom F σ • w.comap (algebraMap F K) := by
  refine Subtype.ext (AbsoluteValue.ext fun y => ?_)
  show w (σ.symm (algebraMap F K y)) = w (algebraMap F K ((AlgEquiv.restrictNormalHom F σ).symm y))
  rw [show (AlgEquiv.restrictNormalHom F σ).symm = AlgEquiv.restrictNormalHom F σ⁻¹ from
      (map_inv (AlgEquiv.restrictNormalHom F) σ).symm,
    algebraMap_restrictNormalHom F]
  rfl

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The isomorphisms of completions at the infinite places attached to an automorphism and to its
restriction to the middle field agree on the completion of the middle field**: both sides are
continuous and agree on the dense image of the middle field. -/
theorem infiniteCompletionGalEquiv_infiniteCompletionComap_restrict (w : InfinitePlace K)
    (σ : Gal(K/k)) (c : (w.comap (algebraMap F K)).Completion) :
    infiniteCompletionGalEquiv w σ (infiniteCompletionComap F w c)
      = infiniteCompletionComap F (σ • w)
          (ringCast (fun u : InfinitePlace F => u.Completion) (comap_smul_algebraMap F σ w).symm
            (infiniteCompletionGalEquiv (w.comap (algebraMap F K))
              (AlgEquiv.restrictNormalHom F σ) c)) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_infiniteCompletionGalEquiv w σ).comp (continuous_infiniteCompletionComap F w))
      ((continuous_infiniteCompletionComap F (σ • w)).comp
        ((continuous_ringCast _ _).comp
          (continuous_infiniteCompletionGalEquiv (w.comap (algebraMap F K))
            (AlgEquiv.restrictNormalHom F σ))))
  · intro x
    set y : F := WithAbs.equiv (w.comap (algebraMap F K)).1 x with hy
    have h1 : infiniteCompletionComap F w (infiniteCoe y (w.comap (algebraMap F K)))
        = infiniteCoe (algebraMap F K y) w := infiniteCompletionComap_coe F w _
    have h2 : infiniteCompletionComap F (σ • w)
          (infiniteCoe (AlgEquiv.restrictNormalHom F σ y) ((σ • w).comap (algebraMap F K)))
        = infiniteCoe (algebraMap F K (AlgEquiv.restrictNormalHom F σ y)) (σ • w) :=
      infiniteCompletionComap_coe F (σ • w) _
    show infiniteCompletionGalEquiv w σ
        (infiniteCompletionComap F w (infiniteCoe y (w.comap (algebraMap F K))))
      = infiniteCompletionComap F (σ • w)
          (ringCast _ (comap_smul_algebraMap F σ w).symm
            (infiniteCompletionGalEquiv (w.comap (algebraMap F K))
              (AlgEquiv.restrictNormalHom F σ) (infiniteCoe y (w.comap (algebraMap F K)))))
    rw [h1, infiniteCompletionGalEquiv_infiniteCoe, infiniteCompletionGalEquiv_infiniteCoe,
      ringCast_infiniteCoe, h2, algebraMap_restrictNormalHom F]

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The transports of the local units at the infinite places attached to an automorphism and to
its restriction to the middle field agree on the local units of the middle field.** -/
theorem unitsFamily_map_infiniteUnitsComap_restrict (w : InfinitePlace K) (σ : Gal(K/k))
    (c : Additive ((w.comap (algebraMap F K)).Completion)ˣ) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.map σ w (infiniteUnitsComap F w c)
      = infiniteUnitsComap F (σ • w)
          (famCast (fun u : InfinitePlace F => Additive (u.Completion)ˣ)
            (comap_smul_algebraMap F σ w).symm
            ((infiniteRingFamily (k := k) (K := F)).unitsFamily.map
              (AlgEquiv.restrictNormalHom F σ) (w.comap (algebraMap F K)) c)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_infiniteUnitsComap]
  show infiniteCompletionGalEquiv w σ
      ((Additive.toMul (infiniteUnitsComap F w c) : (w.Completion)ˣ) : w.Completion)
    = algebraMap (((σ • w).comap (algebraMap F K)).Completion) ((σ • w).Completion)
        (ringCast (fun u : InfinitePlace F => u.Completion) (comap_smul_algebraMap F σ w).symm
          (infiniteCompletionGalEquiv (w.comap (algebraMap F K)) (AlgEquiv.restrictNormalHom F σ)
            ((Additive.toMul c : ((w.comap (algebraMap F K)).Completion)ˣ) :
              (w.comap (algebraMap F K)).Completion)))
  rw [coe_infiniteUnitsComap, algebraMap_infiniteCompletion F w,
    algebraMap_infiniteCompletion F (σ • w)]
  exact infiniteCompletionGalEquiv_infiniteCompletionComap_restrict F w σ _

end PlaceRestrict

end InverseGalois.CFT
