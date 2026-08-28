/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.AdicFixed
import InverseGalois.CFT.Units.InfiniteFixed

/-!
# Places and completions in a tower of number fields

A tower of number fields induces a tower of places: a place of the top field lies over a place of
the middle field, which lies over a place of the bottom field, and the place so obtained is the
place of the bottom field that the place of the top field lies over directly.  For a finite place
this is the transitivity of the prime below; for an infinite place it is the transitivity of the
restriction of an absolute value.

The same holds for the completions.  Both ways of getting from the completion of the bottom field
into the completion of the top field extend the inclusion of the bottom field into the top field,
which is dense, so they agree.  Passing to unit groups gives the statement in the form the ideles
need.

Because the place below is only equal to, not the same as, the place obtained in two steps, the
comparison has to be stated with a transport of the completion along that equality; the transports
are the ones already used for the Galois action.

## Main results

* `InverseGalois.CFT.primeUnder_primeUnder`: **the prime below a prime below is the prime below.**
* `InverseGalois.CFT.comap_comap_algebraMap`: **the place below a place below is the place below.**
* `InverseGalois.CFT.adicCompletionComap_trans`: **the inclusions of the completions at the finite
  places compose to the inclusion of the completion at the bottom.**
* `InverseGalois.CFT.infiniteCompletionComap_trans`: **the inclusions of the completions at the
  infinite places compose to the inclusion of the completion at the bottom.**
* `InverseGalois.CFT.adicUnitsComap_trans`, `InverseGalois.CFT.infiniteUnitsComap_trans`: the same
  for the local unit groups.

## Tags

number field, tower, place, completion, prime below
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField NumberField.InfinitePlace

section PlaceTower

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]

/-! ### The finite places of a tower -/

variable (k F) in
omit [NumberField k] in
/-- **The prime below a prime below is the prime below**: the two contractions compose to the
contraction along the composite. -/
theorem primeUnder_primeUnder (w : HeightOneSpectrum (𝓞 K)) :
    primeUnder (𝓞 k) (primeUnder (𝓞 F) w) = primeUnder (𝓞 k) w :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 k) (B := 𝓞 F) w.asIdeal)

variable (k F) in
/-- **The inclusions of the completions at the finite places of a tower compose to the inclusion of
the completion at the bottom**: all three maps extend the inclusion of the bottom field, whose image
is dense. -/
theorem adicCompletionComap_trans (w : HeightOneSpectrum (𝓞 K))
    (c : (primeUnder (𝓞 k) w).adicCompletion k) :
    adicCompletionComap (𝓞 F) (k := F) (K := K) w
        (adicCompletionComap (𝓞 k) (k := k) (K := F) (primeUnder (𝓞 F) w)
          (ringCast (fun p : HeightOneSpectrum (𝓞 k) => p.adicCompletion k)
            (primeUnder_primeUnder k F w).symm c))
      = adicCompletionComap (𝓞 k) (k := k) (K := K) w c := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      (((continuous_adicCompletionComap (𝓞 F) (k := F) (K := K) w).comp
        (continuous_adicCompletionComap (𝓞 k) (k := k) (K := F) (primeUnder (𝓞 F) w))).comp
          (continuous_ringCast _ _))
      (continuous_adicCompletionComap (𝓞 k) (k := k) (K := K) w)
  · intro x
    set y : k := WithVal.equiv ((primeUnder (𝓞 k) w).valuation k) x with hy
    have h1 : adicCompletionComap (𝓞 k) (k := k) (K := F) (primeUnder (𝓞 F) w)
          (adicCoe y (primeUnder (𝓞 k) (primeUnder (𝓞 F) w)))
        = adicCoe (algebraMap k F y) (primeUnder (𝓞 F) w) :=
      adicCompletionComap_coe (𝓞 k) (primeUnder (𝓞 F) w) y
    have h2 : adicCompletionComap (𝓞 F) (k := F) (K := K) w
          (adicCoe (algebraMap k F y) (primeUnder (𝓞 F) w))
        = adicCoe (algebraMap F K (algebraMap k F y)) w :=
      adicCompletionComap_coe (𝓞 F) w (algebraMap k F y)
    have h3 : adicCompletionComap (𝓞 k) (k := k) (K := K) w (adicCoe y (primeUnder (𝓞 k) w))
        = adicCoe (algebraMap k K y) w := adicCompletionComap_coe (𝓞 k) w y
    show adicCompletionComap (𝓞 F) (k := F) (K := K) w
        (adicCompletionComap (𝓞 k) (k := k) (K := F) (primeUnder (𝓞 F) w)
          (ringCast _ (primeUnder_primeUnder k F w).symm (adicCoe y (primeUnder (𝓞 k) w))))
      = adicCompletionComap (𝓞 k) (k := k) (K := K) w (adicCoe y (primeUnder (𝓞 k) w))
    rw [ringCast_adicCoe, h1, h2, h3, ← IsScalarTower.algebraMap_apply k F K]

variable (k F) in
/-- **The inclusions of the local unit groups at the finite places of a tower compose to the
inclusion of the local units at the bottom.** -/
theorem adicUnitsComap_trans (w : HeightOneSpectrum (𝓞 K))
    (u : Additive ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    adicUnitsComap F w
        (adicUnitsComap k (primeUnder (𝓞 F) w)
          (famCast (fun p : HeightOneSpectrum (𝓞 k) => Additive (p.adicCompletion k)ˣ)
            (primeUnder_primeUnder k F w).symm u))
      = adicUnitsComap k w u := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_adicUnitsComap, coe_adicUnitsComap, coe_adicUnitsComap]
  show adicCompletionComap (𝓞 F) (k := F) (K := K) w
      (adicCompletionComap (𝓞 k) (k := k) (K := F) (primeUnder (𝓞 F) w)
        (ringCast (fun p : HeightOneSpectrum (𝓞 k) => p.adicCompletion k)
          (primeUnder_primeUnder k F w).symm
          ((Additive.toMul u : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
            (primeUnder (𝓞 k) w).adicCompletion k)))
    = adicCompletionComap (𝓞 k) (k := k) (K := K) w
        ((Additive.toMul u : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
          (primeUnder (𝓞 k) w).adicCompletion k)
  exact adicCompletionComap_trans k F w _

/-! ### The infinite places of a tower -/

variable (k F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The place below a place below is the place below**: the two restrictions compose to the
restriction along the composite. -/
theorem comap_comap_algebraMap (w : InfinitePlace K) :
    (w.comap (algebraMap F K)).comap (algebraMap k F) = w.comap (algebraMap k K) := by
  rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]

variable (k F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The inclusions of the completions at the infinite places of a tower compose to the inclusion
of the completion at the bottom**: all three maps extend the inclusion of the bottom field, whose
image is dense. -/
theorem infiniteCompletionComap_trans (w : InfinitePlace K)
    (c : (w.comap (algebraMap k K)).Completion) :
    infiniteCompletionComap F w
        (infiniteCompletionComap k (w.comap (algebraMap F K))
          (ringCast (fun u : InfinitePlace k => u.Completion)
            (comap_comap_algebraMap k F w).symm c))
      = infiniteCompletionComap k w c := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      (((continuous_infiniteCompletionComap F w).comp
        (continuous_infiniteCompletionComap k (w.comap (algebraMap F K)))).comp
          (continuous_ringCast _ _))
      (continuous_infiniteCompletionComap k w)
  · intro x
    set y : k := WithAbs.equiv (w.comap (algebraMap k K)).1 x with hy
    have h1 : infiniteCompletionComap k (w.comap (algebraMap F K))
          (infiniteCoe y ((w.comap (algebraMap F K)).comap (algebraMap k F)))
        = infiniteCoe (algebraMap k F y) (w.comap (algebraMap F K)) :=
      infiniteCompletionComap_coe k (w.comap (algebraMap F K)) _
    have h2 : infiniteCompletionComap F w
          (infiniteCoe (algebraMap k F y) (w.comap (algebraMap F K)))
        = infiniteCoe (algebraMap F K (algebraMap k F y)) w :=
      infiniteCompletionComap_coe F w _
    have h3 : infiniteCompletionComap k w (infiniteCoe y (w.comap (algebraMap k K)))
        = infiniteCoe (algebraMap k K y) w := infiniteCompletionComap_coe k w _
    show infiniteCompletionComap F w
        (infiniteCompletionComap k (w.comap (algebraMap F K))
          (ringCast _ (comap_comap_algebraMap k F w).symm
            (infiniteCoe y (w.comap (algebraMap k K)))))
      = infiniteCompletionComap k w (infiniteCoe y (w.comap (algebraMap k K)))
    rw [ringCast_infiniteCoe, h1, h2, h3, ← IsScalarTower.algebraMap_apply k F K]

variable (k F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The inclusions of the local unit groups at the infinite places of a tower compose to the
inclusion of the local units at the bottom.** -/
theorem infiniteUnitsComap_trans (w : InfinitePlace K)
    (u : Additive ((w.comap (algebraMap k K)).Completion)ˣ) :
    infiniteUnitsComap F w
        (infiniteUnitsComap k (w.comap (algebraMap F K))
          (famCast (fun v : InfinitePlace k => Additive (v.Completion)ˣ)
            (comap_comap_algebraMap k F w).symm u))
      = infiniteUnitsComap k w u := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_infiniteUnitsComap, coe_infiniteUnitsComap, coe_infiniteUnitsComap]
  show infiniteCompletionComap F w
      (infiniteCompletionComap k (w.comap (algebraMap F K))
        (ringCast (fun v : InfinitePlace k => v.Completion)
          (comap_comap_algebraMap k F w).symm
          ((Additive.toMul u : ((w.comap (algebraMap k K)).Completion)ˣ) :
            (w.comap (algebraMap k K)).Completion)))
    = infiniteCompletionComap k w
        ((Additive.toMul u : ((w.comap (algebraMap k K)).Completion)ˣ) :
          (w.comap (algebraMap k K)).Completion)
  exact infiniteCompletionComap_trans k F w _

end PlaceTower

end InverseGalois.CFT
