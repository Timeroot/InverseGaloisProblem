/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleFixed
import InverseGalois.CFT.Units.PlaceTower

/-!
# The ideles of a tower of number fields

An idele of the bottom field of a tower may be read in the top field in two ways: directly, or by
first reading it in the middle field.  The two agree, because at each place the comparison is the
transitivity of the inclusions of the completions.

## Main results

* `InverseGalois.CFT.fullIdeleComap_trans`: **the inclusions of the local unit groups of a tower
  compose to the inclusion at the bottom.**
* `InverseGalois.CFT.ideleComap_trans`: **the inclusions of the ideles of a tower compose to the
  inclusion at the bottom.**

## Tags

number field, idele, tower, completion
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField NumberField.InfinitePlace

section IdeleTower

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois F K] [IsGalois k K]

variable (k F K) in
omit [IsGalois k F] [IsGalois F K] [IsGalois k K] in
/-- **The inclusions of the local unit groups of a tower compose to the inclusion at the bottom**:
at each place the comparison is the transitivity of the inclusions of the completions. -/
theorem fullIdeleComap_trans (x : FullIdele k) :
    fullIdeleComap F K (fullIdeleComap k F x) = fullIdeleComap k K x := by
  refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
  · show infiniteUnitsComap F w
        (infiniteUnitsComap k (w.comap (algebraMap F K))
          (x.1 ((w.comap (algebraMap F K)).comap (algebraMap k F))))
      = infiniteUnitsComap k w (x.1 (w.comap (algebraMap k K)))
    rw [← famCast_apply_section (fun u : InfinitePlace k => Additive (u.Completion)ˣ)
      (comap_comap_algebraMap k F w).symm x.1]
    exact infiniteUnitsComap_trans k F w _
  · show adicUnitsComap F v
        (adicUnitsComap k (primeUnder (𝓞 F) v) (x.2 (primeUnder (𝓞 k) (primeUnder (𝓞 F) v))))
      = adicUnitsComap k v (x.2 (primeUnder (𝓞 k) v))
    rw [← famCast_apply_section (fun p : HeightOneSpectrum (𝓞 k) => Additive (p.adicCompletion k)ˣ)
      (primeUnder_primeUnder k F v).symm x.2]
    exact adicUnitsComap_trans k F v _

variable (k F K) in
/-- **The inclusions of the ideles of a tower compose to the inclusion at the bottom.** -/
theorem ideleComap_trans (y : ↥(idele k)) :
    ideleComap F K (ideleComap k F y) = ideleComap k K y :=
  Subtype.ext (fullIdeleComap_trans k F K (y : FullIdele k))

end IdeleTower

end InverseGalois.CFT
