/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.ChartCompare
import InverseGalois.Rigidity.RET.Genus.SimplyConnected
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# The logarithmic derivation at the far end, place by place

Whether a function on a cover of the line is regular at the far end is a condition read place by
place: the model of the cover over the second chart is a Dedekind domain with the function field of
the cover as its field of fractions, and such a domain is the intersection of its local rings.  So
the question of whether the logarithmic derivation of the line at the far end preserves the
functions regular there is a question about one place at a time, namely whether a function of
non-negative order at a place of the cover over the far end has a logarithmic derivative of
non-negative order there.

## Main results

* `Rigidity.RET.mem_inftyIntegers_iff_ord_nonneg` — a function is regular at the far end exactly
  when it has non-negative order at every place of the model over the second chart.
* `Rigidity.RET.logDeriv_mem_inftyIntegers_of_ord_nonneg` — the logarithmic derivation preserves
  the functions regular at the far end as soon as it does so at every place separately.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

section LogTame

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra k[X] F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [IsScalarTower k k[X] F]
  [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [IsGalois (RatFunc k) F]

omit [CharZero k] [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- **A function is regular at the far end of the line exactly when it has non-negative order at
every place of the cover there.**  The model of the cover over the second chart is a Dedekind
domain with the function field of the cover as its field of fractions, hence the intersection of
its local rings. -/
theorem mem_inftyIntegers_iff_ord_nonneg {y : F} :
    y ∈ inftyIntegers k F ↔
      ∀ v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F), 0 ≤ ord F v y := by
  constructor
  · intro hy v
    have hy' : IsIntegral ↥(inftyChart k) y := mem_inftyIntegers.1 hy
    have hrw : y = algebraMap ↥(integralClosure ↥(inftyChart k) F) F ⟨y, hy'⟩ := rfl
    rw [hrw]
    exact ord_nonneg (K := F) v _
  · intro h
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_ord_nonneg F h
    rw [mem_inftyIntegers, ← hr]
    exact r.2

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- **The logarithmic derivation preserves the functions regular at the far end of the line as
soon as it does so at every place separately.** -/
theorem logDeriv_mem_inftyIntegers_of_ord_nonneg
    (h : ∀ (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F)) (y : F),
      0 ≤ ord F v y → 0 ≤ ord F v (coord k F * lineDeriv k F y))
    {y : F} (hy : y ∈ inftyIntegers k F) :
    coord k F * lineDeriv k F y ∈ inftyIntegers k F :=
  mem_inftyIntegers_iff_ord_nonneg.2 fun v =>
    h v y (mem_inftyIntegers_iff_ord_nonneg.1 hy v)

end LogTame

end Rigidity.RET
