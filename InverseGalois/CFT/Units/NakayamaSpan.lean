/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.BaseTateSylow

/-!
# When the comparison of Tate and Nakayama, together with the ideles, spans

The everywhere locally trivial classes of the units of a Galois extension of number fields,
tensored with coefficients killed by a prime, are exactly the classes the comparison of Tate and
Nakayama produces from the coefficients three degrees lower, as soon as one span holds: over a
Sylow subgroup for the prime, the classes the comparison produces together with the classes coming
from the ideles fill the complete cohomology of the idele classes tensored with the coefficients.

That span is a statement about the extension, not about the coefficients: it says that the failure
of the comparison to be surjective is entirely accounted for by the places.  For coefficients that
are free as abelian groups the comparison is surjective outright and the span is automatic, which
is why the statement for a lattice needs no hypothesis at all.  For coefficients killed by a prime
the comparison acquires an error term, and the span is the assertion that the places already carry
that error.

This file names the span and records the statement it yields.  Naming it separates the part of the
theory that the general machinery of a class formation supplies from the part that is genuinely
about the arithmetic of the extension, and lets the statement be used wherever it is needed without
carrying a Sylow subgroup and a choice of coefficients through every intermediate result.

## Main definitions

* `InverseGalois.CFT.HasIdeleClassNakayamaSpan`: **the comparison of Tate and Nakayama over a Sylow
  subgroup, together with the classes coming from the ideles, spans the complete cohomology of the
  idele classes tensored with any coefficients killed by the prime.**

## Main results

* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_span`: **the everywhere locally trivial classes
  of the units tensored with coefficients killed by a prime are exactly the classes the comparison
  of Tate and Nakayama produces**, whenever the span holds.

## Tags

number field, idele class group, Tate-Nakayama, Sylow subgroup, locally trivial
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (p : ℕ) [Fact p.Prime]

/-- **The comparison of Tate and Nakayama for the idele class group and the fundamental class, read
over a Sylow subgroup for a prime, together with the classes coming from the ideles, spans the
complete cohomology of the idele classes tensored with coefficients killed by that prime.**  The
comparison is surjective on coefficients that are free as abelian groups; on coefficients killed by
a prime it need not be, and the span says the shortfall comes from the places. -/
def HasIdeleClassNakayamaSpan : Prop :=
  ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
    LinearMap.range (resTateNakayamaTwoMap (P : Subgroup Gal(K/k)) (ideleClassRep k K)
        (baseFundamentalClass k K) W n)
      ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
        (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤

variable {k K p}

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**,
whenever the comparison of Tate and Nakayama over a Sylow subgroup for the prime spans together
with the classes coming from the ideles.  A Sylow subgroup exists because the Galois group is
finite, so the span may be applied to any one of them. -/
theorem range_shaTorusPTorsionMap_of_span (h : HasIdeleClassNakayamaSpan k K p)
    (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0) (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  obtain ⟨P⟩ : Nonempty (Sylow p Gal(K/k)) := inferInstance
  exact range_shaTorusPTorsionMap_of_sylow_nakayama k K W hW P n (h W hW P n)

end

end InverseGalois.CFT
