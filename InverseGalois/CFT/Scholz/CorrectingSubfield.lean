/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaTransport
import InverseGalois.CFT.Scholz.CompositumTransport
import InverseGalois.CFT.Scholz.RamificationControl

/-!
# The correcting character of a subfield of the ambient field

The character correcting the ramification at one prime is built inside an algebraic closure of the
rationals, as a subfield of a cyclotomic field, whereas the solution it corrects lives over a much
larger field.  The two are related by an inclusion of subfields of the same algebraic closure, and
everything the correction needs travels along that inclusion: the copy of the small field inside the
large one ramifies at the same primes, is totally ramified where the small one is, and carries the
same character read through the isomorphism of the two copies.

## Main results

* `InverseGalois.CFT.hasCorrectingChar_of_le`: **a cyclic subfield ramified at a single prime and
  totally ramified there, together with a character with image the kernel of the embedding problem,
  is a correcting character for every larger field containing it.**

## Tags

correcting character, totally ramified, intermediate field, embedding problem
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {L : Type*} [Field L] [CharZero L] {D M : IntermediateField ℚ L}
variable {G H : Type*} [Group G] [Group H] {p : ℕ}

/-- **A subfield ramified at a single prime and totally ramified there provides a correcting
character for any larger field containing it.**  The copy of the subfield inside the larger field is
normal over the rationals, ramifies at the same prime only, is totally ramified there, and its
Galois group is the same, so the character travels with it. -/
theorem hasCorrectingChar_of_le (hDM : D ≤ M) [NumberField ↥M] [IsGalois ℚ ↥M] [NumberField ↥D]
    [IsGalois ℚ ↥D] {f : G →* H} (hp : p.Prime) (hDram : ramifiedSet ↥D ⊆ {p})
    (hDtot : ∀ (Q : Ideal (𝓞 ↥D)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
      Ideal.inertia Gal(↥D/ℚ) Q = ⊤)
    (χ : Gal(↥D/ℚ) →* G) (hrange : χ.range = f.ker) (P : Ideal (𝓞 ↥M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hcanc : HasInertiaCancellation ↥M P f.ker) :
    HasCorrectingChar ↥M f p := by
  haveI : NumberField ↥(IntermediateField.restrict hDM) := ⟨⟩
  haveI : IsGalois ℚ ↥(IntermediateField.restrict hDM) := ⟨⟩
  refine hasCorrectingChar_of_normal hp (IntermediateField.restrict hDM) ?_ ?_
    (χ.comp (AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hDM).symm).toMonoidHom) ?_ P
    hcanc
  · rw [ramifiedSet_restrict]
    exact hDram
  · intro Q hQp hQo
    haveI := hQp
    haveI := hQo
    exact inertia_eq_top_of_algEquiv (IntermediateField.restrict_algEquiv hDM) hp hDtot Q
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hDM).symm).surjective,
      ← MonoidHom.range_eq_map, hrange]

end InverseGalois.CFT
