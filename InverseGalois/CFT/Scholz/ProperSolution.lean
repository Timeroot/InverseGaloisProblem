/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CentralEmbedding
import InverseGalois.CFT.Kummer.RootsInBase
import InverseGalois.CFT.Scholz.BaseChange
import InverseGalois.CFT.Scholz.CompositumTransport

/-!
# Solving the central step over the cyclotomic base

The Scholz-Reichardt induction is handed a central Frattini embedding problem with kernel of prime
order `ℓ` and a field `A` of `ℓ`-power degree satisfying Serre's condition.  The local-global
criterion for such a problem needs a primitive `ℓ`-th root of unity in its base field, so it is
applied over the cyclotomic field `ℚ(μ_ℓ)` and to the compositum of `A` with that field.

Everything the criterion asks for is available: the cyclotomic field contains the root of unity by
construction, the kernel is cyclic of order `ℓ` and therefore maps isomorphically onto the `ℓ`-th
roots of unity of the base, and the local hypothesis at the ramified places is the transport of
Serre's condition for `A` recorded in `InverseGalois.CFT.isCyclic_and_exists_hasResidueChar_sup`.

## Main results

* `InverseGalois.CFT.hasProperSolution_cycBaseChange`: **a central Frattini embedding problem with
  kernel of odd prime order `ℓ` is solvable over an extension of the compositum of `A` with the
  `ℓ`-th cyclotomic field**, whenever `A` has `ℓ`-power degree, satisfies Serre's condition one
  level above that power, and its ramified primes split completely in the cyclotomic field.

## Tags

embedding problem, Scholz condition, cyclotomic base change, roots of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain IntermediateField MulAction NumberField InverseGalois.NumberTheory

variable {ℓ : ℕ} [NeZero ℓ]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of odd prime order `ℓ` is solvable over an
extension of the compositum of `A` with the `ℓ`-th cyclotomic field.**  The field `A` is required to
have `ℓ`-power degree, to satisfy Serre's condition one level above that power, and to ramify only
at primes splitting completely in the cyclotomic field; those are exactly the hypotheses under which
the decomposition group at a ramified place of the compositum is cyclic and the residue
characteristic is congruent to one modulo the product of `ℓ` with its order. -/
theorem hasProperSolution_cycBaseChange (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = ℓ) {t : H → G} (ht : ∀ h, f (t h) = h) {M : ℕ}
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hG : IsPGroup ℓ Gal(↥A/ℚ)) (hs : IsScholz ℓ (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ M)
    (hsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥(cycSubfield ℓ) p)
    {π : Gal(↥(cycBaseChange ℓ A)/↥(cycSubfield ℓ)) →* H} (hπ : Function.Surjective π) :
    HasProperSolution (cycBaseChange ℓ A) f π := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsCyclic ↥f.ker := isCyclic_of_prime_card hcard
  obtain ⟨χ, hχinj, -, hχsurj⟩ :=
    exists_monoidHom_units_of_card (k := ↥(cycSubfield ℓ)) (cycRootBase_spec ℓ) hcard
  exact exists_surjective_hom_of_forall_ramified_primeResidue hodd (cycRootBase_spec ℓ) hZ hfr
    hcard hπ hχinj hχsurj ht
    (fun v hnr => isCyclic_and_exists_hasResidueChar_sup A (cycSubfield ℓ) hℓ hG hs hdvd hsplit
      v hnr)

end InverseGalois.CFT
