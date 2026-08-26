/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.PGroupInertia
import InverseGalois.CFT.Scholz.RamificationControl

/-!
# The local input of the ramification correction

Removing an unwanted ramified prime from a solution of a central embedding problem with kernel of
order `ℓ` needs one local fact at that prime: the value of the solution on the inertia subgroup is
already a power of the value of the correcting character there.  Away from `ℓ` this is free, because
in an extension of `ℓ`-power degree the inertia subgroup at another prime is cyclic, and on a cyclic
group every homomorphism into a group of order `ℓ` is a power of a surjective one.

At `ℓ` itself the inertia subgroup is an `ℓ`-group and need not be cyclic, so the fact has to be
read off the local field instead: the homomorphisms of order dividing `ℓ` of the inertia subgroup
at `ℓ` form a group of order `ℓ`, one generator of which is the totally ramified cyclotomic
character of conductor `ℓ ^ 2`.  That is the content of the condition recorded here.

## Main definitions

* `InverseGalois.CFT.IsInertiaRankOneAt`: at the prime itself, in an extension of `ℓ`-power degree,
  cancellation on the inertia subgroup against any character reaching a prescribed group of order
  `ℓ`.

## Main results

* `InverseGalois.CFT.hasInertiaCancellation_of_isPGroup`: **in an extension of `ℓ`-power degree the
  cancellation needed by the twist is available at every prime**, from cyclicity away from `ℓ` and
  from the recorded condition at `ℓ`.

## Tags

inertia subgroup, local field, character, embedding problem, Scholz condition
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- **Cancellation on the inertia subgroup at the residue characteristic.**  At a prime of a Galois
number field of `ℓ`-power degree lying over `ℓ`, a homomorphism with values in a group of order `ℓ`
is, on the inertia subgroup, a power of any homomorphism which reaches that whole group there. -/
def IsInertiaRankOneAt (ℓ : ℕ) : Prop :=
  ∀ (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A],
    IsPGroup ℓ Gal(↥A/ℚ) →
    ∀ (P : Ideal (𝓞 ↥A)) [P.IsPrime] [P.LiesOver (Ideal.span {(ℓ : ℤ)})] (G : Type) [Group G]
      (C : Subgroup G), Nat.card ↥C = ℓ → HasInertiaCancellation ↥A P C

variable {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
  {G : Type} [Group G] {ℓ p : ℕ}

/-- **In an extension of `ℓ`-power degree the cancellation needed by the twist is available at
every prime.**  Away from `ℓ` the inertia subgroup is cyclic, and at `ℓ` the cancellation is the
recorded local condition. -/
theorem hasInertiaCancellation_of_isPGroup (hℓ : ℓ.Prime) (hrank : IsInertiaRankOneAt ℓ)
    (hG : IsPGroup ℓ Gal(↥A/ℚ)) (hp : p.Prime) (P : Ideal (𝓞 ↥A)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (C : Subgroup G) (hC : Nat.card ↥C = ℓ) :
    HasInertiaCancellation ↥A P C := by
  by_cases hne : p = ℓ
  · subst hne
    exact hrank A hG P G C hC
  · haveI := isCyclic_inertia_of_isPGroup hℓ hp hne hG P
    exact hasInertiaCancellation_of_isCyclic P C

end InverseGalois.CFT
