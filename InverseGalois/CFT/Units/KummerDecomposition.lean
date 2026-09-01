/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerRes
import InverseGalois.CFT.Units.InfiniteDecomposition

/-!
# A unit of a number field that is locally a power is a power

For a number field containing a primitive root of unity of the relevant order, the first cohomology
of the absolute Galois group with coefficients in those roots of unity has no class that dies on
every decomposition subgroup.  Under the Kummer isomorphism that says exactly that a unit which
becomes a power in the decomposition field at every nonzero prime is already a power in the base.

Nothing new is needed for it.  A cocycle for a trivial action is a homomorphism, and a
homomorphism of the Galois group which kills a finite Galois level and every decomposition subgroup
is trivial, because the group acts transitively on the primes above a prime of that level; that is
the vanishing of the everywhere locally trivial classes in degree one.  The Kummer isomorphism
turns it into a statement about radicals.

The statement is not in conflict with the exceptional case of the theorem of Grunwald and Wang,
which needs the base to *lack* a primitive root of unity of the relevant order.

## Main results

* `InverseGalois.CFT.IsKummerData.localPowers_finiteDecompositionSubgroups`: **the units of a
  number field that are powers in the decomposition field at every nonzero prime are exactly the
  powers.**
* `InverseGalois.CFT.exists_pow_eq_of_forall_isPrime`: **a unit of a number field with a primitive
  `n`-th root of unity which has an `n`-th root fixed by the stabiliser of every nonzero prime of
  an algebraic closure is an `n`-th power.**
* `InverseGalois.CFT.kummerEquivAlgebraicClosure`: the Kummer isomorphism over an algebraic
  closure, between the units of the base modulo `n`-th powers and the first cohomology of the
  absolute Galois group with coefficients in the `n`-th roots of unity.

## Tags

number field, Kummer theory, decomposition group, local-global principle, Galois cohomology
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology MulAction NumberField

open scoped Pointwise

/-! ### The Kummer isomorphism over an algebraic closure -/

section Closure

variable {k : Type*} [Field k] {n : ℕ} [NeZero n]

/-- **The `n`-th roots of unity of a field with a primitive one are Kummer data for an algebraic
closure.** -/
theorem isKummerData_algebraicClosure {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    letI := rootsOfUnityTrivialAction (k := k) (Ω := AlgebraicClosure k) (n := n)
    IsKummerData k (AlgebraicClosure k) ↥(rootsOfUnity n k) (rootsOfUnity n k).subtype n :=
  isKummerData_rootsOfUnity hζ fun a => exists_units_pow_eq a

variable [PerfectField k]

/-- **The Kummer isomorphism over an algebraic closure**: for a field with a primitive `n`-th root
of unity, the units modulo the `n`-th powers are the first cohomology of the absolute Galois group
with coefficients in the `n`-th roots of unity. -/
noncomputable def kummerEquivAlgebraicClosure {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    letI := rootsOfUnityTrivialAction (k := k) (Ω := AlgebraicClosure k) (n := n)
    kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range ≃*
      SmoothH1 Gal(AlgebraicClosure k/k) ↥(rootsOfUnity n k) := by
  letI := rootsOfUnityTrivialAction (k := k) (Ω := AlgebraicClosure k) (n := n)
  exact (isKummerData_algebraicClosure hζ).kummerEquiv

end Closure

/-! ### The locally trivial classes vanish -/

section Decomposition

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n]

/-- **The first cohomology with trivial coefficients of the Galois group of an arbitrary Galois
extension of a number field has no class dying on every decomposition subgroup at a nonzero
prime.** -/
theorem sha1_finiteDecompositionSubgroups_eq_bot (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m) :
    sha1 M (finiteDecompositionSubgroups k Ω) = ⊥ :=
  eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (eq_one_of_mem_sha1 htriv z hz)

namespace IsKummerData

/-- **The units of a number field that are `n`-th powers in the decomposition field at every
nonzero prime are exactly the `n`-th powers.** -/
theorem localPowers_finiteDecompositionSubgroups (h : IsKummerData k Ω M ι n) :
    h.localPowers (finiteDecompositionSubgroups k Ω) = (powMonoidHom n : kˣ →* kˣ).range := by
  refine le_antisymm (fun a ha => ?_) (h.range_pow_le_localPowers _)
  rw [← h.ker_kummerHom, MonoidHom.mem_ker]
  exact eq_one_of_mem_sha1 h.smul_eq _ ha

/-- **A unit that is locally an `n`-th power is an `n`-th power.** -/
theorem exists_pow_eq_of_mem_localPowers (h : IsKummerData k Ω M ι n) {a : kˣ}
    (ha : a ∈ h.localPowers (finiteDecompositionSubgroups k Ω)) : ∃ b : kˣ, b ^ n = a := by
  rw [h.localPowers_finiteDecompositionSubgroups, MonoidHom.mem_range] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, hb⟩

end IsKummerData

end Decomposition

/-! ### The statement about radicals -/

section Radical

variable {k : Type*} [Field k] [NumberField k] {n : ℕ} [NeZero n]

/-- **A unit of a number field with a primitive `n`-th root of unity which has an `n`-th root fixed
by the stabiliser of every nonzero prime of an algebraic closure is an `n`-th power.** -/
theorem exists_pow_eq_of_forall_isPrime {ζ : k} (hζ : IsPrimitiveRoot ζ n) {a : kˣ}
    (ha : ∀ P : Ideal (𝓞 (AlgebraicClosure k)), P.IsPrime → P ≠ ⊥ →
      ∃ b ∈ IntermediateField.fixedField (stabilizer Gal(AlgebraicClosure k/k) P),
        b ^ n = algebraMap k (AlgebraicClosure k) (a : k)) :
    ∃ b : kˣ, b ^ n = a := by
  letI := rootsOfUnityTrivialAction (k := k) (Ω := AlgebraicClosure k) (n := n)
  have h := isKummerData_algebraicClosure hζ
  refine h.exists_pow_eq_of_mem_localPowers ?_
  rw [h.mem_localPowers_iff_mem_fixedField]
  rintro D ⟨P, hPp, hPbot, rfl⟩
  exact ha P hPp hPbot

end Radical

end InverseGalois.CFT
