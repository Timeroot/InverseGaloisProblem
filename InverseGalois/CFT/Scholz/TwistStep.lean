/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.InertiaTwist

/-!
# Removing one unwanted ramified prime from a solution of an embedding problem

A solution of a central embedding problem is a surjection onto the larger group lifting the given
surjection onto the quotient, and the field it cuts out is the fixed field of its kernel.  The
Scholz–Reichardt construction needs solutions whose ramification is prescribed, and produces them by
correcting an arbitrary solution one prime at a time.

The correction at a prime is a pointwise twist by a character with values in the kernel of the
embedding problem, which is central, so that the twist is again a homomorphism, and which is
ramified only at the prime being corrected, so that nothing is disturbed elsewhere.  If the
character is surjective on the inertia subgroup at that prime — for instance because it is totally
ramified there — and the inertia subgroup is cyclic, then a suitable power of the character cancels
the solution on inertia and the twisted solution is unramified at the prime.  Because the kernel
lies in the Frattini subgroup the twist is still surjective, and because the kernel is killed by the
surjection the twist still lifts the same map.

The statement below is arranged so that the whole step is visible at once: the set of primes
ramifying in the field cut out by the twisted solution is contained in the corresponding set for the
original solution with the corrected prime removed.  Iterating over the finitely many unwanted
primes therefore terminates.

## Main results

* `InverseGalois.CFT.exists_twist_ramifiedSet_sdiff`: **a solution of a central embedding problem
  whose kernel lies in the Frattini subgroup may be twisted by a character ramified at a single
  prime into a solution of the same embedding problem which loses that prime and acquires no other
  ramification.**

## Tags

embedding problem, central extension, twist, character, ramified prime, Frattini subgroup
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M] {p : ℕ}
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- **One step of the ramification correction.**  A power of the character cancels the solution on
the inertia subgroup at the prime, which the character reaches in full, so the twisted solution is
unramified there; at every other prime the character is trivial on inertia, so the twisted solution
is trivial on inertia wherever the original one is.  Surjectivity survives because the kernel lies
in the Frattini subgroup, and the lifted map is unchanged because the kernel is killed. -/
theorem exists_twist_ramifiedSet_sdiff {f : G →* H} (hf : Function.Surjective f)
    (hfr : f.ker ≤ frattini G) (hZ : f.ker ≤ Subgroup.center G) (ψ χ : Gal(M/ℚ) →* G)
    (hψ : Function.Surjective ψ) (hχ : χ.range ≤ f.ker) (hp : p.Prime)
    (hχram : ramifiedSet ↥(IntermediateField.fixedField χ.ker) ⊆ {p})
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    [IsCyclic ↥(Ideal.inertia Gal(M/ℚ) P)]
    (hχP : (Ideal.inertia Gal(M/ℚ) P).map χ = f.ker)
    (hψP : (Ideal.inertia Gal(M/ℚ) P).map ψ ≤ f.ker) :
    ∃ ψ' : Gal(M/ℚ) →* G, Function.Surjective ψ' ∧ f.comp ψ' = f.comp ψ ∧
      ramifiedSet ↥(IntermediateField.fixedField ψ'.ker) ⊆
        ramifiedSet ↥(IntermediateField.fixedField ψ.ker) \ {p} := by
  have hχker : ∀ x, χ x ∈ f.ker := fun x => hχ ⟨x, rfl⟩
  have hχcen : ∀ x, χ x ∈ Subgroup.center G := fun x => hZ (hχker x)
  obtain ⟨a, ha⟩ := exists_zpow_notMem_ramifiedSet_fixedField_ker hp ψ χ hχcen P
    (hψP.trans hχP.ge)
  set ψ' := mulCentral ψ (zpowCentral χ hχcen a) (zpowCentral_mem_center χ hχcen a) with hψ'def
  refine ⟨ψ', surjective_mulCentral hf hfr hψ (zpowCentral_mem_center χ hχcen a)
      (fun x => zpowCentral_mem χ hχcen a hχker x),
    comp_mulCentral (zpowCentral_mem_center χ hχcen a)
      (fun x => zpowCentral_mem χ hχcen a hχker x), ?_⟩
  have key : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ ramifiedSet ↥(IntermediateField.fixedField ψ.ker) →
      q ∉ ramifiedSet ↥(IntermediateField.fixedField ψ'.ker) := by
    intro q hq hqp hqψ
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hq
    obtain ⟨⟨Q, hQp, hQo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 M)
    haveI := hQp
    haveI := hQo
    have hqχ : q ∉ ramifiedSet ↥(IntermediateField.fixedField χ.ker) := fun h => hqp (hχram h)
    exact notMem_ramifiedSet_fixedField_ker_mulCentral hq ψ (zpowCentral χ hχcen a)
      (zpowCentral_mem_center χ hχcen a) Q
      (fun σ hσ => eq_one_of_notMem_ramifiedSet_fixedField_ker ψ hq hqψ Q hσ)
      (fun σ hσ => by
        rw [zpowCentral_apply, eq_one_of_notMem_ramifiedSet_fixedField_ker χ hq hqχ Q hσ,
          one_zpow])
  intro q hq
  have hqp : q ≠ p := by
    rintro rfl
    exact ha hq
  refine ⟨?_, fun h => hqp (Set.mem_singleton_iff.mp h)⟩
  by_contra hc
  exact key q hq.1 hqp hc hq

end InverseGalois.CFT
