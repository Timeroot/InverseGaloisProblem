/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.Scholz.TwistStep

/-!
# Confining the ramification of a solution to a prescribed set of primes

A solution of a central Frattini embedding problem may ramify at primes where it is not wanted.
Each such prime can be removed by a twist, provided a character of the right shape is available
there: one with values in the kernel of the embedding problem, ramified at that prime only, and
surjective on the inertia subgroup there.  The twist changes neither the surjectivity of the
solution nor the map it lifts, and it removes the offending prime without introducing any other.

Removing the primes one at a time therefore terminates, because only finitely many primes ramify
in a number field.  The statement below performs that induction against a finite set of primes
bounding the ones to be removed: the corrected solution ramifies only inside the prescribed set,
and only at primes at which the original solution already ramified.

The hypothesis that the composite with the surjection is unramified at each prime to be removed is
exactly what makes the twist possible — it says that the solution takes values in the kernel on
inertia there, which is where the character reaches everything.  It is stable under twisting,
because a twist does not change that composite.

## Main definitions

* `InverseGalois.CFT.HasCorrectingChar`: the character data available at a prime for the twist.

## Main results

* `InverseGalois.CFT.hasCorrectingChar_of_normal`: a character of a normal subextension ramified
  only at the prime and totally ramified there, with image the whole kernel, inflates to a
  correcting character upstairs.
* `InverseGalois.CFT.exists_twist_ramifiedSet_inter`: **a solution of a central Frattini embedding
  problem can be twisted so that it ramifies only inside a prescribed set of primes**, provided a
  correcting character is available at every prime outside that set at which it might ramify.

## Tags

embedding problem, twist, character, ramified prime, Frattini subgroup
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

open IntermediateField

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M]
variable {G H : Type*} [Group G] [Group H]

/-- **The character data available at a prime for the twist.**  A character of the Galois group
with values in the kernel of the embedding problem, trivial on the inertia subgroup at every other
prime, and mapping the cyclic inertia subgroup at some prime above this one onto the whole
kernel. -/
def HasCorrectingChar (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M] {G H : Type*}
    [Group G] [Group H] (f : G →* H) (p : ℕ) : Prop :=
  ∃ (χ : Gal(M/ℚ) →* G) (P : Ideal (𝓞 M)) (_ : P.IsPrime)
    (_ : P.LiesOver (Ideal.span {(p : ℤ)})) (_ : IsCyclic ↥(Ideal.inertia Gal(M/ℚ) P)),
      χ.range ≤ f.ker ∧
        (∀ q : ℕ, q.Prime → q ≠ p → ∀ Q : Ideal (𝓞 M), Q.IsPrime →
          Q.LiesOver (Ideal.span {(q : ℤ)}) → ∀ σ ∈ Ideal.inertia Gal(M/ℚ) Q, χ σ = 1) ∧
        (Ideal.inertia Gal(M/ℚ) P).map χ = f.ker

/-- **A character of a normal subextension inflates to a correcting character.**  Restriction to a
normal subextension carries inertia onto inertia, so the inflated character is trivial on inertia at
a prime unramified in the subextension and reaches, at the prime where the subextension is totally
ramified, everything the character reaches, namely the whole kernel. -/
theorem hasCorrectingChar_of_normal {f : G →* H} {p : ℕ} (hp : p.Prime) (F : IntermediateField ℚ M)
    [Normal ℚ ↥F] (hFram : ramifiedSet ↥F ⊆ {p})
    (hFtot : ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(p : ℤ)})),
      Ideal.inertia Gal(↥F/ℚ) Q = ⊤)
    (χ : Gal(↥F/ℚ) →* G) (hrange : χ.range = f.ker) (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] [IsCyclic ↥(Ideal.inertia Gal(M/ℚ) P)] :
    HasCorrectingChar M f p := by
  haveI : NumberField ↥F := ⟨⟩
  haveI : IsGalois ℚ ↥F := ⟨⟩
  refine ⟨χ.comp (AlgEquiv.restrictNormalHom ↥F), P, inferInstance, inferInstance, inferInstance,
    ?_, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩
    exact hrange.le ⟨AlgEquiv.restrictNormalHom ↥F σ, rfl⟩
  · intro q hq hqp Q hQp hQo σ hσ
    haveI := hQp
    haveI := hQo
    haveI := liesOver_under_intermediateField (p := q) F Q
    have hmem : AlgEquiv.restrictNormalHom ↥F σ ∈ Ideal.inertia Gal(↥F/ℚ) (Q.under (𝓞 ↥F)) :=
      map_inertia_le_inertia F Q ⟨σ, hσ, rfl⟩
    rw [inertia_eq_bot_of_notMem_ramifiedSet hq _ fun h => hqp (hFram h), Subgroup.mem_bot] at hmem
    rw [MonoidHom.comp_apply, hmem, map_one]
  · haveI := liesOver_under_intermediateField (p := p) F P
    rw [← Subgroup.map_map, map_inertia_eq_inertia F hp P, hFtot _ inferInstance inferInstance,
      ← MonoidHom.range_eq_map, hrange]

variable [Finite G]

/-- **The ramification of a solution of a central Frattini embedding problem can be confined to a
prescribed set of primes.**  The primes to be removed are bounded by a finite set, and the
induction erases them one at a time: at each step a correcting character cancels the solution on
inertia at one prime, which leaves the ramification elsewhere untouched and the lifted map
unchanged, so the bound shrinks by one prime and the process stops. -/
theorem exists_twist_ramifiedSet_inter {f : G →* H} (hf : Function.Surjective f)
    (hfr : f.ker ≤ frattini G) (hZ : f.ker ≤ Subgroup.center G) (S : Set ℕ) :
    ∀ (T : Finset ℕ) (ψ : Gal(M/ℚ) →* G), Function.Surjective ψ →
      (∀ p ∈ T, p ∉ S → HasCorrectingChar M f p) →
      (∀ p ∈ T, p ∉ S → p ∉ ramifiedSet ↥(fixedField (f.comp ψ).ker)) →
      ramifiedSet ↥(fixedField ψ.ker) \ S ⊆ ↑T →
      ∃ ψ' : Gal(M/ℚ) →* G, Function.Surjective ψ' ∧ f.comp ψ' = f.comp ψ ∧
        ramifiedSet ↥(fixedField ψ'.ker) ⊆ ramifiedSet ↥(fixedField ψ.ker) ∩ S := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro ψ hψ hchar hπ hsub
    by_cases hemp : ramifiedSet ↥(fixedField ψ.ker) \ S = ∅
    · have hS := Set.diff_eq_empty.mp hemp
      exact ⟨ψ, hψ, rfl, fun q hq => ⟨hq, hS hq⟩⟩
    obtain ⟨p, hpram, hpS⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    have hpT : p ∈ T := hsub ⟨hpram, hpS⟩
    have hp : p.Prime := hpram.1
    obtain ⟨χ, P, hPp, hPo, hcyc, hχrange, hχram, hχmap⟩ := hchar p hpT hpS
    haveI := hPp
    haveI := hPo
    haveI := hcyc
    have hψP : (Ideal.inertia Gal(M/ℚ) P).map ψ ≤ f.ker := by
      intro x hx
      obtain ⟨σ, hσ, rfl⟩ := hx
      exact MonoidHom.mem_ker.mpr
        (eq_one_of_notMem_ramifiedSet_fixedField_ker (f.comp ψ) hp (hπ p hpT hpS) P hσ)
    obtain ⟨ψ₁, hψ₁, hcomp, hram₁⟩ :=
      exists_twist_ramifiedSet_sdiff hf hfr hZ ψ χ hψ hχrange hp hχram P hχmap hψP
    have hπ₁ : ∀ q ∈ T.erase p, q ∉ S → q ∉ ramifiedSet ↥(fixedField (f.comp ψ₁).ker) := by
      intro q hq hqS
      rw [hcomp]
      exact hπ q (Finset.mem_of_mem_erase hq) hqS
    have hsub₁ : ramifiedSet ↥(fixedField ψ₁.ker) \ S ⊆ ↑(T.erase p) := by
      intro q hq
      have h1 := hram₁ hq.1
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun hqp => h1.2 (Set.mem_singleton_iff.mpr hqp),
          Finset.mem_coe.mp (hsub ⟨h1.1, hq.2⟩)⟩)
    obtain ⟨ψ', hψ', hcomp', hram'⟩ := ih (T.erase p) (Finset.erase_ssubset hpT) ψ₁ hψ₁
      (fun q hq hqS => hchar q (Finset.mem_of_mem_erase hq) hqS) hπ₁ hsub₁
    refine ⟨ψ', hψ', hcomp'.trans hcomp, fun q hq => ?_⟩
    obtain ⟨hq1, hq2⟩ := hram' hq
    exact ⟨(hram₁ hq1).1, hq2⟩

end InverseGalois.CFT
