/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PGroupCompositum
import InverseGalois.CFT.Scholz.CorrectingCharacter
import InverseGalois.CFT.Scholz.CorrectingSubfield
import InverseGalois.CFT.Scholz.InertiaRankOne
import InverseGalois.CFT.Scholz.PGroupSolution

/-!
# A solution ramifying no more than the problem it solves

The central step of the Scholz–Reichardt induction solves the embedding problem but says nothing
about where the solution ramifies: the field it produces can pick up new ramified primes, and the
induction cannot afford them.  Those primes are few, they are known — the residue characteristic
and the primes congruent to one modulo it — and each of them carries a cyclic extension of the
rationals of degree the residue characteristic, ramified there and nowhere else, which cancels the
unwanted ramification when the solution is twisted by it.

Adjoining all of those cyclic extensions at once keeps the degree a power of the residue
characteristic, so the twists can be performed one after another inside a single field; and cutting
the twisted solution down to the field it defines returns a solution of the original embedding
problem whose field ramifies only where the field the problem is posed over already ramified.

## Main results

* `InverseGalois.CFT.exists_galEquiv_ramifiedSet_subset`: **a central Frattini embedding problem
  with kernel of prime order over a field satisfying the level condition has a solution which
  ramifies nowhere outside the ramified set of that field.**

## Tags

embedding problem, Scholz condition, ramified prime, twist, `p`-group
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

open IntermediateField

/-! ### The ramified set of the field cut out by a solution -/

section RamifiedSet

variable {L : Type*} [Field L] [CharZero L] {G H : Type*} [Group G] [Group H]

/-- The field cut out by an injective solution is the whole field. -/
theorem ramifiedSet_fixedField_ker_of_injective {E : Type*} [Field E] [NumberField E]
    [IsGalois ℚ E] (ψ : Gal(E/ℚ) →* G) (hψ : Function.Injective ψ) :
    ramifiedSet ↥(IntermediateField.fixedField ψ.ker) = ramifiedSet E := by
  rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ, IntermediateField.fixedField_bot]
  exact ramifiedSet_eq_of_ringEquiv (IntermediateField.topEquiv (F := ℚ) (E := E)).toRingEquiv

/-- The field cut out by the composite of a solution with the surjection it lifts is the field the
embedding problem is posed over. -/
theorem ramifiedSet_fixedField_ker_comp {A E : IntermediateField ℚ L} (hAE : A ≤ E)
    [NumberField ↥A] [IsGalois ℚ ↥A] [NumberField ↥E] [IsGalois ℚ ↥E] {f : G →* H}
    (ψ : Gal(↥E/ℚ) →* G) (e : Gal(↥A/ℚ) ≃* H) (hcomp : ∀ τ, f (ψ τ) = e (galRestrictLE hAE τ)) :
    ramifiedSet ↥(IntermediateField.fixedField (f.comp ψ).ker) = ramifiedSet ↥A := by
  have hker : (f.comp ψ).ker = (galRestrictLE hAE).ker := by
    ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, hcomp σ,
      EmbeddingLike.map_eq_one_iff]
  rw [hker, fixedField_ker_galRestrictLE hAE, ramifiedSet_restrict]

end RamifiedSet

/-! ### The corrected solution -/

variable {ℓ : ℕ}

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of prime order over a field satisfying the
level condition has a solution ramifying nowhere outside the ramified set of that field.**  The
solution produced by the central step is enlarged by the cyclic extensions of degree `ℓ` attached to
the finitely many primes at which it ramifies unnecessarily, which leaves the degree a power of `ℓ`;
inside that enlargement the unwanted primes are removed one at a time by twisting, and the twisted
solution is cut down to the field it defines. -/
theorem exists_galEquiv_ramifiedSet_subset (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hrank : IsInertiaRankOneAt ℓ) {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (hpg : IsPGroup ℓ G)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = ℓ)
    (hHdvd : Nat.card H ∣ ℓ ^ N) (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A]
    [NumberField ↥A] (hsch : IsScholz ℓ (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* H) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAL : A ≤ L), NumberField ↥L ∧
      IsGalois ℚ ↥L ∧ ramifiedSet ↥L ⊆ ramifiedSet ↥A ∧
      ∃ ψ : Gal(↥L/ℚ) ≃* G, ∀ τ, f (ψ τ) = e (galRestrictLE hAL τ) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the solution of the embedding problem, with Galois group the group to be realised
  obtain ⟨L₀, hAL₀, hNF₀, hGal₀, ψ₀, hcomp₀⟩ :=
    exists_galEquiv_of_centralStep hℓ hodd hf hpg hZ hfr hcard hHdvd A hsch e
  haveI := hNF₀
  haveI := hGal₀
  have hpg₀ : IsPGroup ℓ Gal(↥L₀/ℚ) := hpg.of_equiv ψ₀.symm
  -- the primes at which it ramifies unnecessarily
  set S : Set ℕ := ramifiedSet ↥A with hSdef
  set T : Finset ℕ :=
    (finite_ramifiedSet ↥L₀).toFinset \ (finite_ramifiedSet ↥A).toFinset with hTdef
  have hTmem : ∀ p ∈ T, p ∈ ramifiedSet ↥L₀ ∧ p ∉ S := by
    intro p hp
    rw [hTdef, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    exact hp
  have hclass : ∀ p ∈ T, p.Prime ∧ (p = ℓ ∨ ℓ ∣ p - 1) := by
    intro p hp
    obtain ⟨hmem, hnot⟩ := hTmem p hp
    refine ⟨hmem.1, eq_or_dvd_sub_one_of_mem_ramifiedSet hℓ hpg₀ hZ hcard ψ₀.toMonoidHom ?_ ?_⟩
    · rw [ramifiedSet_fixedField_ker_of_injective ψ₀.toMonoidHom ψ₀.injective]
      exact hmem
    · rw [ramifiedSet_fixedField_ker_comp hAL₀ ψ₀.toMonoidHom e hcomp₀]
      exact hnot
  -- the cyclic extension of degree `ℓ` correcting each of them
  have hex : ∀ q : {q // q ∈ T}, ∃ Dq : IntermediateField ℚ (AlgebraicClosure ℚ),
      ∃ _ : NumberField ↥Dq, IsGalois ℚ ↥Dq ∧ IsPGroup ℓ Gal(↥Dq/ℚ) ∧
        ramifiedSet ↥Dq ⊆ {q.1} ∧
        (∀ (Q : Ideal (𝓞 ↥Dq)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q.1 : ℤ)})),
          Ideal.inertia Gal(↥Dq/ℚ) Q = ⊤) ∧ ∃ χ : Gal(↥Dq/ℚ) →* G, χ.range = f.ker := by
    intro q
    obtain ⟨hq, hcond⟩ := hclass q.1 q.2
    exact exists_totallyRamified_hom_range_eq hℓ hq hcond f.ker hcard
  choose D hDNF hDgal hDpg hDram hDtot χ hχrange using hex
  haveI : ∀ q, NumberField ↥(D q) := hDNF
  haveI : ∀ q, IsGalois ℚ ↥(D q) := hDgal
  -- the field over which all the twists take place
  set M : IntermediateField ℚ (AlgebraicClosure ℚ) := L₀ ⊔ Finset.univ.sup D with hMdef
  haveI : FiniteDimensional ℚ ↥(Finset.univ.sup D) := finiteDimensional_finsetSup D Finset.univ
  haveI : Normal ℚ ↥(Finset.univ.sup D) := normal_finsetSup D Finset.univ
  haveI : FiniteDimensional ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : Normal ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := ⟨⟩
  have hpgM : IsPGroup ℓ Gal(↥M/ℚ) := by
    rw [hMdef]
    exact isPGroup_sup L₀ (Finset.univ.sup D) hpg₀ (isPGroup_finsetSup D hDpg Finset.univ)
  have hL₀M : L₀ ≤ M := by rw [hMdef]; exact le_sup_left
  have hAM : A ≤ M := hAL₀.trans hL₀M
  have hDM : ∀ q, D q ≤ M := by
    intro q
    rw [hMdef]
    exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ q))
  -- the solution, read over that field
  set Ψ : Gal(↥M/ℚ) →* G := ψ₀.toMonoidHom.comp (galRestrictLE hL₀M) with hΨdef
  have hΨsurj : Function.Surjective Ψ := ψ₀.surjective.comp (galRestrictLE_surjective hL₀M)
  have hcompM : ∀ σ, f (Ψ σ) = e (galRestrictLE hAM σ) := by
    intro σ
    rw [hΨdef]
    exact (hcomp₀ (galRestrictLE hL₀M σ)).trans
      (congrArg e (galRestrictLE_galRestrictLE hAL₀ hL₀M σ))
  have hfixΨ : ramifiedSet ↥(IntermediateField.fixedField Ψ.ker) = ramifiedSet ↥L₀ := by
    have hker : Ψ.ker = (galRestrictLE hL₀M).ker := by
      rw [hΨdef]
      ext σ
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]
    rw [hker, fixedField_ker_galRestrictLE hL₀M, ramifiedSet_restrict]
  have hfixcomp : ramifiedSet ↥(IntermediateField.fixedField (f.comp Ψ).ker) = ramifiedSet ↥A :=
    ramifiedSet_fixedField_ker_comp hAM Ψ e hcompM
  -- every unwanted prime has a correcting character available
  have hchar : ∀ p ∈ T, p ∉ S → HasCorrectingChar ↥M f p := by
    intro p hpT _
    obtain ⟨hp, -⟩ := hclass p hpT
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hp
    obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
    haveI := hPp
    haveI := hPo
    exact hasCorrectingChar_of_le (hDM ⟨p, hpT⟩) hp (hDram ⟨p, hpT⟩) (hDtot ⟨p, hpT⟩)
      (χ ⟨p, hpT⟩) (hχrange ⟨p, hpT⟩) P
      (hasInertiaCancellation_of_isPGroup hℓ hrank hpgM hp P f.ker hcard)
  have hπ : ∀ p ∈ T, p ∉ S → p ∉ ramifiedSet ↥(IntermediateField.fixedField (f.comp Ψ).ker) := by
    intro p _ hpS
    rw [hfixcomp]
    exact hpS
  have hcharΨ : ∀ p ∈ T, p ∉ S → HasCorrectingCharAt ↥M f p Ψ := fun p hpT hpS =>
    hasCorrectingCharAt_of_hasCorrectingChar (hclass p hpT).1 (hchar p hpT hpS) (hπ p hpT hpS)
  have hsub : ramifiedSet ↥(IntermediateField.fixedField Ψ.ker) \ S ⊆ ↑T := by
    rw [hfixΨ]
    intro q hq
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Set.Finite.mem_toFinset _ |>.mpr hq.1, ?_⟩)
    exact fun h => hq.2 ((Set.Finite.mem_toFinset _).mp h)
  obtain ⟨ψ', hψ'surj, hψ'comp, hψ'ram⟩ :=
    exists_twist_ramifiedSet_inter hf hfr hZ S T (fun q hq => (hclass q hq).1) Ψ hΨsurj hcharΨ hπ
      hsub
  -- the field cut out by the twisted solution
  have hker' : ψ'.ker ≤ (galRestrictLE hAM).ker := by
    intro σ hσ
    have h1 : e (galRestrictLE hAM σ) = 1 := by
      rw [← hcompM σ, ← MonoidHom.comp_apply, ← hψ'comp, MonoidHom.comp_apply,
        MonoidHom.mem_ker.mp hσ, map_one]
    exact MonoidHom.mem_ker.mpr (by simpa using h1)
  have hAL' : A ≤ cutField ψ' := le_cutField ψ' hAM hker'
  haveI : FiniteDimensional ℚ ↥(cutField ψ') :=
    (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField ψ'.ker)).toLinearEquiv.finiteDimensional
  haveI : NumberField ↥(cutField ψ') := ⟨⟩
  haveI : IsGalois ℚ ↥(cutField ψ') := ⟨⟩
  have hramL : ramifiedSet ↥(cutField ψ') =
      ramifiedSet ↥(IntermediateField.fixedField ψ'.ker) := by
    have h1 := ramifiedSet_restrict (cutField_le ψ')
    rw [restrict_cutField_le] at h1
    exact h1.symm
  refine ⟨cutField ψ', hAL', inferInstance, inferInstance, ?_,
    galEquivCutField ψ' hψ'surj, fun τ => ?_⟩
  · rw [hramL]
    exact fun q hq => (hψ'ram hq).2
  · obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (cutField_le ψ') τ
    rw [galEquivCutField_galRestrictLE ψ' hψ'surj σ,
      galRestrictLE_galRestrictLE hAL' (cutField_le ψ') σ, ← MonoidHom.comp_apply, hψ'comp,
      MonoidHom.comp_apply]
    exact hcompM σ

end InverseGalois.CFT
