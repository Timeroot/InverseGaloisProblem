/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE
import InverseGalois.CFT.Scholz.FrobeniusDefect
import InverseGalois.CFT.SplitInertiaPrime

/-!
# Residue degree one at a single prime

Serre's condition `(S_N)` asks for residue degree one at every ramified prime.  The residue
correction of the Scholz–Reichardt construction cares about one prime at a time, so the condition is
recorded here prime by prime: a rational prime has split inertia in a number field when the
decomposition group at a prime above it is its inertia group.  One prime above the rational prime
decides the matter, because the Galois group permutes them transitively.

The condition is read off from a single element: an arithmetic Frobenius generates the decomposition
group modulo inertia, so residue degree one is exactly the statement that an arithmetic Frobenius
lies in the inertia group.  That is the form in which the condition appears in the residue
correction, where a solution of a central embedding problem over a field `L` is seen inside a larger
field `M` and the defect it carries at a ramified prime is measured against the image of the inertia
group.  Since the solution is the restriction map to `L` followed by an isomorphism, the defect
vanishes exactly when the prime has split inertia in `L`; in particular the answer does not depend
on the field `M` the solution is read inside.

## Main definitions

* `InverseGalois.CFT.IsSplitInertiaAt`: a rational prime has residue degree one in a number field.

## Main results

* `InverseGalois.CFT.isSplitInertiaAt_iff_mem_inertia`: **residue degree one at a prime is exactly
  the statement that an arithmetic Frobenius above it lies in the inertia group.**
* `InverseGalois.CFT.mem_map_inertia_iff_isSplitInertiaAt`: **a solution of a central step absorbs
  an arithmetic Frobenius into the image of the inertia group exactly when the prime has split
  inertia in the field the solution lives over.**
* `InverseGalois.CFT.exists_forall_mem_map_inertia_iff`: the same statement, quantified over the
  primes above the rational prime as the residue correction states it.

## Tags

Scholz–Reichardt, residue degree, inertia subgroup, decomposition group, Frobenius
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

set_option synthInstance.maxHeartbeats 1000000

set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

/-! ### Residue degree one at a single prime -/

/-- A rational prime has **split inertia** in a number field when its residue degree there is one,
that is, when the decomposition group at a prime above it is its inertia group. -/
def IsSplitInertiaAt (K : Type*) [Field K] [NumberField K] (q : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) →
    (Ideal.span {(q : ℤ)}).inertiaDeg P = 1

/-- Split inertia is split inertia at every ramified prime. -/
theorem isSplitInertia_iff_forall_isSplitInertiaAt (K : Type*) [Field K] [NumberField K] :
    IsSplitInertia K ↔ ∀ q ∈ ramifiedSet K, IsSplitInertiaAt K q := Iff.rfl

/-- A field with split inertia has split inertia at each of its ramified primes. -/
theorem IsSplitInertia.isSplitInertiaAt {K : Type*} [Field K] [NumberField K]
    (h : IsSplitInertia K) {q : ℕ} (hq : q ∈ ramifiedSet K) : IsSplitInertiaAt K q := h q hq

/-- Split inertia at a prime is an isomorphism invariant, the residue degree at a prime being read
off from the prime under it in the ring of integers. -/
theorem IsSplitInertiaAt.of_ringEquiv {E F : Type*} [Field E] [Field F] [NumberField E]
    [NumberField F] {q : ℕ} (hq : q.Prime) (e : E ≃+* F) (h : IsSplitInertiaAt E q) :
    IsSplitInertiaAt F q := by
  intro P hPprime hPover
  haveI := hPprime
  haveI := isMaximal_span_prime hq
  set f := mapAlgEquivInt e with hf
  set Q : Ideal (𝓞 E) := Ideal.comap (f : 𝓞 E →+* 𝓞 F) P with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQo : Q.LiesOver (Ideal.span {(q : ℤ)}) := by
    refine ⟨?_⟩
    have hunder : Q.under ℤ = P.under ℤ := by
      rw [Ideal.under, Ideal.under, hQ, Ideal.comap_comap]
      congr 1
      exact Subsingleton.elim _ _
    rw [hunder]
    exact hPover.over
  have hdeg := Ideal.inertiaDeg_comap_eq (Ideal.span {(q : ℤ)}) f P
  rw [← hdeg]
  exact h Q hQp hQo

/-! ### Residue degree one and the Frobenius -/

section Galois

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {q : ℕ}

/-- **One prime above `q` decides split inertia at `q`.**  The Galois group permutes the primes
above `q` transitively, and conjugation carries the decomposition group and the inertia subgroup of
one to those of another. -/
theorem isSplitInertiaAt_of_stabilizer_le (hq : q.Prime) (P : Ideal (𝓞 N)) [P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(q : ℤ)}))
    (hle : MulAction.stabilizer Gal(N/ℚ) P ≤ Ideal.inertia Gal(N/ℚ) P) :
    IsSplitInertiaAt N q := by
  intro Q hQprime hQover
  haveI := hQprime
  haveI := hQover
  refine (inertiaDeg_eq_one_iff_inertia_eq_stabilizer hq Q).mpr
    (le_antisymm (Ideal.inertia_le_stabilizer Q) ?_)
  have h := forall_stabilizer_le_of_stabilizer_le (⊥ : Subgroup Gal(N/ℚ)) P hP
    (by simpa using hle) Q hQover
  simpa using h

/-- **Split inertia at a prime is exactly the statement that an arithmetic Frobenius above it lies
in the inertia group.**  The decomposition group is generated by the inertia group together with an
arithmetic Frobenius, so the two coincide precisely when the Frobenius is already there. -/
theorem isSplitInertiaAt_iff_mem_inertia (hq : q.Prime) (P : Ideal (𝓞 N)) [P.IsPrime]
    [hPo : P.LiesOver (Ideal.span {(q : ℤ)})] {σ : Gal(N/ℚ)} (hσ : IsArithFrobAt ℤ σ P) :
    IsSplitInertiaAt N q ↔ σ ∈ Ideal.inertia Gal(N/ℚ) P := by
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hq hPo
  haveI : Finite (𝓞 N ⧸ P) := finite_quotient_of_ne_bot P hP0
  constructor
  · intro h
    rw [(inertiaDeg_eq_one_iff_inertia_eq_stabilizer hq P).mp (h P inferInstance inferInstance)]
    exact mem_stabilizer_of_isArithFrobAt P hσ
  · intro hmem
    refine isSplitInertiaAt_of_stabilizer_le hq P hPo ?_
    refine (stabilizer_le_inertia_sup_zpowers P hP0 hσ).trans (sup_le le_rfl ?_)
    rwa [Subgroup.zpowers_le]

/-- **Every rational prime has a prime above it in a Galois number field carrying an arithmetic
Frobenius.** -/
theorem exists_isArithFrobAt_liesOver (hq : q.Prime) :
    ∃ P : Ideal (𝓞 N), ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
      ∃ σ : Gal(N/ℚ), IsArithFrobAt ℤ σ P := by
  haveI := isMaximal_span_prime hq
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) (Ideal.span {(q : ℤ)})
  haveI := hPmax
  haveI := hPover
  haveI : P.IsPrime := hPmax.isPrime
  haveI : Finite (𝓞 N ⧸ P) :=
    finite_quotient_of_ne_bot P (ne_bot_of_liesOver_natCast hq hPover)
  exact ⟨P, inferInstance, hPover, arithFrobAt ℤ Gal(N/ℚ) P,
    IsArithFrobAt.arithFrobAt ℤ Gal(N/ℚ) P⟩

end Galois

/-! ### The prime seen through a solution of a central step -/

section Solution

variable {L M : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] [IsGalois ℚ ↥L]
  [NumberField ↥M] [IsGalois ℚ ↥M] {G : Type*} [Group G]

/-- **A solution of a central step absorbs an arithmetic Frobenius into the image of the inertia
group exactly when the prime has split inertia in the field the solution lives over.**  The solution
is the restriction map to that field followed by an injection, restriction carries inertia onto
inertia and an arithmetic Frobenius to an arithmetic Frobenius, so the condition upstairs is the
condition downstairs. -/
theorem mem_map_inertia_iff_isSplitInertiaAt (hLM : L ≤ M) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (Θ : Gal(↥M/ℚ) →* G) (hΘ : ∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) {q : ℕ} (hq : q.Prime)
    (P : Ideal (𝓞 ↥M)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})] {σ : Gal(↥M/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) :
    Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ ↔ IsSplitInertiaAt ↥L q := by
  haveI : NumberField ↥(IntermediateField.restrict hLM) := ⟨⟩
  haveI : IsGalois ℚ ↥(IntermediateField.restrict hLM) := ⟨⟩
  haveI := liesOver_under_intermediateField (p := q) (IntermediateField.restrict hLM) P
  set φ : ↥L ≃ₐ[ℚ] ↥(IntermediateField.restrict hLM) :=
    IntermediateField.restrict_algEquiv hLM with hφ
  set ψ₁ : Gal(↥(IntermediateField.restrict hLM)/ℚ) ≃* G :=
    (AlgEquiv.autCongr φ).symm.trans ψ₀ with hψ₁
  have hΘeq : Θ = ψ₁.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hLM)) := by
    refine MonoidHom.ext fun τ => ?_
    rw [hΘ τ]
    rfl
  have hmap : (Ideal.inertia Gal(↥M/ℚ) P).map Θ
      = (Ideal.inertia Gal(↥(IntermediateField.restrict hLM)/ℚ)
          (P.under (𝓞 ↥(IntermediateField.restrict hLM)))).map ψ₁.toMonoidHom := by
    rw [hΘeq, ← Subgroup.map_map, map_inertia_eq_inertia (IntermediateField.restrict hLM) hq P]
  have hval : Θ σ = ψ₁.toMonoidHom
      (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hLM) σ) := by
    rw [hΘ σ]
    rfl
  have hmem : Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ ↔
      AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hLM) σ ∈
        Ideal.inertia Gal(↥(IntermediateField.restrict hLM)/ℚ)
          (P.under (𝓞 ↥(IntermediateField.restrict hLM))) := by
    rw [hmap, hval, Subgroup.mem_map]
    refine ⟨?_, fun h => ⟨_, h, rfl⟩⟩
    rintro ⟨x, hx, hxeq⟩
    have hx' : x = AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hLM) σ :=
      ψ₁.injective hxeq
    exact hx' ▸ hx
  rw [hmem, ← isSplitInertiaAt_iff_mem_inertia hq
    (P.under (𝓞 ↥(IntermediateField.restrict hLM)))
    (isArithFrobAt_restrictNormal (IntermediateField.restrict hLM) σ P hσ)]
  exact ⟨fun h => IsSplitInertiaAt.of_ringEquiv hq φ.symm.toRingEquiv h,
    fun h => IsSplitInertiaAt.of_ringEquiv hq φ.toRingEquiv h⟩

/-- **The defect a solution of a central step carries at a rational prime vanishes exactly when the
prime has split inertia in the field the solution lives over.**  This is the condition the residue
correction reads at a ramified prime, in the form it is stated there: at one prime above the
rational prime and for every arithmetic Frobenius there. -/
theorem exists_forall_mem_map_inertia_iff (hLM : L ≤ M) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (Θ : Gal(↥M/ℚ) →* G) (hΘ : ∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) {q : ℕ} (hq : q.Prime) :
    (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
      ∀ τ : Gal(↥M/ℚ), IsArithFrobAt ℤ τ P → Θ τ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ)
      ↔ IsSplitInertiaAt ↥L q := by
  constructor
  · rintro ⟨P, hPp, hPo, hP⟩
    haveI := hPp
    haveI := hPo
    haveI : Finite (𝓞 ↥M ⧸ P) :=
      finite_quotient_of_ne_bot P (ne_bot_of_liesOver_natCast hq hPo)
    have hfrob := IsArithFrobAt.arithFrobAt ℤ Gal(↥M/ℚ) P
    exact (mem_map_inertia_iff_isSplitInertiaAt hLM ψ₀ Θ hΘ hq P hfrob).mp (hP _ hfrob)
  · intro h
    obtain ⟨P, hPp, hPo, -⟩ := exists_isArithFrobAt_liesOver (N := ↥M) hq
    haveI := hPp
    haveI := hPo
    exact ⟨P, hPp, hPo, fun τ hτ =>
      (mem_map_inertia_iff_isSplitInertiaAt hLM ψ₀ Θ hΘ hq P hτ).mpr h⟩

end Solution

end InverseGalois.CFT
