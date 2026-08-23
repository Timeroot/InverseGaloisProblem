/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Product
import InverseGalois.CFT.Cyclotomic.BuildingBlock
import InverseGalois.CFT.Disjoint
import InverseGalois.Solvable.Nilpotent

/-!
# Splitting off a finite abelian factor

The split case of the Scholz–Reichardt induction: an inverse Galois group over `ℚ` stays one
after multiplying by an arbitrary finite abelian group.  Nothing about the given group is used
beyond the existence of a realizing field `K₁`, because the abelian factor is realized by a
*new* extension whose ramification is confined to a single auxiliary prime `q` chosen to split
completely in `K₁`.

The mechanism is the one that drives the whole Scholz–Reichardt construction.  A cyclic factor
of order `n` is cut out of the cyclotomic field `ℚ(ζ_q)` for a prime `q ≡ 1 (mod n)`; the
resulting field `K₂` ramifies only at `q`, while `q` is unramified in `K₁` because it splits
completely there.  Disjoint ramification forces `K₁ ⊓ K₂ = ⊥`, the two fields are therefore
linearly disjoint, and the Galois group of the compositum is the product of the two Galois
groups.  A general finite abelian group is a product of cyclic groups, so the cyclic case is
applied once per factor.

## Main results

* `InverseGalois.CFT.inf_eq_bot_of_ramifiedSet_disjoint'` — two intermediate fields of an
  arbitrary extension of `ℚ` with disjoint ramification meet in `ℚ`.
* `InverseGalois.CFT.inf_eq_bot_of_splitsCompletely'` — the same over an arbitrary ambient
  extension, for a prime that splits completely in one field and carries all the ramification
  of the other.
* `IsInverseGalois.prod_cyclic` — an inverse Galois group times `Multiplicative (ZMod n)` is an
  inverse Galois group.
* `IsInverseGalois.prod_pi_zmod` — the same for a finite product of such cyclic groups.
* `IsInverseGalois.prod_abelian` — an inverse Galois group times a finite abelian group is an
  inverse Galois group.
-/

open Module NumberField InverseGalois.NumberTheory

noncomputable section

namespace InverseGalois.CFT

/-! ### Disjoint ramification inside an arbitrary extension of `ℚ` -/

/-- **Two intermediate fields with disjoint ramification meet in `ℚ`.**  Unlike
`InverseGalois.CFT.inf_eq_bot_of_ramifiedSet_disjoint`, the ambient field is not required to be
a number field, only the two intermediate fields themselves. -/
theorem inf_eq_bot_of_ramifiedSet_disjoint' {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField A] [NumberField B]
    (h : Disjoint (ramifiedSet A) (ramifiedSet B)) : A ⊓ B = ⊥ := by
  haveI : FiniteDimensional ℚ ↥(A ⊓ B) := by
    have hincl := IntermediateField.inclusion (inf_le_left : A ⊓ B ≤ A)
    exact FiniteDimensional.of_injective hincl.toLinearMap hincl.injective
  haveI : NumberField ↥(A ⊓ B) := ⟨⟩
  letI : Algebra ↥(A ⊓ B) ↥A := (IntermediateField.inclusion inf_le_left).toAlgebra
  letI : Algebra ↥(A ⊓ B) ↥B := (IntermediateField.inclusion inf_le_right).toAlgebra
  exact IntermediateField.finrank_eq_one_iff.mp
    (finrank_eq_one_of_ramifiedSet_disjoint ↥(A ⊓ B) ↥A ↥B h)

/-- **The disjointness criterion, over an arbitrary ambient extension of `ℚ`.**  A field in which
the prime `q` splits completely meets a field ramified only at `q` in `ℚ`. -/
theorem inf_eq_bot_of_splitsCompletely' {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField A] [NumberField B] {q : ℕ}
    (hA : SplitsCompletely (↥A) q) (hB : ramifiedSet ↥B ⊆ {q}) : A ⊓ B = ⊥ := by
  refine inf_eq_bot_of_ramifiedSet_disjoint' A B (Set.disjoint_right.mpr fun p hp hpA => ?_)
  rw [Set.mem_singleton_iff.mp (hB hp)] at hpA
  exact notMem_ramifiedSet_of_splitsCompletely hA hpA

end InverseGalois.CFT

/-! ### A cyclic factor -/

open InverseGalois.CFT in
/-- **Multiplying by a finite cyclic group preserves the inverse Galois property.**  If `G` is a
Galois group over `ℚ` and `n ≠ 0`, then so is `G × Multiplicative (ZMod n)`. -/
theorem IsInverseGalois.prod_cyclic {G : Type*} [Group G] (hG : IsInverseGalois G) {n : ℕ}
    (hn : n ≠ 0) : IsInverseGalois (G × Multiplicative (ZMod n)) := by
  -- Realize `G` inside the algebraic closure of `ℚ`.
  obtain ⟨L₁, _, _, _, _, ⟨φ₁⟩⟩ := hG
  let i₁ : L₁ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  obtain ⟨hg₁, ⟨ψ₁⟩⟩ := IsInverseGalois.galois_image_in_algClosure L₁ i₁
  haveI := hg₁
  haveI : FiniteDimensional ℚ i₁.fieldRange := FiniteDimensional.of_injective
    (AlgEquiv.ofInjectiveField i₁).symm.toLinearMap (AlgEquiv.ofInjectiveField i₁).symm.injective
  haveI : NumberField ↥i₁.fieldRange := ⟨⟩
  -- Choose an auxiliary prime `q ≡ 1 (mod n)` splitting completely in it.
  obtain ⟨q, -, hqp, hqmod, hsplit⟩ :=
    exists_prime_splitsCompletely_and_modEq ↥i₁.fieldRange n hn 0
  haveI : Fact q.Prime := ⟨hqp⟩
  have hdvd : n ∣ q - 1 := (Nat.modEq_iff_dvd' hqp.one_lt.le).1 hqmod.symm
  obtain ⟨F, hFgal, hFcyc, hFrank, -⟩ := exists_cyclic_intermediateField_of_dvd hqp hdvd
  haveI := hFgal
  -- Transport the cyclic field into the algebraic closure.
  let ψ : CyclotomicField q ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let j : ↥F →ₐ[ℚ] AlgebraicClosure ℚ := ψ.comp F.val
  let e : ↥F ≃ₐ[ℚ] ↥j.fieldRange := AlgEquiv.ofInjectiveField j
  haveI : IsGalois ℚ ↥j.fieldRange := IsGalois.of_algEquiv e
  haveI : FiniteDimensional ℚ ↥j.fieldRange :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  haveI : NumberField ↥j.fieldRange := ⟨⟩
  -- Its ramification is confined to `q`, because it embeds into `ℚ(ζ_q)`.
  letI : Algebra ↥j.fieldRange (CyclotomicField q ℚ) :=
    ((F.val.comp e.symm.toAlgHom : ↥j.fieldRange →ₐ[ℚ] CyclotomicField q ℚ)).toRingHom.toAlgebra
  have hram : ramifiedSet ↥j.fieldRange ⊆ {q} :=
    ramifiedSet_subset_singleton hqp fun Q _ hQ hmem => isUnramifiedAt_of_not_mem q Q hQ hmem
  have hinf : i₁.fieldRange ⊓ j.fieldRange = ⊥ :=
    inf_eq_bot_of_splitsCompletely' _ _ hsplit hram
  -- The second Galois group is cyclic of order `n`.
  have hcard : Nat.card Gal(↥F/ℚ) = n := by
    rw [IsGalois.card_aut_eq_finrank, hFrank]
  have hec : Nonempty (Gal(↥F/ℚ) ≃* Multiplicative (ZMod n)) := by
    rw [← hcard]
    exact ⟨(zmodCyclicMulEquiv hFcyc).symm⟩
  obtain ⟨ec⟩ := hec
  exact IsInverseGalois.of_disjoint_intermediate_fields _ _ hinf (ψ₁.symm.trans φ₁)
    (e.autCongr.symm.trans ec)

/-! ### A finite abelian factor -/

/-- **Multiplying by a finite product of cyclic groups preserves the inverse Galois property.** -/
theorem IsInverseGalois.prod_pi_zmod {G : Type*} [Group G] (hG : IsInverseGalois G) (k : ℕ)
    (m : Fin k → ℕ) (hm : ∀ i, m i ≠ 0) :
    IsInverseGalois (G × ∀ i : Fin k, Multiplicative (ZMod (m i))) := by
  induction k generalizing G with
  | zero => exact hG.of_mulEquiv (MulEquiv.prodUnique (M := G) (N := _)).symm
  | succ k ih =>
    have h1 : IsInverseGalois (G × Multiplicative (ZMod (m 0))) := hG.prod_cyclic (hm 0)
    have h2 := ih h1 (fun i => m i.succ) fun i => hm i.succ
    exact h2.of_mulEquiv (MulEquiv.prodAssoc.trans ((MulEquiv.refl G).prodCongr
      (SylowReduction.mulEquivPiFinSucc fun i => Multiplicative (ZMod (m i))).symm))

/-- **Multiplying by a finite abelian group preserves the inverse Galois property.**  If `G` is a
Galois group over `ℚ` and `A` is a finite abelian group, then `G × A` is a Galois group over
`ℚ`. -/
theorem IsInverseGalois.prod_abelian {G : Type*} [Group G] {A : Type*} [CommGroup A] [Finite A]
    (hG : IsInverseGalois G) : IsInverseGalois (G × A) := by
  obtain ⟨ι, hι, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI := hι
  set eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with heι
  have key := hG.prod_pi_zmod (Fintype.card ι) (fun jj => n (eι.symm jj)) fun jj => by
    show n (eι.symm jj) ≠ 0
    have := hn1 (eι.symm jj)
    omega
  refine key.of_mulEquiv ((MulEquiv.refl G).prodCongr ?_)
  exact (SylowReduction.mulEquivPiCongrLeft'
    (fun i => Multiplicative (ZMod (n i))) eι).symm.trans e.symm

end
