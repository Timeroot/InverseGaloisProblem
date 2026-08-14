/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.NilpotentCycles
import InverseGalois.Rigidity.RET.AbelianCycles
import InverseGalois.Rigidity.RET.CyclicCycles

/-!
# A cover of the line is branched over finitely many points

Every finite Galois cover of the line ramifies over only finitely many points of the affine line.
The reason is elementary: a deck transformation other than the identity moves some element of the
integral model, and the product of the conjugates of the difference is a nonzero polynomial in the
coordinate; wherever that polynomial does not vanish, the transformation cannot lie in an inertia
group.  Taking one polynomial for each of the finitely many nontrivial deck transformations bounds
the branch locus by a finite set of points.

All the results about branch cycles are stated for a cover together with a tuple of points outside
which it is unramified.  The finiteness proved here supplies that tuple, so those results become
statements about an arbitrary cover: a cyclic cover of the line unramified at infinity has a system
of branch cycles over *some* finite tuple of points, and likewise for the weaker conclusions
available for nilpotent and arbitrary deck groups.

## Main results

* `Rigidity.RET.LineCover.exists_unramifiedOutside_finite` — every cover of the line is unramified
  outside a finite set of points of the affine line.
* `Rigidity.RET.exists_branchCycleGenSystem_of_comm'` — an abelian cover of the line unramified at
  infinity has a system of branch cycles over a finite tuple of points.
* `Rigidity.RET.exists_branchCycles_mod_commutator'` — for an arbitrary deck group, the same with
  generation only modulo commutators.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

namespace LineCover

/-! ### A nonzero polynomial witnessing that a deck transformation is not everywhere inertial -/

/-- A deck transformation other than the identity moves some element of the integral model: the
deck group acts faithfully on it. -/
theorem exists_smul_ne (L : LineCover) {σ : L.deck} (hσ : σ ≠ 1) :
    ∃ x : Bring L.M, σ • x ≠ x := by
  haveI : FaithfulSMul L.deck (Bring L.M) := IsGaloisGroup.faithful (A := Polynomial k)
  by_contra h
  push_neg at h
  exact hσ (FaithfulSMul.eq_of_smul_eq_smul (α := Bring L.M) fun x => by rw [h x, one_smul])

/-- **A nontrivial deck transformation is inertial only over the roots of a fixed nonzero
polynomial.**  Choose an element of the integral model that the transformation moves; the product
of the conjugates of the difference is fixed by the whole deck group, hence is a polynomial in the
coordinate, and it is nonzero.  Whenever the transformation lies in an inertia group above a point,
the difference lies in that place, hence so does the product, hence the polynomial vanishes at the
point. -/
theorem exists_poly_of_ne_one (L : LineCover) {σ : L.deck} (hσ : σ ≠ 1) :
    ∃ c : Polynomial k, c ≠ 0 ∧ ∀ t : k, L.IsInertiaAt t σ → c.eval t = 0 := by
  classical
  obtain ⟨x, hx⟩ := L.exists_smul_ne hσ
  set y : Bring L.M := σ • x - x with hy
  have hy0 : y ≠ 0 := sub_ne_zero.mpr hx
  set z : Bring L.M := ∏ τ : L.deck, τ • y with hz
  -- the product over the deck group is invariant, hence a polynomial in the coordinate
  have hzinv : ∀ ρ : L.deck, ρ • z = z := by
    intro ρ
    rw [hz, Finset.smul_prod']
    exact Fintype.prod_bijective (fun τ => ρ * τ) (Group.mulLeft_bijective ρ) _ _
      fun τ => (mul_smul ρ τ y).symm
  obtain ⟨c, hc⟩ := Algebra.IsInvariant.isInvariant (A := Polynomial k) (G := L.deck) z hzinv
  have hz0 : z ≠ 0 := by
    rw [hz]
    refine Finset.prod_ne_zero_iff.mpr fun τ _ h => hy0 ?_
    have hτ : τ • y = τ • (0 : Bring L.M) := by rw [h, smul_zero]
    exact MulAction.injective τ hτ
  refine ⟨c, fun h => hz0 (by rw [← hc, h, map_zero]), ?_⟩
  intro t hσt
  obtain ⟨Q, hQmax, hQover, hQin⟩ := hσt
  -- the difference lies in the place, hence so does the whole product
  have hyQ : y ∈ Q := hQin x
  have hzQ : z ∈ Q := by
    rw [hz, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : L.deck))]
    exact Q.mul_mem_left _ (by rwa [one_smul])
  -- so the polynomial lies in the place `X - t` of the line
  have hcQ : c ∈ placeP t := by
    have : algebraMap (Polynomial k) (Bring L.M) c ∈ Q := by rw [hc]; exact hzQ
    rw [hQover.over]
    exact this
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hcQ
  rw [hb]
  simp

/-! ### Finiteness of the branch locus -/

/-- **Every cover of the line is unramified outside a finite set of points of the affine line.** -/
theorem exists_unramifiedOutside_finite (L : LineCover) :
    ∃ S : Set k, S.Finite ∧ L.IsUnramifiedOutside S := by
  classical
  haveI : Finite L.deck := inferInstance
  choose c hc0 hc using fun σ : {σ : L.deck // σ ≠ 1} => L.exists_poly_of_ne_one σ.2
  refine ⟨⋃ σ : {σ : L.deck // σ ≠ 1}, {t : k | (c σ).eval t = 0}, ?_, ?_⟩
  · refine Set.finite_iUnion fun σ => ?_
    refine Set.Finite.subset ((c σ).roots.toFinset : Finset k).finite_toSet fun t ht => ?_
    simp only [Set.mem_setOf_eq] at ht
    simp [Multiset.mem_toFinset, hc0 σ, IsRoot, ht]
  · intro t ht σ hσt
    by_contra hσ
    exact ht (Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, hc ⟨σ, hσ⟩ t hσt⟩)

/-- A finite set of points of the line is the range of an injective tuple. -/
theorem exists_fin_range {S : Set k} (hS : S.Finite) :
    ∃ (r : ℕ) (t : Fin r → k), Function.Injective t ∧ Set.range t = S := by
  classical
  obtain ⟨F, rfl⟩ := hS.exists_finset_coe
  refine ⟨F.card, fun i => (F.equivFin.symm i : k), ?_, ?_⟩
  · exact Subtype.coe_injective.comp F.equivFin.symm.injective
  · ext u
    constructor
    · rintro ⟨i, rfl⟩
      exact (F.equivFin.symm i).2
    · intro hu
      exact ⟨F.equivFin ⟨u, hu⟩, by simp⟩

/-- **Every cover of the line is unramified outside the range of an injective tuple of points.** -/
theorem exists_unramifiedOutside_range (L : LineCover) :
    ∃ (r : ℕ) (t : Fin r → k), Function.Injective t ∧ L.IsUnramifiedOutside (Set.range t) := by
  obtain ⟨S, hSfin, hS⟩ := L.exists_unramifiedOutside_finite
  obtain ⟨r, t, ht, hrange⟩ := exists_fin_range hSfin
  exact ⟨r, t, ht, hrange ▸ hS⟩

/-- **The last of a system of distinguished branch cycles is redundant**: the ordered product of
the whole system is trivial, so the last entry is the inverse of the product of the others, and the
others already generate the deck group. -/
theorem IsBranchCycleGenSystem.closure_castSucc_eq_top {L : LineCover} {r : ℕ}
    {t : Fin (r + 1) → k} {g : Fin (r + 1) → L.deck} (hg : L.IsBranchCycleGenSystem t g) :
    Subgroup.closure (Set.range fun i : Fin r => g i.castSucc) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← hg.top]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe]
  induction i using Fin.lastCases with
  | last =>
    have hsplit : (List.ofFn g).prod
        = (List.ofFn fun i : Fin r => g i.castSucc).prod * g (Fin.last r) := by
      rw [List.ofFn_succ', List.prod_concat]
    have hlast : g (Fin.last r) = ((List.ofFn fun i : Fin r => g i.castSucc).prod)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← hsplit]; exact hg.prod)
    rw [hlast]
    refine Subgroup.inv_mem _ (Subgroup.list_prod_mem _ fun x hx => ?_)
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨j, rfl⟩
  | cast j => exact Subgroup.subset_closure ⟨j, rfl⟩

end LineCover

/-! ### Branch cycles without a prescribed branch locus -/

/-- **A cyclic cover of the line unramified at infinity has a system of branch cycles.**  The
branch locus is finite, and over a finite tuple of points containing it the branch cycles exist. -/
theorem exists_branchCycleGenSystem_of_isCyclic' (L : LineCover) [IsCyclic L.deck]
    (hinf : L.IsUnramifiedAtInfinity) :
    ∃ (r : ℕ) (t : Fin r → k) (g : Fin r → L.deck),
      Function.Injective t ∧ L.IsBranchCycleGenSystem t g := by
  obtain ⟨r, t, ht, hout⟩ := L.exists_unramifiedOutside_range
  obtain ⟨g, hg⟩ := exists_branchCycleGenSystem_of_isCyclic L t ht hout hinf
  exact ⟨r, t, g, ht, hg⟩

/-- **A cover of the line with abelian deck group, unramified at infinity, has a system of branch
cycles over a finite tuple of points.** -/
theorem exists_branchCycleGenSystem_of_comm' (L : LineCover) (hab : ∀ a b : L.deck, a * b = b * a)
    (hinf : L.IsUnramifiedAtInfinity) :
    ∃ (r : ℕ) (t : Fin r → k) (g : Fin r → L.deck),
      Function.Injective t ∧ L.IsBranchCycleGenSystem t g := by
  obtain ⟨r, t, ht, hout⟩ := L.exists_unramifiedOutside_range
  obtain ⟨g, hg⟩ := exists_branchCycleGenSystem_of_comm L hab t ht hout hinf
  exact ⟨r, t, g, ht, hg⟩

/-- **A cover of the line with nilpotent deck group, unramified at infinity, is generated by
distinguished inertia elements over a finite tuple of points**, whose ordered product is a
commutator. -/
theorem exists_branchCycles_of_isNilpotent' (L : LineCover) [Group.IsNilpotent L.deck]
    (hinf : L.IsUnramifiedAtInfinity) :
    ∃ (r : ℕ) (t : Fin r → k) (g : Fin r → L.deck), Function.Injective t ∧
      (∀ i, L.IsInertiaGenAt (t i) (g i)) ∧ Subgroup.closure (Set.range g) = ⊤ ∧
      (List.ofFn g).prod ∈ commutator L.deck := by
  obtain ⟨r, t, ht, hout⟩ := L.exists_unramifiedOutside_range
  obtain ⟨g, hgin, hgtop, hgprod⟩ := exists_branchCycles_of_isNilpotent L t ht hout hinf
  exact ⟨r, t, g, ht, hgin, hgtop, hgprod⟩

/-- **Every cover of the line unramified at infinity has distinguished inertia elements over a
finite tuple of points** which generate the deck group as a normal subgroup, generate it modulo
commutators, and have commutator ordered product. -/
theorem exists_branchCycles_mod_commutator' (L : LineCover) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ (r : ℕ) (t : Fin r → k) (g : Fin r → L.deck), Function.Injective t ∧
      (∀ i, L.IsInertiaGenAt (t i) (g i)) ∧ Subgroup.normalClosure (Set.range g) = ⊤ ∧
      Subgroup.closure (Set.range g) ⊔ commutator L.deck = ⊤ ∧
      (List.ofFn g).prod ∈ commutator L.deck := by
  obtain ⟨r, t, ht, hout⟩ := L.exists_unramifiedOutside_range
  obtain ⟨g, hgin, hgnorm, hgtop, hgprod⟩ := exists_branchCycles_mod_commutator L t ht hout hinf
  exact ⟨r, t, g, ht, hgin, hgnorm, hgtop, hgprod⟩

end Rigidity.RET
