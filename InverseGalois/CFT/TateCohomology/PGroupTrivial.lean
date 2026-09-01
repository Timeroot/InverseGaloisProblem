/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Iterate
import InverseGalois.CFT.TateCohomology.PGroupInvariants

/-!
# A representation of a p-group killed by p with a single vanishing degree

Let `G` be a finite `p`-group and let `A` be a representation of `G` all of whose vectors are killed
by `p`.  A linear retraction of the inclusion of the invariants produces an equivariant map from `A`
to the functions on `G` with values in the invariants, sending a vector to the record of the
retracted translates.  Its kernel is a stable subspace meeting the invariants only in the origin, so
it vanishes; and if the first cohomology of `A` vanishes then its image is everything, because a
function is invariant modulo the image exactly when the record of its translates is a one-cocycle,
and a one-cocycle is a coboundary.

So such a representation with vanishing first cohomology is the representation on the functions on
the group, whose complete cohomology vanishes in every degree.  Over the field with `p` elements a
retraction is available for free, and iterated dimension shifting stays in characteristic `p`, so
there the same conclusion follows from the vanishing of the complete cohomology in one single
degree, wherever that degree is.

## Main definitions

* `InverseGalois.CFT.Tate.invariantsEmb`: the equivariant map to the functions on the group with
  values in the invariants.
* `InverseGalois.CFT.Tate.invariantsRetraction`: a linear retraction of the inclusion of the
  invariants over the field with `p` elements.

## Main results

* `InverseGalois.CFT.Tate.inducedIsoOfIsZeroH1`: **a representation of a `p`-group killed by `p`
  with no first cohomology and a retracted invariant subspace is the representation on the
  functions on the group.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_single`: **a representation of a `p`-group in
  characteristic `p` with no complete cohomology in one degree has none in any degree.**

## Tags

Tate cohomology, cohomologically trivial, p-group, induced representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ### The record of the retracted translates -/

section General

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The equivariant map to the functions on the group with values in the invariants**, sending a
vector to the record of its retracted translates. -/
def invariantsEmb (A : Rep k G) (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) :
    ↥A.V →ₗ[k] (G → ↥(A.ρ.invariants)) where
  toFun a x := r (A.ρ x a)
  map_add' a b := by funext x; simp
  map_smul' c a := by funext x; simp

omit [Finite G] in
@[simp]
theorem invariantsEmb_apply (A : Rep k G) (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) (a : ↥A.V) (x : G) :
    invariantsEmb A r a x = r (A.ρ x a) := rfl

omit [Finite G] in
/-- **The record of the retracted translates is equivariant.** -/
theorem invariantsEmb_equivariant (A : Rep k G) (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) (g : G)
    (a : ↥A.V) : invariantsEmb A r (A.ρ g a)
      = inducedRep k G ↥(A.ρ.invariants) g (invariantsEmb A r a) := by
  funext x
  rw [inducedRep_apply, invariantsEmb_apply, invariantsEmb_apply]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]

omit [Finite G] in
/-- **An invariant vector goes to the constant function with that value.** -/
theorem invariantsEmb_coe (A : Rep k G) (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants))
    (hr : ∀ v : ↥(A.ρ.invariants), r (v : ↥A.V) = v) (v : ↥(A.ρ.invariants)) (x : G) :
    invariantsEmb A r (v : ↥A.V) x = v := by
  rw [invariantsEmb_apply, v.2 x, hr]

/-! ### Injectivity and surjectivity -/

/-- **The record of the retracted translates is injective.** -/
theorem invariantsEmb_injective (hG : IsPGroup p G) (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) (hr : ∀ v : ↥(A.ρ.invariants), r (v : ↥A.V) = v) :
    Function.Injective (invariantsEmb A r) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  obtain ⟨b, hbmem, hb0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hst : ∀ g : G, LinearMap.ker (invariantsEmb A r) ≤
      (LinearMap.ker (invariantsEmb A r)).comap (A.ρ g) := by
    intro g a ha
    refine Submodule.mem_comap.2 (LinearMap.mem_ker.2 ?_)
    rw [invariantsEmb_equivariant, LinearMap.mem_ker.1 ha, map_zero]
  obtain ⟨c, hcmem, hc0, hcinv⟩ :=
    exists_invariant_mem_ne_zero_of_nsmul hG A.ρ hp hst hbmem hb0
  refine hc0 ?_
  have h1 : invariantsEmb A r c 1 = (⟨c, hcinv⟩ : ↥(A.ρ.invariants)) :=
    invariantsEmb_coe A r hr ⟨c, hcinv⟩ 1
  rw [LinearMap.mem_ker.1 hcmem] at h1
  have h2 : (⟨c, hcinv⟩ : ↥(A.ρ.invariants)) = 0 := by rw [← h1]; rfl
  exact congrArg Subtype.val h2

/-- **The record of the retracted translates is surjective when the first cohomology vanishes.** -/
theorem invariantsEmb_surjective (hG : IsPGroup p G) (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) (hr : ∀ v : ↥(A.ρ.invariants), r (v : ↥A.V) = v)
    (h1 : Limits.IsZero (groupCohomology A 1)) :
    Function.Surjective (invariantsEmb A r) := by
  have hpM : ∀ w : ↥(A.ρ.invariants), p • w = 0 := by
    intro w
    refine Subtype.ext ?_
    have h := hp (w : ↥A.V)
    simpa using h
  have hpF : ∀ f : G → ↥(A.ρ.invariants), p • f = 0 := fun f => funext fun x => hpM (f x)
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hst : ∀ g : G, LinearMap.range (invariantsEmb A r) ≤
      (LinearMap.range (invariantsEmb A r)).comap
        (inducedRep k G ↥(A.ρ.invariants) g) := by
    intro g x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.1 hx
    exact Submodule.mem_comap.2
      (LinearMap.mem_range.2 ⟨A.ρ g a, invariantsEmb_equivariant A r g a⟩)
  have hex : ∃ f : G → ↥(A.ρ.invariants), f ∉ LinearMap.range (invariantsEmb A r) := by
    by_contra hall
    push_neg at hall
    exact hne (Submodule.eq_top_iff'.2 hall)
  obtain ⟨f0, hf0⟩ := hex
  obtain ⟨f1, hf1, hf1inv⟩ :=
    exists_notMem_invariant_mod_of_nsmul hG (inducedRep k G ↥(A.ρ.invariants)) hpF hst hf0
  have hmem : ∀ g : G, ∃ y : ↥A.V, invariantsEmb A r y
      = inducedRep k G ↥(A.ρ.invariants) g f1 - f1 :=
    fun g => LinearMap.mem_range.1 (hf1inv g)
  choose c hc using hmem
  have hcoc : c ∈ groupCohomology.cocycles₁ A := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h'
    refine invariantsEmb_injective hG A hp r hr ?_
    have key : inducedRep k G ↥(A.ρ.invariants) (g * h') f1
        = inducedRep k G ↥(A.ρ.invariants) g
          (inducedRep k G ↥(A.ρ.invariants) h' f1) := by
      rw [map_mul]; rfl
    rw [hc, map_add, invariantsEmb_equivariant, hc, hc, key, map_sub]
    abel
  have hz : groupCohomology.H1π A = 0 := h1.eq_zero_of_tgt _
  have hzero : groupCohomology.H1π A ⟨c, hcoc⟩ = 0 := by rw [hz]; simp
  obtain ⟨a, ha⟩ :=
    LinearMap.mem_range.1 ((groupCohomology.H1π_eq_zero_iff ⟨c, hcoc⟩).1 hzero)
  have hag : ∀ g : G, c g = A.ρ g a - a := by
    intro g
    have h3 := congrFun ha g
    rw [groupCohomology.d₀₁_hom_apply] at h3
    exact h3.symm
  have hw : ∀ g : G, inducedRep k G ↥(A.ρ.invariants) g (f1 - invariantsEmb A r a)
      = f1 - invariantsEmb A r a := by
    intro g
    have h2 := hc g
    rw [hag g, map_sub, invariantsEmb_equivariant] at h2
    have h8 : inducedRep k G ↥(A.ρ.invariants) g f1
        = inducedRep k G ↥(A.ρ.invariants) g (invariantsEmb A r a)
          - invariantsEmb A r a + f1 := by
      rw [h2]; abel
    rw [map_sub, h8]
    abel
  have hconst : ∀ x : G, (f1 - invariantsEmb A r a) x = (f1 - invariantsEmb A r a) 1 :=
    (mem_invariants_inducedRep_iff _).1 hw
  have hveq : invariantsEmb A r
      (((f1 - invariantsEmb A r a) 1 : ↥(A.ρ.invariants)) : ↥A.V)
        = f1 - invariantsEmb A r a := by
    funext x
    rw [invariantsEmb_coe A r hr]
    exact (hconst x).symm
  refine hf1 (LinearMap.mem_range.2
    ⟨(((f1 - invariantsEmb A r a) 1 : ↥(A.ρ.invariants)) : ↥A.V) + a, ?_⟩)
  rw [map_add, hveq]
  abel

/-! ### Cohomological triviality -/

/-- **A representation of a `p`-group killed by `p` with no first cohomology and a retracted
invariant subspace is the representation on the functions on the group.** -/
def inducedIsoOfIsZeroH1 (hG : IsPGroup p G) (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants)) (hr : ∀ v : ↥(A.ρ.invariants), r (v : ↥A.V) = v)
    (h1 : Limits.IsZero (groupCohomology A 1)) :
    A ≅ Rep.of (inducedRep k G ↥(A.ρ.invariants)) :=
  Action.mkIso
    (LinearEquiv.ofBijective (invariantsEmb A r)
      ⟨invariantsEmb_injective hG A hp r hr,
        invariantsEmb_surjective hG A hp r hr h1⟩).toModuleIso fun g => by
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    exact invariantsEmb_equivariant A r g a

/-- **A representation of a `p`-group killed by `p` with no first cohomology and a retracted
invariant subspace has no complete cohomology in any degree.** -/
theorem isZero_tateModule_of_isZero_H1 (hG : IsPGroup p G) (A : Rep k G)
    (hp : ∀ v : ↥A.V, p • v = 0) (r : ↥A.V →ₗ[k] ↥(A.ρ.invariants))
    (hr : ∀ v : ↥(A.ρ.invariants), r (v : ↥A.V) = v)
    (h1 : Limits.IsZero (groupCohomology A 1)) (n : ℤ) :
    Limits.IsZero (tateModule A n) :=
  isZero_tateModule_of_iso (inducedIsoOfIsZeroH1 hG A hp r hr h1) n
    (isZero_tateModule_inducedRep n)

end General

/-! ### The field with `p` elements -/

section Field

variable {G : Type} [Group G] [Finite G]

/-- **A linear retraction of the inclusion of the invariants.** -/
def invariantsRetraction (A : Rep (ZMod p) G) : ↥A.V →ₗ[ZMod p] ↥(A.ρ.invariants) :=
  A.ρ.invariants.subtype.leftInverse

omit [Finite G] in
theorem invariantsRetraction_coe (A : Rep (ZMod p) G) (v : ↥(A.ρ.invariants)) :
    invariantsRetraction A (v : ↥A.V) = v :=
  LinearMap.leftInverse_apply_of_inj (Submodule.ker_subtype _) v

/-- **A representation of a `p`-group in characteristic `p` with no first cohomology has no complete
cohomology in any degree.** -/
theorem isZero_tateModule_of_isZero_H1_zmod (hG : IsPGroup p G) (A : Rep (ZMod p) G)
    (h1 : Limits.IsZero (groupCohomology A 1)) (n : ℤ) :
    Limits.IsZero (tateModule A n) :=
  isZero_tateModule_of_isZero_H1 hG A (fun v => nsmul_prime_eq_zero v) (invariantsRetraction A)
    (invariantsRetraction_coe A) h1 n

/-- **A representation of a `p`-group in characteristic `p` with no complete cohomology in one
degree has none in any degree.** -/
theorem isZero_tateModule_of_isZero_single (hG : IsPGroup p G) (A : Rep (ZMod p) G) {i : ℤ}
    (hi : Limits.IsZero (tateModule A i)) (n : ℤ) : Limits.IsZero (tateModule A n) := by
  rcases le_total i 1 with hle | hle
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 1 - i := ⟨(1 - i).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hB1 : Limits.IsZero (tateModule (coshiftIter A j) 1) :=
      isZero_tateModule_congr (by omega) (isZero_tateModule_coshiftIter A j i hi)
    exact isZero_tateModule_of_isZero_coshiftIter A j n
      (isZero_tateModule_of_isZero_H1_zmod hG _ hB1 (n + j))
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = i - 1 := ⟨(i - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hB1 : Limits.IsZero (tateModule (shiftIter A j) 1) :=
      isZero_tateModule_shiftIter A j 1 (isZero_tateModule_congr (by omega) hi)
    exact isZero_tateModule_congr (by omega)
      (isZero_tateModule_of_isZero_shiftIter A j (n - j)
        (isZero_tateModule_of_isZero_H1_zmod hG _ hB1 (n - j)))

end Field

end

end InverseGalois.CFT.Tate
