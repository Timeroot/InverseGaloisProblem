/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.BlockRealization
import InverseGalois.Solvable.PCentralCharacter

/-!
# Blocks matched to the generators of a free object

A realization of the free object of rank `d` and positive `2`-class comes with `d` distinguished
generators of its Galois group.  If the field carries square roots of `d` pairwise disjoint blocks
of primes whose signs match those generators — the `i`-th square root changed in sign by the `k`-th
generator exactly when `i = k` — then the joint sign character is the coordinate character of the
free object read through the realization.  That character is onto and has its kernel inside the
Frattini subgroup, which are exactly the two conditions under which the blocks account for every
square root of a rational number in the field.

Matching the generators is a much more usable invariant to carry along an induction than
independence of the characters, because it is preserved by construction under the operations the
dyadic induction performs on a realization.

## Main definitions

* `InverseGalois.CFT.sqrtSignHom`: the joint sign character of a family of square roots, as a
  homomorphism on the Galois group.

## Main results

* `InverseGalois.CFT.isBlockSpanned_of_sqrtSign_gen`: **a realization of a free object of positive
  `2`-class whose blocks have square roots matching the distinguished generators is spanned by
  those blocks.**

## Tags

Scholz–Reichardt, block, square root, sign character, free `2`-group, Frattini subgroup
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The joint sign character -/

/-- The **joint sign character** of a family of square roots of base elements: the automorphism is
sent to the vector of signs by which it moves them. -/
noncomputable def sqrtSignHom {F M : Type*} [Field F] [Field M] [Algebra F M] [CharZero M]
    {ι : Type*} {n : ι → F} (v : ι → M) (hv : ∀ i, v i ≠ 0)
    (hvsq : ∀ i, v i ^ 2 = algebraMap F M (n i)) : Gal(M/F) →* Multiplicative (ι → ZMod 2) :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd fun i => sqrtSign (v i) σ) fun σ τ =>
    congrArg Multiplicative.ofAdd (funext fun i => sqrtSign_apply_mul (hv i) (hvsq i) σ τ)

theorem sqrtSignHom_apply {F M : Type*} [Field F] [Field M] [Algebra F M] [CharZero M] {ι : Type*}
    {n : ι → F} (v : ι → M) (hv : ∀ i, v i ≠ 0)
    (hvsq : ∀ i, v i ^ 2 = algebraMap F M (n i)) (σ : Gal(M/F)) :
    sqrtSignHom v hv hvsq σ = Multiplicative.ofAdd fun i => sqrtSign (v i) σ :=
  rfl

/-! ### Square roots matching the distinguished generators -/

/-- **A realization of a free object of positive `2`-class whose blocks have square roots matching
the distinguished generators is spanned by those blocks.**  Read through the realization, the joint
sign character sends the `k`-th generator to the `k`-th standard basis vector, so it is the
coordinate character of the free object: it is onto, and its kernel is the first term of the lower
`2`-central series, which lies inside the Frattini subgroup. -/
theorem isBlockSpanned_of_sqrtSign_gen {d c : ℕ} (hc : 1 ≤ c)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    {block : Fin d → Finset ℕ} (hprime : ∀ i, ∀ p ∈ block i, p.Prime)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (e : Gal(↥A/ℚ) ≃* FreePClass 2 d c) (v : Fin d → ↥A)
    (hvsq : ∀ i, v i ^ 2 = algebraMap ℚ ↥A ((∏ p ∈ block i, p : ℕ) : ℚ))
    (hgen : ∀ k i, sqrtSign (v i) (e.symm (FreePClass.gen 2 d c k)) = if i = k then 1 else 0) :
    IsBlockSpanned A block := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : ∀ i, v i ≠ 0 := by
    intro i hzero
    have h0 : algebraMap ℚ ↥A ((∏ p ∈ block i, p : ℕ) : ℚ) = 0 := by
      rw [← hvsq i, hzero, zero_pow (by norm_num : 2 ≠ 0)]
    have hP : ((∏ p ∈ block i, p : ℕ) : ℚ) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ ↥A).injective).mp h0
    exact prod_prime_ne_zero (hprime i) (by exact_mod_cast hP)
  set χ : Gal(↥A/ℚ) →* Multiplicative (Fin d → ZMod 2) := sqrtSignHom v hv hvsq with hχdef
  set ψ : FreePClass 2 d c →* Multiplicative (Fin d → ZMod 2) := χ.comp e.symm.toMonoidHom with hψ
  have hψgen : ∀ k, ψ (FreePClass.gen 2 d c k) = Multiplicative.ofAdd (Pi.single k 1) := by
    intro k
    show Multiplicative.ofAdd (fun i => sqrtSign (v i) (e.symm (FreePClass.gen 2 d c k)))
      = Multiplicative.ofAdd (Pi.single k 1)
    exact congrArg _ (funext fun i => by rw [Pi.single_apply]; exact hgen k i)
  refine isBlockSpanned_of_sqrtSign_surjective A hprime hdisj v hvsq ?_ ?_
  · intro f
    obtain ⟨g, hg⟩ := FreePClass.surjective_of_apply_gen hc hψgen (Multiplicative.ofAdd f)
    exact ⟨e.symm g, congrArg Multiplicative.toAdd hg⟩
  · intro σ hσ
    have hmem : e σ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      show χ (e.symm (e σ)) = 1
      rw [e.symm_apply_apply]
      exact congrArg Multiplicative.ofAdd (funext hσ)
    have hcomap : frattini (FreePClass 2 d c) ≤ (frattini Gal(↥A/ℚ)).comap e.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective e.symm.surjective
    simpa using hcomap (FreePClass.ker_le_frattini_of_apply_gen hc hψgen hmem)

end InverseGalois.CFT
