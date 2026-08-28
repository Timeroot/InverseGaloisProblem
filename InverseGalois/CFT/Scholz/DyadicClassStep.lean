/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.ElementaryAbelianSolutionTwo
import InverseGalois.CFT.Scholz.StrongScholz
import InverseGalois.Solvable.PCentralTower

/-!
# Raising the `2`-class of a realization

The rung of the tower of free objects of a fixed rank is a central embedding problem: the kernel of
the projection from `2`-class `c + 1` to `2`-class `c` is the last nontrivial term of the lower
`2`-central series, hence central, of exponent two, and — once the class below is at least one —
inside the Frattini subgroup.  A problem of that shape over a field satisfying Serre's condition is
solved with no new ramification at all, by dividing the kernel one line at a time.

That gives the *uncorrected* solution of the class step: a field with the right Galois group, over
the realization one class down and ramified nowhere new.  Because the extension is Frattini, no
new square root of a rational number appears in it, so the blocks of the realization below account
for the square roots of the solution as well, and the invariant of the induction survives the step
untouched.  What the uncorrected solution does not control is the Frobenius defect at the ramified
primes, which is what the correction of the residues has to repair afterwards.

## Main results

* `InverseGalois.CFT.exists_solution_classStep`: **the rung of the tower of free objects is solvable
  with no new ramification** over a field satisfying Serre's condition at one level higher.
* `InverseGalois.CFT.exists_uncorrected_classStep`: the same over a strong Scholz realization, with
  the blocks carried along.
* `InverseGalois.CFT.exists_card_freePClass_dvd_two_pow`: the order of a free object is a power of
  two, so the level condition can always be met.

## Tags

Scholz–Reichardt, `2`-class, free object, central embedding problem, Frattini extension
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The Frattini condition on the automorphisms fixing the base -/

/-- **The automorphisms of a solution fixing the field below lie in the Frattini subgroup**, when
the kernel of the embedding problem does.  The Galois group of the solution is carried onto the
solving group by an isomorphism compatible with the problem, and the Frattini subgroup is carried
along with it. -/
theorem ker_galRestrictLE_le_frattini_of_comp
    {A L : IntermediateField ℚ (AlgebraicClosure ℚ)} [Normal ℚ ↥A] (hAL : A ≤ L)
    {G H : Type*} [Group G] [Group H] {f : G →* H} (hfr : f.ker ≤ frattini G)
    {e : Gal(↥A/ℚ) ≃* H} {ψ : Gal(↥L/ℚ) ≃* G}
    (hcomp : ∀ τ, f (ψ τ) = e (galRestrictLE hAL τ)) :
    (galRestrictLE hAL).ker ≤ frattini Gal(↥L/ℚ) := by
  intro σ hσ
  have hker : ψ σ ∈ f.ker := by
    rw [MonoidHom.mem_ker, hcomp σ, MonoidHom.mem_ker.mp hσ, map_one]
  have hcomap : frattini G ≤ (frattini Gal(↥L/ℚ)).comap ψ.symm.toMonoidHom :=
    frattini_le_comap_frattini_of_surjective ψ.symm.surjective
  simpa using hcomap (hfr hker)

/-! ### The level condition on the free objects -/

/-- **The order of a free object of `2`-class `c` is a power of two**, so the level condition of the
class step can always be met by taking the level large enough. -/
theorem exists_card_freePClass_dvd_two_pow (δ c : ℕ) :
    ∃ N : ℕ, Nat.card (FreePClass 2 δ c) ∣ 2 ^ N := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (FreePClass.isPGroup 2 δ c)
  exact ⟨n, hn ▸ dvd_rfl⟩

/-! ### The uncorrected solution of the class step -/

/-- **The rung of the tower of free objects is solvable with no new ramification.**  The kernel of
the projection from `2`-class `c + 1` to `2`-class `c` is central, of exponent two and, the class
below being at least one, inside the Frattini subgroup, so the problem is a central Frattini
embedding problem with elementary abelian kernel; over a field satisfying Serre's condition at one
level above the order of the group below, such a problem has a solution ramified nowhere outside the
field it solves over. -/
theorem exists_solution_classStep {δ c N : ℕ} (hc : 1 ≤ c)
    (hdvd : Nat.card (FreePClass 2 δ c) ∣ 2 ^ N)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hsch : IsScholz 2 (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* FreePClass 2 δ c) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAL : A ≤ L), NumberField ↥L ∧
      IsGalois ℚ ↥L ∧ ramifiedSet ↥L ⊆ ramifiedSet ↥A ∧
      ∃ ψ : Gal(↥L/ℚ) ≃* FreePClass 2 δ (c + 1),
        ∀ τ, FreePClass.proj 2 δ c (ψ τ) = e (galRestrictLE hAL τ) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_galEquiv_ramifiedSet_subset_elemAbTwo (FreePClass.proj_surjective 2 δ c)
    (FreePClass.isPGroup 2 δ (c + 1)) (FreePClass.ker_proj_le_center 2 δ c)
    (FreePClass.ker_proj_le_frattini 2 δ c hc)
    (fun _ hz => FreePClass.pow_eq_one_of_mem_ker_proj 2 δ c hz) hdvd A hsch e

/-- **The class step over a strong Scholz realization, with the blocks carried along.**  The
solution of the rung ramifies nowhere new, and being a Frattini extension it contains no new square
root of a rational number, so the blocks of the realization below still account for the square roots
of the solution. -/
theorem exists_uncorrected_classStep {δ c N : ℕ} (hc : 1 ≤ c)
    (hdvd : Nat.card (FreePClass 2 δ c) ∣ 2 ^ N) (R : StrongScholzRealization δ c (N + 1)) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAL : R.carrier ≤ L) (_ : NumberField ↥L),
      IsGalois ℚ ↥L ∧ ramifiedSet ↥L ⊆ ramifiedSet ↥R.carrier ∧ IsBlockSpanned L R.block ∧
        ∃ ψ : Gal(↥L/ℚ) ≃* FreePClass 2 δ (c + 1),
          ∀ τ, FreePClass.proj 2 δ c (ψ τ) = R.galEquiv (galRestrictLE hAL τ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hAL, hNF, hGal, hram, ψ, hcomp⟩ :=
    exists_solution_classStep hc hdvd R.carrier R.isScholz R.galEquiv
  haveI := hNF
  haveI := hGal
  refine ⟨L, hAL, hNF, hGal, hram, ?_, ψ, hcomp⟩
  exact R.isBlockSpanned.of_le_of_ker_le_frattini hAL
    (ker_galRestrictLE_le_frattini_of_comp hAL (FreePClass.ker_proj_le_frattini 2 δ c hc) hcomp)

end InverseGalois.CFT
