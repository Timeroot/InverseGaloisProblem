/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.ClassStepData
import InverseGalois.CFT.Scholz.CoverObstruction
import InverseGalois.CFT.Scholz.DyadicInduction
import InverseGalois.CFT.Scholz.DyadicStage

/-!
# Starting the dyadic climb

The dyadic climb needs a cover whose obstructions are already orthogonal to every hyperplane it
will ever test.  That cannot be arranged for a fixed rank: the obstruction of a block is a single
bit and there is no room to move it.  It can be arranged by paying with rank.  Realising the free
object of rank `d * r` instead of rank `d`, one has `r` copies of every block to choose from, and
collapsing the large free object along a vector of bits merges the selected copies of each row into
one block of the small one.  The obstruction of a merged block is the sum of the obstructions of the
copies selected, so choosing the vector of bits is choosing which sums have to vanish — and a
counting argument over the field with two elements says that for `r` large enough some nonzero
vector makes all of them vanish at once.

What makes that work is that the obstruction of a prime of a block, tested against an arbitrary
subgroup of the kernel of the projection, is decided by two elements of the group that do not depend
on the subgroup: a generator of the inertia subgroup at the prime and the central part of an
arithmetic Frobenius above it.  The central parts of the primes of a block multiply to one element
per copy of a row, the collapse carries those elements down, and the vector of bits is chosen to
kill the product of the ones selected.  For a hyperplane containing the distinguished central
element of the row there is then nothing to prove, since the obstruction of the row is exactly the
character read on that product; and for a hyperplane missing it the inertia subgroup already fills
up the whole kernel, so every prime of the row is unobstructed.

## Main results

* `InverseGalois.CFT.nonempty_strongScholzRealization_succ`: **a rung of the induction of large
  enough rank shrinks to a stage of the dyadic climb**, hence to a strong Scholz realization of the
  free object of the next `2`-class.
* `InverseGalois.CFT.isDyadicClassStepSolvable`: **the class-raising step of the dyadic
  Scholz–Reichardt induction.**

## Tags

Scholz–Reichardt, Shafarevich, `2`-class, free object, shrinking, block, obstruction, prime two
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Bookkeeping -/

private theorem zmod_two_eq_of_eq_zero_iff : ∀ u v : ZMod 2, (u = 0 ↔ v = 0) → u = v := by decide

private theorem zmod_two_eq_one_of_ne_zero : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by decide

private theorem blockDefect_biUnion {K : Type*} [Field K] [NumberField K] {ι : Type*}
    [DecidableEq ι] {s : Finset ι} {t : ι → Finset ℕ} (hs : (↑s : Set ι).PairwiseDisjoint t) :
    blockDefect K (s.biUnion t) = ∑ j ∈ s, blockDefect K (t j) := by
  simp only [blockDefect]
  exact Finset.sum_biUnion hs

private theorem blockDefect_eq_sum {K : Type*} [Field K] [NumberField K] {B : Finset ℕ}
    {F : ℕ → ZMod 2} (h : ∀ p ∈ B, canonicalDefect K p = F p) :
    blockDefect K B = ∑ p ∈ B, F p :=
  Finset.sum_congr rfl h

private theorem sum_filter_eq {r : ℕ} (a : Fin r → ZMod 2) {A : Type*} [AddCommMonoid A]
    (F : Fin r → A) :
    ∑ j ∈ Finset.univ.filter (fun j => a j = 1), F j
      = (((List.finRange r).filter fun j => decide (a j = 1)).map F).sum := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange r).filter _)]
  congr 1
  ext j
  simp

/-! ### The obstruction of a merged block -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **A merged block of the shrunken rung is unobstructed in the subfield a hyperplane cuts out of
the shrunken solution.**  Cutting a subfield out of the shrunken solution is cutting out the
subfield its preimage under the collapse cuts out of the large solution, so the obstruction of a
prime of the block is the obstruction the large cover records, which is the membership of the
central part in the inertia subgroup together with the preimage — equivalently, of the collapsed
central part in the collapsed inertia subgroup together with the hyperplane.  The collapsed inertia
subgroup meets the kernel of the projection in the distinguished central element of the row, so
either the hyperplane misses that element, and together they fill the whole kernel and every prime
of the row is unobstructed, or it contains it, and the obstruction of each prime is the character
read on the collapsed central part.  Summing over the row, the character is read on the collapsed
product, which the vector of bits was chosen to make trivial. -/
private theorem blockDefect_shrink_eq_zero {d r n M : ℕ} (D : ClassStepData (d * r) (n + 1) M)
    (X Θ : Fin (d * r) → ℕ → FreePClass 2 (d * r) (n + 2))
    (hΘker : ∀ k q, q ∈ D.base.block k → Θ k q ∈ (FreePClass.proj 2 (d * r) (n + 1)).ker)
    (hXcoord : ∀ k q, q ∈ D.base.block k →
      FreePClass.coordClass 2 (d * r) (Nat.succ_pos (n + 1)) (X k q)
        = Multiplicative.ofAdd (Pi.single k 1))
    (hΘdef : ∀ k q, q ∈ D.base.block k →
      ∀ (W : Subgroup (FreePClass 2 (d * r) (n + 2))) [W.Normal],
        canonicalDefect ↥(cutField ((QuotientGroup.mk' W).comp D.galEquiv.toMonoidHom)) q = 0
          ↔ Θ k q ∈ Subgroup.zpowers (X k q) ⊔ W)
    (a : Fin r → ZMod 2) {j₀ : Fin r} (hj₀ : a j₀ = 1)
    (Θrow : Fin d → Fin r → FreePClass 2 (d * r) (n + 2))
    (hΘrow : ∀ i j, Θrow i j
      = (((D.base.block (finProdFinEquiv (i, j))).toList).map (Θ (finProdFinEquiv (i, j)))).prod)
    (hrow : ∀ i : Fin d, (((List.finRange r).filter fun j => decide (a j = 1)).map
      fun j => FreePClass.collapse a (Θrow i j)).prod = 1)
    (V : Subgroup (FreePClass 2 d (n + 2))) [hV : V.Normal]
    (φ : Additive ↥((FreePClass.proj 2 d (n + 1)).ker) →+ ZMod 2)
    (hVeq : V = (FreePClass.proj 2 d (n + 1)).ker ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) φ)
    (i : Fin d) :
    blockDefect ↥(cutField ((QuotientGroup.mk' V).comp (D.shrink a hj₀).galEquiv.toMonoidHom))
      ((D.base.shrink a hj₀).block i) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hVc : (V.comap (FreePClass.collapse a)).Normal := hV.comap _
  have hVZ : V ≤ (FreePClass.proj 2 d (n + 1)).ker := by rw [hVeq]; exact inf_le_left
  have hblk : (D.base.shrink a hj₀).block i
      = (Finset.univ.filter fun j => a j = 1).biUnion
          fun j => D.base.block (finProdFinEquiv (i, j)) := rfl
  -- cutting a subfield out of the shrunken solution is cutting out its preimage upstairs
  have hbridge : cutField ((QuotientGroup.mk' V).comp (D.shrink a hj₀).galEquiv.toMonoidHom)
      = cutField ((QuotientGroup.mk' (V.comap (FreePClass.collapse a))).comp
          D.galEquiv.toMonoidHom) :=
    cutField_comap_comp (kerField_le (solutionCollapse D.galEquiv a))
      (D.shrink a hj₀).galEquiv.toMonoidHom D.galEquiv.toMonoidHom (FreePClass.collapse a)
      (fun τ => galEquivKerField_galRestrictLE (solutionCollapse D.galEquiv a)
        (solutionCollapse_surjective D.galEquiv a hj₀) τ) V
  -- the obstruction of a prime of the row, read downstairs
  have hkey : ∀ j : Fin r, a j = 1 → ∀ q ∈ D.base.block (finProdFinEquiv (i, j)),
      (canonicalDefect ↥(cutField ((QuotientGroup.mk' V).comp
          (D.shrink a hj₀).galEquiv.toMonoidHom)) q = 0
        ↔ FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) q)
            ∈ Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i) ⊔ V) := by
    intro j hj q hq
    have hcoordg : FreePClass.coordClass 2 d (Nat.succ_pos (n + 1))
        (FreePClass.collapse a (X (finProdFinEquiv (i, j)) q))
        = Multiplicative.ofAdd (Pi.single i 1) :=
      FreePClass.coordClass_collapse_of_coordClass a hj (hXcoord _ q hq)
    have hgΘ : FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) q)
        ∈ (FreePClass.proj 2 d (n + 1)).ker :=
      FreePClass.collapse_mem_ker_proj n d r a (hΘker _ q hq)
    rw [canonicalDefect_of_eq hbridge q, hΘdef _ q hq (V.comap (FreePClass.collapse a)),
      mem_sup_comap_iff (FreePClass.collapse a), MonoidHom.map_zpowers,
      mem_sup_iff_mem_inf_sup hVZ (Subgroup.one_mem _) hgΘ (one_mul _).symm,
      FreePClass.zpowers_inf_ker_proj hcoordg]
  by_cases hzg :
      charValue ((FreePClass.proj 2 d (n + 1)).ker) φ (FreePClass.zGen 2 d (n + 1) i) = 0
  · -- the hyperplane contains the distinguished central element of the row
    have hzV : FreePClass.zGen 2 d (n + 1) i ∈ V := by
      rw [hVeq]
      exact Subgroup.mem_inf.mpr ⟨FreePClass.zGen_mem_ker_proj 2 d (n + 1) i,
        (mem_charKer φ).mpr ⟨FreePClass.zGen_mem_ker_proj 2 d (n + 1) i, hzg⟩⟩
    have hsupV : Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i) ⊔ V = V :=
      sup_eq_right.mpr (Subgroup.zpowers_le.mpr hzV)
    have hval : ∀ j : Fin r, a j = 1 → ∀ q ∈ D.base.block (finProdFinEquiv (i, j)),
        canonicalDefect ↥(cutField ((QuotientGroup.mk' V).comp
            (D.shrink a hj₀).galEquiv.toMonoidHom)) q
          = charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
              (FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) q)) := by
      intro j hj q hq
      have hgΘ : FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) q)
          ∈ (FreePClass.proj 2 d (n + 1)).ker :=
        FreePClass.collapse_mem_ker_proj n d r a (hΘker _ q hq)
      refine zmod_two_eq_of_eq_zero_iff _ _ ?_
      rw [hkey j hj q hq, hsupV, hVeq, Subgroup.mem_inf, mem_charKer]
      exact ⟨fun h => h.2.2, fun h => ⟨hgΘ, hgΘ, h⟩⟩
    -- summing the character over the row
    have hstep : ∀ j ∈ Finset.univ.filter fun j : Fin r => a j = 1,
        blockDefect ↥(cutField ((QuotientGroup.mk' V).comp
            (D.shrink a hj₀).galEquiv.toMonoidHom)) (D.base.block (finProdFinEquiv (i, j)))
          = charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
              (FreePClass.collapse a (Θrow i j)) := by
      intro j hjmem
      have hj : a j = 1 := (Finset.mem_filter.mp hjmem).2
      have hlist : ∀ z ∈ ((D.base.block (finProdFinEquiv (i, j))).toList).map
          (Θ (finProdFinEquiv (i, j))), z ∈ (FreePClass.proj 2 (d * r) (n + 1)).ker := by
        intro z hz
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
        exact hΘker _ q (Finset.mem_toList.mp hq)
      have hprod : charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
          (FreePClass.collapse a (Θrow i j))
          = (((D.base.block (finProdFinEquiv (i, j))).toList).map fun p =>
              charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
                (FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) p))).sum := by
        rw [hΘrow i j, map_list_prod, charValue_list_prod φ (l := ((D.base.block
          (finProdFinEquiv (i, j))).toList).map (Θ (finProdFinEquiv (i, j))) |>.map
            (FreePClass.collapse a)) ?_, List.map_map, List.map_map]
        · rfl
        · intro z hz
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
          exact FreePClass.collapse_mem_ker_proj n d r a (hlist w hw)
      rw [blockDefect_eq_sum (F := fun p => charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
          (FreePClass.collapse a (Θ (finProdFinEquiv (i, j)) p))) fun p hp => hval j hj p hp,
        hprod, ← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
    have hzero : charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
        ((((List.finRange r).filter fun j => decide (a j = 1)).map fun j =>
          FreePClass.collapse a (Θrow i j)).prod)
        = ((((List.finRange r).filter fun j => decide (a j = 1)).map fun j =>
            FreePClass.collapse a (Θrow i j)).map
              (charValue ((FreePClass.proj 2 d (n + 1)).ker) φ)).sum := by
      refine charValue_list_prod φ ?_
      intro z hz
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
      refine FreePClass.collapse_mem_ker_proj n d r a ?_
      rw [hΘrow i j]
      refine Subgroup.list_prod_mem _ ?_
      intro w hw
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
      exact hΘker _ q (Finset.mem_toList.mp hq)
    rw [hrow i, charValue_one, List.map_map] at hzero
    rw [hblk, blockDefect_biUnion (D.base.shrinkBlock_pairwiseDisjoint a i),
      Finset.sum_congr rfl hstep, sum_filter_eq a]
    exact hzero.symm
  · -- the hyperplane misses the distinguished central element of the row
    have hsupZ : Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i) ⊔ V
        = (FreePClass.proj 2 d (n + 1)).ker := by
      rw [hVeq, sup_comm]
      exact sup_inf_charKer_zpowers le_rfl (FreePClass.zGen_mem_ker_proj 2 d (n + 1) i) hzg
    rw [hblk]
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨j, hjmem, hpj⟩ := Finset.mem_biUnion.mp hp
    have hj : a j = 1 := (Finset.mem_filter.mp hjmem).2
    rw [hkey j hj p hpj, hsupZ]
    exact FreePClass.collapse_mem_ker_proj n d r a (hΘker _ p hpj)

/-! ### The class-raising step -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **A rung of the induction of large enough rank shrinks to a strong Scholz realization of the
free object of the next `2`-class.**  Every prime of every block of the realization the rung stands
on has its obstruction recorded by two elements of the group, and the central parts of the primes of
a block multiply to one element per copy of a row.  A vector of bits killing the collapse of the
product of the selected copies of every row makes the shrunken rung a stage of the dyadic climb over
the whole kernel of the projection, and the climb turns that stage into a realization. -/
theorem nonempty_strongScholzRealization_succ {d r n N M : ℕ} (hNM : N + 2 ≤ M)
    (D : ClassStepData (d * r) (n + 1) M)
    (hcollapse : ∀ θ : Fin d → Fin r → FreePClass 2 (d * r) (n + 1 + 1),
      (∀ i j, θ i j ∈ lowerPCentralSeries 2 (FreePClass 2 (d * r) (n + 1 + 1)) (n + 1)) →
      ∃ a : Fin r → ZMod 2, a ≠ 0 ∧ ∀ i : Fin d,
        (((List.finRange r).filter fun j => decide (a j = 1)).map
          fun j => FreePClass.collapse a (θ i j)).prod = 1) :
    Nonempty (StrongScholzRealization d (n + 2) N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the two elements deciding the obstruction of each prime of each block
  have hex : ∀ (k : Fin (d * r)) (q : ℕ), q ∈ D.base.block k →
      ∃ x θ : FreePClass 2 (d * r) (n + 2), θ ∈ (FreePClass.proj 2 (d * r) (n + 1)).ker ∧
        FreePClass.coordClass 2 (d * r) (Nat.succ_pos (n + 1)) x
          = Multiplicative.ofAdd (Pi.single k 1) ∧
        ∀ (W : Subgroup (FreePClass 2 (d * r) (n + 2))) [W.Normal],
          (canonicalDefect ↥(cutField ((QuotientGroup.mk' W).comp D.galEquiv.toMonoidHom)) q = 0
            ↔ θ ∈ Subgroup.zpowers x ⊔ W) := fun k q hq =>
    D.base.exists_centralPart D.le D.galEquiv D.comp hq
      (D.base.ne_two_of_mem_block (by omega) hq)
  choose! X Θ hΘker hXcoord hΘdef using hex
  -- the central parts of a row, multiplied
  set Θrow : Fin d → Fin r → FreePClass 2 (d * r) (n + 2) := fun i j =>
    (((D.base.block (finProdFinEquiv (i, j))).toList).map (Θ (finProdFinEquiv (i, j)))).prod
  have hΘrow : ∀ i j, Θrow i j
      = (((D.base.block (finProdFinEquiv (i, j))).toList).map
          (Θ (finProdFinEquiv (i, j)))).prod := fun i j => rfl
  have hΘrowmem : ∀ i j,
      Θrow i j ∈ lowerPCentralSeries 2 (FreePClass 2 (d * r) (n + 1 + 1)) (n + 1) := by
    intro i j
    rw [← FreePClass.ker_proj 2 (d * r) (n + 1), hΘrow i j]
    refine Subgroup.list_prod_mem _ ?_
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact hΘker _ q (Finset.mem_toList.mp hq)
  obtain ⟨a, ha0, hrow⟩ := hcollapse Θrow hΘrowmem
  obtain ⟨j₀, hj₀'⟩ := Function.ne_iff.mp ha0
  have hj₀ : a j₀ = 1 := zmod_two_eq_one_of_ne_zero _ (by simpa using hj₀')
  -- the kernel of the projection cuts the shrunken realization out of the shrunken solution
  have hcut : cutField ((QuotientGroup.mk' (FreePClass.proj 2 d (n + 1)).ker).comp
      (D.shrink a hj₀).galEquiv.toMonoidHom) = (D.shrink a hj₀).base.carrier :=
    (D.shrink a hj₀).base.cutField_mk'_ker_proj (D.shrink a hj₀).le (D.shrink a hj₀).galEquiv
      (D.shrink a hj₀).comp
  refine ClimbStage.nonempty_realization (R := D.base.shrink a hj₀) (N := N)
    { cover := (D.shrink a hj₀).top
      le := (D.shrink a hj₀).le
      galEquiv := (D.shrink a hj₀).galEquiv
      comp := (D.shrink a hj₀).comp
      le_ker := le_rfl
      primes := (finite_ramifiedSet ↥(D.shrink a hj₀).top).toFinset
      primes_prime := fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1
      primes_mod_four := ?_
      block_subset := ?_
      cover_ramified := fun q hq => (Set.Finite.mem_toFinset _).mpr hq
      base_splits := ?_
      base_isScholz := isScholz_of_eq hcut.symm ((D.shrink a hj₀).base.isScholz.mono (by omega))
      cover_over := isScholzOver_of_eq hcut.symm ((D.shrink a hj₀).ramified.mono (by omega))
      defect := ?_ }
  · intro q hq
    have h1 : q ≡ 1 [MOD 2 ^ M] := by
      rcases (D.shrink a hj₀).ramified q ((Set.Finite.mem_toFinset _).mp hq) with hb | ⟨hm, -⟩
      · exact (D.shrink a hj₀).base.isScholz.1 q hb
      · exact hm
    have h4 : q ≡ 1 [MOD 4] := by
      have h24 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h24]
      exact h1.of_dvd (pow_dvd_pow 2 (by omega))
    simpa [Nat.ModEq] using h4
  · exact fun i q hq => (Set.Finite.mem_toFinset _).mpr (ramifiedSet_of_le (D.shrink a hj₀).le
      ((D.shrink a hj₀).base.mem_ramifiedSet_of_mem_block hq))
  · intro q hq hnr
    rw [ramifiedSet_of_eq hcut] at hnr
    exact splitsCompletely_of_eq hcut.symm
      (((D.shrink a hj₀).ramified q ((Set.Finite.mem_toFinset _).mp hq)).resolve_left hnr).2
  · rintro V hVn ⟨φ, hVeq⟩ i
    haveI := hVn
    exact blockDefect_shrink_eq_zero D X Θ hΘker hXcoord hΘdef a hj₀ Θrow hΘrow hrow V φ hVeq i

/-- **The class-raising step of the dyadic Scholz–Reichardt induction.**  Realising the free object
of a rank large enough for the counting argument, one turn of the induction produces a rung whose
shrinkings all carry the same free object of the next class; the vector of bits the counting
argument supplies picks the one whose obstructions vanish, and the dyadic climb corrects it into a
strong Scholz realization at the level asked for. -/
theorem isDyadicClassStepSolvable : IsDyadicClassStepSolvable := by
  intro c d N hc ih
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, -, hcollapse⟩ := FreePClass.exists_rankMultiplier (n + 1) d
  obtain ⟨k, hk⟩ := (FreePClass.isPGroup 2 (d * r) (n + 1)).exists_card_eq
  obtain ⟨R⟩ := ih (d * r) (max k (N + 2) + 1)
  obtain ⟨D⟩ := nonempty_classStepData (δ := d * r) (c := n + 1) (N := max k (N + 2)) hc
    (hk ▸ pow_dvd_pow 2 (le_max_left k (N + 2))) R
  exact nonempty_strongScholzRealization_succ (by omega) D hcollapse

end InverseGalois.CFT
