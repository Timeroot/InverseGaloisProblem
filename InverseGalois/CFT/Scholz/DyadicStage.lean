/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicLiftCorrection
import InverseGalois.CFT.Scholz.DyadicStageTransition
import InverseGalois.Solvable.CentralDualChain

/-!
# A stage of the dyadic climb

At the prime two the central step of the Scholz–Reichardt induction cannot be solved in one go: the
kernel of the projection between two consecutive free objects is a whole elementary abelian group,
while the residue correction is only available for a kernel of order two.  The way round is to
climb, cutting that kernel down one hyperplane at a time and correcting at every stage.

A stage of the climb is a cover of the realization one class lower, together with the subgroup of
the kernel the climb has cut down to, the finite set of primes the correction has to watch, and the
Scholz conditions on the subfield that subgroup cuts out of the cover.  What makes the climb go is
the extra condition carried along: every hyperplane of the current subgroup cuts out a subfield all
of whose blocks have vanishing obstruction.  That is exactly the hypothesis the residue correction
on a cover asks for, and it is what a stage has to re-establish for its successor — which is
possible because putting the element the stage was built on back into a subgroup changes neither
the hyperplane condition nor the obstruction of any block.

Once the subgroup has been cut down to the trivial one the cover itself is the field cut out, and
the square roots and the identification of the group carried by the realization below turn it into
a realization of the free object of the next class.

## Main results

* `InverseGalois.CFT.ClimbStage`: the data of one stage of the dyadic climb.
* `InverseGalois.CFT.ClimbStage.congr`: a stage transports along an equality of subgroups.
* `InverseGalois.CFT.ClimbStage.toRealization`: **a stage that has cut the kernel down to the
  trivial subgroup is a strong Scholz realization of the free object of the next class.**
* `InverseGalois.CFT.ClimbStage.step`: **one stage of the dyadic climb**, producing from a
  character not vanishing somewhere on the current subgroup a stage over the hyperplane it cuts.
* `InverseGalois.CFT.ClimbStage.exists_bot_of_chain`: a stage descends along a list of characters
  separating the points of the subgroup it has cut down to.
* `InverseGalois.CFT.ClimbStage.nonempty_realization`: **a stage over the whole kernel of the
  projection is a strong Scholz realization of the free object of the next `2`-class.**

## Tags

Scholz–Reichardt, Shafarevich, central embedding problem, block, cover, hyperplane, prime two
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Transporting the conditions along an equality of fields -/

section Transport

variable {E E' : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥E] [NumberField ↥E']
  {ℓ N q : ℕ}

omit [NumberField ↥E] in
private theorem ramifiedSet_of_eq (h : E = E') : ramifiedSet ↥E = ramifiedSet ↥E' := by
  subst h
  rfl

private theorem blockDefect_of_eq (h : E = E') (B : Finset ℕ) :
    blockDefect ↥E B = blockDefect ↥E' B := by
  subst h
  rfl

private theorem isSplitInertiaAt_of_eq (h : E = E') (hq : IsSplitInertiaAt ↥E q) :
    IsSplitInertiaAt ↥E' q := by
  subst h
  exact hq

private theorem splitsCompletely_of_eq (h : E = E') (hq : SplitsCompletely ↥E q) :
    SplitsCompletely ↥E' q := by
  subst h
  exact hq

private theorem isScholz_of_eq (h : E = E') (hE : IsScholz ℓ N ↥E) : IsScholz ℓ N ↥E' := by
  subst h
  exact hE

private theorem isScholzOver_of_eq {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
    (h : E = E') (hE : IsScholzOver ℓ N ↥E ↥L) : IsScholzOver ℓ N ↥E' ↥L := by
  subst h
  exact hE

end Transport

/-- Two equal normal subgroups cut the same obstruction out of a cover. -/
private theorem blockDefect_cutField_congr {T : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [NumberField ↥T] [IsGalois ℚ ↥T] {G : Type*} [Group G] {U U' : Subgroup G} [U.Normal]
    [U'.Normal] (h : U = U') (Ψ : Gal(↥T/ℚ) →* G) (B : Finset ℕ) :
    blockDefect ↥(cutField ((QuotientGroup.mk' U).comp Ψ)) B
      = blockDefect ↥(cutField ((QuotientGroup.mk' U').comp Ψ)) B := by
  subst h
  rfl

/-! ### The data of a stage -/

/-- **One stage of the dyadic climb.**  A cover of the realization `R` of the free object of
`2`-class `n + 1` realising the free object of `2`-class `n + 2`, a subgroup `Y` of the kernel of
the projection between them that the climb has cut down to, and a finite set of primes carrying the
Scholz conditions for the subfield `Y` cuts out of the cover.  The last field is the invariant the
climb propagates: every subgroup cut out of `Y` by a character has all of its blocks unobstructed
in the subfield it cuts out of the cover. -/
structure ClimbStage {d n M : ℕ} (R : StrongScholzRealization d (n + 1) M) (N : ℕ)
    (Y : Subgroup (FreePClass 2 d (n + 2))) [Y.Normal] where
  /-- The cover, realising the free object of `2`-class `n + 2`. -/
  cover : IntermediateField ℚ (AlgebraicClosure ℚ)
  [numberField : NumberField ↥cover]
  [isGalois : IsGalois ℚ ↥cover]
  /-- The realization the climb starts from lies inside the cover. -/
  le : R.carrier ≤ cover
  /-- The identification of the group of the cover with the free object. -/
  galEquiv : Gal(↥cover/ℚ) ≃* FreePClass 2 d (n + 2)
  /-- The identification is compatible with the one carried by the realization below. -/
  comp : ∀ τ, FreePClass.proj 2 d (n + 1) (galEquiv τ) = R.galEquiv (galRestrictLE le τ)
  /-- The subgroup cut down to lies in the kernel of the projection. -/
  le_ker : Y ≤ (FreePClass.proj 2 d (n + 1)).ker
  /-- The primes the stage keeps track of. -/
  primes : Finset ℕ
  /-- The primes kept track of are prime. -/
  primes_prime : ∀ q ∈ primes, q.Prime
  /-- The primes kept track of are congruent to one modulo four. -/
  primes_mod_four : ∀ q ∈ primes, q % 4 = 1
  /-- Every block is made of primes kept track of. -/
  block_subset : ∀ i, R.block i ⊆ primes
  /-- The cover ramifies only at primes kept track of. -/
  cover_ramified : ramifiedSet ↥cover ⊆ primes
  /-- Every prime kept track of and unramified in the subfield cut out splits completely there. -/
  base_splits : ∀ q ∈ primes,
    q ∉ ramifiedSet ↥(cutField ((QuotientGroup.mk' Y).comp galEquiv.toMonoidHom)) →
      SplitsCompletely ↥(cutField ((QuotientGroup.mk' Y).comp galEquiv.toMonoidHom)) q
  /-- The subfield cut out satisfies Serre's condition. -/
  base_isScholz :
    IsScholz 2 (N + 2) ↥(cutField ((QuotientGroup.mk' Y).comp galEquiv.toMonoidHom))
  /-- The cover ramifies harmlessly over the subfield cut out. -/
  cover_over : IsScholzOver 2 (N + 2)
    ↥(cutField ((QuotientGroup.mk' Y).comp galEquiv.toMonoidHom)) ↥cover
  /-- **The invariant of the climb**: every subgroup a character cuts out of `Y` leaves all the
  blocks unobstructed in the subfield it cuts out of the cover. -/
  defect : ∀ (V : Subgroup (FreePClass 2 d (n + 2))) [V.Normal],
    (∃ φ : Additive ↥((FreePClass.proj 2 d (n + 1)).ker) →+ ZMod 2,
      V = Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) φ) →
      ∀ i, blockDefect ↥(cutField ((QuotientGroup.mk' V).comp galEquiv.toMonoidHom))
        (R.block i) = 0

attribute [instance] ClimbStage.numberField ClimbStage.isGalois

namespace ClimbStage

variable {d n M N : ℕ} {R : StrongScholzRealization d (n + 1) M}
  {Y : Subgroup (FreePClass 2 d (n + 2))} [Y.Normal]

/-- A stage transports along an equality of subgroups. -/
def congr (st : ClimbStage R N Y) (Y' : Subgroup (FreePClass 2 d (n + 2))) [Y'.Normal]
    (h : Y' = Y) : ClimbStage R N Y' := by
  subst h
  exact st

/-! ### The end of the climb -/

/-- The trivial subgroup cuts out the whole cover. -/
theorem cutField_bot (st : ClimbStage R N (⊥ : Subgroup (FreePClass 2 d (n + 2)))) :
    cutField ((QuotientGroup.mk' (⊥ : Subgroup (FreePClass 2 d (n + 2)))).comp
      st.galEquiv.toMonoidHom) = st.cover := by
  refine cutField_eq_self_of_ker_eq_bot _ ?_
  rw [ker_mk'_comp, MonoidHom.comap_bot, MonoidHom.ker_eq_bot_iff]
  exact st.galEquiv.injective

/-- **A stage that has cut the kernel down to the trivial subgroup is a strong Scholz realization
of the free object of the next `2`-class.**  The cover is then the field the stage has cut out, so
it satisfies Serre's condition; the blocks, the square roots and their signs come from the
realization below, read inside the cover. -/
noncomputable def toRealization (st : ClimbStage R N (⊥ : Subgroup (FreePClass 2 d (n + 2)))) :
    StrongScholzRealization d (n + 2) N where
  carrier := st.cover
  isScholz := (isScholz_of_eq st.cutField_bot st.base_isScholz).mono (by omega)
  block := R.block
  blockPrime := R.blockPrime
  blockDisjoint := R.blockDisjoint
  galEquiv := st.galEquiv
  sqrt := R.sqrtIn st.le
  sqrt_sq := R.sqrtIn_sq st.le
  sqrtSign_gen := R.sqrtSign_gen_cover st.le st.galEquiv st.comp

/-! ### One stage of the climb -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **One stage of the dyadic climb.**  A character not vanishing at an element of the current
subgroup cuts it down to a hyperplane, and the two quotients by the subgroup and by the hyperplane
differ by a kernel of order two lifting to the cyclic group generated by the omitted element.  That
is a central Frattini embedding problem over the field the current subgroup cuts out of the cover,
and the invariant of the stage says exactly that the obstruction of every block of the field the
hyperplane cuts out vanishes; so the residue correction on the cover applies and produces a solution
satisfying Serre's condition and split at every prime kept track of.

The new cover carries the invariant one step further: a subgroup cut out of the hyperplane by a
character becomes, after the omitted element is put back, a subgroup cut out of the old subgroup by
a corrected character, and putting that element back changes neither the field the old subgroup
cuts out of the old cover nor the obstruction of any block. -/
theorem step (st : ClimbStage R N Y)
    (β : Additive ↥((FreePClass.proj 2 d (n + 1)).ker) →+ ZMod 2)
    {w : FreePClass 2 d (n + 2)} (hwY : w ∈ Y)
    (hβw : charValue ((FreePClass.proj 2 d (n + 1)).ker) β w ≠ 0)
    (Y' : Subgroup (FreePClass 2 d (n + 2))) [Y'.Normal]
    (hY' : Y' = Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) β)
    (hcase : ∀ i, FreePClass.zGen 2 d (n + 1) i ∈ Y' ∨
      FreePClass.zGen 2 d (n + 1) i ∉ Y ∨
      w ∈ Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i)) :
    Nonempty (ClimbStage R N Y') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  have hZc : (FreePClass.proj 2 d (n + 1)).ker ≤ Subgroup.center (FreePClass 2 d (n + 2)) :=
    FreePClass.ker_proj_le_center 2 d (n + 1)
  have hZfr : (FreePClass.proj 2 d (n + 1)).ker ≤ frattini (FreePClass 2 d (n + 2)) :=
    FreePClass.ker_proj_le_frattini 2 d (n + 1) (Nat.le_add_left 1 n)
  -- the hyperplane and the element it omits
  have hY'Y : Y' ≤ Y := by rw [hY']; exact inf_le_left
  have hY'Z : Y' ≤ (FreePClass.proj 2 d (n + 1)).ker := hY'Y.trans st.le_ker
  have hwZ : w ∈ (FreePClass.proj 2 d (n + 1)).ker := st.le_ker hwY
  have hw2 : w ^ 2 = 1 := FreePClass.pow_eq_one_of_mem_ker_proj 2 d (n + 1) hwZ
  have hwY' : w ∉ Y' := by
    intro hmem
    rw [hY', Subgroup.mem_inf, mem_charKer] at hmem
    exact hβw hmem.2.2
  have hsup : Y' ⊔ Subgroup.zpowers w = Y := by
    rw [hY']
    exact sup_inf_charKer_zpowers st.le_ker hwY hβw
  haveI : (Subgroup.zpowers w).Normal := normal_of_le_center (Subgroup.zpowers_le.mpr (hZc hwZ))
  -- the embedding problem posed by the two quotients
  have hfg : ∀ x : FreePClass 2 d (n + 2),
      QuotientGroup.mk' Y x = quotientStep hY'Y (QuotientGroup.mk' Y' x) := fun _ => rfl
  have hZker : (QuotientGroup.mk' Y).ker ≤ Subgroup.center (FreePClass 2 d (n + 2)) := by
    rw [QuotientGroup.ker_mk']
    exact st.le_ker.trans hZc
  have hfrker : (QuotientGroup.mk' Y).ker ≤ frattini (FreePClass 2 d (n + 2)) := by
    rw [QuotientGroup.ker_mk']
    exact st.le_ker.trans hZfr
  have hcard : Nat.card ↥(quotientStep hY'Y).ker = 2 := card_ker_quotientStep hY'Y hsup hw2 hwY'
  obtain ⟨s, hsw, hs⟩ := exists_section_quotientStep hY'Y hsup hw2 hwY'
  -- the field the current subgroup cuts out of the cover
  have hAsurj : Function.Surjective ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom) :=
    (QuotientGroup.mk'_surjective Y).comp st.galEquiv.surjective
  have hAT : cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom) ≤ st.cover :=
    cutField_le _
  have hcomp₀ : ∀ τ, QuotientGroup.mk' Y (st.galEquiv τ)
      = galEquivCutField _ hAsurj (galRestrictLE hAT τ) :=
    fun τ => (galEquivCutField_galRestrictLE _ hAsurj τ).symm
  have hcutR : cutField ((FreePClass.proj 2 d (n + 1)).comp st.galEquiv.toMonoidHom) = R.carrier :=
    cutField_eq_of_galEquiv_comp st.le R.galEquiv st.galEquiv (FreePClass.proj 2 d (n + 1))
      fun τ => (st.comp τ).symm
  have hRA : R.carrier ≤ cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom) := by
    rw [← hcutR]
    refine cutField_le_cutField _ _ ?_
    rw [ker_mk'_comp, ← MonoidHom.comap_ker]
    exact Subgroup.comap_mono st.le_ker
  -- the blocks account for the square roots of that field
  have hfrT : (galRestrictLE st.le).ker ≤ frattini Gal(↥st.cover/ℚ) :=
    ker_galRestrictLE_le_frattini_of_comp st.le hZfr st.comp
  have hspanT : IsBlockSpanned st.cover R.block :=
    (R.isBlockSpanned (Nat.le_add_left 1 n)).of_le_of_ker_le_frattini st.le hfrT
  have hspan : IsBlockSpanned (cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom))
      R.block := by
    rintro S hS b ⟨u, huA, hu⟩
    exact hspanT S hS b ⟨u, hAT huA, hu⟩
  have hAS : ∀ q ∈ ramifiedSet ↥(cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom)),
      q ∈ st.primes := fun q hq => st.cover_ramified (ramifiedSet_of_le hAT hq)
  have hdefect : ∀ i, blockDefect
      ↥(cutField ((QuotientGroup.mk' Y').comp st.galEquiv.toMonoidHom)) (R.block i) = 0 :=
    st.defect Y' ⟨β, hY'⟩
  -- the residue correction on the cover
  obtain ⟨E, T', hAE, hET', instE, instEG, instT', instT'G, hschE, hsplitE, hramT', hlevelT',
      ψ, Ψ, hfψ, hψΨ, hinv⟩ :=
    exists_scholz_solution_lift_two_blockDefect (N := N + 1) (f := quotientStep hY'Y)
      (g := QuotientGroup.mk' Y') (fg := QuotientGroup.mk' Y) hfg (quotientStep_surjective hY'Y)
      (QuotientGroup.mk'_surjective Y') hZker hfrker hcard s hs
      (cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom)) st.base_isScholz
      (galEquivCutField _ hAsurj) st.cover hAT st.cover_over st.galEquiv hcomp₀ st.primes
      st.primes_prime hAS st.base_splits st.primes_mod_four hspan st.block_subset hdefect
  haveI := instE
  haveI := instEG
  haveI := instT'
  haveI := instT'G
  have hEcut : cutField ((QuotientGroup.mk' Y').comp Ψ.toMonoidHom) = E :=
    cutField_eq_of_galEquiv_comp hET' ψ Ψ (QuotientGroup.mk' Y') hψΨ
  have hAT' : cutField ((QuotientGroup.mk' Y).comp st.galEquiv.toMonoidHom) ≤ T' := hAE.trans hET'
  have hRT' : R.carrier ≤ T' := hRA.trans hAT'
  -- the new identification is still compatible with the realization below
  have hcomp' : ∀ τ, FreePClass.proj 2 d (n + 1) (Ψ τ) = R.galEquiv (galRestrictLE hRT' τ) := by
    intro τ
    obtain ⟨υ, hυ⟩ := galRestrictLE_surjective hAT (galRestrictLE hAT' τ)
    have e1 : QuotientGroup.mk' Y (Ψ τ)
        = galEquivCutField _ hAsurj (galRestrictLE hAE (galRestrictLE hET' τ)) := by
      rw [← hfψ, hψΨ]
      rfl
    have e2 : galRestrictLE hAE (galRestrictLE hET' τ) = galRestrictLE hAT υ := by
      rw [galRestrictLE_galRestrictLE hAE hET' τ, hυ]
    have h1 : QuotientGroup.mk' Y (Ψ τ) = QuotientGroup.mk' Y (st.galEquiv υ) := by
      rw [e1, e2, ← hcomp₀ υ]
    have hmem : (st.galEquiv υ)⁻¹ * Ψ τ ∈ Y := by
      have hk : QuotientGroup.mk' Y ((st.galEquiv υ)⁻¹ * Ψ τ) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have hker := (MonoidHom.mem_ker (f := QuotientGroup.mk' Y)).mpr hk
      rwa [QuotientGroup.ker_mk'] at hker
    have h2 : FreePClass.proj 2 d (n + 1) (Ψ τ)
        = FreePClass.proj 2 d (n + 1) (st.galEquiv υ) := by
      have hk : FreePClass.proj 2 d (n + 1) ((st.galEquiv υ)⁻¹ * Ψ τ) = 1 :=
        MonoidHom.mem_ker.mp (st.le_ker hmem)
      rw [map_mul, map_inv, inv_mul_eq_one] at hk
      exact hk.symm
    rw [h2, st.comp υ]
    congr 1
    rw [← galRestrictLE_galRestrictLE hRA hAT' τ, ← hυ, galRestrictLE_galRestrictLE hRA hAT υ]
  refine ⟨{ cover := T'
            le := hRT'
            galEquiv := Ψ
            comp := hcomp'
            le_ker := hY'Z
            primes := st.primes ∪ (finite_ramifiedSet ↥E).toFinset
            primes_prime := ?_
            primes_mod_four := ?_
            block_subset := ?_
            cover_ramified := ?_
            base_splits := ?_
            base_isScholz := ?_
            cover_over := ?_
            defect := ?_ }⟩
  · intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact st.primes_prime q h
    · exact ((finite_ramifiedSet ↥E).mem_toFinset.mp h).1
  · intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact st.primes_mod_four q h
    · have hqE : q ∈ ramifiedSet ↥E := (finite_ramifiedSet ↥E).mem_toFinset.mp h
      have hmod : q ≡ 1 [MOD 4] := (hschE.isLevel q hqE).of_dvd ⟨2 ^ N, by ring⟩
      simpa [Nat.ModEq] using hmod
  · exact fun i => (st.block_subset i).trans Finset.subset_union_left
  · intro q hq
    rcases hramT' hq with h | h
    · exact Finset.mem_union_left _ (st.cover_ramified h)
    · exact Finset.mem_union_right _ ((finite_ramifiedSet ↥E).mem_toFinset.mpr h)
  · intro q hq hqr
    rw [ramifiedSet_of_eq hEcut] at hqr
    have hqS : q ∈ st.primes := by
      rcases Finset.mem_union.mp hq with h | h
      · exact h
      · exact absurd ((finite_ramifiedSet ↥E).mem_toFinset.mp h) hqr
    exact splitsCompletely_of_eq hEcut.symm
      (splitsCompletely_of_isSplitInertiaAt (st.primes_prime q hqS) (hsplitE q hqS) hqr)
  · exact isScholz_of_eq hEcut.symm hschE
  · refine isScholzOver_of_eq hEcut.symm ?_
    intro q hq
    by_cases hqE : q ∈ ramifiedSet ↥E
    · exact Or.inl hqE
    · have hqS : q ∈ st.primes := by
        rcases hramT' hq with h | h
        · exact st.cover_ramified h
        · exact absurd h hqE
      exact Or.inr ⟨hlevelT' q hq, splitsCompletely_of_isSplitInertiaAt (st.primes_prime q hqS)
        (hsplitE q hqS) hqE⟩
  · intro V hVn hex i
    haveI := hVn
    obtain ⟨φ, hV⟩ := hex
    obtain ⟨γ, hγ⟩ := exists_sup_zpowers_eq_inf_charKer β φ hwZ hwY hβw
    haveI : (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ).Normal :=
      normal_of_le_center (inf_le_left.trans (st.le_ker.trans hZc))
    have hVY' : V ≤ Y' := by rw [hV]; exact inf_le_left
    have hsupV : V ⊔ Subgroup.zpowers w
        = Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ := by
      rw [hV, hY']
      exact hγ
    have hcase' : FreePClass.zGen 2 d (n + 1) i ∈ Y' ∨
        FreePClass.zGen 2 d (n + 1) i ∉ Y' ⊔ Subgroup.zpowers w ∨
        w ∈ Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i) := by
      rw [hsup]
      exact hcase i
    have hq2 : ∀ q ∈ R.block i, q ≠ 2 := by
      intro q hq hq2
      have h4 := st.primes_mod_four q (st.block_subset i hq)
      rw [hq2] at h4
      norm_num at h4
    have hsplitb : ∀ q ∈ R.block i,
        IsSplitInertiaAt ↥(cutField ((QuotientGroup.mk' Y').comp Ψ.toMonoidHom)) q :=
      fun q hq => isSplitInertiaAt_of_eq hEcut.symm (hsplitE q (st.block_subset i hq))
    have h1 := blockDefect_cutField_sup_zpowers R hRT' Ψ hcomp' hY'Z hVY' hwZ hwY' hcase' hq2
      hsplitb
    have hzV : ∀ z : ↥(quotientStep hY'Y).ker,
        QuotientGroup.mk' (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ)
          ((s z : FreePClass 2 d (n + 2))) = 1 := by
      intro z
      have hmem : (s z : FreePClass 2 d (n + 2))
          ∈ Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ := by
        rw [← hsupV]
        exact Subgroup.mem_sup_right (hsw z)
      have hker : (s z : FreePClass 2 d (n + 2))
          ∈ (QuotientGroup.mk' (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ)).ker := by
        rwa [QuotientGroup.ker_mk']
      exact MonoidHom.mem_ker.mp hker
    have h2 := hinv _
      (QuotientGroup.mk' (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ)) hzV
    calc blockDefect ↥(cutField ((QuotientGroup.mk' V).comp Ψ.toMonoidHom)) (R.block i)
        = blockDefect ↥(cutField ((QuotientGroup.mk' (V ⊔ Subgroup.zpowers w)).comp
            Ψ.toMonoidHom)) (R.block i) := h1
      _ = blockDefect ↥(cutField ((QuotientGroup.mk'
            (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ)).comp Ψ.toMonoidHom))
            (R.block i) := blockDefect_cutField_congr hsupV Ψ.toMonoidHom (R.block i)
      _ = blockDefect ↥(cutField ((QuotientGroup.mk'
            (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) γ)).comp st.galEquiv.toMonoidHom))
            (R.block i) := blockDefect_of_eq h2 _
      _ = 0 := st.defect _ ⟨γ, rfl⟩ i

end ClimbStage

/-! ### Climbing the whole chain -/

section Chain

variable {d n M N : ℕ} {R : StrongScholzRealization d (n + 1) M}

namespace ClimbStage

/-- **A stage of the dyadic climb descends along a list of characters separating the points of the
subgroup it has cut down to.**  At each character of the list one of two things happens: either the
character vanishes on the whole subgroup, and the list moves on with the stage unchanged, or it does
not, and a stage over the hyperplane the character cuts is built on an element of the subgroup the
character does not kill.  That element is taken to be one of the distinguished central elements
whenever the character sees one of them, which is what makes every distinguished element either stay
inside the hyperplane, sit outside the subgroup already, or be the very element the stage is built
on. -/
theorem exists_bot_of_chain :
    ∀ (L : List (Additive ↥((FreePClass.proj 2 d (n + 1)).ker) →+ ZMod 2)),
      (∀ φ ∈ L, ∀ i₁ i₂ : Fin d,
          charValue ((FreePClass.proj 2 d (n + 1)).ker) φ (FreePClass.zGen 2 d (n + 1) i₁) ≠ 0 →
          charValue ((FreePClass.proj 2 d (n + 1)).ker) φ (FreePClass.zGen 2 d (n + 1) i₂) ≠ 0 →
          i₁ = i₂) →
        ∀ {Y : Subgroup (FreePClass 2 d (n + 2))} [Y.Normal], ClimbStage R N Y →
          (∀ g ∈ Y, (∀ φ ∈ L, charValue ((FreePClass.proj 2 d (n + 1)).ker) φ g = 0) → g = 1) →
            Nonempty (ClimbStage R N (⊥ : Subgroup (FreePClass 2 d (n + 2)))) := by
  classical
  intro L
  induction L with
  | nil =>
    intro _ Y _ st hsep
    exact ⟨st.congr ⊥ ((Subgroup.eq_bot_iff_forall Y).mpr fun g hg => hsep g hg (by simp)).symm⟩
  | cons φ L ih =>
    intro huniq Y _ st hsep
    have htail : ∀ ψ ∈ L, ∀ i₁ i₂ : Fin d,
        charValue ((FreePClass.proj 2 d (n + 1)).ker) ψ (FreePClass.zGen 2 d (n + 1) i₁) ≠ 0 →
        charValue ((FreePClass.proj 2 d (n + 1)).ker) ψ (FreePClass.zGen 2 d (n + 1) i₂) ≠ 0 →
        i₁ = i₂ := fun ψ hψ => huniq ψ (List.mem_cons_of_mem _ hψ)
    by_cases hall : ∀ y ∈ Y, charValue ((FreePClass.proj 2 d (n + 1)).ker) φ y = 0
    · refine ih htail st fun g hg hL => hsep g hg fun ψ hψ => ?_
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact hall g hg
      · exact hL ψ hψ'
    · push_neg at hall
      obtain ⟨w₀, hw₀Y, hw₀⟩ := hall
      obtain ⟨w, hwY, hφw, hcase⟩ : ∃ w ∈ Y,
          charValue ((FreePClass.proj 2 d (n + 1)).ker) φ w ≠ 0 ∧
            ∀ i : Fin d, FreePClass.zGen 2 d (n + 1) i
                ∈ Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) φ ∨
              FreePClass.zGen 2 d (n + 1) i ∉ Y ∨
              w ∈ Subgroup.zpowers (FreePClass.zGen 2 d (n + 1) i) := by
        by_cases hex : ∃ i : Fin d, FreePClass.zGen 2 d (n + 1) i ∈ Y ∧
            charValue ((FreePClass.proj 2 d (n + 1)).ker) φ (FreePClass.zGen 2 d (n + 1) i) ≠ 0
        · obtain ⟨i₀, hi₀Y, hi₀⟩ := hex
          refine ⟨_, hi₀Y, hi₀, fun i => ?_⟩
          by_cases hiY : FreePClass.zGen 2 d (n + 1) i ∈ Y
          · by_cases hv : charValue ((FreePClass.proj 2 d (n + 1)).ker) φ
                (FreePClass.zGen 2 d (n + 1) i) = 0
            · exact Or.inl (Subgroup.mem_inf.mpr ⟨hiY, (mem_charKer φ).mpr
                ⟨FreePClass.zGen_mem_ker_proj 2 d (n + 1) i, hv⟩⟩)
            · have hii : i₀ = i := huniq φ (by simp) i₀ i hi₀ hv
              subst hii
              exact Or.inr (Or.inr (Subgroup.mem_zpowers _))
          · exact Or.inr (Or.inl hiY)
        · push_neg at hex
          refine ⟨w₀, hw₀Y, hw₀, fun i => ?_⟩
          by_cases hiY : FreePClass.zGen 2 d (n + 1) i ∈ Y
          · exact Or.inl (Subgroup.mem_inf.mpr ⟨hiY, (mem_charKer φ).mpr
              ⟨FreePClass.zGen_mem_ker_proj 2 d (n + 1) i, hex i hiY⟩⟩)
          · exact Or.inr (Or.inl hiY)
      haveI : (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) φ).Normal :=
        normal_of_le_center (inf_le_left.trans
          (st.le_ker.trans (FreePClass.ker_proj_le_center 2 d (n + 1))))
      obtain ⟨st'⟩ :=
        st.step φ hwY hφw (Y ⊓ charKer ((FreePClass.proj 2 d (n + 1)).ker) φ) rfl hcase
      refine ih htail st' fun g hg hL => hsep g (Subgroup.mem_inf.mp hg).1 fun ψ hψ => ?_
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact ((mem_charKer _).mp (Subgroup.mem_inf.mp hg).2).2
      · exact hL ψ hψ'

/-- **The dyadic climb reaches the trivial subgroup.**  The distinguished central elements attached
to the generators are independent in the kernel of the projection, so they are listed by a family of
characters separating the points of that kernel, no two of which see the same distinguished element
and none of which sees two; climbing along that list cuts the kernel down to the trivial
subgroup. -/
theorem exists_bot (st : ClimbStage R N ((FreePClass.proj 2 d (n + 1)).ker)) :
    Nonempty (ClimbStage R N (⊥ : Subgroup (FreePClass 2 d (n + 2)))) := by
  classical
  haveI : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  obtain ⟨t, chi, hsep, -, huniq⟩ :=
    exists_charChain (z := fun i : Fin d => FreePClass.zGen 2 d (n + 1) i)
      (FreePClass.ker_proj_le_center 2 d (n + 1))
      (fun w hw => FreePClass.pow_eq_one_of_mem_ker_proj 2 d (n + 1) hw)
      (fun i => FreePClass.zGen_mem_ker_proj 2 d (n + 1) i)
      fun i => FreePClass.zGen_notMem_closure Nat.one_lt_two d (n + 1) i
  refine exists_bot_of_chain (List.ofFn chi) (fun φ hφ i₁ i₂ h₁ h₂ => ?_) st
    fun g hg hL => hsep g hg fun k => hL (chi k) (List.mem_ofFn.mpr ⟨k, rfl⟩)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hφ
  exact huniq k i₁ i₂ h₁ h₂

/-- **A stage of the dyadic climb over the whole kernel of the projection is a strong Scholz
realization of the free object of the next `2`-class.**  Climbing down to the trivial subgroup makes
the cover itself the field the climb cuts out. -/
theorem nonempty_realization (st : ClimbStage R N ((FreePClass.proj 2 d (n + 1)).ker)) :
    Nonempty (StrongScholzRealization d (n + 2) N) :=
  (exists_bot st).map toRealization

end ClimbStage

end Chain

end InverseGalois.CFT
