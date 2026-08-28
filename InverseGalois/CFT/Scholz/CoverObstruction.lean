/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicStageTransition
import InverseGalois.Solvable.DispositionCharacter

/-!
# The obstruction of a prime of a block, carried by a single central element

Over a cover realising the free object of one `2`-class more than the realization below it, the
obstruction of a prime of a block in the subfield cut out by a normal subgroup is a membership
statement in the group: the central part of an arithmetic Frobenius above the prime has to lie in
the subgroup together with the inertia subgroup.  Since the inertia subgroup at such a prime is
cyclic, the whole of that information is carried by two elements of the group, a generator of the
inertia subgroup and the central part, neither of which depends on the subgroup being tested.

Isolating those two elements is what lets the shrinking process of the dyadic induction see the
obstructions before it knows which subgroup it will end up testing.  The other half of what the
shrinking process needs is the compatibility of the whole picture with a collapse of the free
object of composite rank: the field a subgroup cuts out of the shrunken cover is the field its
preimage cuts out of the large cover, membership in a join with a preimage is membership of the
image in the join with the image, and the coordinates of a generator of an inertia subgroup are
merged by the collapse just as the blocks are.

## Main results

* `InverseGalois.CFT.mem_sup_comap_iff`: **membership in a join with a preimage is membership of
  the image in the join with the image.**
* `InverseGalois.CFT.cutField_comap_comp`: **a subgroup cuts the same field out of a smaller field
  as its preimage cuts out of a larger one.**
* `InverseGalois.FreePClass.coordClass_collapse_of_coordClass`: the collapse sends an element with
  the coordinates of a distinguished generator of a selected copy to one with the coordinates of the
  corresponding generator below.
* `InverseGalois.CFT.StrongScholzRealization.cutField_mk'_ker_proj`: the kernel of the projection
  cuts the realization below out of the cover.
* `InverseGalois.CFT.StrongScholzRealization.exists_centralPart`: **the obstruction of a prime of a
  block in every subfield of the cover at once is decided by two elements of the group**, a
  generator of the inertia subgroup and the central part of an arithmetic Frobenius.

## Tags

Scholz–Reichardt, Scholz obstruction, block, cover, inertia subgroup, collapse, Shafarevich
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois

/-! ### The collapse read on the coordinates and along the tower -/

namespace FreePClass

variable {n d r : ℕ}

/-- **The collapse sends an element with the coordinates of a distinguished generator of a selected
copy to one with the coordinates of the corresponding generator below.** -/
theorem coordClass_collapse_of_coordClass (a : Fin r → ZMod 2) {i : Fin d} {j : Fin r}
    (hj : a j = 1) {x : FreePClass 2 (d * r) (n + 1)}
    (hx : coordClass 2 (d * r) (Nat.succ_pos n) x
      = Multiplicative.ofAdd (Pi.single (finProdFinEquiv (i, j)) 1)) :
    coordClass 2 d (Nat.succ_pos n) (collapse a x) = Multiplicative.ofAdd (Pi.single i 1) := by
  have h : coordClass 2 d (Nat.succ_pos n) (collapse a x)
      = mergeChar d a (coordClass 2 (d * r) (Nat.succ_pos n) x) :=
    DFunLike.congr_fun (coordClass_comp_collapse (n := n) (d := d) a) x
  refine Multiplicative.toAdd.injective (funext fun i' => ?_)
  show Multiplicative.toAdd (coordClass 2 d (Nat.succ_pos n) (collapse a x)) i'
    = (Pi.single i (1 : ZMod 2) : Fin d → ZMod 2) i'
  rw [h, hx, mergeChar_single d a (i, j) i']
  simp [hj]

/-- **The collapse carries the kernel of the projection into the kernel of the projection.** -/
theorem collapse_mem_ker_proj (m d r : ℕ) (a : Fin r → ZMod 2)
    {x : FreePClass 2 (d * r) (m + 1 + 1)} (hx : x ∈ (proj 2 (d * r) (m + 1)).ker) :
    collapse a x ∈ (proj 2 d (m + 1)).ker := by
  have h : proj 2 d (m + 1) (collapse a x) = collapse a (proj 2 (d * r) (m + 1) x) :=
    DFunLike.congr_fun (proj_comp_collapse m d r a) x
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [h, hx, map_one]

end FreePClass

namespace CFT

/-! ### Membership in a join -/

section Group

variable {G H : Type*} [Group G] [Group H]

/-- A factor lying in one of two subgroups is invisible to membership in their join. -/
theorem mem_sup_mul_left_iff {J W : Subgroup G} {j θ : G} (hj : j ∈ J) :
    j * θ ∈ J ⊔ W ↔ θ ∈ J ⊔ W := by
  refine ⟨fun h => ?_, fun h => Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) h⟩
  have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (T := W) hj)) h
  rwa [inv_mul_cancel_left] at h2

/-- **Membership in a join with a preimage is membership of the image in the join with the
image.** -/
theorem mem_sup_comap_iff (f : G →* H) {J : Subgroup G} {V : Subgroup H} [hV : V.Normal] {x : G} :
    x ∈ J ⊔ V.comap f ↔ f x ∈ J.map f ⊔ V := by
  haveI : (V.comap f).Normal := hV.comap f
  constructor
  · intro hx
    obtain ⟨j, hj, y, hy, rfl⟩ := exists_mul_eq_of_mem_sup hx
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem f hj))
      (Subgroup.mem_sup_right (Subgroup.mem_comap.mp hy))
  · intro hx
    obtain ⟨j', hj', v, hv, hjv⟩ := exists_mul_eq_of_mem_sup hx
    rw [Subgroup.mem_map] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    have hmem : j⁻¹ * x ∈ V.comap f := by
      rw [Subgroup.mem_comap, map_mul, map_inv, hjv, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hv
    have hx' : x = j * (j⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hmem)

end Group

/-! ### Cutting a field out of a subextension -/

section CutField

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E E' : IntermediateField F L}
  [FiniteDimensional F ↥E] [IsGalois F ↥E] [FiniteDimensional F ↥E'] [IsGalois F ↥E']
  {G G' : Type*} [Group G] [Group G']

/-- **A subgroup cuts the same field out of a smaller field as its preimage cuts out of a larger
one**, whenever the two identifications of the Galois groups agree along restriction. -/
theorem cutField_comap_comp (h : E ≤ E') (ψ : Gal(↥E/F) →* G) (Ψ : Gal(↥E'/F) →* G') (g : G' →* G)
    (hg : ∀ τ, ψ (galRestrictLE h τ) = g (Ψ τ)) (V : Subgroup G) [hV : V.Normal] :
    cutField ((QuotientGroup.mk' V).comp ψ)
      = cutField ((QuotientGroup.mk' (V.comap g)).comp Ψ) := by
  haveI : (V.comap g).Normal := hV.comap g
  rw [← cutField_comp_galRestrictLE h ((QuotientGroup.mk' V).comp ψ)]
  refine cutField_eq_of_ker_eq _ _ ?_
  rw [MonoidHom.comp_assoc, ker_mk'_comp, ker_mk'_comp, Subgroup.comap_comap]
  exact congrArg (fun f => Subgroup.comap f V) (MonoidHom.ext hg)

end CutField

/-! ### Transporting the conditions along an equality of fields -/

section Transport

variable {E E' : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥E] [NumberField ↥E']
  {ℓ N q : ℕ}

omit [NumberField ↥E] in
/-- Equal fields ramify at the same primes. -/
theorem ramifiedSet_of_eq (h : E = E') : ramifiedSet ↥E = ramifiedSet ↥E' := by
  subst h
  rfl

/-- Equal fields carry the same obstruction at a prime. -/
theorem canonicalDefect_of_eq (h : E = E') (q : ℕ) :
    canonicalDefect ↥E q = canonicalDefect ↥E' q := by
  subst h
  rfl

/-- Equal fields carry the same obstruction of a block. -/
theorem blockDefect_of_eq (h : E = E') (B : Finset ℕ) :
    blockDefect ↥E B = blockDefect ↥E' B := by
  subst h
  rfl

/-- Residue degree one transports along an equality of fields. -/
theorem isSplitInertiaAt_of_eq (h : E = E') (hq : IsSplitInertiaAt ↥E q) :
    IsSplitInertiaAt ↥E' q := by
  subst h
  exact hq

/-- Splitting completely transports along an equality of fields. -/
theorem splitsCompletely_of_eq (h : E = E') (hq : SplitsCompletely ↥E q) :
    SplitsCompletely ↥E' q := by
  subst h
  exact hq

/-- Serre's condition transports along an equality of fields. -/
theorem isScholz_of_eq (h : E = E') (hE : IsScholz ℓ N ↥E) : IsScholz ℓ N ↥E' := by
  subst h
  exact hE

/-- Harmless ramification transports along an equality of the field below. -/
theorem isScholzOver_of_eq {M : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥M]
    (h : E = E') (hE : IsScholzOver ℓ N ↥E ↥M) : IsScholzOver ℓ N ↥E' ↥M := by
  subst h
  exact hE

end Transport

/-- **Harmless ramification weakens as the exponent decreases.** -/
theorem IsScholzOver.mono {ℓ N M : ℕ} {A E : Type*} [Field A] [NumberField A] [Field E]
    [NumberField E] (h : IsScholzOver ℓ N A E) (hMN : M ≤ N) : IsScholzOver ℓ M A E := fun q hq =>
  (h q hq).imp id fun hsp => ⟨hsp.1.of_dvd (pow_dvd_pow ℓ hMN), hsp.2⟩

/-! ### The central part of a Frobenius at a prime of a block -/

namespace StrongScholzRealization

variable {d n M q : ℕ} {T : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥T]
  [IsGalois ℚ ↥T]

/-- **The kernel of the projection cuts the realization below out of the cover.** -/
theorem cutField_mk'_ker_proj (R : StrongScholzRealization d (n + 1) M) (hAT : R.carrier ≤ T)
    (Ψ : Gal(↥T/ℚ) ≃* FreePClass 2 d (n + 2))
    (hcomp : ∀ τ, FreePClass.proj 2 d (n + 1) (Ψ τ) = R.galEquiv (galRestrictLE hAT τ)) :
    cutField ((QuotientGroup.mk' (FreePClass.proj 2 d (n + 1)).ker).comp Ψ.toMonoidHom)
      = R.carrier := by
  rw [← cutField_eq_of_galEquiv_comp hAT R.galEquiv Ψ (FreePClass.proj 2 d (n + 1))
    fun τ => (hcomp τ).symm]
  refine cutField_eq_of_ker_eq _ _ ?_
  rw [ker_mk'_comp, MonoidHom.comap_ker]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The obstruction of a prime of a block in every subfield of the cover at once is decided by
two elements of the group.**  The inertia subgroup at an odd prime of a block is cyclic, and its
generator has the coordinates of the distinguished generator attached to the block; the prime has
residue degree one in the realization below, which is the field the kernel of the projection cuts
out of the cover, so an arithmetic Frobenius above it factors into a part in the inertia subgroup
and a central part.  Testing a subgroup then only asks whether the central part lies in it together
with the inertia subgroup. -/
theorem exists_centralPart (R : StrongScholzRealization d (n + 1) M) (hAT : R.carrier ≤ T)
    (Ψ : Gal(↥T/ℚ) ≃* FreePClass 2 d (n + 2))
    (hcomp : ∀ τ, FreePClass.proj 2 d (n + 1) (Ψ τ) = R.galEquiv (galRestrictLE hAT τ))
    {i : Fin d} (hq : q ∈ R.block i) (hq2 : q ≠ 2) :
    ∃ x θ : FreePClass 2 d (n + 2), θ ∈ (FreePClass.proj 2 d (n + 1)).ker ∧
      FreePClass.coordClass 2 d (Nat.succ_pos (n + 1)) x = Multiplicative.ofAdd (Pi.single i 1) ∧
      ∀ (W : Subgroup (FreePClass 2 d (n + 2))) [W.Normal],
        canonicalDefect ↥(cutField ((QuotientGroup.mk' W).comp Ψ.toMonoidHom)) q = 0
          ↔ θ ∈ Subgroup.zpowers x ⊔ W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqp : q.Prime := R.blockPrime i q hq
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hqp
  obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 ↥T)
  haveI := hPp
  haveI := hPo
  haveI : Finite (𝓞 ↥T ⧸ P) := finite_quotient_of_ne_bot P (ne_bot_of_liesOver_natCast hqp hPo)
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(↥T/ℚ), IsArithFrobAt ℤ σ P :=
    ⟨_, IsArithFrobAt.arithFrobAt ℤ Gal(↥T/ℚ) P⟩
  obtain ⟨x, hx⟩ := exists_inertia_eq_zpowers hqp hq2
    ((FreePClass.isPGroup 2 d (n + 2)).of_equiv Ψ.symm) P
  have hcoord := R.coordClass_inertia_generator_cover hAT Ψ hcomp (Nat.succ_pos (n + 1)) hq hq2 P hx
  have hsplitR : IsSplitInertiaAt ↥R.carrier q :=
    R.isScholz.2.isSplitInertiaAt (R.mem_ramifiedSet_of_mem_block hq)
  have hsplit : IsSplitInertiaAt
      ↥(cutField ((QuotientGroup.mk' (FreePClass.proj 2 d (n + 1)).ker).comp Ψ.toMonoidHom)) q :=
    isSplitInertiaAt_of_eq (R.cutField_mk'_ker_proj hAT Ψ hcomp).symm hsplitR
  obtain ⟨j, hj, θ, hθZ, hxeq⟩ :=
    exists_mul_eq_of_isSplitInertiaAt Ψ (FreePClass.proj 2 d (n + 1)).ker hqp P hσ hsplit
  rw [hx, MonoidHom.map_zpowers] at hj
  simp only [MulEquiv.coe_toMonoidHom] at hj
  refine ⟨Ψ x, θ, hθZ, hcoord, fun W hW => ?_⟩
  haveI := hW
  rw [canonicalDefect_eq_zero_iff, isSplitInertiaAt_cutField_mk'_iff Ψ W hqp P hσ, hxeq, hx,
    MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom]
  exact mem_sup_mul_left_iff hj

end StrongScholzRealization

end CFT

end InverseGalois
