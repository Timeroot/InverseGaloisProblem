/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CyclotomicLevel
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.Solvable.Shafarevich.CyclicLift
import InverseGalois.Solvable.Shafarevich.LevelOneCharacter
import InverseGalois.Solvable.Shafarevich.LevelRung

/-!
# The archimedean places, named by the family

Local solvability of a step of the ladder was settled at the finite places, where the decomposition
subgroup of a prime is generated modulo inertia by the Frobenius and the property carried by the
solutions supplies the ramified case.  The family the local conditions are read on holds the
decomposition subgroups at the infinite places as well, and nothing in the finite-place argument
reaches them.

The way past that is not to solve the step there but to arrange that the step is never asked: the
conditions of local solvability are only read at the members of the wider family which the finite
one does not *name*, and the archimedean places can all be named, being finitely many up to
conjugacy over the base.  Naming them would ordinarily cost arithmetic, every clause of the package
which quantifies over the family having to be re-proved at the new members.  It costs nothing here.
The base realization cuts out a field containing a primitive root of unity whose order is the square
of the prime the ladder climbs, and that root is fixed by the kernel of the realization; an
automorphism fixing an archimedean place and a root of unity of order more than two is the identity,
because otherwise it would act on the place as complex conjugation and the root would be real.  So
the stabiliser of an archimedean place meets the kernel of the base realization trivially, and every
clause of the package which asks something of a member of the family *wherever the base realization
is trivial* asks it of the identity alone.

That makes the enlargement a matter of bookkeeping: a solution, a character of the first rung and a
repair along a family stay one along any larger family whose new members meet the kernel trivially,
and a subgroup meeting the kernel trivially has a finite elementary quotient for free.

## Main results

* `InverseGalois.Shafarevich.eq_one_of_mem_stabilizer_infinitePlace_of_mem_ker` — **an automorphism
  fixing an archimedean place which the base realization kills is the identity**, the kernel of the
  realization fixing the roots of unity of order the square of the prime.
* `InverseGalois.Shafarevich.exists_infinitePlace_family` — **finitely many archimedean places whose
  stabilisers have every archimedean stabiliser among their conjugates.**
* `InverseGalois.Shafarevich.hasLocalLift_isSplitTotallyRamified_of_forall_infinitePlace` — **the
  step is locally solvable along every decomposition subgroup** once the family names every
  archimedean stabiliser up to conjugacy.
* `InverseGalois.Shafarevich.hasRungData_append` — **the package the ladder consumes, for a family
  enlarged by subgroups the base realization meets trivially.**

## Tags

Shafarevich's theorem, embedding problem, archimedean place, root of unity, decomposition subgroup
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### A root of unity of order more than two is not real -/

section Root

/-- A primitive root of unity of order more than two is moved by complex conjugation. -/
theorem conj_ne_self_of_isPrimitiveRoot {z : ℂ} {m : ℕ} (hm : 2 < m) (hz : IsPrimitiveRoot z m) :
    (starRingEnd ℂ) z ≠ z := by
  intro hconj
  have him : z.im = 0 := Complex.conj_eq_iff_im.1 hconj
  have habs : |z.re| = ‖z‖ := Complex.abs_re_eq_norm.2 him
  have hone : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one (by omega)
  have hre : z.re = 1 ∨ z.re = -1 := abs_eq_abs.1 (by rw [habs, hone, abs_one])
  rcases hre with h1 | h1
  · exact hz.ne_one (by omega) (Complex.ext (by simp [h1]) (by simp [him]))
  · have hzneg : z = -1 := Complex.ext (by simp [h1]) (by simp [him])
    have hord : m = orderOf z := hz.eq_orderOf
    simp only [hzneg, orderOf_neg_one, ringChar.eq_zero, OfNat.zero_ne_ofNat,
      ↓reduceIte] at hord
    omega

end Root

/-! ### The stabiliser of an archimedean place meets the kernel trivially -/

section Stabilizer

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **An automorphism fixing an archimedean place and fixing a root of unity of order more than two
is the identity.**  Such an automorphism either fixes the place's embedding, and is then the
identity, or composes with it to complex conjugation, in which case the image of the root of unity
would be a real primitive root of unity of order more than two. -/
theorem eq_one_of_mem_stabilizer_infinitePlace_of_fixed {m : ℕ} (hm : 2 < m) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ m) (w : InfinitePlace Ω) {σ : Gal(Ω/k)}
    (hσ : σ ∈ stabilizer Gal(Ω/k) w) (hfix : σ ζ = ζ) : σ = 1 := by
  have hmk : InfinitePlace.mk (w.embedding.comp (σ.symm : Ω →+* Ω))
      = InfinitePlace.mk w.embedding := by
    rw [← InfinitePlace.smul_mk, InfinitePlace.mk_embedding]
    exact mem_stabilizer_iff.1 hσ
  have hsymm : σ.symm ζ = ζ := by
    have h0 : σ.symm (σ ζ) = σ.symm ζ := by rw [hfix]
    rw [AlgEquiv.symm_apply_apply] at h0
    exact h0.symm
  rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
  · have hid : ∀ x : Ω, σ x = x := by
      intro x
      have h1 : w.embedding (σ.symm (σ x)) = w.embedding (σ x) := RingHom.congr_fun h (σ x)
      rw [AlgEquiv.symm_apply_apply] at h1
      exact (w.embedding.injective h1).symm
    exact AlgEquiv.ext fun x => (hid x).trans (AlgEquiv.one_apply x).symm
  · have hc : (starRingEnd ℂ) (w.embedding (σ.symm ζ)) = w.embedding ζ := RingHom.congr_fun h ζ
    rw [hsymm] at hc
    exact absurd hc (conj_ne_self_of_isPrimitiveRoot hm
      (hζ.map_of_injective w.embedding.injective))

end Stabilizer

section Kernel

variable {ℓ : ℕ} {k Ω : Type} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {U : Type*} [Group U]

/-- **An automorphism fixing an archimedean place which the base realization kills is the
identity.**  The kernel of the realization fixes the roots of unity of order the square of the
prime, and that order is more than two. -/
theorem eq_one_of_mem_stabilizer_infinitePlace_of_mem_ker (hℓ : 2 ≤ ℓ) {φ : Gal(Ω/k) →* U}
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y) (w : InfinitePlace Ω)
    {x : Gal(Ω/k)} (hx : x ∈ stabilizer Gal(Ω/k) w) (hφ : φ x = 1) : x = 1 := by
  have hpos : 0 < ℓ * ℓ := Nat.mul_pos (by omega) (by omega)
  haveI : NeZero (ℓ * ℓ) := ⟨hpos.ne'⟩
  have hlt : 2 < ℓ * ℓ := by
    have h4 : 2 * 2 ≤ ℓ * ℓ := Nat.mul_le_mul hℓ hℓ
    omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isAlgClosure k Ω (ℓ * ℓ)
  obtain ⟨u, huval⟩ : ∃ u : Ωˣ, (u : Ω) = ζ := ⟨(hζ.isUnit hpos.ne').unit, IsUnit.unit_spec _⟩
  have hupow : u ^ (ℓ * ℓ) = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, huval, hζ.pow_eq_one, Units.val_one]
  have hfixu : x • u = u := hmu u hupow x (MonoidHom.mem_ker.2 hφ)
  have hfix : x ζ = ζ := by
    have h0 : x ((u : Ωˣ) : Ω) = ((u : Ωˣ) : Ω) := congrArg (fun t : Ωˣ => (t : Ω)) hfixu
    rwa [huval] at h0
  exact eq_one_of_mem_stabilizer_infinitePlace_of_fixed hlt hζ w hx hfix

end Kernel

/-! ### Finitely many archimedean places, up to conjugacy -/

section Family

variable (k Ω : Type*) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **Finitely many archimedean places of a Galois extension of a number field whose stabilisers
have every archimedean stabiliser among their conjugates.**  One place is chosen above each
archimedean place of the base, and any place is carried to the chosen one above the same place of
the base by an automorphism, which conjugates the stabilisers into one another. -/
theorem exists_infinitePlace_family :
    ∃ (s : ℕ) (W : Fin s → InfinitePlace Ω), ∀ w : InfinitePlace Ω,
      stabilizer Gal(Ω/k) w ∈ conjFamily fun μ => stabilizer Gal(Ω/k) (W μ) := by
  classical
  choose W hW using InfinitePlace.comap_surjective (k := k) (K := Ω)
  refine ⟨Fintype.card (InfinitePlace k),
    fun μ => W ((Fintype.equivFin (InfinitePlace k)).symm μ), fun w => ?_⟩
  obtain ⟨ρ, hρ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
    (k := k) (K := Ω) (w := W (w.comap (algebraMap k Ω))) (w' := w) (hW _)
  refine ⟨Fintype.equivFin (InfinitePlace k) (w.comap (algebraMap k Ω)), ρ, ?_⟩
  simp only [Equiv.symm_apply_apply]
  conv_lhs => rw [← hρ]
  exact stabilizer_smul_eq_stabilizer_map_conj ρ _

end Family

/-! ### Conjugates of an appended family -/

section Append

variable {Γ : Type*} [Group Γ] {t s : ℕ} (D : Fin t → Subgroup Γ) (E : Fin s → Subgroup Γ)

/-- A conjugate of a member of a family is a conjugate of a member of a family it is appended in
front of. -/
theorem conjFamily_append_left : conjFamily D ⊆ conjFamily (Fin.append D E) := by
  rintro _ ⟨ν, σ, rfl⟩
  exact ⟨Fin.castAdd s ν, σ, by rw [Fin.append_left]⟩

/-- A conjugate of a member of a family is a conjugate of a member of a family it is appended
behind. -/
theorem conjFamily_append_right : conjFamily E ⊆ conjFamily (Fin.append D E) := by
  rintro _ ⟨μ, σ, rfl⟩
  exact ⟨Fin.natAdd t μ, σ, by rw [Fin.append_right]⟩

end Append

/-! ### Subgroups the base realization meets trivially -/

section Free

variable {ℓ : ℕ} {U S : Type} [Group U] [Group S] {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- A subgroup all of whose elements are trivial has a finite elementary quotient. -/
theorem hasFiniteElementaryQuotient_of_forall_eq_one (ℓ : ℕ) {Γ : Type u} [Group Γ]
    [TopologicalSpace Γ] {D : Subgroup Γ} (h : ∀ x ∈ D, x = 1) :
    HasFiniteElementaryQuotient ℓ D := by
  refine ⟨PUnit, inferInstance, inferInstance, 1, fun M _ _ a _ => ⟨1, fun x => ?_⟩⟩
  have hx : x = 1 := Subtype.ext (h (x : Γ) x.2)
  rw [hx, _root_.map_one, _root_.map_one]

/-- **A solution along a family is a solution along any family whose new members the base
realization meets trivially**, the clause the family carries being an obligation at the elements
the base realization kills and there being none but the identity there. -/
theorem levelSolution_of_forall_mem {φ : Gal(Ω/k) →* U} {T T' : Set (Subgroup Gal(Ω/k))}
    {P : LevelProperty ℓ U S k Ω} {m j : ℕ} (h : LevelSolution ℓ U S φ T P m j)
    (hT : ∀ A ∈ T', A ∈ T ∨ ∀ x ∈ A, φ x = 1 → x = 1) :
    LevelSolution ℓ U S φ T' P m j := by
  obtain ⟨Φ, hsurj, hsm, hover, hfam, hP⟩ := h
  refine ⟨Φ, hsurj, hsm, hover, fun A hA x hxA hx => ?_, hP⟩
  rcases hT A hA with hmem | htriv
  · exact hfam A hmem x hxA hx
  · rw [htriv x hxA hx, _root_.map_one]

variable [Finite U] [Finite S]

omit [Finite U] [Finite S] in
/-- **The character of the first rung along a family serves any family whose new members the base
realization meets trivially.** -/
theorem hasLevelOneCharacter_of_forall_mem {φ : Gal(Ω/k) →* U} {T T' : Set (Subgroup Gal(Ω/k))}
    {n : ℕ} (h : HasLevelOneCharacter ℓ U S φ T n)
    (hT : ∀ A ∈ T', A ∈ T ∨ ∀ x ∈ A, φ x = 1 → x = 1) :
    HasLevelOneCharacter ℓ U S φ T' n := by
  obtain ⟨r, hr, χ, W, hnorm, hW, hWφ, hWχ, hTk, hram⟩ := h
  refine ⟨r, hr, χ, W, hnorm, hW, hWφ, hWχ, fun A hA x hxA hx u => ?_, hram⟩
  rcases hT A hA with hmem | htriv
  · exact hTk A hmem x hxA hx u
  · rw [htriv x hxA hx, mul_one, inv_mul_cancel]
    exact one_mem _

variable [Fact ℓ.Prime]

/-- **The repair of the property along a family serves any family holding it whose new members the
base realization meets trivially.** -/
theorem hasSolutionRepair_of_forall {n j : ℕ} {φ : Gal(Ω/k) →* U} {t t' : ℕ}
    {D : Fin t → Subgroup Gal(Ω/k)} {D' : Fin t' → Subgroup Gal(Ω/k)}
    {P : LevelProperty ℓ U S k Ω} (h : HasSolutionRepair ℓ U n S j φ D P)
    (hD : ∀ ν : Fin t, ∃ μ : Fin t', D' μ = D ν)
    (hD' : ∀ μ : Fin t', (∃ ν : Fin t, D' μ = D ν) ∨ ∀ x ∈ D' μ, φ x = 1 → x = 1) :
    HasSolutionRepair ℓ U n S j φ D' P := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun Φ f hsm hover hP hsurj hfsm hlift hfam => ?_⟩
  refine levelSolution_of_forall_mem (hN Φ f hsm hover hP hsurj hfsm hlift ?_) ?_
  · intro ν x hx hx1
    obtain ⟨μ, hμ⟩ := hD ν
    exact hfam μ x (by rw [hμ]; exact hx) hx1
  · rintro A ⟨μ, rfl⟩
    rcases hD' μ with ⟨ν, hν⟩ | htriv
    · exact Or.inl ⟨ν, hν.symm⟩
    · exact Or.inr htriv

end Free

/-! ### Local solvability along every decomposition subgroup -/

section Local

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω]

/-- **The step is locally solvable along every decomposition subgroup**, once the finite family
names every archimedean stabiliser up to conjugacy.

At a finite place the local solution comes from the Frobenius when the solution is unramified and
from the cyclic lifting supplied by the property when it is not; at an infinite place nothing is
asked, the stabiliser there being a conjugate of a named member of the family. -/
theorem hasLocalLift_isSplitTotallyRamified_of_forall_infinitePlace (hS : IsPGroup ℓ S)
    (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (hinf : ∀ w : InfinitePlace Ω, stabilizer Gal(Ω/k) w ∈ conjFamily D)
    (hD : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      stabilizer Gal(Ω/k) P ∉ conjFamily D → ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1) :
    HasLocalLift ℓ U n S j φ D (decompositionSubgroups k Ω) (IsSplitTotallyRamified ℓ U S φ) := by
  have hram : HasSplitRamifiedLift ℓ U n S j φ :=
    hasSplitRamifiedLift_of_hasCyclicLift ℓ U n S j hS φ fun P N _ _ _ hμ =>
      hasCyclicLift_of_fixed_rootsOfUnity ℓ (isClosed_stabilizer_ideal P) N
        fun ζ hζ σ => hμ ζ hζ (σ : Gal(Ω/k)) σ.2
  intro Φ hsm hover hfam hprop A hA hAD
  rcases hA with ⟨P, hPp, hPbot, hAP⟩ | ⟨w, rfl⟩
  · refine hasLocalLift_of_hasSplitRamifiedLift ℓ U n S j φ D {A} ?_ hD hram
      Φ hsm hover hfam hprop A rfl hAD
    intro B hB
    rw [Set.mem_singleton_iff] at hB
    subst hB
    exact ⟨P, hPp, hPbot, hAP⟩
  · exact absurd (hinf w) hAD

end Local

/-! ### The package, for an enlarged family -/

section Package

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
  [DiscreteTopology U] (S : Type) [Group S] [Finite S] {k Ω : Type*} [Field k] [Field Ω]
  [Algebra k Ω]

/-- **The package the ladder consumes, for a family enlarged by subgroups the base realization
meets trivially.**

The bottom of the ladder, the first rung and the repair of the property are read along the enlarged
family, and each of the three carries an obligation only at the elements the base realization kills;
at a new member there are none but the identity.  A new member has a finite elementary quotient for
the same reason, meeting the kernel trivially.  Local solvability and the shrinking away of the
locally trivial classes are asked of the enlarged family outright. -/
theorem hasRungData_append {φ : Gal(Ω/k) →* U} {t s : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}
    {E : Fin s → Subgroup Gal(Ω/k)} (hE : ∀ μ : Fin s, ∀ x ∈ E μ, φ x = 1 → x = 1)
    {T : Set (Subgroup Gal(Ω/k))} {P : LevelProperty ℓ U S k Ω}
    (hzero : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) P m 0)
    (hone : ∀ n : ℕ, LevelSolution ℓ U S φ (Set.range D) P n 1)
    (hstab : IsShrinkStable ℓ U S P)
    (hfeq : ∀ ν : Fin t, HasFiniteElementaryQuotient ℓ (D ν ⊓ φ.ker))
    (hlift : ∀ n j : ℕ, 1 ≤ j → HasLocalLift ℓ U n S j φ (Fin.append D E) T P)
    (hsha : ∀ n j : ℕ, 1 ≤ j → HasShrinkableSha ℓ U n S j φ T)
    (hrepair : ∀ n j : ℕ, 1 ≤ j → HasSolutionRepair ℓ U n S j φ D P) :
    HasRungData ℓ U S φ (Fin.append D E) T P := by
  have hrange : ∀ A ∈ Set.range (Fin.append D E), A ∈ Set.range D ∨ ∀ x ∈ A, φ x = 1 → x = 1 := by
    rintro A ⟨ν, rfl⟩
    refine Fin.addCases (motive := fun ν => Fin.append D E ν ∈ Set.range D ∨
      ∀ x ∈ Fin.append D E ν, φ x = 1 → x = 1) (fun i => ?_) (fun i => ?_) ν
    · exact Or.inl ⟨i, (Fin.append_left D E i).symm⟩
    · refine Or.inr ?_
      rw [Fin.append_right]
      exact hE i
  refine ⟨fun m => levelSolution_of_forall_mem (hzero m) hrange,
    fun m => levelSolution_of_forall_mem (hone m) hrange, hstab, fun ν => ?_,
    fun m j hj => ⟨hlift m j hj, hsha m j hj, ?_⟩⟩
  · refine Fin.addCases (motive := fun ν =>
      HasFiniteElementaryQuotient ℓ (Fin.append D E ν ⊓ φ.ker)) (fun i => ?_) (fun i => ?_) ν
    · simp only [Fin.append_left]
      exact hfeq i
    · simp only [Fin.append_right]
      refine hasFiniteElementaryQuotient_of_forall_eq_one ℓ fun x hx => ?_
      exact hE i x (Subgroup.mem_inf.1 hx).1 (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).2)
  · refine hasSolutionRepair_of_forall (hrepair m j hj)
      (fun ν => ⟨Fin.castAdd s ν, Fin.append_left D E ν⟩) fun μ => ?_
    refine Fin.addCases (motive := fun μ => (∃ ν : Fin t, Fin.append D E μ = D ν) ∨
      ∀ x ∈ Fin.append D E μ, φ x = 1 → x = 1) (fun i => ?_) (fun i => ?_) μ
    · exact Or.inl ⟨i, Fin.append_left D E i⟩
    · refine Or.inr ?_
      rw [Fin.append_right]
      exact hE i

end Package

end InverseGalois.Shafarevich
