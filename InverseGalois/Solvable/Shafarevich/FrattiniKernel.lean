/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.MinimalKernel
import InverseGalois.Solvable.Shafarevich.SplitAbelian

/-!
# Minimal kernels either split off or sit inside the Frattini subgroup

An embedding problem `π : E ↠ W` whose kernel `A` is abelian and *minimal* among the nontrivial
normal subgroups of `E` admits a sharp dichotomy.  Either `A` is contained in the Frattini subgroup
of `E`, or it has a proper supplement `M`, and then `A ⊓ M` is normal in `E`: it is normalized by
`M` because `A` is normal, and by `A` because `A` is commutative.  Minimality forces `A ⊓ M = ⊥`,
so `M` is a complement, `E` is the semidirect product `A ⋊ M`, and `M` maps isomorphically onto
`W`.  The embedding problem is then *split* with abelian kernel, a case that the wreath product
construction settles outright over `ℚ(T)`.

What is left is the Frattini case, and that is the arithmetic core of Shafarevich's theorem.

## Main results

* `Shafarevich.exists_isComplement'_of_not_le_frattini` — a minimal normal commutative subgroup not
  contained in the Frattini subgroup has a complement.
* `Shafarevich.FrattiniKernelEP`, `Shafarevich.FrattiniKernelEPRegular` — the residual arithmetic
  hypothesis: embedding problems whose kernel is a minimal elementary abelian normal subgroup
  *inside the Frattini subgroup*.
* `Shafarevich.SplitAbelianEP` — split embedding problems with abelian kernel, over `ℚ`.
* `Shafarevich.CyclicWreathEP` and `Shafarevich.splitAbelianEP_of_cyclicWreathEP` — the split half
  needs only wreath products by a finite *cyclic* group.
* `Shafarevich.elementaryAbelianKernel_of_frattini` — the dichotomy, for an arbitrary
  quotient-closed realization predicate.
* `Shafarevich.elementaryAbelianKernelEPRegular_of_frattiniKernelEPRegular` — over `ℚ(T)` the split
  half is unconditional, so the regular form of Shafarevich's theorem rests on the Frattini case
  alone.
* `Shafarevich.isSolvable_isRegularInverseGalois_of_frattiniKernelEPRegular` and
  `Shafarevich.isSolvable_isInverseGalois_of_frattiniKernelEP` — the resulting forms of
  Shafarevich's theorem.
-/

namespace Shafarevich

/-! ## Extracting a complement -/

variable {G : Type*} [Group G]

/-- **A minimal normal commutative subgroup not contained in the Frattini subgroup has a
complement.**

The Frattini subgroup is the intersection of the maximal subgroups, so a subgroup `A` outside it
has a proper supplement `M`.  The intersection `A ⊓ M` is normalized by `M`, because `A` is normal
in the ambient group, and by `A`, because `A` is commutative; hence it is normal in `A ⊔ M`, which
is everything.  Minimality leaves `A ⊓ M = ⊥` — the alternative `A ⊓ M = A` would put `A` inside
`M` and make `M` the whole group. -/
theorem exists_isComplement'_of_not_le_frattini [IsCoatomic (Subgroup G)] {A : Subgroup G}
    [hA : A.Normal] [IsMulCommutative ↥A]
    (hmin : ∀ N : Subgroup G, N.Normal → N ≤ A → N = ⊥ ∨ N = A) (hfr : ¬ A ≤ frattini G) :
    ∃ M : Subgroup G, A.IsComplement' M := by
  obtain ⟨M, hMne, hsup⟩ := exists_proper_supplement_of_not_le_frattini hfr
  -- Conjugation by an element of `M` preserves `A ⊓ M`.
  have hconj : ∀ u ∈ M, ∀ x ∈ A ⊓ M, u * x * u⁻¹ ∈ A ⊓ M := by
    rintro u hu x ⟨hxA, hxM⟩
    exact Subgroup.mem_inf.mpr
      ⟨hA.conj_mem x hxA u, M.mul_mem (M.mul_mem hu hxM) (M.inv_mem hu)⟩
  have hMle : M ≤ (A ⊓ M).normalizer := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    refine fun x => ⟨fun hx => hconj u hu x hx, fun hx => ?_⟩
    have h2 := hconj u⁻¹ (inv_mem hu) _ hx
    rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x by group] at h2
  -- Conjugation by an element of `A` fixes `A ⊓ M` pointwise.
  have hAle : A ≤ (A ⊓ M).normalizer := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfix : ∀ y ∈ A, a * y * a⁻¹ = y := by
      intro y hy
      rw [Subgroup.mul_comm_of_mem_isMulCommutative A ha hy]
      group
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hfix x hx.1]; exact hx
    · have hxA : x ∈ A := by
        have h3 := mul_mem (mul_mem (inv_mem ha) (Subgroup.mem_inf.mp hx).1) ha
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h3
      rwa [hfix x hxA] at hx
  have hnorm : (A ⊓ M).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← hsup]
    exact sup_le hAle hMle
  rcases hmin (A ⊓ M) hnorm inf_le_left with hbot | heq
  · refine ⟨M, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hbot) ?_⟩
    rw [← Subgroup.normal_mul A M, hsup, Subgroup.coe_top]
  · exact absurd ((sup_eq_right.mpr (inf_eq_left.mp heq)).symm.trans hsup) hMne

/-! ## The arithmetic hypotheses -/

/-- **Every embedding problem over `ℚ` whose minimal elementary abelian kernel lies inside the
Frattini subgroup is solvable.**

The residual half of `ElementaryAbelianKernelEP` once the split half has been separated off. -/
def FrattiniKernelEP : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime] (π : E →* W),
    Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
    (∀ x : ↥π.ker, x ^ p = 1) →
    (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) →
    π.ker ≠ ⊥ → π.ker ≤ frattini E →
    IsInverseGalois W → IsInverseGalois E

/-- **Every embedding problem whose minimal elementary abelian kernel lies inside the Frattini
subgroup is solvable regularly over `ℚ(T)`.**

The regular analogue of `FrattiniKernelEP`. -/
def FrattiniKernelEPRegular : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime] (π : E →* W),
    Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
    (∀ x : ↥π.ker, x ^ p = 1) →
    (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) →
    π.ker ≠ ⊥ → π.ker ≤ frattini E →
    IsRegularInverseGalois W → IsRegularInverseGalois E

/-- **Every split embedding problem over `ℚ` with finite abelian kernel is solvable.**

Ikeda's theorem.  Its regular analogue over `ℚ(T)` is unconditional in this development
(`Shafarevich.splitAbelianEP_regular`), but the wreath product construction that proves it consumes
a *regular* realization of the base group, so the statement over `ℚ` is recorded separately. -/
def SplitAbelianEP : Prop :=
  ∀ (A U : Type) [CommGroup A] [Finite A] [Group U] [Finite U] (φ : U →* MulAut A),
    IsInverseGalois U → IsInverseGalois (A ⋊[φ] U)

/-- **Wreathing a realizable group by a finite cyclic group preserves realizability over `ℚ`.**

This single statement carries the whole split half of Shafarevich's theorem: the abelian kernel of
a split embedding problem is a quotient of a wreath product with the same base group, and a wreath
product by a finite abelian group is built out of wreath products by finite cyclic ones. -/
def CyclicWreathEP : Prop :=
  ∀ (C U : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group U] [Finite U],
    IsInverseGalois U → IsInverseGalois (C ≀ᵣ U)

/-- **A cyclic bottom group suffices for the split half.**

`RegularWreathProduct.toSemidirectProduct` presents `A ⋊[φ] U` as a quotient of `A ≀ᵣ U`, whose
action does not depend on `φ`, and `IsInverseGalois.wreath_of_isCyclic` builds `A ≀ᵣ U` for an
arbitrary finite abelian `A` out of the cyclic case. -/
theorem splitAbelianEP_of_cyclicWreathEP (h : CyclicWreathEP) : SplitAbelianEP :=
  fun A U _ _ _ _ φ hU =>
    IsInverseGalois.semidirectProduct_of_wreath φ
      (IsInverseGalois.wreath_of_isCyclic (fun C H _ _ _ _ _ hH => h C H hH) A U hU)

/-! ## The dichotomy -/

/-- **An embedding problem with minimal elementary abelian kernel is either split or a Frattini
problem.**

The statement is for an arbitrary realization predicate `P` inherited by quotients.  A trivial
kernel makes the surjection an isomorphism; a kernel inside the Frattini subgroup is handed to
`hfr`; and otherwise `exists_isComplement'_of_not_le_frattini` writes `E` as a semidirect product
`ker π ⋊ M` with `M ≅ W`, which is what `hsplit` solves. -/
theorem elementaryAbelianKernel_of_frattini {P : ∀ (G : Type) [Group G], Prop}
    (hquot : IsQuotientClosed P)
    (hsplit : ∀ (A U : Type) [CommGroup A] [Finite A] [Group U] [Finite U] (φ : U →* MulAut A),
      P U → P (A ⋊[φ] U))
    (hfr : ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime]
      (π : E →* W), Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
      (∀ x : ↥π.ker, x ^ p = 1) →
      (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) →
      π.ker ≠ ⊥ → π.ker ≤ frattini E → P W → P E)
    (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime] (π : E →* W)
    (hπ : Function.Surjective ⇑π) (hcomm : IsMulCommutative ↥π.ker)
    (hpow : ∀ x : ↥π.ker, x ^ p = 1)
    (hmin : ∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) (hW : P W) : P E := by
  haveI := hcomm
  by_cases hbot : π.ker = ⊥
  · exact hquot.of_mulEquiv
      (MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hbot, hπ⟩).symm hW
  by_cases hle : π.ker ≤ frattini E
  · exact hfr E W p π hπ hcomm hpow hmin hbot hle hW
  -- The split case: the kernel has a complement `M`, and `π` restricts to an isomorphism `M ≃ W`.
  obtain ⟨M, hM⟩ := exists_isComplement'_of_not_le_frattini hmin hle
  have hinf : π.ker ⊓ M = ⊥ := disjoint_iff.mp hM.disjoint
  have hinj : Function.Injective ⇑(π.comp M.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : E) ∈ π.ker ⊓ M := ⟨MonoidHom.mem_ker.mp hx, x.2⟩
    rw [hinf] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hsurj : Function.Surjective ⇑(π.comp M.subtype) := by
    intro w
    obtain ⟨e, rfl⟩ := hπ w
    have hmem : e ∈ (↑(π.ker ⊔ M) : Set E) := by rw [hM.sup_eq_top]; trivial
    rw [Subgroup.normal_mul] at hmem
    obtain ⟨a, ha, m, hm, rfl⟩ := hmem
    refine ⟨⟨m, hm⟩, ?_⟩
    simp [MonoidHom.mem_ker.mp ha]
  exact hquot.of_mulEquiv (SemidirectProduct.mulEquivSubgroup hM)
    (hsplit ↥π.ker ↥M _
      (hquot.of_mulEquiv (MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm hW))

/-- **Over `ℚ(T)` the split half of the dichotomy is unconditional**, so embedding problems with
minimal elementary abelian kernel reduce to those whose kernel lies inside the Frattini subgroup. -/
theorem elementaryAbelianKernelEPRegular_of_frattiniKernelEPRegular
    (h : FrattiniKernelEPRegular) : ElementaryAbelianKernelEPRegular :=
  fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hW =>
    elementaryAbelianKernel_of_frattini isQuotientClosed_isRegularInverseGalois
      (fun A U _ _ _ _ φ hU => splitAbelianEP_regular A U φ hU)
      (fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hbot hle hW =>
        h E W p π hπ hcomm hpow hmin hbot hle hW)
      E W p π hπ hcomm hpow hmin hW

/-- **Over `ℚ` the two halves of the dichotomy together give embedding problems with minimal
elementary abelian kernel.** -/
theorem elementaryAbelianKernelEP_of_frattiniKernelEP (h : FrattiniKernelEP)
    (hs : SplitAbelianEP) : ElementaryAbelianKernelEP :=
  fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hW =>
    elementaryAbelianKernel_of_frattini isQuotientClosed_isInverseGalois
      (fun A U _ _ _ _ φ hU => hs A U φ hU)
      (fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hbot hle hW =>
        h E W p π hπ hcomm hpow hmin hbot hle hW)
      E W p π hπ hcomm hpow hmin hW

/-! ## Shafarevich's theorem, reduced to the Frattini case -/

/-- **The regular form of Shafarevich's theorem, reduced to Frattini embedding problems.**

If every embedding problem whose kernel is a minimal elementary abelian normal subgroup inside the
Frattini subgroup is solvable regularly over `ℚ(T)`, then every finite solvable group is the Galois
group of a regular extension of `ℚ(T)`. -/
theorem isSolvable_isRegularInverseGalois_of_frattiniKernelEPRegular (h : FrattiniKernelEPRegular)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : IsRegularInverseGalois G :=
  isSolvable_isRegularInverseGalois_of_elementaryAbelianKernelEPRegular
    (elementaryAbelianKernelEPRegular_of_frattiniKernelEPRegular h) G

/-- **Shafarevich's theorem, reduced to Frattini embedding problems and to split embedding problems
with abelian kernel.** -/
theorem isSolvable_isInverseGalois_of_frattiniKernelEP (h : FrattiniKernelEP)
    (hs : SplitAbelianEP) (G : Type) [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  isSolvable_isInverseGalois_of_elementaryAbelianKernelEP
    (elementaryAbelianKernelEP_of_frattiniKernelEP h hs) G

/-- **Shafarevich's theorem, reduced to Frattini embedding problems and to wreath products by a
finite cyclic group.** -/
theorem isSolvable_isInverseGalois_of_frattiniKernelEP_of_cyclicWreathEP (h : FrattiniKernelEP)
    (hc : CyclicWreathEP) (G : Type) [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  isSolvable_isInverseGalois_of_frattiniKernelEP h (splitAbelianEP_of_cyclicWreathEP hc) G

end Shafarevich
