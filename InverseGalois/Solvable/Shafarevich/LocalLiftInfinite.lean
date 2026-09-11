/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.Solvable.Shafarevich.CyclicLift
import InverseGalois.Solvable.Shafarevich.LevelOneFamily

/-!
# Local solvability at the archimedean places

Local solvability of a step of the ladder was settled at the finite places, where the decomposition
subgroup of a prime is generated modulo inertia by the Frobenius and the property carried by the
solutions supplies the ramified case.  The family the local conditions are read on holds the
decomposition subgroups at the infinite places as well, and there the argument is of an entirely
different kind, and shorter: an automorphism fixing an archimedean place is an involution, so the
image of such a decomposition subgroup is killed by two, while the layer being added is killed by
the odd prime the ladder climbs.  The two orders are coprime, and a homomorphism into a finite
group lifts along a surjection whose kernel has order coprime to the image, by the splitting of an
extension of coprime orders.

The splitting is Schur–Zassenhaus, applied not to the whole group upstairs but to the preimage of
the image of the homomorphism, whose quotient by the kernel of the surjection is that image; a
complement there maps isomorphically onto the image, and the inverse of that isomorphism composed
with the homomorphism is the lift.  The lift factors through the same quotient the homomorphism
does, so it is smooth for free.

Putting the two cases together gives local solvability along the whole family of decomposition
subgroups, finite and infinite places at once, which is the shape the ladder asks for.

## Main results

* `InverseGalois.Shafarevich.exists_monoidHom_comp_eq_of_coprime` — **a homomorphism into a finite
  group lifts along a surjection whose kernel has order coprime to the order of the image**, by a
  complement to the kernel inside the preimage of the image.
* `InverseGalois.Shafarevich.exists_smoothHom_lift_of_sq_eq_one` — **the step has a local solution
  along a subgroup all of whose elements are involutions**, the prime being odd.
* `InverseGalois.Shafarevich.hasLocalLift_isSplitTotallyRamified_decompositionSubgroups` — **the
  step is locally solvable along every decomposition subgroup**, at the finite and at the infinite
  places together.

## Tags

Shafarevich's theorem, embedding problem, archimedean place, Schur-Zassenhaus, complement
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Lifting along a surjection of coprime kernel -/

section Coprime

/-- **A homomorphism into a finite group lifts along a surjection whose kernel has order coprime to
the order of the image.**

The preimage of the image has the kernel of the surjection as a normal subgroup of coprime index,
so that subgroup has a complement; the complement maps isomorphically onto the image, and the lift
is the inverse of that isomorphism read on the values of the homomorphism.  The lift is trivial
wherever the homomorphism is. -/
theorem exists_monoidHom_comp_eq_of_coprime {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite B] {E : B →* C} (hE : Function.Surjective E) (ψ : A →* C)
    (hcop : Nat.Coprime (Nat.card ↥E.ker) (Nat.card ↥ψ.range)) :
    ∃ g : A →* B, (∀ x, E (g x) = ψ x) ∧ ψ.ker ≤ g.ker := by
  classical
  set R : Subgroup C := ψ.range with hRdef
  set N : Subgroup B := Subgroup.comap E R with hNdef
  have hkerle : E.ker ≤ N := by
    intro x hx
    rw [hNdef, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  have hmemR : ∀ x : ↥N, E ((N.subtype) x) ∈ R := fun x => Subgroup.mem_comap.1 x.2
  set E' : ↥N →* ↥R := (E.comp N.subtype).codRestrict R hmemR with hE'def
  have hE'apply : ∀ x : ↥N, (E' x : C) = E (x : B) := fun _ => rfl
  have hE'surj : Function.Surjective E' := by
    rintro ⟨r, hr⟩
    obtain ⟨b, rfl⟩ := hE r
    exact ⟨⟨b, Subgroup.mem_comap.2 hr⟩, rfl⟩
  have hker' : E'.ker = E.ker.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← Subtype.coe_inj,
      hE'apply]
    exact Iff.rfl
  haveI : (E.ker.subgroupOf N).Normal := (MonoidHom.normal_ker E).subgroupOf N
  have hcard : Nat.card ↥(E.ker.subgroupOf N) = Nat.card ↥E.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have hindex : (E.ker.subgroupOf N).index = Nat.card ↥R := by
    rw [← hker']
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective E' hE'surj).toEquiv
  obtain ⟨Cc, hCc⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := E.ker.subgroupOf N) (by rw [hcard, hindex]; exact hcop)
  set θ : ↥Cc →* ↥R := E'.comp Cc.subtype with hθdef
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcKn : (c : ↥N) ∈ E.ker.subgroupOf N := by
      rw [← hker', MonoidHom.mem_ker]
      exact hc
    exact Subtype.ext (Subgroup.disjoint_def.1 hCc.disjoint hcKn c.2)
  have hθsurj : Function.Surjective θ := by
    intro r
    obtain ⟨x, hx⟩ := hE'surj r
    obtain ⟨⟨a, c⟩, hac⟩ := hCc.2 x
    refine ⟨c, ?_⟩
    have ha1 : E' ((a : ↥N)) = 1 := by
      have hmem : (a : ↥N) ∈ E'.ker := by
        rw [hker']
        exact a.2
      exact MonoidHom.mem_ker.1 hmem
    show E' ((c : ↥N)) = r
    rw [← hx, ← hac, _root_.map_mul, ha1, one_mul]
  set e : ↥Cc ≃* ↥R := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩ with hedef
  refine ⟨(N.subtype.comp Cc.subtype).comp (e.symm.toMonoidHom.comp ψ.rangeRestrict),
    fun x => ?_, fun x hx => ?_⟩
  · have hee := congrArg (fun z : ↥R => (z : C)) (e.apply_symm_apply (ψ.rangeRestrict x))
    exact hee
  · rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : ψ.rangeRestrict x = 1 := Subtype.ext hx
    show N.subtype (Cc.subtype (e.symm (ψ.rangeRestrict x))) = 1
    rw [h1, _root_.map_one, _root_.map_one, _root_.map_one]

end Coprime

/-! ### The local solution along a subgroup of involutions -/

section Involution

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω]

omit [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **The step has a local solution along a subgroup all of whose elements are involutions.**

The image of such a subgroup is killed by two and the layer being added is killed by the odd prime,
so the orders are coprime and the solution lifts.  The lift dies wherever the solution does, hence
is constant on the cosets of the same open subgroup, hence is smooth. -/
theorem exists_smoothHom_lift_of_sq_eq_one (hℓ2 : ℓ ≠ 2)
    (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j) (hsm : IsSmoothHom Φ) (A : Subgroup Gal(Ω/k))
    (hA : ∀ x : ↥A, x ^ 2 = 1) :
    ∃ g : ↥A →* GenericQuot ℓ U n S (j + 1),
      IsSmooth₁ (g : ↥A → GenericQuot ℓ U n S (j + 1)) ∧
        ∀ x : ↥A, (layerExtension ℓ (genericAut U n S) j).rightHom (g x) = Φ (x : Gal(Ω/k)) := by
  haveI : Finite (GenericQuot ℓ U n S (j + 1)) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Finite (GenericQuot ℓ U n S j) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψsm : IsSmooth₁ ((Φ.comp A.subtype : ↥A →* GenericQuot ℓ U n S j) :
      ↥A → GenericQuot ℓ U n S j) :=
    isSmooth₁_comp (continuous_subtype _)
      (isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hsm))
  have hkerP : IsPGroup ℓ ↥(layerExtension ℓ (genericAut U n S) j).rightHom.ker := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_rightHom_eq_one ℓ U n S j (MonoidHom.mem_ker.1 x.2)
  have hrangeP : IsPGroup 2 ↥(Φ.comp A.subtype).range := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← _root_.map_pow, hA x, _root_.map_one]
  obtain ⟨a, ha⟩ := hkerP.exists_card_eq
  obtain ⟨b, hb⟩ := hrangeP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(layerExtension ℓ (genericAut U n S) j).rightHom.ker)
      (Nat.card ↥(Φ.comp A.subtype).range) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : ℓ.Prime) Nat.prime_two).2 hℓ2)
  obtain ⟨g, hg, hgker⟩ := exists_monoidHom_comp_eq_of_coprime
    (layerExtension ℓ (genericAut U n S) j).rightHom_surjective (Φ.comp A.subtype) hcop
  refine ⟨g, ?_, fun x => hg x⟩
  obtain ⟨N, hN, hu⟩ := hψsm
  refine ⟨N, hN, fun x m hm => ?_⟩
  have hm1 : (Φ.comp A.subtype) m = 1 := by
    have h1 := hu 1 m hm
    rwa [one_mul, _root_.map_one] at h1
  show g (x * m) = g x
  rw [_root_.map_mul, MonoidHom.mem_ker.1 (hgker (MonoidHom.mem_ker.2 hm1)), mul_one]

/-! ### Local solvability along every decomposition subgroup -/

/-- **Local solvability of the step at a family holding decomposition subgroups and subgroups of
involutions is the ramified case alone.**

A member of the wider family which is the decomposition subgroup of a prime is handled by the
finite-place argument, applied to the one-member family it forms, and a member all of whose
elements are involutions is handled by the coprimality of the orders. -/
theorem hasLocalLift_of_hasSplitRamifiedLift_of_sq (hℓ2 : ℓ ≠ 2) (φ : Gal(Ω/k) →* U) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (hT : ∀ A ∈ T, (∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P ≠ ⊥ ∧ A = stabilizer Gal(Ω/k) P) ∨
      ∀ x : ↥A, x ^ 2 = 1)
    (hD : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      stabilizer Gal(Ω/k) P ∉ conjFamily D → ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1)
    (hram : HasSplitRamifiedLift ℓ U n S j φ) :
    HasLocalLift ℓ U n S j φ D T (IsSplitTotallyRamified ℓ U S φ) := by
  intro Φ hsm hover hfam hprop A hA hAD
  rcases hT A hA with hfin | hinv
  · refine hasLocalLift_of_hasSplitRamifiedLift ℓ U n S j φ D {A} ?_ hD hram
      Φ hsm hover hfam hprop A rfl hAD
    intro B hB
    rw [Set.mem_singleton_iff] at hB
    subst hB
    exact hfin
  · exact exists_smoothHom_lift_of_sq_eq_one ℓ U n S j hℓ2 Φ hsm A hinv

/-- **The step is locally solvable along every decomposition subgroup.**

At a finite place the local solution comes from the Frobenius when the solution is unramified and
from the cyclic lifting supplied by the property when it is not; at an infinite place it comes from
the coprimality of two and the odd prime.  Nothing beyond the restriction the solutions already
carry, and the finite family naming every prime where the base realization ramifies, is asked. -/
theorem hasLocalLift_isSplitTotallyRamified_decompositionSubgroups (hℓ2 : ℓ ≠ 2)
    (hS : IsPGroup ℓ S) (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (hD : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      stabilizer Gal(Ω/k) P ∉ conjFamily D → ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1) :
    HasLocalLift ℓ U n S j φ D (decompositionSubgroups k Ω) (IsSplitTotallyRamified ℓ U S φ) := by
  refine hasLocalLift_of_hasSplitRamifiedLift_of_sq ℓ U n S j hℓ2 φ D _ ?_ hD
    (hasSplitRamifiedLift_of_hasCyclicLift ℓ U n S j hS φ fun P N _ _ _ hμ =>
      hasCyclicLift_of_fixed_rootsOfUnity ℓ (isClosed_stabilizer_ideal P) N
        fun ζ hζ σ => hμ ζ hζ (σ : Gal(Ω/k)) σ.2)
  rintro A (⟨P, hPp, hPbot, hAP⟩ | ⟨w, rfl⟩)
  · exact Or.inl ⟨P, hPp, hPbot, hAP⟩
  · refine Or.inr fun x => Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact sq_eq_one_of_mem_stabilizer_infinitePlace w x.2

end Involution

end InverseGalois.Shafarevich
