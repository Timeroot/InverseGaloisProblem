/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Graded
import InverseGalois.CFT.TateCohomology.Transfer

/-!
# Shapiro's lemma for complete cohomology

A representation of a subgroup coinduces one of the whole group: the equivariant functions on the
group with values in the representation, translated by the group.  Shapiro's lemma says that the
complete cohomology of the group with coefficients in the coinduced representation is the complete
cohomology of the subgroup with coefficients in the representation it comes from, in every degree.

In the positive degrees this is the theorem of Mathlib for ordinary group cohomology, and in the
degrees below minus one it is the theorem of Mathlib for group homology, applied to the induced
representation, which for a subgroup of finite index is isomorphic to the coinduced one.  The two
middle degrees are proved here directly, and both isomorphisms come from explicit maps.

An equivariant function is determined by its values on a transversal, and it is invariant exactly
when it is constant; so evaluation at the neutral element identifies the invariants of the two
representations.  In the other direction the function supported on the subgroup carrying all the
translates of a vector gives a map from the representation to the coinduced one, and summing the
classes of the values at a transversal gives a map back; the two are mutually inverse on the
coinvariants.  Under that pair of identifications the norm of the group becomes the norm of the
subgroup, because a group is the product of a transversal and the subgroup, and a commuting square
of that shape transports both middle Tate groups.

The statement is what turns a cohomology of a family indexed by the places of a number field into
the cohomology of a single place: the ideles of a Galois extension are, place by place of the base
field, coinduced from the decomposition group of a chosen place above it.

## Main definitions

* `InverseGalois.CFT.Tate.coindEval`: evaluation of an equivariant function at the neutral element.
* `InverseGalois.CFT.Tate.coindDelta`: the equivariant function attached to a vector.
* `InverseGalois.CFT.Tate.coindCosetSum`: the sum over a transversal of the classes of the values of
  an equivariant function.
* `InverseGalois.CFT.Tate.transportH0`, `InverseGalois.CFT.Tate.transportHm1`: the transport of the
  two middle Tate groups along an equivalence compatible with the norm.
* `InverseGalois.CFT.Tate.tateShapiroEquiv`: **Shapiro's lemma for complete cohomology.**

## Main results

* `InverseGalois.CFT.Tate.coindInvariantsEquiv`: **the invariants of a coinduced representation are
  the invariants of the representation**, by evaluation at the neutral element.
* `InverseGalois.CFT.Tate.coindCoinvariantsEquiv`: **the coinvariants of a coinduced representation
  are the coinvariants of the representation**, by summing over a transversal.
* `InverseGalois.CFT.Tate.coindV_eq_sum_coindDelta`: an equivariant function is the sum of the
  translates of the functions attached to its values at a transversal.
* `InverseGalois.CFT.Tate.coindInvariantsEquiv_coinvariantsNorm`: **the norm commutes with the two
  identifications.**
* `InverseGalois.CFT.Tate.tateShapiroH0`, `InverseGalois.CFT.Tate.tateShapiroHm1`: **Shapiro's lemma
  in the two middle degrees.**

## Tags

Tate cohomology, Shapiro's lemma, coinduced representation, transversal, norm
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### Transporting the two middle Tate groups along an equivalence -/

section Transport

variable {k G₁ G₂ V W : Type u} [CommRing k] [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (σ : Representation k G₁ V) (τ : Representation k G₂ W)
  (ei : ↥σ.invariants ≃ₗ[k] ↥τ.invariants) (ec : Coinvariants σ ≃ₗ[k] Coinvariants τ)
  (hsq : ∀ z, ei (coinvariantsNorm σ z) = coinvariantsNorm τ (ec z))

include hsq in
/-- An equivalence of the invariants compatible with the norm carries the norms onto the norms. -/
theorem map_range_coinvariantsNorm :
    Submodule.map (ei : ↥σ.invariants →ₗ[k] ↥τ.invariants)
        (LinearMap.range (coinvariantsNorm σ)) = LinearMap.range (coinvariantsNorm τ) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨-, ⟨z, rfl⟩, rfl⟩
    exact ⟨ec z, (hsq z).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨coinvariantsNorm σ (ec.symm w), ⟨_, rfl⟩, by rw [hsq, ec.apply_symm_apply]⟩

/-- **Transport of the Tate group in degree zero** along an equivalence of the invariants
compatible with the norm. -/
def transportH0 : H0 σ ≃ₗ[k] H0 τ :=
  Submodule.Quotient.equiv _ _ ei (map_range_coinvariantsNorm σ τ ei ec hsq)

include hsq in
/-- An equivalence of the coinvariants compatible with the norm carries the classes killed by the
norm onto the classes killed by the norm. -/
theorem map_ker_coinvariantsNorm :
    Submodule.map (ec : Coinvariants σ →ₗ[k] Coinvariants τ)
        (LinearMap.ker (coinvariantsNorm σ)) = LinearMap.ker (coinvariantsNorm τ) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hsq, hz, map_zero]
  · intro hy
    refine ⟨ec.symm y, ?_, ec.apply_symm_apply y⟩
    have h := hsq (ec.symm y)
    rw [ec.apply_symm_apply, hy] at h
    exact ei.map_eq_zero_iff.1 h

/-- **Transport of the Tate group in degree minus one** along an equivalence of the coinvariants
compatible with the norm. -/
def transportHm1 : Hm1 σ ≃ₗ[k] Hm1 τ :=
  (ec.submoduleMap (LinearMap.ker (coinvariantsNorm σ))).trans
    (LinearEquiv.ofEq _ _ (map_ker_coinvariantsNorm σ τ ei ec hsq))

end Transport

variable {k G V : Type u} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {S : Subgroup G} (ρ : Representation k S V)

theorem mem_coindV_iff (f : G → V) :
    f ∈ coindV S.subtype ρ ↔ ∀ (s : S) (g : G), f ((s : G) * g) = ρ s (f g) := Iff.rfl

theorem coindV_apply_mul (f : ↥(coindV S.subtype ρ)) (s : S) (g : G) :
    (f : G → V) ((s : G) * g) = ρ s ((f : G → V) g) := f.2 s g

theorem coind_apply_coe (h : G) (f : ↥(coindV S.subtype ρ)) (g : G) :
    ((coind S.subtype ρ h f : ↥(coindV S.subtype ρ)) : G → V) g = (f : G → V) (g * h) := rfl

/-- Evaluation at the neutral element. -/
def coindEval : ↥(coindV S.subtype ρ) →ₗ[k] V :=
  (LinearMap.proj (1 : G)).comp (coindV S.subtype ρ).subtype

theorem coindEval_apply (f : ↥(coindV S.subtype ρ)) : coindEval ρ f = (f : G → V) 1 := rfl

theorem coindEval_coind (s : S) (f : ↥(coindV S.subtype ρ)) :
    coindEval ρ (coind S.subtype ρ (s : G) f) = ρ s (coindEval ρ f) := by
  rw [coindEval_apply, coind_apply_coe, one_mul, coindEval_apply, ← mul_one ((s : G)),
    coindV_apply_mul]

/-- The invariants of the coinduced representation are the constant functions. -/
theorem mem_invariants_coind_iff (f : ↥(coindV S.subtype ρ)) :
    f ∈ (coind S.subtype ρ).invariants ↔ ∀ g : G, (f : G → V) g = (f : G → V) 1 := by
  constructor
  · intro hf g
    have h := congrArg (fun z : ↥(coindV S.subtype ρ) => (z : G → V) 1) (hf g)
    simpa using h
  · intro hf g
    refine Subtype.ext (funext fun x => ?_)
    rw [coind_apply_coe, hf (x * g), hf x]

/-! ### The invariants -/

/-- The constant function at an invariant vector. -/
def coindConst (v : ↥ρ.invariants) : ↥(coindV S.subtype ρ) :=
  ⟨Function.const G (v : V), fun s _ => (v.2 s).symm⟩

theorem coindConst_apply (v : ↥ρ.invariants) (g : G) :
    (coindConst ρ v : G → V) g = (v : V) := rfl

theorem coindConst_mem_invariants (v : ↥ρ.invariants) :
    coindConst ρ v ∈ (coind S.subtype ρ).invariants :=
  (mem_invariants_coind_iff ρ _).2 fun _ => rfl

theorem coindEval_mem_invariants {z : ↥(coindV S.subtype ρ)}
    (hz : z ∈ (coind S.subtype ρ).invariants) : coindEval ρ z ∈ ρ.invariants := fun s => by
  have h := coindV_apply_mul ρ z s 1
  rw [mul_one] at h
  rw [coindEval_apply, ← h, (mem_invariants_coind_iff ρ z).1 hz]

/-- Evaluation at the neutral element, on the invariants. -/
def coindInvariantsHom : ↥(coind S.subtype ρ).invariants →ₗ[k] ↥ρ.invariants :=
  ((coindEval ρ).domRestrict _).codRestrict _ fun z => coindEval_mem_invariants ρ z.2

/-- The constant functions, on the invariants. -/
def coindConstHom : ↥ρ.invariants →ₗ[k] ↥(coind S.subtype ρ).invariants where
  toFun v := ⟨coindConst ρ v, coindConst_mem_invariants ρ v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The invariants of a coinduced representation are the invariants of the representation**,
by evaluation at the neutral element. -/
def coindInvariantsEquiv : ↥(coind S.subtype ρ).invariants ≃ₗ[k] ↥ρ.invariants :=
  LinearEquiv.ofLinear (coindInvariantsHom ρ) (coindConstHom ρ) (by ext; rfl)
    (by
      refine LinearMap.ext fun z => Subtype.ext (Subtype.ext (funext fun g => ?_))
      exact ((mem_invariants_coind_iff ρ (z : ↥(coindV S.subtype ρ))).1 z.2 g).symm)

theorem coindInvariantsEquiv_apply (z : ↥(coind S.subtype ρ).invariants) :
    (coindInvariantsEquiv ρ z : V) = ((z : ↥(coindV S.subtype ρ)) : G → V) 1 := rfl

/-! ### The equivariant function attached to a vector -/

omit [AddCommGroup V] [Module k V] in
theorem rep_mul_apply {H W : Type*} [Monoid H] [AddCommGroup W] [Module k W]
    (σ : Representation k H W) (a b : H) (w : W) : σ (a * b) w = σ a (σ b w) := by
  rw [map_mul]
  rfl

open scoped Classical in
/-- The function supported on the subgroup that carries the translates of a vector. -/
def coindDeltaFun (v : V) : G → V := fun g => if h : g ∈ S then ρ ⟨g, h⟩ v else 0

theorem coindDeltaFun_of_mem (v : V) {g : G} (hg : g ∈ S) :
    coindDeltaFun ρ v g = ρ ⟨g, hg⟩ v := dif_pos hg

theorem coindDeltaFun_of_notMem (v : V) {g : G} (hg : g ∉ S) : coindDeltaFun ρ v g = 0 :=
  dif_neg hg

theorem coindDeltaFun_mem (v : V) : coindDeltaFun ρ v ∈ coindV S.subtype ρ := fun s g => by
  show coindDeltaFun ρ v ((s : G) * g) = ρ s (coindDeltaFun ρ v g)
  by_cases hg : g ∈ S
  · rw [coindDeltaFun_of_mem ρ v hg, coindDeltaFun_of_mem ρ v (S.mul_mem s.2 hg),
      show (⟨(s : G) * g, S.mul_mem s.2 hg⟩ : S) = s * ⟨g, hg⟩ from rfl, rep_mul_apply]
  · rw [coindDeltaFun_of_notMem ρ v hg, coindDeltaFun_of_notMem ρ v
      (fun h => hg (by simpa using S.mul_mem (S.inv_mem s.2) h)), map_zero]

theorem coindDeltaFun_add (v w : V) :
    coindDeltaFun ρ (v + w) = coindDeltaFun ρ v + coindDeltaFun ρ w := by
  refine funext fun g => ?_
  simp only [Pi.add_apply]
  by_cases hg : g ∈ S
  · rw [coindDeltaFun_of_mem ρ _ hg, coindDeltaFun_of_mem ρ _ hg, coindDeltaFun_of_mem ρ _ hg,
      map_add]
  · rw [coindDeltaFun_of_notMem ρ _ hg, coindDeltaFun_of_notMem ρ _ hg,
      coindDeltaFun_of_notMem ρ _ hg, add_zero]

theorem coindDeltaFun_smul (c : k) (v : V) :
    coindDeltaFun ρ (c • v) = c • coindDeltaFun ρ v := by
  refine funext fun g => ?_
  simp only [Pi.smul_apply]
  by_cases hg : g ∈ S
  · rw [coindDeltaFun_of_mem ρ _ hg, coindDeltaFun_of_mem ρ _ hg, map_smul]
  · rw [coindDeltaFun_of_notMem ρ _ hg, coindDeltaFun_of_notMem ρ _ hg, smul_zero]

/-- **The equivariant function attached to a vector**: the one supported on the subgroup that
carries all of its translates. -/
def coindDelta : V →ₗ[k] ↥(coindV S.subtype ρ) where
  toFun v := ⟨coindDeltaFun ρ v, coindDeltaFun_mem ρ v⟩
  map_add' v w := Subtype.ext (coindDeltaFun_add ρ v w)
  map_smul' c v := Subtype.ext (coindDeltaFun_smul ρ c v)

theorem coindDelta_coe (v : V) : (coindDelta ρ v : G → V) = coindDeltaFun ρ v := rfl

/-- The function attached to a translate is the translate of the function. -/
theorem coindDelta_apply_smul (s : S) (v : V) :
    coindDelta ρ (ρ s v) = coind S.subtype ρ (s : G) (coindDelta ρ v) := by
  refine Subtype.ext (funext fun g => ?_)
  rw [coind_apply_coe, coindDelta_coe, coindDelta_coe]
  by_cases hg : g ∈ S
  · rw [coindDeltaFun_of_mem ρ _ hg, coindDeltaFun_of_mem ρ _ (S.mul_mem hg s.2),
      show (⟨g * (s : G), S.mul_mem hg s.2⟩ : S) = ⟨g, hg⟩ * s from rfl, rep_mul_apply]
  · rw [coindDeltaFun_of_notMem ρ _ hg, coindDeltaFun_of_notMem ρ _
      (fun h => hg (by simpa using S.mul_mem h (S.inv_mem s.2)))]

/-! ### The class of a value depends only on its coset -/

theorem mk_coindV_apply_eq (f : ↥(coindV S.subtype ρ)) {a b : G} (h : a * b⁻¹ ∈ S) :
    Coinvariants.mk ρ ((f : G → V) a) = Coinvariants.mk ρ ((f : G → V) b) := by
  have key : (f : G → V) a = ρ ⟨a * b⁻¹, h⟩ ((f : G → V) b) := by
    simpa using coindV_apply_mul ρ f ⟨a * b⁻¹, h⟩ b
  rw [key, Coinvariants.mk_self_apply]

theorem mk_coindV_apply_out (f : ↥(coindV S.subtype ρ)) (g : G) :
    Coinvariants.mk ρ ((f : G → V) g)
      = Coinvariants.mk ρ ((f : G → V) ((QuotientGroup.mk g⁻¹ : G ⧸ S).out)⁻¹) := by
  refine mk_coindV_apply_eq ρ f ?_
  have h : ((QuotientGroup.mk g⁻¹ : G ⧸ S).out)⁻¹ * g⁻¹ ∈ S :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  simpa using S.inv_mem h

/-! ### The sum over a transversal -/

/-- **The sum over the cosets of the classes of the values of an equivariant function** at the
chosen representatives. -/
def coindCosetSum : ↥(coindV S.subtype ρ) →ₗ[k] Coinvariants ρ :=
  ∑ᶠ c : G ⧸ S, (Coinvariants.mk ρ).comp
    ((LinearMap.proj ((c.out)⁻¹ : G)).comp (coindV S.subtype ρ).subtype)

theorem coindCosetSum_eq_sum [Fintype (G ⧸ S)] :
    coindCosetSum ρ = ∑ c : G ⧸ S, (Coinvariants.mk ρ).comp
      ((LinearMap.proj ((c.out)⁻¹ : G)).comp (coindV S.subtype ρ).subtype) :=
  finsum_eq_sum_of_fintype _

theorem coindCosetSum_apply [Fintype (G ⧸ S)] (f : ↥(coindV S.subtype ρ)) :
    coindCosetSum ρ f = ∑ c : G ⧸ S, Coinvariants.mk ρ ((f : G → V) ((c.out)⁻¹)) := by
  rw [coindCosetSum_eq_sum]
  simp [LinearMap.sum_apply]

variable [Finite G]

/-- **The sum over a transversal does not see a translation.** -/
theorem coindCosetSum_coind (x : G) (f : ↥(coindV S.subtype ρ)) :
    coindCosetSum ρ (coind S.subtype ρ x f) = coindCosetSum ρ f := by
  letI := Fintype.ofFinite (G ⧸ S)
  rw [coindCosetSum_apply, coindCosetSum_apply]
  refine Fintype.sum_equiv (MulAction.toPerm x⁻¹) _ _ fun c => ?_
  have hq : (QuotientGroup.mk (((c.out)⁻¹ * x)⁻¹) : G ⧸ S) = (x⁻¹ : G) • c := by
    rw [mul_inv_rev, inv_inv]
    exact MulAction.Quotient.mk_smul_out (H := S) x⁻¹ c
  rw [coind_apply_coe, mk_coindV_apply_out ρ f ((c.out)⁻¹ * x), hq]
  rfl

/-! ### The coinvariants -/

omit [Finite G] in
theorem mem_iff_eq_mk_inv (g : G) (c : G ⧸ S) :
    g * c.out ∈ S ↔ (QuotientGroup.mk g⁻¹ : G ⧸ S) = c := by
  constructor
  · intro h
    exact (QuotientGroup.eq.2 (by simpa using h)).trans (QuotientGroup.out_eq' c)
  · rintro rfl
    simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g⁻¹ : G ⧸ S)).symm

omit [Finite G] in
theorem inv_out_mem_iff (c : G ⧸ S) :
    ((c.out)⁻¹ : G) ∈ S ↔ (QuotientGroup.mk (1 : G) : G ⧸ S) = c := by
  rw [Subgroup.inv_mem_iff]
  have h := mem_iff_eq_mk_inv (S := S) 1 c
  rw [one_mul, inv_one] at h
  exact h

omit [Finite G] in
/-- **An equivariant function is the sum of the translates of the functions attached to its values
at a transversal.** -/
theorem coindV_eq_sum_coindDelta [Fintype (G ⧸ S)] (f : ↥(coindV S.subtype ρ)) :
    f = ∑ c : G ⧸ S, coind S.subtype ρ c.out (coindDelta ρ ((f : G → V) ((c.out)⁻¹))) := by
  classical
  refine Subtype.ext (funext fun g => ?_)
  have hcoe : ((∑ c : G ⧸ S,
        coind S.subtype ρ c.out (coindDelta ρ ((f : G → V) ((c.out)⁻¹))) :
        ↥(coindV S.subtype ρ)) : G → V) g
      = ∑ c : G ⧸ S, coindDeltaFun ρ ((f : G → V) ((c.out)⁻¹)) (g * c.out) := by
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hcoe, Finset.sum_eq_single (QuotientGroup.mk g⁻¹ : G ⧸ S)]
  · have hg : g * (QuotientGroup.mk g⁻¹ : G ⧸ S).out ∈ S := (mem_iff_eq_mk_inv g _).2 rfl
    rw [coindDeltaFun_of_mem ρ _ hg]
    have h := coindV_apply_mul ρ f ⟨_, hg⟩ ((QuotientGroup.mk g⁻¹ : G ⧸ S).out)⁻¹
    rw [mul_inv_cancel_right] at h
    exact h
  · intro c _ hc
    exact coindDeltaFun_of_notMem ρ _ fun h => hc (((mem_iff_eq_mk_inv g c).1 h).symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Finite G] in
/-- **The class of the function attached to a vector**, as a map out of the coinvariants. -/
def coindCoinvariantsDelta : Coinvariants ρ →ₗ[k] Coinvariants (coind S.subtype ρ) :=
  Coinvariants.lift ρ ((Coinvariants.mk (coind S.subtype ρ)).comp (coindDelta ρ)) fun s =>
    LinearMap.ext fun v => by
      show Coinvariants.mk (coind S.subtype ρ) (coindDelta ρ (ρ s v))
        = Coinvariants.mk (coind S.subtype ρ) (coindDelta ρ v)
      rw [coindDelta_apply_smul, Coinvariants.mk_self_apply]

omit [Finite G] in
theorem coindCoinvariantsDelta_mk (v : V) :
    coindCoinvariantsDelta ρ (Coinvariants.mk ρ v)
      = Coinvariants.mk (coind S.subtype ρ) (coindDelta ρ v) := rfl

/-- **The sum over a transversal**, as a map out of the coinvariants. -/
def coindCoinvariantsSum : Coinvariants (coind S.subtype ρ) →ₗ[k] Coinvariants ρ :=
  Coinvariants.lift (coind S.subtype ρ) (coindCosetSum ρ) fun x =>
    LinearMap.ext fun f => coindCosetSum_coind ρ x f

theorem coindCoinvariantsSum_mk (f : ↥(coindV S.subtype ρ)) :
    coindCoinvariantsSum ρ (Coinvariants.mk (coind S.subtype ρ) f) = coindCosetSum ρ f := rfl

theorem coindCoinvariantsSum_delta (v : V) :
    coindCoinvariantsSum ρ (coindCoinvariantsDelta ρ (Coinvariants.mk ρ v))
      = Coinvariants.mk ρ v := by
  classical
  letI := Fintype.ofFinite (G ⧸ S)
  rw [coindCoinvariantsDelta_mk, coindCoinvariantsSum_mk, coindCosetSum_apply,
    Finset.sum_eq_single (QuotientGroup.mk (1 : G) : G ⧸ S)]
  · rw [coindDelta_coe, coindDeltaFun_of_mem ρ v ((inv_out_mem_iff _).2 rfl),
      Coinvariants.mk_self_apply]
  · intro c _ hc
    rw [coindDelta_coe,
      coindDeltaFun_of_notMem ρ v fun h => hc (((inv_out_mem_iff c).1 h).symm), map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coindCoinvariantsDelta_sum (f : ↥(coindV S.subtype ρ)) :
    coindCoinvariantsDelta ρ (coindCoinvariantsSum ρ (Coinvariants.mk (coind S.subtype ρ) f))
      = Coinvariants.mk (coind S.subtype ρ) f := by
  classical
  letI := Fintype.ofFinite (G ⧸ S)
  rw [coindCoinvariantsSum_mk, coindCosetSum_apply, map_sum]
  conv_rhs => rw [coindV_eq_sum_coindDelta ρ f]
  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [coindCoinvariantsDelta_mk, Coinvariants.mk_self_apply]

/-- **The coinvariants of a coinduced representation are the coinvariants of the
representation**, by summing the values at a transversal. -/
def coindCoinvariantsEquiv : Coinvariants (coind S.subtype ρ) ≃ₗ[k] Coinvariants ρ :=
  LinearEquiv.ofLinear (coindCoinvariantsSum ρ) (coindCoinvariantsDelta ρ)
    (Coinvariants.hom_ext (LinearMap.ext fun v => coindCoinvariantsSum_delta ρ v))
    (Coinvariants.hom_ext (LinearMap.ext fun f => coindCoinvariantsDelta_sum ρ f))

theorem coindCoinvariantsEquiv_mk (f : ↥(coindV S.subtype ρ)) :
    coindCoinvariantsEquiv ρ (Coinvariants.mk (coind S.subtype ρ) f) = coindCosetSum ρ f := rfl

/-! ### The norm -/

omit [Finite G] in
/-- **The norm of an equivariant function is the constant function at the sum of its values.** -/
theorem coe_normMap_coind [Fintype G] (f : ↥(coindV S.subtype ρ)) (g : G) :
    ((normMap (coind S.subtype ρ) f : ↥(coindV S.subtype ρ)) : G → V) g
      = ∑ y : G, (f : G → V) y := by
  rw [normMap_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

omit [Finite G] in
/-- **The sum of the values of an equivariant function is the sum over a transversal of the norms
of its values at the chosen representatives.** -/
theorem sum_coindV_apply [Fintype G] [Fintype S] [Fintype (G ⧸ S)]
    (f : ↥(coindV S.subtype ρ)) :
    ∑ y : G, (f : G → V) y = ∑ c : G ⧸ S, normMap ρ ((f : G → V) ((c.out)⁻¹)) := by
  rw [← Fintype.sum_equiv (cosetRightEquiv S)
      (fun p : (G ⧸ S) × S => (f : G → V) ((p.2 : G) * (p.1.out)⁻¹))
      (fun y : G => (f : G → V) y) fun _ => rfl,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => by
    rw [normMap_apply]
    exact Finset.sum_congr rfl fun s _ => coindV_apply_mul ρ f s _

/-- **The norm commutes with the two equivalences**: the square formed by the norm of the coinduced
representation, the norm of the representation, the sum over a transversal on the coinvariants and
the evaluation at the neutral element on the invariants commutes. -/
theorem coindInvariantsEquiv_coinvariantsNorm (z : Coinvariants (coind S.subtype ρ)) :
    coindInvariantsEquiv ρ (coinvariantsNorm (coind S.subtype ρ) z)
      = coinvariantsNorm ρ (coindCoinvariantsEquiv ρ z) := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite ↥S
  letI := Fintype.ofFinite (G ⧸ S)
  obtain ⟨f, rfl⟩ := Coinvariants.mk_surjective (coind S.subtype ρ) z
  refine Subtype.ext ?_
  have hL : (coindInvariantsEquiv ρ
        (coinvariantsNorm (coind S.subtype ρ) (Coinvariants.mk (coind S.subtype ρ) f)) : V)
      = ∑ y : G, (f : G → V) y := by
    rw [coindInvariantsEquiv_apply]
    exact coe_normMap_coind ρ f 1
  have hR : (coinvariantsNorm ρ
        (coindCoinvariantsEquiv ρ (Coinvariants.mk (coind S.subtype ρ) f)) : V)
      = ∑ c : G ⧸ S, normMap ρ ((f : G → V) ((c.out)⁻¹)) := by
    rw [coindCoinvariantsEquiv_mk, coindCosetSum_apply, map_sum, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun c _ => coinvariantsNorm_mk ρ _
  rw [hL, hR, sum_coindV_apply]

/-! ### Shapiro's lemma -/

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {S : Subgroup G} (B : Rep k S)

/-- **Shapiro's lemma in degree zero.** -/
def tateShapiroH0 : H0 (Rep.coind S.subtype B).ρ ≃ₗ[k] H0 B.ρ :=
  transportH0 _ _ (coindInvariantsEquiv B.ρ) (coindCoinvariantsEquiv B.ρ)
    (coindInvariantsEquiv_coinvariantsNorm B.ρ)

/-- **Shapiro's lemma in degree minus one.** -/
def tateShapiroHm1 : Hm1 (Rep.coind S.subtype B).ρ ≃ₗ[k] Hm1 B.ρ :=
  transportHm1 _ _ (coindInvariantsEquiv B.ρ) (coindCoinvariantsEquiv B.ρ)
    (coindInvariantsEquiv_coinvariantsNorm B.ρ)

open scoped Classical in
/-- **Shapiro's lemma for complete cohomology**: the complete cohomology of a group with
coefficients in a coinduced representation is the complete cohomology of the subgroup with
coefficients in the representation it is coinduced from, in every degree. -/
def tateShapiroEquiv : (n : ℤ) → (tateModule (Rep.coind S.subtype B) n ≃ₗ[k] tateModule B n)
  | .ofNat 0 => tateShapiroH0 B
  | .ofNat (m + 1) => (groupCohomology.coindIso B (m + 1)).toLinearEquiv
  | .negSucc 0 => tateShapiroHm1 B
  | .negSucc (m + 1) =>
      (tateMapIso (Rep.indCoindIso B).symm (Int.negSucc (m + 1))).toLinearEquiv.trans
        (groupHomology.indIso S B (m + 1)).toLinearEquiv

end Shapiro

end

end InverseGalois.CFT.Tate
