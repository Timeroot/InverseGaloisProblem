/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.GeomNormal
import InverseGalois.Rigidity.RET.Wreath.Intercept
import InverseGalois.Rigidity.RET.Wreath.KummerPinch
import InverseGalois.Rigidity.RET.Wreath.LayerHom
import InverseGalois.Rigidity.RET.RegularCyclic
import InverseGalois.Solvable.WreathCyclic

/-!
# A wreath product by a cyclic group, regularly over `ℚ(T)`

Let `H` be a group already realized regularly over `ℚ(T)`, and let `C` be a finite cyclic group.
The compositum of the pullbacks of a fixed cyclic cover along all the conjugates of a primitive
element of a realization of `H` carries the wreath product `C ≀ᵣ H`, and it is again regular.

The construction is assembled from pieces built elsewhere: a conjugate configuration records the
two extensions and the family of substitutions, and its coordinate homomorphism into the wreath
product is injective.  What is missing is the reverse inequality on the order of the Galois group,
and that is a statement about degrees over the *geometric* line `ℚ̄(T)`, where the cyclic cover
becomes a radical.  Over `ℚ̄(T)` the pullbacks are the radicals of translated Kummer radicands, an
intercept can be chosen so that these radicands are independent modulo `n`-th powers, and Kummer
theory then multiplies the degrees.  Comparing the resulting degree `n^m · m` with the degree of the
compositum over `ℚ(T)`, which the coordinate homomorphism bounds by `n^m · m` from above, pins both
inequalities to equalities at once: the group is the whole wreath product, and no constants were
gained.

## Main results

* `Rigidity.RET.Wreath.transcendental_add_const` — transcendence survives translation by a constant.
* `Rigidity.RET.Wreath.isRegularInverseGalois_wreath_cyclic` — the wreath product of a regularly
  realizable group by a finite cyclic group is regularly realizable.
* `IsRegularInverseGalois.wreath` — a wreath product by a finite abelian group preserves regular
  realizability.
* `isRegularInverseGalois_of_isSemiabelian` — every semiabelian group is a regular inverse Galois
  group over `ℚ(T)`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

/-! ## Two small transfer lemmas -/

/-- **Translating by a constant preserves transcendence.**  A constant is algebraic, and the
elements algebraic over the constants form a field, so an algebraic translate would force the
original element to be algebraic too. -/
theorem transcendental_add_const {F : Type*} [Field F] [Algebra k F] {x : F}
    (hx : Transcendental k x) (a : k) : Transcendental k (x + algebraMap k F a) := by
  intro halg
  refine hx (mem_algebraicClosure_iff.mp ?_)
  have h1 : x + algebraMap k F a ∈ algebraicClosure k F := mem_algebraicClosure_iff.mpr halg
  have h2 : algebraMap k F a ∈ algebraicClosure k F := (algebraicClosure k F).algebraMap_mem a
  simpa using sub_mem h1 h2

/-- **A rational number is the same whether it is read through the constants or directly.** -/
theorem algebraMap_rat_const (q : ℚ) : algebraMap k QTbar (algebraMap ℚ k q) = (q : QTbar) := by
  rw [eq_ratCast (algebraMap ℚ k) q, map_ratCast]

/-- **The constants lie in every intermediate field of `ℚ̄(T)‾ / ℚ̄(T)`.** -/
theorem algebraMap_const_mem (V : IntermediateField (RatFunc k) QTbar) (a : k) :
    algebraMap k QTbar a ∈ V := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) QTbar]
  exact V.algebraMap_mem _

/-! ## The wreath product by a cyclic group -/

/-- **A wreath product by a finite cyclic group is a regular inverse Galois group** as soon as the
top group is one. -/
theorem isRegularInverseGalois_wreath_cyclic (C H : Type) [CommGroup C] [Finite C] [IsCyclic C]
    [Group H] [Finite H] (hH : IsRegularInverseGalois H) :
    IsRegularInverseGalois (C ≀ᵣ H) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  -- The regular realization of `H`, with a transcendental primitive element.
  obtain ⟨E, _, _, galH, θ, hregE, hprim, hθ⟩ := exists_baseField hH
  -- The regular realization of `C`, embedded into `ℚ̄(T)‾`.
  obtain ⟨L₂, _, _, _, _, _, _, hreg₂, ⟨φ₂⟩⟩ :=
    (Rigidity.RET.IsRegularInverseGalois.of_isCyclic : IsRegularInverseGalois C)
  haveI : Algebra.IsAlgebraic QT L₂ := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨ιL⟩ : Nonempty (L₂ →ₐ[QT] QTbar) := ⟨IsAlgClosed.lift⟩
  have ψ : L₂ ≃ₐ[QT] ↥ιL.fieldRange := AlgEquiv.ofInjectiveField ιL
  haveI : IsGalois QT ↥ιL.fieldRange := IsGalois.of_algEquiv ψ
  haveI : FiniteDimensional QT ↥ιL.fieldRange :=
    FiniteDimensional.of_injective ψ.symm.toLinearMap ψ.symm.injective
  have galC : (↥ιL.fieldRange ≃ₐ[QT] ↥ιL.fieldRange) ≃* C := ψ.autCongr.symm.trans φ₂
  haveI : IsCyclic (↥ιL.fieldRange ≃ₐ[QT] ↥ιL.fieldRange) :=
    isCyclic_of_injective galC.toMonoidHom galC.injective
  have hregNf : algebraicClosure ℚ ↥ιL.fieldRange = ⊥ :=
    Rigidity.RET.algebraicClosure_eq_bot_of_ringHom ψ.symm.toRingHom hreg₂
  haveI := isCyclic_geomClosure ιL.fieldRange
  -- Over the geometric line the layer is a radical extension.
  obtain ⟨r, t, e, y, hinj, hgcd, hypow, -⟩ :=
    exists_kummer_generator (geomClosure ιL.fieldRange)
  have hdeg : Module.finrank (RatFunc k) ↥(geomClosure ιL.fieldRange) = Nat.card C := by
    rw [finrank_geomClosure _ hregNf, ← IsGalois.card_aut_eq_finrank QT ↥ιL.fieldRange]
    exact Nat.card_congr galC.toEquiv
  rw [hdeg] at hgcd hypow
  haveI : NeZero (Nat.card C) := ⟨Nat.card_pos.ne'⟩
  -- A rational intercept making the conjugate radicands independent.
  obtain ⟨c₀, hne₀, hind⟩ :=
    exists_good_intercept E hregE galH hprim hθ t hinj e (n := Nat.card C) hgcd
  obtain ⟨ε, hεmem, hεX⟩ := exists_epsilon E galH hθ L₂ c₀
  -- The conjugate configuration.
  let d : ConjugateData H C :=
    { N := L₂
      regular_N := hreg₂
      galA := φ₂
      E := E
      regular_E := hregE
      galH := galH
      θ := θ
      adjoin_θ := hprim
      transcendental_θ := hθ
      c := c₀
      ε := ε
      ε_mem := hεmem
      ε_X := hεX }
  -- The substituted elements are transcendental over the constants.
  have hu : ∀ h : H, Transcendental k (((galH.symm h θ : ↥E) : QTbar) + (c₀ : QTbar)) := by
    intro h
    have h1 : Transcendental ℚ ((galH.symm h) θ) :=
      transcendental_ringHom (galH.symm h).toAlgHom.toRingHom hθ
    have h2 : Transcendental ℚ (((galH.symm h) θ : ↥E) : QTbar) :=
      transcendental_ringHom (IntermediateField.val E).toRingHom h1
    have h3 := transcendental_add_const (transcendental_const_of_rat h2) (algebraMap ℚ k c₀)
    rwa [algebraMap_rat_const] at h3
  -- The layer maps.
  have hlayer : ∀ h : H, ∃ f : ↥(geomClosure ιL.fieldRange) →+* QTbar,
      (∀ q : RatFunc k,
          f (algebraMap (RatFunc k) ↥(geomClosure ιL.fieldRange) q) = paramHom _ (hu h) q) ∧
        ∀ Z : Subfield QTbar, (∀ a : k, algebraMap k QTbar a ∈ Z) →
          ((((galH.symm h θ : ↥E) : QTbar) + (c₀ : QTbar)) ∈ Z) → (∀ x : L₂, ε h x ∈ Z) →
          ∀ z : ↥(geomClosure ιL.fieldRange), f z ∈ Z := fun h =>
    exists_layerHom ιL (geomClosure ιL.fieldRange) (geomClosure_eq_adjoin _).symm (hu h)
      (ε h) (hεX h)
  choose σ hσparam hσmem using hlayer
  -- The radicals attached to the layers.
  have hwpow : ∀ h : H, (σ h y) ^ Nat.card C
      = ((conjRadicand (geomConj E galH θ) t e (algebraMap ℚ k c₀) h :
          ↥(geomClosure E)) : QTbar) := by
    intro h
    have h1 : σ h (y ^ Nat.card C)
        = Polynomial.aeval (((galH.symm h θ : ↥E) : QTbar) + (c₀ : QTbar)) (multiA t e) := by
      rw [hypow, hσparam h, paramHom_algebraMap]
    have h2 : ((conjRadicand (geomConj E galH θ) t e (algebraMap ℚ k c₀) h :
          ↥(geomClosure E)) : QTbar)
        = conjRadicand (fun j => ((geomConj E galH θ j : ↥(geomClosure E)) : QTbar)) t e
            (algebraMap ℚ k c₀) h :=
      map_conjRadicand (geomConj E galH θ) t e (algebraMap ℚ k c₀) (geomVal E) h
    have h3 : conjRadicand (fun j => ((geomConj E galH θ j : ↥(geomClosure E)) : QTbar)) t e
        (algebraMap ℚ k c₀) h
        = Polynomial.aeval (((galH.symm h θ : ↥E) : QTbar) + (c₀ : QTbar)) (multiA t e) := by
      unfold conjRadicand
      rw [algebraMap_rat_const, Polynomial.aeval_def]
      rfl
    rw [h2, h3, ← h1, map_pow]
  -- The radicals lie in the geometric closure of the compositum.
  have hwmem : ∀ h : H, σ h y ∈ geomClosure d.M := by
    intro h
    refine hσmem h (geomClosure d.M).toSubfield (algebraMap_const_mem _) ?_ ?_ y
    · refine add_mem (le_geomClosure d.M _ (d.E_le_M (SetLike.coe_mem _))) ?_
      rw [← algebraMap_rat_const c₀]
      exact algebraMap_const_mem _ _
    · exact fun x => le_geomClosure d.M _ (d.ε_mem_M h x)
  -- Kummer theory multiplies the degrees.
  obtain ⟨ζ₀, hζ₀⟩ := Rigidity.RET.exists_primitiveRoot_k (Nat.card C)
  obtain ⟨LL, -, -, hmin, hfr⟩ :=
    exists_intermediateField_finrank_radicals (ι := H) (n := Nat.card C) (geomClosure E)
      (algebraMap k ↥(geomClosure E) ζ₀)
      (hζ₀.map_of_injective (algebraMap k ↥(geomClosure E)).injective)
      (fun h => conjRadicand (geomConj E galH θ) t e (algebraMap ℚ k c₀) h)
      (fun h => conjRadicand_ne_zero _ _ _ _ (hne₀ h)) hind (fun h => σ h y) hwpow
  have hEbfr : Module.finrank (RatFunc k) ↥(geomClosure E) = Nat.card H := by
    rw [finrank_geomClosure E hregE, ← IsGalois.card_aut_eq_finrank QT ↥E]
    exact Nat.card_congr galH.toEquiv
  have hLfr : Module.finrank (RatFunc k) ↥LL = Nat.card C ^ Nat.card H * Nat.card H := by
    rw [hfr, hEbfr, ← Nat.card_eq_fintype_card (α := H)]
  -- The degree pinch.
  have hLle : LL ≤ geomClosure d.M := hmin _ (geomClosure_mono d.E_le_M) hwmem
  have hchain1 : Nat.card C ^ Nat.card H * Nat.card H
      ≤ Module.finrank (RatFunc k) ↥(geomClosure d.M) := by
    rw [← hLfr]
    exact finrank_le_finrank_of_le hLle
  have hchain2 : Module.finrank (RatFunc k) ↥(geomClosure d.M) ≤ Module.finrank QT ↥d.M :=
    finrank_geomClosure_le d.M
  have hcardG : Nat.card d.G = Module.finrank QT ↥d.M := IsGalois.card_aut_eq_finrank QT ↥d.M
  have hchain3 : Nat.card d.G ≤ Nat.card C ^ Nat.card H * Nat.card H := by
    rw [← RegularWreathProduct.card (D := C) (Q := H)]
    exact Nat.card_le_card_of_injective _ d.wreathHom_injective
  set A : ℕ := Nat.card C ^ Nat.card H * Nat.card H with hA
  have heq1 : Module.finrank (RatFunc k) ↥(geomClosure d.M) = Module.finrank QT ↥d.M := by omega
  have heq2 : Nat.card d.G = A := by omega
  rw [hA] at heq2
  obtain ⟨Φ⟩ := d.nonempty_mulEquiv_of_card heq2
  exact ⟨↥d.M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, regular_of_finrank_geomClosure d.M heq1, ⟨Φ⟩⟩

end Rigidity.RET.Wreath

/-- **A wreath product by a finite abelian group preserves regular realizability.**  An abelian
group is an iterated extension of cyclic ones, and each cyclic step is a wreath product by a cyclic
group. -/
theorem IsRegularInverseGalois.wreath (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H]
    (hH : IsRegularInverseGalois H) : IsRegularInverseGalois (A ≀ᵣ H) :=
  IsRegularInverseGalois.wreath_of_isCyclic
    (fun C H _ _ _ _ _ hH => Rigidity.RET.Wreath.isRegularInverseGalois_wreath_cyclic C H hH)
    A H hH

/-- **Every semiabelian group is a regular inverse Galois group over `ℚ(T)`.**  The reduction of
Dentzer and Stoll expresses a semiabelian group as an iterated quotient of wreath products by
abelian groups, and a wreath product by an abelian group is realized by the compositum of the
pullbacks of a cyclic cover along the conjugates of a primitive element. -/
theorem isRegularInverseGalois_of_isSemiabelian {G : Type} [Group G] [Finite G]
    (hG : IsSemiabelian G) : IsRegularInverseGalois G :=
  IsSemiabelian.isRegularInverseGalois
    (fun A H _ _ _ _ hH => IsRegularInverseGalois.wreath A H hH) hG
