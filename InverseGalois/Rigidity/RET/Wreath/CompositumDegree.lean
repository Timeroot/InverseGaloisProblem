/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Natural irrationalities: the degree of a compositum over a possibly infinite base

Fix a field `F` sitting inside a field `Ω`, and inside `Ω` two intermediate fields: a **finite
Galois** extension `V / F`, and a completely arbitrary extension `B / F` — in the application
`F = ℚ(T)` and `B = ℚ̄(T)`, which is very far from finite over `F`.  The classical theorem of
natural irrationalities compares the compositum `V · B` with `V`:

> restricting an automorphism of `V · B` fixing `B` to the subfield `V` is an injection of
> `Gal(V·B / B)` into `Gal(V / F)`, with image the subgroup fixing `V ⊓ B`.

Counting elements turns that into the degree formula `[V·B : B] = [V : V ⊓ B]`, and in particular
`[V·B : B] = [V : F]` exactly when `V ⊓ B = F`.  This file proves the injection, the resulting
degree bound, and both directions of the equality criterion.

Mathlib's `IntermediateField.LinearDisjoint` API contains the same mathematics, but only for
extensions that are *both* finite: `IntermediateField.LinearDisjoint.iff_inf_eq_bot` carries a
`[FiniteDimensional F B]` hypothesis, which the intended `B = ℚ̄(T)` does not satisfy.  The proofs
below therefore avoid finiteness of `B` altogether.  The mechanism is the primitive element `θ`
of the finite separable extension `V / F`: the compositum is `B⟮θ⟯`, so every degree in sight is
the degree of a minimal polynomial of the single element `θ` over a varying base, and minimal
polynomials only ever get smaller as the base grows.  For the converse one shows that
`minpoly B θ` cannot shrink at all when `V ⊓ B = F`: it divides `minpoly F θ`, which splits in `V`
because `V / F` is normal, so its roots — and hence its coefficients — lie in `V`; they lie in `B`
by construction, hence in `V ⊓ B = F`.

The compositum is written `V ⊔ B`, and its degree over `B` is the `Module.finrank` of `↥(V ⊔ B)`
over `↥B`.  That needs an `↥B`-algebra structure on `↥(V ⊔ B)`, which Mathlib does not provide
for a pair of intermediate fields; the instances below supply it as the one coming from
`IntermediateField.extendScalars`, so that the resulting degree agrees definitionally with
`IntermediateField.relfinrank`, the instance-free relative degree, and the tower laws of
`Mathlib/FieldTheory/Relrank.lean` become available.

## Main results

* `Rigidity.RET.Wreath.instAlgebraSupRight` — `↥(V ⊔ B)` is an `↥B`-algebra, and
  `Rigidity.RET.Wreath.instAlgebraSupLeft` — it is a `↥V`-algebra, with the evident towers over
  `F`.
* `Rigidity.RET.Wreath.instFiniteDimensionalSup` — the compositum is finite over `B` as soon as
  `V` is finite over `F`.
* `Rigidity.RET.Wreath.finrank_sup_eq_relfinrank` — the degree of the compositum over `B` is the
  relative degree of `Mathlib/FieldTheory/Relrank.lean`.
* `Rigidity.RET.Wreath.restrictHom` — restriction of an automorphism of the compositum fixing `B`
  to the normal subfield `V`.
* `Rigidity.RET.Wreath.restrictHom_injective` — that restriction is injective: an automorphism
  fixing `B` and `V` pointwise fixes the field they generate.
* `Rigidity.RET.Wreath.finrank_sup_le_finrank` — the compositum has degree at most `[V : F]`
  over `B`.
* `Rigidity.RET.Wreath.inf_eq_bot_of_finrank_sup_eq` — if that bound is attained then `V` and `B`
  meet only in `F`.
* `Rigidity.RET.Wreath.finrank_sup_eq_of_inf_eq_bot` — conversely, if `V` and `B` meet only in `F`
  then the bound is attained.
* `Rigidity.RET.Wreath.finrank_sup_eq_iff_inf_eq_bot` — the two previous statements combined.
-/

open IntermediateField Module Polynomial

namespace Rigidity.RET.Wreath

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable (B V : IntermediateField F Ω)

/-! ### The compositum as an algebra over each of its two factors -/

/-- **The compositum is an algebra over the right-hand factor.**  The structure map is the
inclusion `↥B → ↥(V ⊔ B)`, presented as the one that `IntermediateField.extendScalars` puts on
the intermediate field `V ⊔ B` of `Ω / B`, so that degrees computed with it agree with
`IntermediateField.relfinrank`. -/
noncomputable instance instAlgebraSupRight : Algebra ↥B ↥(V ⊔ B) :=
  inferInstanceAs (Algebra ↥B ↥(extendScalars (le_sup_right : B ≤ V ⊔ B)))

/-- **The compositum is a module over the right-hand factor.**  This is the module structure
underlying `Rigidity.RET.Wreath.instAlgebraSupRight`, recorded separately because the generic
search from `Algebra` to `Module` is expensive at these subtypes. -/
noncomputable instance instModuleSupRight : Module ↥B ↥(V ⊔ B) := Algebra.toModule

/-- **The tower `F ⊆ B ⊆ V · B`.** -/
instance instTowerSupRight : IsScalarTower F ↥B ↥(V ⊔ B) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **The compositum is an algebra over the left-hand factor.**  The structure map is the
inclusion `↥V → ↥(V ⊔ B)`; it is what lets an automorphism of the compositum be restricted to the
normal subfield `V`. -/
noncomputable instance instAlgebraSupLeft : Algebra ↥V ↥(V ⊔ B) :=
  inferInstanceAs (Algebra ↥V ↥(extendScalars (le_sup_left : V ≤ V ⊔ B)))

/-- **The compositum is a module over the left-hand factor.** -/
noncomputable instance instModuleSupLeft : Module ↥V ↥(V ⊔ B) := Algebra.toModule

/-- **The tower `F ⊆ V ⊆ V · B`.** -/
instance instTowerSupLeft : IsScalarTower F ↥V ↥(V ⊔ B) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **The degree of the compositum over `B` is a relative degree.**  Both sides are the degree of
`V ⊔ B` over the subfield `B` it contains; the right-hand side is Mathlib's instance-free
`IntermediateField.relfinrank`, through which the tower laws are available. -/
theorem finrank_sup_eq_relfinrank : finrank ↥B ↥(V ⊔ B) = B.relfinrank (V ⊔ B) :=
  (IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : B ≤ V ⊔ B)).symm

/-! ### Restriction to the Galois factor -/

/-- **Forgetting that an automorphism of the compositum is `B`-linear.**  An `↥B`-algebra
automorphism of `V ⊔ B` is in particular an `F`-algebra automorphism, and this is that operation
as a homomorphism of groups. -/
noncomputable def restrictScalarsHom :
    (↥(V ⊔ B) ≃ₐ[↥B] ↥(V ⊔ B)) →* (↥(V ⊔ B) ≃ₐ[F] ↥(V ⊔ B)) where
  toFun σ := σ.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Restriction of the Galois group of the compositum to the Galois factor.**  Because `V / F`
is normal, an `F`-automorphism of `V ⊔ B` maps `V` into itself, so an automorphism of `V ⊔ B`
fixing `B` pointwise induces an `F`-automorphism of `V`. -/
noncomputable def restrictHom [Normal F ↥V] :
    (↥(V ⊔ B) ≃ₐ[↥B] ↥(V ⊔ B)) →* (↥V ≃ₐ[F] ↥V) :=
  (AlgEquiv.restrictNormalHom ↥V).comp (restrictScalarsHom B V)

variable {B V}

/-- **An element fixed by an automorphism lies in the fixed field of the group it generates.**
The elements fixed by a given automorphism form a subgroup of the Galois group, so a single
fixed point is fixed by every word in that automorphism and its inverse. -/
theorem mem_fixedField_closure {K L : Type*} [Field K] [Field L] [Algebra K L]
    {σ : L ≃ₐ[K] L} {x : L} (h : σ x = x) :
    x ∈ IntermediateField.fixedField (Subgroup.closure {σ}) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  have hle : Subgroup.closure ({σ} : Set (L ≃ₐ[K] L)) ≤ MulAction.stabilizer (L ≃ₐ[K] L) x := by
    rw [Subgroup.closure_le]
    rintro g rfl
    exact h
  exact hle hf

variable (B V)

/-- **Natural irrationalities, group form: restriction to `V` is injective.**  An automorphism of
`V ⊔ B` in the kernel fixes `B` pointwise because it is `B`-linear and fixes `V` pointwise by
assumption; its fixed field is therefore an intermediate field of `Ω / F` containing both `V` and
`B`, hence containing the field `V ⊔ B` they generate. -/
theorem restrictHom_injective [Normal F ↥V] : Function.Injective (restrictHom B V) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  set τ : ↥(V ⊔ B) ≃ₐ[F] ↥(V ⊔ B) := σ.restrictScalars F with hτ
  set E : IntermediateField F ↥(V ⊔ B) :=
    IntermediateField.fixedField (Subgroup.closure {τ}) with hE
  have hsub : V ⊔ B ≤ IntermediateField.lift E := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hmem : x ∈ V ⊔ B := (le_sup_left : V ≤ V ⊔ B) hx
      have hfix : τ (⟨x, hmem⟩ : ↥(V ⊔ B)) = ⟨x, hmem⟩ := by
        have h1 := AlgEquiv.restrictNormal_commutes τ ↥V (⟨x, hx⟩ : ↥V)
        rw [show AlgEquiv.restrictNormal τ ↥V = 1 from hσ] at h1
        exact h1.symm
      exact (IntermediateField.mem_lift (⟨x, hmem⟩ : ↥(V ⊔ B))).mpr (mem_fixedField_closure hfix)
    · have hmem : x ∈ V ⊔ B := (le_sup_right : B ≤ V ⊔ B) hx
      have hfix : τ (⟨x, hmem⟩ : ↥(V ⊔ B)) = ⟨x, hmem⟩ := σ.commutes (⟨x, hx⟩ : ↥B)
      exact (IntermediateField.mem_lift (⟨x, hmem⟩ : ↥(V ⊔ B))).mpr (mem_fixedField_closure hfix)
  ext y
  have hy : (y : Ω) ∈ IntermediateField.lift E := hsub y.2
  have hyE : y ∈ E := (IntermediateField.mem_lift y).mp hy
  rw [IntermediateField.mem_fixedField_iff] at hyE
  exact congrArg Subtype.val (hyE τ (Subgroup.subset_closure rfl))

/-! ### The compositum as a simple extension of `B` -/

variable {B V}

/-- **An element of a finite extension is integral.** -/
theorem isIntegral_of_mem [FiniteDimensional F ↥V] {x : Ω} (hx : x ∈ V) : IsIntegral F x :=
  (IsIntegral.of_finite F (⟨x, hx⟩ : ↥V)).map V.val

/-- **Adjoining a set to `F` and then enlarging the base to `K` is adjoining it to `K`.**  If the
field `W` is generated over `F` by a set `S` together with a subfield `K`, then, read as an
extension of `K`, it is generated by `S` alone. -/
theorem extendScalars_eq_adjoin {K W : IntermediateField F Ω} (S : Set Ω) (h : K ≤ W)
    (hW : W = IntermediateField.adjoin F S ⊔ K) :
    IntermediateField.extendScalars h = IntermediateField.adjoin ↥K S := by
  subst hW
  refine le_antisymm ?_ (IntermediateField.adjoin_le_iff.mpr ?_)
  · rw [IntermediateField.extendScalars_le_iff]
    exact sup_le (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin ↥K S))
      fun x hx => (IntermediateField.adjoin ↥K S).algebraMap_mem (⟨x, hx⟩ : ↥K)
  · exact fun x hx => (le_sup_left : IntermediateField.adjoin F S ≤ _)
      (IntermediateField.subset_adjoin F S hx)

/-- **A relative degree computed by a minimal polynomial.**  If `W` is generated over its subfield
`K` by a single element `θ` integral over `K`, then `[W : K]` is the degree of the minimal
polynomial of `θ` over `K`. -/
theorem relfinrank_eq_natDegree_minpoly {K W : IntermediateField F Ω} {θ : Ω} (h : K ≤ W)
    (hW : W = F⟮θ⟯ ⊔ K) (hθ : IsIntegral ↥K θ) :
    K.relfinrank W = (minpoly ↥K θ).natDegree := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le h, extendScalars_eq_adjoin {θ} h hW,
    IntermediateField.adjoin.finrank hθ]

variable (B V)

/-- **The compositum is finite over `B`.**  A finite set generating `V` over `F` generates the
compositum over `B`, and its elements are integral over `B`. -/
instance instFiniteDimensionalSup [FiniteDimensional F ↥V] :
    FiniteDimensional ↥B ↥(V ⊔ B) := by
  obtain ⟨S, hS⟩ := (IntermediateField.essFiniteType_iff (K := V)).mp inferInstance
  have hmem : ∀ x ∈ (S : Set Ω), IsIntegral ↥B x := fun x hx =>
    (isIntegral_of_mem (V := V) (hS ▸ IntermediateField.subset_adjoin F _ hx)).tower_top
  have hfd : FiniteDimensional ↥B ↥(IntermediateField.adjoin ↥B (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin hmem
  have hEq : IntermediateField.extendScalars (le_sup_right : B ≤ V ⊔ B) =
      IntermediateField.adjoin ↥B (S : Set Ω) :=
    extendScalars_eq_adjoin _ _ (by rw [hS])
  have hres : FiniteDimensional ↥B
      ↥(IntermediateField.extendScalars (le_sup_right : B ≤ V ⊔ B)) := hEq ▸ hfd
  exact hres

variable {B V}

/-- **A primitive element of the Galois factor, read inside `Ω`.**  A finite separable extension
`V / F` is generated by a single element, which can be taken to be an element of the ambient
field `Ω`. -/
theorem exists_primitive_element [FiniteDimensional F ↥V] [Algebra.IsSeparable F ↥V] :
    ∃ θ : Ω, F⟮θ⟯ = V := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F ↥V
  exact ⟨(α : Ω), by rw [← lift_adjoin_simple, hα, lift_top]⟩

variable (B V)

/-! ### The degree of the compositum -/

/-- **The compositum has degree at most `[V : F]` over `B`.**  Writing `V = F⟮θ⟯`, the compositum
is `B⟮θ⟯`, and the minimal polynomial of `θ` over `B` divides its minimal polynomial over `F`. -/
theorem finrank_sup_le_finrank [FiniteDimensional F ↥V] [IsGalois F ↥V] :
    finrank ↥B ↥(V ⊔ B) ≤ finrank F ↥V := by
  obtain ⟨θ, hθ⟩ := exists_primitive_element (V := V)
  have hFint : IsIntegral F θ := isIntegral_of_mem (V := V) (hθ ▸ mem_adjoin_simple_self F θ)
  have hBint : IsIntegral ↥B θ := hFint.tower_top
  have hV : finrank F ↥V = (minpoly F θ).natDegree := by
    rw [← hθ]; exact IntermediateField.adjoin.finrank hFint
  have hVB : finrank ↥B ↥(V ⊔ B) = (minpoly ↥B θ).natDegree := by
    rw [finrank_sup_eq_relfinrank]
    exact relfinrank_eq_natDegree_minpoly le_sup_right (by rw [hθ]) hBint
  rw [hV, hVB]
  have hdvd : minpoly ↥B θ ∣ (minpoly F θ).map (algebraMap F ↥B) :=
    minpoly.dvd_map_of_isScalarTower F ↥B θ
  have hne : (minpoly F θ).map (algebraMap F ↥B) ≠ 0 := by
    simpa using minpoly.ne_zero hFint
  calc (minpoly ↥B θ).natDegree ≤ ((minpoly F θ).map (algebraMap F ↥B)).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly F θ).natDegree := Polynomial.natDegree_map _

/-- **Full degree forces trivial intersection.**  If the compositum already has degree `[V : F]`
over `B`, then the minimal polynomial of a primitive element `θ` of `V` is the same over `F`, over
`V ⊓ B` and over `B`; comparing `[V : V ⊓ B]` with `[V : F]` in the tower `F ⊆ V ⊓ B ⊆ V` leaves
no room for `V ⊓ B` to be larger than `F`. -/
theorem inf_eq_bot_of_finrank_sup_eq [FiniteDimensional F ↥V] [IsGalois F ↥V]
    (h : finrank ↥B ↥(V ⊔ B) = finrank F ↥V) : V ⊓ B = ⊥ := by
  obtain ⟨θ, hθ⟩ := exists_primitive_element (V := V)
  have hFint : IsIntegral F θ := isIntegral_of_mem (V := V) (hθ ▸ mem_adjoin_simple_self F θ)
  have hBint : IsIntegral ↥B θ := hFint.tower_top
  have hWint : IsIntegral ↥(V ⊓ B) θ := hFint.tower_top
  have hV : finrank F ↥V = (minpoly F θ).natDegree := by
    rw [← hθ]; exact IntermediateField.adjoin.finrank hFint
  have hVB : finrank ↥B ↥(V ⊔ B) = (minpoly ↥B θ).natDegree := by
    rw [finrank_sup_eq_relfinrank]
    exact relfinrank_eq_natDegree_minpoly le_sup_right (by rw [hθ]) hBint
  have hWV : (V ⊓ B).relfinrank V = (minpoly ↥(V ⊓ B) θ).natDegree :=
    relfinrank_eq_natDegree_minpoly inf_le_left
      (by rw [hθ]; exact (sup_eq_left.mpr inf_le_left).symm) hWint
  have h1 : (minpoly ↥(V ⊓ B) θ).natDegree ≤ (minpoly F θ).natDegree := by
    refine le_trans (Polynomial.natDegree_le_of_dvd
      (minpoly.dvd_map_of_isScalarTower F ↥(V ⊓ B) θ) ?_) (le_of_eq (Polynomial.natDegree_map _))
    simpa using minpoly.ne_zero hFint
  have h2 : (minpoly ↥B θ).natDegree ≤ (minpoly ↥(V ⊓ B) θ).natDegree := by
    letI : Algebra ↥(V ⊓ B) ↥B :=
      (IntermediateField.inclusion (inf_le_right : V ⊓ B ≤ B)).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(V ⊓ B) ↥B Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine le_trans (Polynomial.natDegree_le_of_dvd
      (minpoly.dvd_map_of_isScalarTower ↥(V ⊓ B) ↥B θ) ?_) (le_of_eq (Polynomial.natDegree_map _))
    simpa using minpoly.ne_zero hWint
  have hn : (0 : ℕ) < (minpoly F θ).natDegree := by
    rw [← hV]; exact Module.finrank_pos
  have hd : (minpoly ↥(V ⊓ B) θ).natDegree = (minpoly F θ).natDegree :=
    le_antisymm h1 (by rw [← hVB, h, hV] at h2; exact h2)
  have key := IntermediateField.finrank_bot_mul_relfinrank (inf_le_left : V ⊓ B ≤ V)
  rw [hWV, hd, hV] at key
  exact IntermediateField.finrank_eq_one_iff.mp
    (Nat.eq_of_mul_eq_mul_right hn (by rw [one_mul]; exact key))

/-- **Trivial intersection forces full degree.**  Let `θ` be a primitive element of `V`.  The
minimal polynomial of `θ` over `B` divides its minimal polynomial over `F`, which splits in `V`
because `V / F` is normal; so the roots of the former lie in `V`, hence so do its coefficients.
Those coefficients lie in `B` as well, therefore in `V ⊓ B = F`, and a polynomial over `F`
annihilating `θ` has degree at least `[V : F]`. -/
theorem finrank_sup_eq_of_inf_eq_bot [FiniteDimensional F ↥V] [IsGalois F ↥V]
    (h : V ⊓ B = ⊥) : finrank ↥B ↥(V ⊔ B) = finrank F ↥V := by
  refine le_antisymm (finrank_sup_le_finrank B V) ?_
  obtain ⟨θ, hθ⟩ := exists_primitive_element (V := V)
  have hθV : θ ∈ V := hθ ▸ mem_adjoin_simple_self F θ
  have hFint : IsIntegral F θ := isIntegral_of_mem (V := V) hθV
  have hBint : IsIntegral ↥B θ := hFint.tower_top
  have hV : finrank F ↥V = (minpoly F θ).natDegree := by
    rw [← hθ]; exact IntermediateField.adjoin.finrank hFint
  have hVB : finrank ↥B ↥(V ⊔ B) = (minpoly ↥B θ).natDegree := by
    rw [finrank_sup_eq_relfinrank]
    exact relfinrank_eq_natDegree_minpoly le_sup_right (by rw [hθ]) hBint
  rw [hV, hVB]
  have hPne : (minpoly F θ).map (algebraMap F Ω) ≠ 0 := by simpa using minpoly.ne_zero hFint
  have hQmonic : ((minpoly ↥B θ).map (algebraMap ↥B Ω)).Monic := (minpoly.monic hBint).map _
  have hQP : (minpoly ↥B θ).map (algebraMap ↥B Ω) ∣ (minpoly F θ).map (algebraMap F Ω) := by
    have h1 := Polynomial.map_dvd (algebraMap ↥B Ω) (minpoly.dvd_map_of_isScalarTower F ↥B θ)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h1
  have hmm : (minpoly F θ).map (algebraMap F Ω) =
      ((minpoly F θ).map (algebraMap F ↥V)).map (algebraMap ↥V Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hmin : minpoly F θ = minpoly F (⟨θ, hθV⟩ : ↥V) :=
    minpoly.algHom_eq V.val V.val.injective (⟨θ, hθV⟩ : ↥V)
  have hsplitV : ((minpoly F θ).map (algebraMap F ↥V)).Splits := by
    rw [hmin]; exact (Normal.splits (inferInstance : Normal F ↥V)) (⟨θ, hθV⟩ : ↥V)
  have hPsplit : ((minpoly F θ).map (algebraMap F Ω)).Splits := by
    rw [hmm]; exact hsplitV.map _
  have hQsplit : ((minpoly ↥B θ).map (algebraMap ↥B Ω)).Splits := hPsplit.of_dvd hPne hQP
  have hProots : ∀ r ∈ ((minpoly F θ).map (algebraMap F Ω)).roots, r ∈ V := by
    intro r hr
    rw [hmm, hsplitV.roots_map (algebraMap ↥V Ω)] at hr
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hr
    exact v.2
  have hQroots : ∀ r ∈ ((minpoly ↥B θ).map (algebraMap ↥B Ω)).roots, r ∈ V := fun r hr =>
    hProots r (Multiset.mem_of_le (Polynomial.roots.le_of_dvd hPne hQP) hr)
  have hliftV : (minpoly ↥B θ).map (algebraMap ↥B Ω) ∈
      Polynomial.lifts (algebraMap ↥V Ω) := by
    rw [hQsplit.eq_prod_roots_of_monic hQmonic]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hp
    exact ⟨X - C (⟨a, hQroots a ha⟩ : ↥V), by simp⟩
  have hliftB : (minpoly ↥B θ).map (algebraMap ↥B Ω) ∈
      Polynomial.lifts (algebraMap ↥B Ω) := ⟨minpoly ↥B θ, rfl⟩
  have hcoeff : ∀ i, ((minpoly ↥B θ).map (algebraMap ↥B Ω)).coeff i ∈
      Set.range (algebraMap F Ω) := by
    intro i
    obtain ⟨v, hv⟩ := (Polynomial.lifts_iff_coeff_lifts _).mp hliftV i
    obtain ⟨b, hb⟩ := (Polynomial.lifts_iff_coeff_lifts _).mp hliftB i
    have hmem : ((minpoly ↥B θ).map (algebraMap ↥B Ω)).coeff i ∈ V ⊓ B := ⟨hv ▸ v.2, hb ▸ b.2⟩
    rw [h] at hmem
    exact IntermediateField.mem_bot.mp hmem
  obtain ⟨r, hr⟩ := (Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff
  have hrmap : r.map (algebraMap F Ω) = (minpoly ↥B θ).map (algebraMap ↥B Ω) := hr
  have haeval : (Polynomial.aeval θ) r = 0 := by
    have h3 : Polynomial.eval θ (r.map (algebraMap F Ω)) = 0 := by
      rw [hrmap, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval ↥B θ
    rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h3
  have hrne : r ≠ 0 := fun h0 => by
    rw [h0, Polynomial.map_zero] at hrmap
    exact hQmonic.ne_zero hrmap.symm
  calc (minpoly F θ).natDegree ≤ r.natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd F θ haeval) hrne
    _ = ((minpoly ↥B θ).map (algebraMap ↥B Ω)).natDegree := by
        rw [← hrmap, Polynomial.natDegree_map]
    _ = (minpoly ↥B θ).natDegree := Polynomial.natDegree_map _

/-- **The theorem of natural irrationalities in degree form.**  For a finite Galois `V / F` and an
arbitrary extension `B / F` inside a common field, the compositum has the full degree `[V : F]`
over `B` exactly when `V` and `B` meet only in `F`. -/
theorem finrank_sup_eq_iff_inf_eq_bot [FiniteDimensional F ↥V] [IsGalois F ↥V] :
    finrank ↥B ↥(V ⊔ B) = finrank F ↥V ↔ V ⊓ B = ⊥ :=
  ⟨inf_eq_bot_of_finrank_sup_eq B V, finrank_sup_eq_of_inf_eq_bot B V⟩

end Rigidity.RET.Wreath
