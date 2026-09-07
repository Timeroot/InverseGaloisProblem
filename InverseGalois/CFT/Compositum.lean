import Mathlib

/-!
# The Galois group of a compositum of two Galois extensions

Let `L / F` be a field extension and let `A B : IntermediateField F L` be two finite Galois
extensions of `F` with `A ⊓ B = ⊥`. Restricting an automorphism of the compositum `A ⊔ B` to
`A` and to `B` gives an isomorphism

`Gal(↥(A ⊔ B)/F) ≃* Gal(A/F) × Gal(B/F)`.

## Main definitions

* `InverseGalois.CFT.galRestrictProd`: the restriction homomorphism
  `Gal(↥(A ⊔ B)/F) →* Gal(A/F) × Gal(B/F)`.
* `InverseGalois.CFT.galEquivProd`: the isomorphism above, for `A ⊓ B = ⊥`.

## Main results

* `InverseGalois.CFT.isGalois_sup`: the compositum of two Galois extensions is Galois.
* `InverseGalois.CFT.finrank_sup_of_inf_eq_bot`: `[A ⊔ B : F] = [A : F] * [B : F]`.
* `InverseGalois.CFT.galRestrictProd_injective`: restriction to `A` and `B` is injective.
* `InverseGalois.CFT.coe_galRestrictProd_fst`, `InverseGalois.CFT.coe_galRestrictProd_snd`:
  the two components of `galRestrictProd σ` act as `σ` does, seen inside `L`.

-/

namespace InverseGalois.CFT

open Module IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- An intermediate field that is normal over the base stays normal when viewed as an
intermediate field of a larger intermediate field. -/
local instance normalRestrict {E E' : IntermediateField F L} (h : E ≤ E') [Normal F E] :
    Normal F ↥(IntermediateField.restrict h) :=
  Normal.of_algEquiv (IntermediateField.restrict_algEquiv h)

/-- Viewing an element of `E` as an element of the larger intermediate field `E'` does not
change its value in `L`. -/
theorem coe_restrict_algEquiv {E E' : IntermediateField F L} (h : E ≤ E') (x : E) :
    ((IntermediateField.restrict_algEquiv h x : E') : L) = (x : L) :=
  rfl

variable (A B : IntermediateField F L)

/-- The two copies of `A` and `B` inside the compositum `A ⊔ B` generate it. -/
theorem restrict_sup_restrict :
    IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B) ⊔
      IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B) = ⊤ := by
  rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
    IntermediateField.lift_restrict, IntermediateField.lift_restrict]

section Normal

variable [Normal F A] [Normal F B]

/-- Restriction of an automorphism of the compositum `A ⊔ B` to the two normal subextensions
`A` and `B`. -/
noncomputable def galRestrictProd : Gal(↥(A ⊔ B)/F) →* Gal(A/F) × Gal(B/F) :=
  MonoidHom.prod
    ((AlgEquiv.autCongr
        (IntermediateField.restrict_algEquiv (le_sup_left : A ≤ A ⊔ B))).symm.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B))))
    ((AlgEquiv.autCongr
        (IntermediateField.restrict_algEquiv (le_sup_right : B ≤ A ⊔ B))).symm.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B))))

/-- Reading off, inside `L`, the restriction of `σ : Gal(E'/F)` to a normal subextension `E`
of `E'`. -/
theorem coe_autCongr_symm_restrictNormalHom {E E' : IntermediateField F L} (h : E ≤ E')
    [Normal F E] (σ : Gal(↥E'/F)) (x : E) :
    (((AlgEquiv.autCongr (IntermediateField.restrict_algEquiv h)).symm
        (AlgEquiv.restrictNormalHom (IntermediateField.restrict h) σ) x : E) : L) =
      ((σ ⟨(x : L), h x.2⟩ : ↥E') : L) := by
  set e := IntermediateField.restrict_algEquiv h with he
  show ((e.symm (AlgEquiv.restrictNormalHom (IntermediateField.restrict h) σ (e x)) : E) : L) = _
  rw [← coe_restrict_algEquiv h
      (e.symm (AlgEquiv.restrictNormalHom (IntermediateField.restrict h) σ (e x))),
    AlgEquiv.apply_symm_apply, AlgEquiv.restrictNormalHom_apply]
  exact congrArg _ (congrArg σ (Subtype.ext (coe_restrict_algEquiv h x)))

/-- The first component of `galRestrictProd` is the restriction of `σ` to `A`. -/
theorem coe_galRestrictProd_fst (σ : Gal(↥(A ⊔ B)/F)) (x : A) :
    (((galRestrictProd A B σ).1 x : A) : L) =
      ((σ ⟨(x : L), (le_sup_left : A ≤ A ⊔ B) x.2⟩ : ↥(A ⊔ B)) : L) :=
  coe_autCongr_symm_restrictNormalHom (le_sup_left : A ≤ A ⊔ B) σ x

/-- The second component of `galRestrictProd` is the restriction of `σ` to `B`. -/
theorem coe_galRestrictProd_snd (σ : Gal(↥(A ⊔ B)/F)) (x : B) :
    (((galRestrictProd A B σ).2 x : B) : L) =
      ((σ ⟨(x : L), (le_sup_right : B ≤ A ⊔ B) x.2⟩ : ↥(A ⊔ B)) : L) :=
  coe_autCongr_symm_restrictNormalHom (le_sup_right : B ≤ A ⊔ B) σ x

theorem galRestrictProd_injective : Function.Injective (galRestrictProd A B) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hA : AlgEquiv.restrictNormalHom
      (IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B)) σ = 1 := by
    have h := congrArg Prod.fst hσ
    simpa only [galRestrictProd, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, Prod.fst_one, EmbeddingLike.map_eq_one_iff] using h
  have hB : AlgEquiv.restrictNormalHom
      (IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B)) σ = 1 := by
    have h := congrArg Prod.snd hσ
    simpa only [galRestrictProd, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, Prod.snd_one, EmbeddingLike.map_eq_one_iff] using h
  have hmemA : σ ∈ (IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := AlgEquiv.restrictNormalHom_apply
      (IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B)) σ ⟨x, hx⟩
    rw [hA] at h
    simpa using h.symm
  have hmemB : σ ∈ (IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := AlgEquiv.restrictNormalHom_apply
      (IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B)) σ ⟨x, hx⟩
    rw [hB] at h
    simpa using h.symm
  have hmem : σ ∈ (⊤ : IntermediateField F ↥(A ⊔ B)).fixingSubgroup := by
    rw [← restrict_sup_restrict A B, IntermediateField.fixingSubgroup_sup]
    exact ⟨hmemA, hmemB⟩
  rw [IntermediateField.fixingSubgroup_top] at hmem
  simpa using hmem

end Normal

section Galois

variable [IsGalois F A] [FiniteDimensional F A] [IsGalois F B] [FiniteDimensional F B]

omit [FiniteDimensional F A] [FiniteDimensional F B] in
/-- The compositum of two Galois subextensions is Galois. -/
theorem isGalois_sup : IsGalois F ↥(A ⊔ B) := inferInstance

omit [IsGalois F B] in
/-- If two finite Galois subextensions meet in the base field, the degree of their compositum
is the product of their degrees. -/
theorem finrank_sup_of_inf_eq_bot (h : A ⊓ B = ⊥) :
    finrank F ↥(A ⊔ B) = finrank F A * finrank F B :=
  (IntermediateField.LinearDisjoint.of_inf_eq_bot h).finrank_sup

/-- For two finite Galois subextensions meeting in the base field, restriction identifies the
Galois group of the compositum with the product of the two Galois groups. -/
noncomputable def galEquivProd (h : A ⊓ B = ⊥) : Gal(↥(A ⊔ B)/F) ≃* Gal(A/F) × Gal(B/F) :=
  MulEquiv.ofBijective (galRestrictProd A B)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨galRestrictProd_injective A B, by
        rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
          IsGalois.card_aut_eq_finrank, finrank_sup_of_inf_eq_bot A B h]⟩)

@[simp]
theorem galEquivProd_apply (h : A ⊓ B = ⊥) (σ : Gal(↥(A ⊔ B)/F)) :
    galEquivProd A B h σ = galRestrictProd A B σ :=
  rfl

end Galois

/-! ### Generating the compositum over an intermediate base field -/

section Tower

variable {k K N P : Type*} [Field k] [Field K] [Field N] [Field P] [Algebra k K] [Algebra k N]
  [Algebra K N] [Algebra k P] [Algebra K P] [IsScalarTower k K P] [Algebra N P]
  [IsScalarTower K N P] [IsScalarTower k N P]

/-- An intermediate field of an extension of the base field is the same set of elements whichever
of the two fields it is read over. -/
theorem restrictScalars_fieldRange :
    ((IsScalarTower.toAlgHom K N P).fieldRange).restrictScalars k
      = (IsScalarTower.toAlgHom k N P).fieldRange :=
  SetLike.ext' <| by
    rw [IntermediateField.coe_restrictScalars, AlgHom.coe_fieldRange, AlgHom.coe_fieldRange,
      IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']

/-- Two intermediate fields generating an extension over the base field also generate it over any
intermediate field: generating is a statement about sets of elements. -/
theorem sup_eq_top_of_restrictScalars_sup_eq_top {X Y : IntermediateField K P}
    (h : X.restrictScalars k ⊔ Y.restrictScalars k = ⊤) : X ⊔ Y = ⊤ := by
  have hle : X.restrictScalars k ⊔ Y.restrictScalars k ≤ (X ⊔ Y).restrictScalars k :=
    sup_le
      (fun x hx => (IntermediateField.mem_restrictScalars k).2
        (SetLike.le_def.1 le_sup_left ((IntermediateField.mem_restrictScalars k).1 hx)))
      (fun x hx => (IntermediateField.mem_restrictScalars k).2
        (SetLike.le_def.1 le_sup_right ((IntermediateField.mem_restrictScalars k).1 hx)))
  refine le_antisymm le_top fun x _ => ?_
  have hx : x ∈ X.restrictScalars k ⊔ Y.restrictScalars k := by
    rw [h]
    exact IntermediateField.mem_top
  exact (IntermediateField.mem_restrictScalars k).1 (hle hx)

end Tower

section Sup

variable {k K M : Type*} [Field k] [Field K] [Field M] [Algebra k K] [Algebra k M]

/-- The image of an intermediate field inside a larger one is that intermediate field, read
inside the larger one. -/
theorem fieldRange_eq_restrict_of_coe {E C : IntermediateField k M} (hle : E ≤ C)
    [Algebra ↥E ↥C] [IsScalarTower k ↥E ↥C]
    (h : ∀ x : ↥E, ((algebraMap ↥E ↥C x : ↥C) : M) = (x : M)) :
    (IsScalarTower.toAlgHom k ↥E ↥C).fieldRange = IntermediateField.restrict hle := by
  refine IntermediateField.ext fun x => ?_
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_restrict]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : ((IsScalarTower.toAlgHom k ↥E ↥C y : ↥C) : M) = (y : M) := h y
    exact hy ▸ y.2
  · exact fun hx => ⟨⟨(x : M), hx⟩, Subtype.ext (h ⟨(x : M), hx⟩)⟩

variable (E₁ E₂ : IntermediateField k M) [Algebra K ↥(E₁ ⊔ E₂)] [IsScalarTower k K ↥(E₁ ⊔ E₂)]
  [Algebra K ↥E₁] [Algebra ↥E₁ ↥(E₁ ⊔ E₂)]
  [IsScalarTower K ↥E₁ ↥(E₁ ⊔ E₂)] [IsScalarTower k ↥E₁ ↥(E₁ ⊔ E₂)]
  [Algebra K ↥E₂] [Algebra ↥E₂ ↥(E₁ ⊔ E₂)]
  [IsScalarTower K ↥E₂ ↥(E₁ ⊔ E₂)] [IsScalarTower k ↥E₂ ↥(E₁ ⊔ E₂)]

/-- **The two copies of two intermediate fields inside their compositum generate it over any
intermediate base field.**  Whether the compositum is generated is a statement about sets of
elements, which does not see the base field it is read over. -/
theorem fieldRange_sup_fieldRange_eq_top
    (hE₁ : ∀ x : ↥E₁, ((algebraMap ↥E₁ ↥(E₁ ⊔ E₂) x : ↥(E₁ ⊔ E₂)) : M) = (x : M))
    (hE₂ : ∀ x : ↥E₂, ((algebraMap ↥E₂ ↥(E₁ ⊔ E₂) x : ↥(E₁ ⊔ E₂)) : M) = (x : M)) :
    (IsScalarTower.toAlgHom K ↥E₁ ↥(E₁ ⊔ E₂)).fieldRange ⊔
      (IsScalarTower.toAlgHom K ↥E₂ ↥(E₁ ⊔ E₂)).fieldRange = ⊤ := by
  refine sup_eq_top_of_restrictScalars_sup_eq_top (k := k) ?_
  rw [restrictScalars_fieldRange, restrictScalars_fieldRange,
    fieldRange_eq_restrict_of_coe (le_sup_left : E₁ ≤ E₁ ⊔ E₂) hE₁,
    fieldRange_eq_restrict_of_coe (le_sup_right : E₂ ≤ E₁ ⊔ E₂) hE₂]
  exact restrict_sup_restrict E₁ E₂

end Sup

end InverseGalois.CFT
