import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.DirectSummand
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

/-!
# Connected objects of the Galois category of finite étale algebras

For a field `K`, the Galois category of finite étale covers of `Spec K` is
`(FiniteEtaleAlgCat K)ᵒᵖ`.  This file establishes the classical dictionary identifying its
**connected objects** with the **finite separable field extensions** of `K`:

>   `op A` is connected  ⟺  `A.obj` is a field.

Geometrically, a finite étale cover of a point `Spec K` is connected exactly when its coordinate ring
has no nontrivial idempotents, i.e. it does not split as a product; over a field such a ring is a
finite separable field extension.  The intermediate `isConnected_op_iff_nontrivial_isIdempotentElem`
records the idempotent-theoretic reformulation, which is what the proof runs through.
-/

open CategoryTheory Limits Functor
open scoped TensorProduct
open Rigidity.RET.Etale (etale_of_isScalarTower etale_moduleFinite)

universe u

namespace Rigidity.RET.Etale.FiniteEtaleAlgCat

variable {K : Type u} [Field K]

/-! ## Morphism-level utilities -/

/-- The underlying algebra map of the morphism built from a `K`-algebra map is that map itself. -/
lemma homAlg_homMk {X Y : FiniteEtaleAlgCat.{u} K} (φ : X.obj →ₐ[K] Y.obj) :
    homAlg K (ObjectProperty.homMk (CommAlgCat.ofHom φ) : X ⟶ Y) = φ := rfl

/-- Two morphisms of finite étale `K`-algebras with the same underlying algebra map are equal. -/
lemma hom_ext_of_homAlg {X Y : FiniteEtaleAlgCat.{u} K} {f g : X ⟶ Y}
    (h : homAlg K f = homAlg K g) : f = g := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  exact h

/-- The isomorphism of finite étale `K`-algebras induced by an algebra isomorphism of their
carriers. -/
def isoOfAlgEquiv {X Y : FiniteEtaleAlgCat.{u} K} (φ : X.obj ≃ₐ[K] Y.obj) : X ≅ Y where
  hom := ObjectProperty.homMk (CommAlgCat.ofHom φ.toAlgHom)
  inv := ObjectProperty.homMk (CommAlgCat.ofHom φ.symm.toAlgHom)
  hom_inv_id := by
    apply hom_ext_of_homAlg
    rw [homAlg_comp, homAlg_id, homAlg_homMk, homAlg_homMk]
    apply AlgHom.ext; intro x
    exact φ.symm_apply_apply x
  inv_hom_id := by
    apply hom_ext_of_homAlg
    rw [homAlg_comp, homAlg_id, homAlg_homMk, homAlg_homMk]
    apply AlgHom.ext; intro y
    exact φ.apply_symm_apply y

/-- A morphism of finite étale `K`-algebras whose underlying algebra map is bijective is an
isomorphism. -/
lemma isIso_of_homAlg_bijective {X Y : FiniteEtaleAlgCat.{u} K} (f : X ⟶ Y)
    (hf : Function.Bijective (homAlg K f)) : IsIso f := by
  have hfeq : f = (isoOfAlgEquiv (AlgEquiv.ofBijective (homAlg K f) hf)).hom := by
    apply hom_ext_of_homAlg
    apply AlgHom.ext; intro x
    rfl
  rw [hfeq]
  infer_instance

/-- The underlying algebra map of an isomorphism of finite étale `K`-algebras is bijective. -/
lemma homAlg_bijective_of_isIso {X Y : FiniteEtaleAlgCat.{u} K} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (homAlg K f) := by
  have k1 := congrArg (homAlg K) (IsIso.hom_inv_id f)
  have k2 := congrArg (homAlg K) (IsIso.inv_hom_id f)
  rw [homAlg_comp, homAlg_id] at k1 k2
  refine ⟨fun a b hab => ?_, fun y => ⟨homAlg K (inv f) y, ?_⟩⟩
  · have ka := DFunLike.congr_fun k1 a
    have kb := DFunLike.congr_fun k1 b
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at ka kb
    rw [← ka, ← kb, hab]
  · have ky := DFunLike.congr_fun k2 y
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at ky
    exact ky

/-! ## Initiality in the opposite category -/

/-- A finite étale `K`-algebra whose carrier is trivial is terminal: into it there is a unique
morphism from any object. -/
noncomputable def subsingleton_isTerminal (A : FiniteEtaleAlgCat.{u} K) [Subsingleton A.obj] :
    IsTerminal A := by
  haveI : ∀ B : FiniteEtaleAlgCat.{u} K, Unique (B ⟶ A) := fun B =>
    ⟨⟨ObjectProperty.homMk (CommAlgCat.ofHom (default : B.obj →ₐ[K] A.obj))⟩, fun m => by
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _⟩
  exact IsTerminal.ofUnique A

/-- **`op A` is non-initial exactly when `A.obj` is nontrivial.**  The initial object of the Galois
category is the opposite of the trivial (one-point) cover. -/
theorem notInitial_op_iff_nontrivial (A : FiniteEtaleAlgCat.{u} K) :
    (IsInitial (Opposite.op A) → False) ↔ Nontrivial A.obj := by
  constructor
  · intro h
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    exact h (initialOpOfTerminal (subsingleton_isTerminal A))
  · intro hnt hI
    haveI := hnt
    haveI hetprod : Algebra.Etale K (A.obj × A.obj) := inferInstance
    have t : IsTerminal A := terminalUnopOfInitial hI
    have hfg : (ObjectProperty.homMk (CommAlgCat.ofHom (AlgHom.fst K A.obj A.obj)) :
          (⟨CommAlgCat.of K (A.obj × A.obj), hetprod⟩ : FiniteEtaleAlgCat.{u} K) ⟶ A)
        = ObjectProperty.homMk (CommAlgCat.ofHom (AlgHom.snd K A.obj A.obj)) :=
      t.hom_ext _ _
    have h := congrArg (homAlg K) hfg
    rw [homAlg_homMk, homAlg_homMk] at h
    have hc := DFunLike.congr_fun h ((1 : A.obj), (0 : A.obj))
    exact one_ne_zero (hc : (1 : A.obj) = 0)

/-! ## Surjectivity and idempotent kernels of epimorphisms -/

/-- An epimorphism of finite étale `K`-algebras has surjective underlying algebra map, and its kernel
is generated by an idempotent. -/
lemma epi_surjective_ker {X Y : FiniteEtaleAlgCat.{u} K} (q : X ⟶ Y) [Epi q] :
    Function.Surjective (homAlg K q) ∧
      ∃ e : X.obj, IsIdempotentElem e ∧
        RingHom.ker (homAlg K q).toRingHom = Ideal.span {e} := by
  set qA := homAlg K q with hqA
  letI : Algebra (X.obj : Type u) (Y.obj : Type u) := qA.toRingHom.toAlgebra
  haveI hstK : IsScalarTower K (X.obj : Type u) (Y.obj : Type u) :=
    IsScalarTower.of_algebraMap_eq (fun x => (qA.commutes x).symm)
  haveI hMKA : Module.Finite K (Y.obj : Type u) := etale_moduleFinite (K := K) (Y.obj : Type u)
  haveI hMKB : Module.Finite K (X.obj : Type u) := etale_moduleFinite (K := K) (X.obj : Type u)
  haveI hRT : Algebra.Etale (X.obj : Type u) (Y.obj : Type u) :=
    etale_of_isScalarTower (K := K) (X.obj : Type u) (Y.obj : Type u)
  haveI hTBA :
      Algebra.Etale (Y.obj : Type u) ((Y.obj : Type u) ⊗[(X.obj : Type u)] (Y.obj : Type u)) :=
    inferInstance
  haveI hTetale :
      Algebra.Etale K ((Y.obj : Type u) ⊗[(X.obj : Type u)] (Y.obj : Type u)) :=
    Algebra.Etale.comp K (Y.obj : Type u) ((Y.obj : Type u) ⊗[(X.obj : Type u)] (Y.obj : Type u))
  set T : FiniteEtaleAlgCat.{u} K :=
    ⟨CommAlgCat.of K ((Y.obj : Type u) ⊗[(X.obj : Type u)] (Y.obj : Type u)), hTetale⟩ with hT_def
  have hcond :
      (q ≫ (ObjectProperty.homMk (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeLeft :
            (Y.obj : Type u) →ₐ[K] (Y.obj : Type u) ⊗[(X.obj : Type u)] (Y.obj : Type u))) : Y ⟶ T))
        = (q ≫ (ObjectProperty.homMk (CommAlgCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            (Y.obj : Type u) →ₐ[(X.obj : Type u)]
              (Y.obj : Type u) ⊗[(X.obj : Type u)]
                (Y.obj : Type u)).restrictScalars K)) : Y ⟶ T)) := by
    apply hom_ext_of_homAlg
    rw [homAlg_comp, homAlg_comp, homAlg_homMk, homAlg_homMk]
    apply AlgHom.ext; intro b
    show (algebraMap (X.obj : Type u) (Y.obj : Type u) b) ⊗ₜ[(X.obj : Type u)] (1 : (Y.obj : Type u))
        = (1 : (Y.obj : Type u)) ⊗ₜ[(X.obj : Type u)]
            (algebraMap (X.obj : Type u) (Y.obj : Type u) b)
    rw [← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
  have hincl := (cancel_epi q).mp hcond
  have htmul : ∀ a : (Y.obj : Type u),
      a ⊗ₜ[(X.obj : Type u)] (1 : (Y.obj : Type u))
        = (1 : (Y.obj : Type u)) ⊗ₜ[(X.obj : Type u)] a := by
    intro a
    have h2 := congrArg (homAlg K) hincl
    rw [homAlg_homMk, homAlg_homMk] at h2
    exact DFunLike.congr_fun h2 a
  haveI : Algebra.IsEpi (X.obj : Type u) (Y.obj : Type u) :=
    (Algebra.isEpi_iff_forall_one_tmul_eq (X.obj : Type u) (Y.obj : Type u)).mpr
      (fun a => (htmul a).symm)
  haveI hfin : Module.Finite (X.obj : Type u) (Y.obj : Type u) :=
    Module.Finite.of_restrictScalars_finite K (X.obj : Type u) (Y.obj : Type u)
  have hsurj : Function.Surjective (algebraMap (X.obj : Type u) (Y.obj : Type u)) :=
    Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp inferInstance
  haveI : IsNoetherianRing (X.obj : Type u) := IsNoetherianRing.of_finite K (X.obj : Type u)
  have hidem : IsIdempotentElem (RingHom.ker (algebraMap (X.obj : Type u) (Y.obj : Type u))) :=
    (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
  have hIfg : (RingHom.ker (algebraMap (X.obj : Type u) (Y.obj : Type u))).FG :=
    IsNoetherian.noetherian _
  obtain ⟨e, he, heI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hIfg).mp hidem
  rw [Ideal.submodule_span_eq] at heI
  exact ⟨hsurj, e, he, heI⟩

/-! ## The connectedness dictionary -/

/-- **Connectedness of `op A`, idempotent form.**  In the Galois category `(FiniteEtaleAlgCat K)ᵒᵖ`,
the object `op A` is connected exactly when its coordinate ring `A.obj` is nontrivial and has no
idempotents besides `0` and `1`. -/
theorem isConnected_op_iff_nontrivial_isIdempotentElem (A : FiniteEtaleAlgCat.{u} K) :
    PreGaloisCategory.IsConnected (Opposite.op A) ↔
      Nontrivial A.obj ∧ ∀ e : A.obj, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro hC
    refine ⟨(notInitial_op_iff_nontrivial A).mp hC.notInitial, fun e he => ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨he0, he1⟩ := hcon
    -- Build the proper, nontrivial quotient `A.obj ⧸ (1 - e)` and its structural morphism.
    haveI : Module.Finite K A.obj := etale_moduleFinite A.obj
    haveI : IsNoetherianRing A.obj := IsNoetherianRing.of_finite K A.obj
    set J : Ideal A.obj := Ideal.span {1 - e} with hJ_def
    haveI hfC : Module.Finite A.obj (A.obj ⧸ J) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ A.obj J).toLinearMap
        (Ideal.Quotient.mkₐ_surjective A.obj J)
    have hmksurj : Function.Surjective (algebraMap A.obj (A.obj ⧸ J)) := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
    have hkerJ : RingHom.ker (algebraMap A.obj (A.obj ⧸ J)) = J := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.mk_ker
    have hJfg : J.FG := IsNoetherian.noetherian J
    have hidemJideal : IsIdempotentElem J := by
      rw [Ideal.isIdempotentElem_iff_of_fg J hJfg]
      exact ⟨1 - e, he.one_sub, by rw [hJ_def, Ideal.submodule_span_eq]⟩
    haveI hfeC : Algebra.FormallyEtale A.obj (A.obj ⧸ J) :=
      (Algebra.FormallyEtale.iff_of_surjective hmksurj).mpr (by rw [hkerJ]; exact hidemJideal)
    haveI hftC : Algebra.FiniteType A.obj (A.obj ⧸ J) := inferInstance
    haveI hfpC : Algebra.FinitePresentation A.obj (A.obj ⧸ J) :=
      (Algebra.FinitePresentation.of_finiteType).mp inferInstance
    haveI hetAC : Algebra.Etale A.obj (A.obj ⧸ J) := ⟨hfeC, hfpC⟩
    haveI hetKC : Algebra.Etale K (A.obj ⧸ J) := Algebra.Etale.comp K A.obj (A.obj ⧸ J)
    set Q : FiniteEtaleAlgCat.{u} K := ⟨CommAlgCat.of K (A.obj ⧸ J), hetKC⟩ with hQ_def
    set mkMor : A ⟶ Q := ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K J)) with hmk
    -- `mkMor` is epi (surjective) but not injective, contradicting connectedness.
    haveI hepiMk : Epi mkMor := by
      apply ConcreteCategory.epi_of_surjective
      intro y
      obtain ⟨x, hx⟩ := Ideal.Quotient.mkₐ_surjective K J y
      exact ⟨x, hx⟩
    -- The quotient is nontrivial: `1 - e` is not a unit since `e ≠ 0`.
    have hJne : J ≠ ⊤ := by
      intro hJtop
      rw [Ideal.eq_top_iff_one, hJ_def, Ideal.mem_span_singleton'] at hJtop
      obtain ⟨c, hc⟩ := hJtop
      have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
      have key : e = 0 := by
        have hz : e * (c * (1 - e)) = 0 := by
          calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
            _ = 0 := by rw [h0, mul_zero]
        rwa [hc, mul_one] at hz
      exact he0 key
    have hYnotInit : IsInitial (Opposite.op Q) → False :=
      (notInitial_op_iff_nontrivial Q).mpr (Ideal.Quotient.nontrivial_iff.mpr hJne)
    haveI : Mono mkMor.op := op_mono_of_epi mkMor
    have hiso : IsIso mkMor.op :=
      hC.noTrivialComponent (Opposite.op Q) mkMor.op hYnotInit
    haveI : IsIso mkMor.op := hiso
    haveI hmkiso : IsIso mkMor := isIso_of_op mkMor
    have hbij := homAlg_bijective_of_isIso mkMor
    -- Injectivity of the quotient map forces `1 - e = 0`, i.e. `e = 1`.
    have h1e : (1 - e : A.obj) = 0 := by
      apply hbij.1
      rw [map_zero]
      show (Ideal.Quotient.mkₐ K J) (1 - e) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hJ_def]
      exact Ideal.mem_span_singleton_self (1 - e)
    exact he1 (sub_eq_zero.mp h1e).symm
  · rintro ⟨hnt, hidem⟩
    refine ⟨(notInitial_op_iff_nontrivial A).mpr hnt, ?_⟩
    intro Y i hi hY
    haveI : Mono i := hi
    -- `i.unop : A ⟶ Y.unop` is an epi; extract surjectivity and the idempotent kernel generator.
    haveI : Epi i.unop := unop_epi_of_mono i
    obtain ⟨hsurj, e, he, hker⟩ := epi_surjective_ker (i.unop)
    rcases hidem e he with rfl | rfl
    · -- `e = 0`: the kernel is trivial, so `i.unop` is injective, hence an isomorphism.
      rw [Ideal.span_singleton_eq_bot.mpr rfl] at hker
      have hinj : Function.Injective (homAlg K i.unop) := by
        rw [injective_iff_map_eq_zero]
        intro a ha
        have hm : a ∈ RingHom.ker (homAlg K i.unop).toRingHom := RingHom.mem_ker.mpr ha
        rw [hker, Ideal.mem_bot] at hm
        exact hm
      have := isIso_of_homAlg_bijective (i.unop) ⟨hinj, hsurj⟩
      haveI : IsIso i.unop := this
      exact (isIso_unop_iff i).mp inferInstance
    · -- `e = 1`: the kernel is everything, forcing `Y.unop` trivial, contradicting `hY`.
      rw [Ideal.span_singleton_one] at hker
      haveI : Subsingleton Y.unop.obj := by
        refine ⟨fun y1 y2 => ?_⟩
        obtain ⟨x1, hx1⟩ := hsurj y1
        obtain ⟨x2, hx2⟩ := hsurj y2
        have e1 : homAlg K i.unop x1 = 0 := by
          have hm : x1 ∈ RingHom.ker (homAlg K i.unop).toRingHom := by
            rw [hker]; exact Submodule.mem_top
          exact RingHom.mem_ker.mp hm
        have e2 : homAlg K i.unop x2 = 0 := by
          have hm : x2 ∈ RingHom.ker (homAlg K i.unop).toRingHom := by
            rw [hker]; exact Submodule.mem_top
          exact RingHom.mem_ker.mp hm
        rw [← hx1, ← hx2, e1, e2]
      exact (hY (Opposite.op_unop Y ▸ initialOpOfTerminal (subsingleton_isTerminal Y.unop))).elim

/-! ## The field characterisation -/

/-- Transfer of the field property along a ring isomorphism. -/
lemma isField_of_ringEquiv {R F : Type u} [CommRing R] [Field F] (φ : R ≃+* F) : IsField R where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (by rw [← map_zero φ, ← map_one φ, h])⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    have h1 : φ a ≠ 0 := fun h => ha (by rw [← map_zero φ] at h; exact φ.injective h)
    refine ⟨φ.symm (φ a)⁻¹, ?_⟩
    apply φ.injective
    rw [map_mul, map_one, φ.apply_symm_apply, mul_inv_cancel₀ h1]

/-- **A finite étale `K`-algebra is a field exactly when it is a nontrivial ring with no nontrivial
idempotents.**  Étaleness over a field presents `A.obj` as a product of separable field extensions;
the connectedness condition selects the single-factor case. -/
theorem isField_iff_nontrivial_isIdempotentElem (A : FiniteEtaleAlgCat.{u} K) :
    IsField A.obj ↔
      Nontrivial A.obj ∧ ∀ e : A.obj, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro hF
    refine ⟨hF.nontrivial, fun e he => ?_⟩
    haveI := hF.isDomain
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro ⟨hnt, hidem⟩
    haveI := hnt
    obtain ⟨I, _, L, _, _, e, _hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A.obj).mp inferInstance
    haveI : Fintype I := Fintype.ofFinite I
    -- The index set is nonempty (else `A.obj` would be trivial).
    haveI hne : Nonempty I := by
      by_contra h
      haveI hem : IsEmpty I := not_nonempty_iff.mp h
      haveI : Subsingleton (∀ i, L i) := ⟨fun a b => funext fun i => (hem.false i).elim⟩
      haveI := e.toEquiv.subsingleton
      exact false_of_nontrivial_of_subsingleton A.obj
    -- The index set is a subsingleton (else a proper indicator is a nontrivial idempotent).
    haveI hss : Subsingleton I := by
      rw [← not_nontrivial_iff_subsingleton]
      rintro hNT
      haveI := hNT
      obtain ⟨i, j, hij⟩ := exists_pair_ne I
      classical
      set x : (∀ k, L k) := Pi.single i (1 : L i) with hx
      have hxidem : x * x = x := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [hx, Pi.single_eq_same]
        · simp [hx, Pi.single_eq_of_ne hk]
      have ha : IsIdempotentElem (e.symm x) := by
        show e.symm x * e.symm x = e.symm x
        rw [← map_mul, hxidem]
      rcases hidem (e.symm x) ha with h0 | h1
      · have hx0 : x = 0 := by
          have hcx := congrArg e h0
          rwa [e.apply_symm_apply, map_zero] at hcx
        have hxi := congrFun hx0 i
        rw [hx, Pi.single_eq_same] at hxi
        simp only [Pi.zero_apply] at hxi
        exact one_ne_zero hxi
      · have hx1 : x = 1 := by
          have hcx := congrArg e h1
          rwa [e.apply_symm_apply, map_one] at hcx
        have hxj := congrFun hx1 j
        rw [hx, Pi.single_eq_of_ne (Ne.symm hij)] at hxj
        simp only [Pi.one_apply] at hxj
        exact zero_ne_one hxj
    haveI : Unique I := uniqueOfSubsingleton (Classical.arbitrary I)
    exact isField_of_ringEquiv (e.toRingEquiv.trans (RingEquiv.piUnique L))

/-- **The connected–field dictionary.**  An object `op A` of the Galois category
`(FiniteEtaleAlgCat K)ᵒᵖ` is connected exactly when the coordinate ring `A.obj` is a field — a finite
separable field extension of `K`. -/
theorem isConnected_op_iff_isField (A : FiniteEtaleAlgCat.{u} K) :
    PreGaloisCategory.IsConnected (Opposite.op A) ↔ IsField A.obj := by
  rw [isConnected_op_iff_nontrivial_isIdempotentElem]
  exact (isField_iff_nontrivial_isIdempotentElem A).symm

end Rigidity.RET.Etale.FiniteEtaleAlgCat
