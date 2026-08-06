import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Fiber
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Equalizer
import InverseGalois.Rigidity.RET.Pi1.Etale.FiberFunctor
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic

open CategoryTheory Limits Functor
open scoped TensorProduct Pointwise
namespace Rigidity.RET.Etale.FiniteEtaleAlgCat
universe u
variable {K : Type u} [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

section Orbit
variable {A : Type u} [CommRing A] [Algebra K A] [Algebra.Etale K A]
variable (G : Type u) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G K A]

instance : SMulCommClass G (FixedPoints.subalgebra K A G) A where
  smul_comm g s a := by
    show g • ((s : A) * a) = (s : A) * (g • a)
    rw [smul_mul', (s.2 g : g • (s : A) = (s : A))]

instance : Algebra.IsInvariant (FixedPoints.subalgebra K A G) A G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

omit [IsAlgClosed Ω] in
/-- The kernel of a `K`-algebra map from a module-finite `K`-algebra into a field is maximal:
the quotient is a finite-dimensional integral domain over a field, hence a field. -/
theorem ker_isMaximal {B : Type u} [CommRing B] [Algebra K B] [Module.Finite K B]
    (f : B →ₐ[K] Ω) : (RingHom.ker f.toRingHom).IsMaximal := by
  haveI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
  haveI : IsDomain (B ⧸ RingHom.ker f.toRingHom) := Ideal.Quotient.isDomain _
  haveI : Module.Finite K (B ⧸ RingHom.ker f.toRingHom) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K _)
  haveI : Algebra.IsIntegral K (B ⧸ RingHom.ker f.toRingHom) := Algebra.IsIntegral.of_finite K _
  exact Ideal.Quotient.maximal_of_isField _
    (isField_of_isIntegral_of_isField' (Field.toIsField K))

omit [IsAlgClosed Ω] in
attribute [local instance] Ideal.Quotient.field in
/-- **Residual step.** Two `K`-points of `A` with the same kernel that agree on the invariant
subalgebra differ by a group element.  This is the decomposition-group surjectivity onto the
residual Galois group. -/
theorem residual
    (f f' : A →ₐ[K] Ω)
    (hker : RingHom.ker f.toRingHom = RingHom.ker f'.toRingHom)
    (hA0 : ∀ x : A, (∀ g : G, g • x = x) → f x = f' x) :
    ∃ s : G, ∀ x : A, f x = f' (s • x) := by
  classical
  haveI : Module.Finite K A := etale_moduleFinite A
  set Q : Ideal A := RingHom.ker f.toRingHom with hQ
  haveI hQmax : Q.IsMaximal := ker_isMaximal Ω f
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : Algebra.Etale K (FixedPoints.subalgebra K A G) :=
    etale_of_injective (FixedPoints.subalgebra K A G).val Subtype.val_injective
  haveI : Module.Finite K (FixedPoints.subalgebra K A G) :=
    etale_moduleFinite (K := K) (FixedPoints.subalgebra K A G)
  set P : Ideal (FixedPoints.subalgebra K A G) := Q.under (FixedPoints.subalgebra K A G) with hP
  haveI : Q.LiesOver P := ⟨rfl⟩
  -- P is the kernel of `f ∘ inclusion`, hence maximal
  have hPeq : P = RingHom.ker (f.comp (FixedPoints.subalgebra K A G).val).toRingHom := by
    apply Ideal.ext
    intro x
    rw [hP, Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
  haveI hPmax : P.IsMaximal := by
    rw [hPeq]; exact ker_isMaximal Ω (f.comp (FixedPoints.subalgebra K A G).val)
  -- residue fields and the two induced embeddings
  have hfk : ∀ a ∈ Q, f.toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  have hf'k : ∀ a ∈ Q, f'.toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp (hker ▸ ha)
  set fbarR : (A ⧸ Q) →+* Ω := Ideal.Quotient.lift Q f.toRingHom hfk with hfbarR
  set fbar'R : (A ⧸ Q) →+* Ω := Ideal.Quotient.lift Q f'.toRingHom hf'k with hfbar'R
  letI : Algebra (A ⧸ Q) Ω := fbar'R.toAlgebra
  have halg : (algebraMap (A ⧸ Q) Ω) = fbar'R := rfl
  letI : Algebra (FixedPoints.subalgebra K A G ⧸ P) Ω :=
    (fbar'R.comp (algebraMap (FixedPoints.subalgebra K A G ⧸ P) (A ⧸ Q))).toAlgebra
  haveI : IsScalarTower (FixedPoints.subalgebra K A G ⧸ P) (A ⧸ Q) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Normal (FixedPoints.subalgebra K A G ⧸ P) (A ⧸ Q) :=
    Ideal.Quotient.normal G P Q
  -- `fbar` as a `(A₀/P)`-algebra hom
  let fbar : (A ⧸ Q) →ₐ[FixedPoints.subalgebra K A G ⧸ P] Ω :=
    { fbarR with
      commutes' := by
        intro r
        obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective r
        show fbarR (algebraMap (FixedPoints.subalgebra K A G ⧸ P) (A ⧸ Q)
            (Ideal.Quotient.mk P a₀)) = _
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        show fbarR (Ideal.Quotient.mk Q ((FixedPoints.subalgebra K A G).val a₀)) = _
        rw [hfbarR, Ideal.Quotient.lift_mk]
        show f ((a₀ : A)) = fbar'R (algebraMap (FixedPoints.subalgebra K A G ⧸ P) (A ⧸ Q)
            (Ideal.Quotient.mk P a₀))
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hfbar'R, Ideal.Quotient.lift_mk]
        exact hA0 (a₀ : A) (fun g => a₀.2 g) }
  -- the residual automorphism
  set σ : (A ⧸ Q) ≃ₐ[FixedPoints.subalgebra K A G ⧸ P] (A ⧸ Q) :=
    Normal.algHomEquivAut (FixedPoints.subalgebra K A G ⧸ P) Ω (E := A ⧸ Q) fbar with hσdef
  have hfbar : (Normal.algHomEquivAut (FixedPoints.subalgebra K A G ⧸ P) Ω
      (E := A ⧸ Q)).symm σ = fbar :=
    (Normal.algHomEquivAut (FixedPoints.subalgebra K A G ⧸ P) Ω (E := A ⧸ Q)).symm_apply_apply fbar
  rw [Normal.algHomEquivAut_symm_apply] at hfbar
  have hσ : ∀ e : A ⧸ Q, fbar e = fbar'R (σ e) := by
    intro e
    have h := AlgHom.congr_fun hfbar e
    simpa [halg] using h.symm
  -- lift the automorphism to a group element via stabilizer surjectivity
  obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective
    (A := FixedPoints.subalgebra K A G) (B := A) G P Q σ
  refine ⟨(s : G), fun x => ?_⟩
  have e1 : f x = fbar (Ideal.Quotient.mk Q x) := by
    show f x = fbarR (Ideal.Quotient.mk Q x)
    rw [hfbarR, Ideal.Quotient.lift_mk]
    rfl
  have e2 : σ (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q ((s : G) • x) := by
    have := AlgEquiv.congr_fun hs (Ideal.Quotient.mk Q x)
    rw [Ideal.Quotient.stabilizerHom_apply] at this
    exact this.symm
  rw [e1, hσ (Ideal.Quotient.mk Q x), e2]
  show fbar'R (Ideal.Quotient.mk Q ((s : G) • x)) = f' ((s : G) • x)
  rw [hfbar'R, Ideal.Quotient.lift_mk]
  rfl

omit [IsAlgClosed Ω] in
/-- **The core orbit lemma.**  For a finite étale `K`-algebra `A` with a finite group `G` acting by
`K`-algebra automorphisms, two `K`-points of `A` into an algebraically closed `Ω` that agree on the
invariant subalgebra `A^G` differ by a group element. -/
theorem coreOrbit
    (h₁ h₂ : A →ₐ[K] Ω)
    (hagree : ∀ x : A, (∀ g : G, g • x = x) → h₁ x = h₂ x) :
    ∃ g : G, ∀ x : A, h₂ x = h₁ (g • x) := by
  classical
  haveI : Module.Finite K A := etale_moduleFinite A
  set 𝔪₁ : Ideal A := RingHom.ker h₁.toRingHom with h𝔪₁
  set 𝔪₂ : Ideal A := RingHom.ker h₂.toRingHom with h𝔪₂
  haveI : 𝔪₁.IsPrime := (ker_isMaximal Ω h₁).isPrime
  haveI : 𝔪₂.IsPrime := (ker_isMaximal Ω h₂).isPrime
  -- the two kernels contract to the same prime of `A^G`
  have hcontract : 𝔪₁.under (FixedPoints.subalgebra K A G)
      = 𝔪₂.under (FixedPoints.subalgebra K A G) := by
    apply Ideal.ext
    intro x
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      RingHom.mem_ker, RingHom.mem_ker]
    have hxfix : ∀ g : G, g • (algebraMap (FixedPoints.subalgebra K A G) A x)
        = algebraMap (FixedPoints.subalgebra K A G) A x := fun g => x.2 g
    show h₁.toRingHom _ = 0 ↔ h₂.toRingHom _ = 0
    rw [show h₁.toRingHom (algebraMap (FixedPoints.subalgebra K A G) A x)
      = h₂.toRingHom (algebraMap (FixedPoints.subalgebra K A G) A x) from
      hagree _ hxfix]
  -- prime transitivity: some `g` sends `𝔪₁` to `𝔪₂`
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (FixedPoints.subalgebra K A G) A G 𝔪₁ 𝔪₂ hcontract
  -- twist `h₁` by `g⁻¹` to get the same kernel as `h₂`
  set f' : A →ₐ[K] Ω := h₁.comp (MulSemiringAction.toAlgHom K A g⁻¹) with hf'
  have hkerf' : RingHom.ker h₂.toRingHom = RingHom.ker f'.toRingHom := by
    apply Ideal.ext
    intro x
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show h₂ x = 0 ↔ h₁ (g⁻¹ • x) = 0
    constructor
    · intro hx
      have hmem : x ∈ 𝔪₂ := RingHom.mem_ker.mpr hx
      rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      exact RingHom.mem_ker.mp hmem
    · intro hx
      have hmem : g⁻¹ • x ∈ 𝔪₁ := RingHom.mem_ker.mpr hx
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hg] at hmem
      exact RingHom.mem_ker.mp hmem
  have hA0' : ∀ x : A, (∀ γ : G, γ • x = x) → h₂ x = f' x := by
    intro x hx
    show h₂ x = h₁ (g⁻¹ • x)
    rw [hx g⁻¹]
    exact (hagree x hx).symm
  obtain ⟨s, hs⟩ := residual Ω G h₂ f' hkerf' hA0'
  refine ⟨g⁻¹ * s, fun x => ?_⟩
  rw [hs x]
  show h₁ (g⁻¹ • (s • x)) = h₁ ((g⁻¹ * s) • x)
  rw [mul_smul]

end Orbit

section Quotient
variable {G : Type u} [Group G] [Finite G]
variable (Fdiag : SingleObj G ⥤ (FiniteEtaleAlgCat.{u} K)ᵒᵖ)

/-- The finite étale `K`-algebra carried by the single object of a `SingleObj G` diagram. -/
abbrev qX : FiniteEtaleAlgCat K := (Fdiag.obj (SingleObj.star G)).unop

/-- Its underlying carrier. -/
abbrev qA : Type u := (qX Fdiag).obj

/-- The underlying `K`-algebra endomorphism of the group element `g`. -/
def qρ (g : G) : qA Fdiag →ₐ[K] qA Fdiag :=
  homAlg K (Fdiag.map (g : SingleObj.star G ⟶ SingleObj.star G)).unop

omit [Finite G] in
theorem qρ_one : qρ Fdiag (1 : G) = AlgHom.id K (qA Fdiag) := by
  show homAlg K (Fdiag.map (𝟙 (SingleObj.star G))).unop = _
  rw [Fdiag.map_id]
  rfl

omit [Finite G] in
theorem qρ_mul (a b : G) : qρ Fdiag (b * a) = (qρ Fdiag a).comp (qρ Fdiag b) := by
  have h : (b * a : SingleObj.star G ⟶ SingleObj.star G)
      = @CategoryStruct.comp (SingleObj G) _ (SingleObj.star G) (SingleObj.star G)
          (SingleObj.star G) a b := rfl
  show homAlg K (Fdiag.map (b * a : SingleObj.star G ⟶ SingleObj.star G)).unop = _
  rw [h, Fdiag.map_comp, unop_comp, homAlg_comp]
  rfl

/-- The group homomorphism `G →* (A ≃ₐ[K] A)` extracted from the diagram: `g` acts as `qρ g⁻¹`,
turning the anti-multiplicative `qρ` into a genuine left action. -/
def qθ : G →* (qA Fdiag ≃ₐ[K] qA Fdiag) where
  toFun g :=
    { qρ Fdiag g⁻¹ with
      invFun := qρ Fdiag g
      left_inv := fun x => by
        have : (qρ Fdiag g).comp (qρ Fdiag g⁻¹) = AlgHom.id K (qA Fdiag) := by
          rw [← qρ_mul, inv_mul_cancel, qρ_one]
        exact AlgHom.congr_fun this x
      right_inv := fun x => by
        have : (qρ Fdiag g⁻¹).comp (qρ Fdiag g) = AlgHom.id K (qA Fdiag) := by
          rw [← qρ_mul, mul_inv_cancel, qρ_one]
        exact AlgHom.congr_fun this x }
  map_one' := by
    ext x
    show qρ Fdiag (1 : G)⁻¹ x = x
    rw [inv_one, qρ_one]; rfl
  map_mul' g₁ g₂ := by
    ext x
    show qρ Fdiag (g₁ * g₂)⁻¹ x = qρ Fdiag g₁⁻¹ (qρ Fdiag g₂⁻¹ x)
    rw [mul_inv_rev]
    have := qρ_mul Fdiag g₁⁻¹ g₂⁻¹
    exact AlgHom.congr_fun this x

/-- The `MulSemiringAction G (qA Fdiag)` extracted from the diagram. -/
noncomputable def qAction : MulSemiringAction G (qA Fdiag) :=
  MulSemiringAction.compHom (qA Fdiag) (qθ Fdiag)

section Colimit
variable [MulSemiringAction G (qA Fdiag)] [SMulCommClass G K (qA Fdiag)]

/-- The invariant subalgebra `A^G`, packaged as a finite étale object. -/
def qInv : FiniteEtaleAlgCat K :=
  ⟨CommAlgCat.of K (FixedPoints.subalgebra K (qA Fdiag) G),
    etale_of_injective (FixedPoints.subalgebra K (qA Fdiag) G).val Subtype.val_injective⟩

/-- The inclusion `A^G ↪ A` as a morphism of finite étale algebras. -/
def qIncl : qInv Fdiag ⟶ qX Fdiag :=
  ObjectProperty.homMk (CommAlgCat.ofHom (FixedPoints.subalgebra K (qA Fdiag) G).val)

omit [Finite G] in
theorem homAlg_qIncl :
    homAlg K (qIncl Fdiag) = (FixedPoints.subalgebra K (qA Fdiag) G).val := by
  simp [qIncl, homAlg]

variable (hact : ∀ (g : G) (x : qA Fdiag), g • x = qρ Fdiag g⁻¹ x)
include hact

omit [Finite G] [SMulCommClass G K (qA Fdiag)] in
/-- Key fixedness: `qρ g` fixes any `G`-fixed element. -/
theorem qρ_fix (g : G) (y : qA Fdiag) (hy : ∀ h : G, h • y = y) :
    qρ Fdiag g y = y := by
  have h := hact g⁻¹ y
  rw [inv_inv] at h
  rw [← h]
  exact hy g⁻¹

/-- The colimit cocone in `(FiniteEtaleAlgCat K)ᵒᵖ` with apex `op(A^G)`. -/
def qCocone : Limits.Cocone Fdiag where
  pt := Opposite.op (qInv Fdiag)
  ι :=
    { app := fun _ => (qIncl Fdiag).op
      naturality := fun _ _ g => by
        apply Quiver.Hom.unop_inj
        show qIncl Fdiag ≫ (Fdiag.map g).unop = qIncl Fdiag
        apply ObjectProperty.hom_ext
        apply CommAlgCat.hom_ext
        show homAlg K (qIncl Fdiag ≫ (Fdiag.map g).unop) = homAlg K (qIncl Fdiag)
        rw [homAlg_comp, homAlg_qIncl]
        apply AlgHom.ext
        intro y
        exact qρ_fix Fdiag hact g _ (fun h => y.2 h) }

omit [Finite G] in
/-- Membership: every leg of a cocone under `Fdiag` lands in the invariant subalgebra. -/
theorem qCocone_mem (s : Limits.Cocone Fdiag)
    (t : (s.pt.unop.obj : Type u)) :
    (homAlg K (s.ι.app (SingleObj.star G)).unop) t
      ∈ FixedPoints.subalgebra K (qA Fdiag) G := by
  show ∀ g : G, g • (homAlg K (s.ι.app (SingleObj.star G)).unop) t
    = (homAlg K (s.ι.app (SingleObj.star G)).unop) t
  intro g
  rw [hact g]
  have hnat := s.w (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)
  have hnat' := congrArg Quiver.Hom.unop hnat
  rw [unop_comp] at hnat'
  have h2 := congrArg (fun m => homAlg K m) hnat'
  simp only [homAlg_comp] at h2
  exact AlgHom.congr_fun h2 t

/-- The factoring morphism `T ⟶ A^G` induced by a cocone `s`. -/
def qDescHom (s : Limits.Cocone Fdiag) : s.pt.unop ⟶ qInv Fdiag :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    (AlgHom.codRestrict (homAlg K (s.ι.app (SingleObj.star G)).unop)
      (FixedPoints.subalgebra K (qA Fdiag) G) (qCocone_mem Fdiag hact s)))

omit [Finite G] in
theorem homAlg_qDescHom (s : Limits.Cocone Fdiag) :
    homAlg K (qDescHom Fdiag hact s)
      = AlgHom.codRestrict (homAlg K (s.ι.app (SingleObj.star G)).unop)
          (FixedPoints.subalgebra K (qA Fdiag) G) (qCocone_mem Fdiag hact s) := by
  simp [qDescHom, homAlg]

/-- The `op(A^G)` cocone is a colimit. -/
def qCoconeIsColimit : Limits.IsColimit (qCocone Fdiag hact) where
  desc s := (qDescHom Fdiag hact s).op
  fac s := fun _ => by
    apply Quiver.Hom.unop_inj
    show qDescHom Fdiag hact s ≫ qIncl Fdiag = (s.ι.app (SingleObj.star G)).unop
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    show homAlg K (qDescHom Fdiag hact s ≫ qIncl Fdiag)
      = homAlg K (s.ι.app (SingleObj.star G)).unop
    rw [homAlg_comp, homAlg_qIncl, homAlg_qDescHom]
    apply AlgHom.ext
    intro t
    rfl
  uniq s m h := by
    apply Quiver.Hom.unop_inj
    show m.unop = qDescHom Fdiag hact s
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    have hstar := h (SingleObj.star G)
    apply AlgHom.ext
    intro t
    apply Subtype.ext
    -- `val (homAlg m.unop t) = homAlg s.ι t = val (φ' t)`
    have hcomp : homAlg K (m.unop ≫ qIncl Fdiag)
        = homAlg K (s.ι.app (SingleObj.star G)).unop := by
      have := congrArg Quiver.Hom.unop hstar
      rw [unop_comp] at this
      exact congrArg (fun r => homAlg K r) this
    rw [homAlg_comp, homAlg_qIncl] at hcomp
    have := AlgHom.congr_fun hcomp t
    show ((FixedPoints.subalgebra K (qA Fdiag) G).val) (homAlg K m.unop t)
      = ((FixedPoints.subalgebra K (qA Fdiag) G).val)
          (homAlg K (qDescHom Fdiag hact s) t)
    rw [homAlg_qDescHom]
    exact this

omit [Finite G] hact in
/-- **Surjectivity on fibres.**  Every `Ω`-point of the invariant subalgebra `A^G` extends to an
`Ω`-point of `A`, because `A` is finite étale (module-finite) over `A^G` via the injective
inclusion. -/
theorem qRestrict_surjective :
    Function.Surjective
      (fun h : qA Fdiag →ₐ[K] Ω =>
        h.comp (FixedPoints.subalgebra K (qA Fdiag) G).val) := by
  haveI : Algebra.Etale K (FixedPoints.subalgebra K (qA Fdiag) G) :=
    etale_of_injective (FixedPoints.subalgebra K (qA Fdiag) G).val Subtype.val_injective
  haveI : Algebra.Etale K (qA Fdiag) := (qX Fdiag).property
  intro p
  obtain ⟨g, hg⟩ := exists_extension Ω (FixedPoints.subalgebra K (qA Fdiag) G).val
    Subtype.val_injective p
  exact ⟨g, hg⟩

omit [IsAlgClosed Ω] in
/-- **Fibres are orbits (constancy direction).**  Any cocone leg of `Fdiag ⋙ fibreFunctor`
identifies two `Ω`-points of `A` that restrict to the same point of `A^G`: by `coreOrbit` they
differ by a group element, and the cocone condition absorbs that group element. -/
theorem qFibre_orbit {s : Limits.Cocone (Fdiag ⋙ fibreFunctor K Ω)}
    (h h' : qA Fdiag →ₐ[K] Ω)
    (hr : h.comp (FixedPoints.subalgebra K (qA Fdiag) G).val
        = h'.comp (FixedPoints.subalgebra K (qA Fdiag) G).val) :
    s.ι.app (SingleObj.star G) h = s.ι.app (SingleObj.star G) h' := by
  classical
  have hagree : ∀ x : qA Fdiag, (∀ g : G, g • x = x) → h x = h' x := by
    intro x hx
    have := AlgHom.congr_fun hr ⟨x, hx⟩
    simpa using this
  obtain ⟨g, hg⟩ := coreOrbit Ω G h h' hagree
  have hcomp : h' = h.comp (qρ Fdiag g⁻¹) := by
    apply AlgHom.ext
    intro x
    rw [hg x, hact g x]
    rfl
  rw [hcomp]
  have hw : (Fdiag ⋙ fibreFunctor K Ω).map (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)
      ≫ s.ι.app (SingleObj.star G) = s.ι.app (SingleObj.star G) := s.w _
  calc s.ι.app (SingleObj.star G) h
      = ((Fdiag ⋙ fibreFunctor K Ω).map (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)
          ≫ s.ι.app (SingleObj.star G)) h := by rw [hw]
    _ = s.ι.app (SingleObj.star G) (h.comp (qρ Fdiag g⁻¹)) := rfl

omit [IsAlgClosed Ω] [Finite G] in
/-- **The mapped cocone leg is restriction to `A^G`.** -/
theorem qFibre_leg (h : qA Fdiag →ₐ[K] Ω) :
    ((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)).ι.app (SingleObj.star G) h
      = h.comp (FixedPoints.subalgebra K (qA Fdiag) G).val := by
  show h.comp (homAlg K (qIncl Fdiag)) = h.comp (FixedPoints.subalgebra K (qA Fdiag) G).val
  rw [homAlg_qIncl]

/-- **The fibre functor preserves the quotient colimit cocone.**  Its image is a colimit in
`FintypeCat`: the fibre `(A^G →ₐ Ω)` is the orbit set of `(A →ₐ Ω)` under `G`. -/
noncomputable def qFibreIsColimit :
    Limits.IsColimit ((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)) where
  desc s := FintypeCat.homMk (fun p =>
    s.ι.app (SingleObj.star G) (qRestrict_surjective Ω Fdiag p).choose)
  fac s j := by
    apply FintypeCat.hom_ext
    intro h
    show s.ι.app (SingleObj.star G)
        (qRestrict_surjective Ω Fdiag
          (((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)).ι.app j h)).choose
      = s.ι.app j h
    apply qFibre_orbit Ω Fdiag hact
    have hspec : (qRestrict_surjective Ω Fdiag
          (((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)).ι.app j h)).choose.comp
            (FixedPoints.subalgebra K (qA Fdiag) G).val
        = ((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)).ι.app j h :=
      (qRestrict_surjective Ω Fdiag _).choose_spec
    rw [hspec]
    exact qFibre_leg Ω Fdiag hact h
  uniq s m hm := by
    apply FintypeCat.hom_ext
    intro p
    obtain ⟨h, hh⟩ := qRestrict_surjective Ω Fdiag p
    have hh' : h.comp (FixedPoints.subalgebra K (qA Fdiag) G).val = p := hh
    have hmstar : ((fibreFunctor K Ω).mapCocone (qCocone Fdiag hact)).ι.app (SingleObj.star G)
        ≫ m = s.ι.app (SingleObj.star G) := hm (SingleObj.star G)
    have key := ConcreteCategory.congr_hom hmstar h
    rw [FintypeCat.comp_apply, qFibre_leg, hh'] at key
    show m p = s.ι.app (SingleObj.star G) (qRestrict_surjective Ω Fdiag p).choose
    refine key.trans ?_
    apply qFibre_orbit Ω Fdiag hact
    have hspec : (qRestrict_surjective Ω Fdiag p).choose.comp
        (FixedPoints.subalgebra K (qA Fdiag) G).val = p :=
      (qRestrict_surjective Ω Fdiag p).choose_spec
    rw [hspec]
    exact hh'

end Colimit

end Quotient

/-- **Quotients by finite groups are preserved by the fibre functor.**  For a finite group `G`, the
fibre functor `F : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat` preserves colimits over `SingleObj G`: the
quotient `op(A^G)` of a `G`-object `op A` has fibre the orbit set of the fibre of `op A`. -/
noncomputable instance preservesQuotients (G : Type u) [Group G] [Finite G] :
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.SingleObj G)
      (fibreFunctor K Ω) where
  preservesColimit {Fdiag} := by
    letI := qAction Fdiag
    haveI : SMulCommClass G K (qA Fdiag) := by
      refine ⟨fun g k x => ?_⟩
      show qρ Fdiag g⁻¹ (k • x) = k • qρ Fdiag g⁻¹ x
      exact _root_.map_smul (qρ Fdiag g⁻¹) k x
    have hact : ∀ (g : G) (x : qA Fdiag), g • x = qρ Fdiag g⁻¹ x := fun _ _ => rfl
    exact preservesColimit_of_preserves_colimit_cocone
      (qCoconeIsColimit Fdiag hact) (qFibreIsColimit Ω Fdiag hact)

/-- **The fibre functor of the Galois category of finite étale `K`-algebras.**  For an algebraically
closed field `Ω ⊇ K`, `fibreFunctor K Ω` satisfies the six Grothendieck fibre-functor conditions: it
preserves terminal objects, pullbacks, finite coproducts, epimorphisms, and quotients by finite
groups, and it reflects isomorphisms.  Together with the `PreGaloisCategory` instance on
`(FiniteEtaleAlgCat K)ᵒᵖ`, this exhibits the finite étale `K`-algebras as a Galois category with a
fibre functor at any geometric point. -/
noncomputable instance : PreGaloisCategory.FiberFunctor (fibreFunctor K Ω) where
  preservesQuotientsByFiniteGroups G := preservesQuotients Ω G

/-- **The finite étale `K`-algebras form a Galois category.**  The opposite category
`(FiniteEtaleAlgCat K)ᵒᵖ` is a `PreGaloisCategory` and admits the fibre functor at the geometric
point `AlgebraicClosure K`, so it is a Grothendieck–Galois category.  Its automorphism group
`Aut (fibreFunctor K (AlgebraicClosure K))` is the étale fundamental group of `Spec K`. -/
noncomputable instance : GaloisCategory (FiniteEtaleAlgCat.{u} K)ᵒᵖ where
  hasFiberFunctor := ⟨fibreFunctor K (AlgebraicClosure K), ⟨inferInstance⟩⟩

end Rigidity.RET.Etale.FiniteEtaleAlgCat
