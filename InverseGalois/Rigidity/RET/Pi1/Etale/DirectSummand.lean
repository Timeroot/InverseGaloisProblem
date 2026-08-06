import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Pushout
import InverseGalois.Rigidity.RET.Pi1.Etale.Equalizer
import Mathlib.CategoryTheory.Galois.Basic

/-!
# Direct summands and the Galois-category structure

A surjection of finite étale `K`-algebras splits: an epimorphism `p : B ⟶ A` exhibits `A` as a
direct summand of `B`, with a complementary factor `C` coming from the idempotent generating the
kernel of `p`.  Dually, every monomorphism in `(FiniteEtaleAlgCat K)ᵒᵖ` splits off a direct summand
(`monoInducesIsoOnDirectSummand_op`).  Together with the terminal object, pullbacks, finite
coproducts, and quotients by finite groups established in the sibling files, this makes
`(FiniteEtaleAlgCat K)ᵒᵖ` a `PreGaloisCategory`.
-/

open CategoryTheory Limits
open scoped TensorProduct

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

/-- **Auxiliary (algebra side).**  An epimorphism `p : B ⟶ A` of finite étale `K`-algebras exhibits
`A` as a direct summand of `B`: there is a complementary factor `C` and a projection `q : B ⟶ C`
making `B` the categorical product of `A` and `C`. -/
private lemma aux {A B : FiniteEtaleAlgCat.{u} K} (p : B ⟶ A) [Epi p] :
    ∃ (C : FiniteEtaleAlgCat.{u} K) (q : B ⟶ C),
      Nonempty (IsLimit (BinaryFan.mk p q)) := by
  -- Two convenient reformulations of morphism equality.
  have homMk_homAlg : ∀ {U V : FiniteEtaleAlgCat.{u} K} (φ0 : (U.obj : Type u) →ₐ[K] (V.obj : Type u)),
      FiniteEtaleAlgCat.homAlg K (ObjectProperty.homMk (CommAlgCat.ofHom φ0) : U ⟶ V) = φ0 := by
    intros; rfl
  have hom_ext' : ∀ {U V : FiniteEtaleAlgCat.{u} K} {f g : U ⟶ V},
      FiniteEtaleAlgCat.homAlg K f = FiniteEtaleAlgCat.homAlg K g → f = g := by
    intro U V f g h
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact h
  -- The underlying algebra map, and the induced `B`-algebra structure on `A`.
  set pA := FiniteEtaleAlgCat.homAlg K p with hpA
  letI : Algebra (B.obj : Type u) (A.obj : Type u) := pA.toRingHom.toAlgebra
  haveI hstK : IsScalarTower K (B.obj : Type u) (A.obj : Type u) :=
    IsScalarTower.of_algebraMap_eq (fun x => (pA.commutes x).symm)
  haveI hMKA : Module.Finite K (A.obj : Type u) := etale_moduleFinite (K := K) (A.obj : Type u)
  haveI hMKB : Module.Finite K (B.obj : Type u) := etale_moduleFinite (K := K) (B.obj : Type u)
  haveI hRT : Algebra.Etale (B.obj : Type u) (A.obj : Type u) :=
    etale_of_isScalarTower (K := K) (B.obj : Type u) (A.obj : Type u)
  -- The tensor square `A ⊗[B] A` is finite étale over `K`.
  haveI hTBA : Algebra.Etale (A.obj : Type u) ((A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u)) :=
    inferInstance
  haveI hTetale : Algebra.Etale K ((A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u)) :=
    Algebra.Etale.comp K (A.obj : Type u) ((A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u))
  set T : FiniteEtaleAlgCat.{u} K :=
    ⟨CommAlgCat.of K ((A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u)), hTetale⟩ with hT_def
  -- The two coprojections `A ⟶ T` agree after precomposition with `p` (scalar move over `B`).
  have hcond :
      (p ≫ (ObjectProperty.homMk (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeLeft :
            (A.obj : Type u) →ₐ[K] (A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u))) : A ⟶ T))
        = (p ≫ (ObjectProperty.homMk (CommAlgCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            (A.obj : Type u) →ₐ[(B.obj : Type u)]
              (A.obj : Type u) ⊗[(B.obj : Type u)] (A.obj : Type u)).restrictScalars K)) : A ⟶ T)) := by
    apply hom_ext'
    rw [FiniteEtaleAlgCat.homAlg_comp, FiniteEtaleAlgCat.homAlg_comp, homMk_homAlg, homMk_homAlg]
    apply AlgHom.ext; intro b
    show (algebraMap (B.obj : Type u) (A.obj : Type u) b) ⊗ₜ[(B.obj : Type u)] (1 : (A.obj : Type u))
        = (1 : (A.obj : Type u)) ⊗ₜ[(B.obj : Type u)] (algebraMap (B.obj : Type u) (A.obj : Type u) b)
    rw [← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
  -- Cancelling the epi `p` yields the tensor-symmetry condition, hence `p` is surjective.
  have hincl := (cancel_epi p).mp hcond
  have htmul : ∀ a : (A.obj : Type u),
      a ⊗ₜ[(B.obj : Type u)] (1 : (A.obj : Type u)) = (1 : (A.obj : Type u)) ⊗ₜ[(B.obj : Type u)] a := by
    intro a
    have h2 := congrArg (FiniteEtaleAlgCat.homAlg K) hincl
    rw [homMk_homAlg, homMk_homAlg] at h2
    exact DFunLike.congr_fun h2 a
  haveI : Algebra.IsEpi (B.obj : Type u) (A.obj : Type u) :=
    (Algebra.isEpi_iff_forall_one_tmul_eq (B.obj : Type u) (A.obj : Type u)).mpr
      (fun a => (htmul a).symm)
  haveI hfin : Module.Finite (B.obj : Type u) (A.obj : Type u) :=
    Module.Finite.of_restrictScalars_finite K (B.obj : Type u) (A.obj : Type u)
  have hsurj : Function.Surjective (algebraMap (B.obj : Type u) (A.obj : Type u)) :=
    Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp inferInstance
  have hsurjpA : Function.Surjective pA := hsurj
  -- The kernel of `p` is an idempotent, finitely generated ideal, hence generated by an idempotent.
  haveI : IsNoetherianRing (B.obj : Type u) := IsNoetherianRing.of_finite K (B.obj : Type u)
  have hidem : IsIdempotentElem (RingHom.ker (algebraMap (B.obj : Type u) (A.obj : Type u))) :=
    (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
  set I : Ideal (B.obj : Type u) := RingHom.ker (algebraMap (B.obj : Type u) (A.obj : Type u))
    with hI_def
  have hIfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨e, he, heI⟩ := (Ideal.isIdempotentElem_iff_of_fg I hIfg).mp hidem
  rw [Ideal.submodule_span_eq] at heI
  -- The complementary idempotent and the complementary quotient `C = B ⧸ (1 - e)`.
  set J : Ideal (B.obj : Type u) := Ideal.span {1 - e} with hJ_def
  haveI hfC : Module.Finite (B.obj : Type u) ((B.obj : Type u) ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (B.obj : Type u) J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (B.obj : Type u) J)
  have hmksurj : Function.Surjective (algebraMap (B.obj : Type u) ((B.obj : Type u) ⧸ J)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  have hkerJ : RingHom.ker (algebraMap (B.obj : Type u) ((B.obj : Type u) ⧸ J)) = J := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.mk_ker
  have hJfg : J.FG := IsNoetherian.noetherian J
  have hidemJideal : IsIdempotentElem J := by
    rw [Ideal.isIdempotentElem_iff_of_fg J hJfg]
    exact ⟨1 - e, he.one_sub, by rw [hJ_def, Ideal.submodule_span_eq]⟩
  haveI hfeC : Algebra.FormallyEtale (B.obj : Type u) ((B.obj : Type u) ⧸ J) :=
    (Algebra.FormallyEtale.iff_of_surjective hmksurj).mpr (by rw [hkerJ]; exact hidemJideal)
  haveI hftC : Algebra.FiniteType (B.obj : Type u) ((B.obj : Type u) ⧸ J) := inferInstance
  haveI hfpC : Algebra.FinitePresentation (B.obj : Type u) ((B.obj : Type u) ⧸ J) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI hetBC : Algebra.Etale (B.obj : Type u) ((B.obj : Type u) ⧸ J) := ⟨hfeC, hfpC⟩
  haveI hetKC : Algebra.Etale K ((B.obj : Type u) ⧸ J) :=
    Algebra.Etale.comp K (B.obj : Type u) ((B.obj : Type u) ⧸ J)
  set CC : FiniteEtaleAlgCat.{u} K :=
    ⟨CommAlgCat.of K ((B.obj : Type u) ⧸ J), hetKC⟩ with hCC_def
  -- Some computations with `e` and the two quotient maps.
  have hpAe : pA e = 0 := by
    have hmem : e ∈ I := by rw [heI]; exact Ideal.mem_span_singleton_self e
    rw [hI_def, RingHom.mem_ker] at hmem
    exact hmem
  have hpA1e : pA (1 - e) = 1 := by rw [map_sub, map_one, hpAe, sub_zero]
  have hmk1e : (Ideal.Quotient.mkₐ K J) (1 - e) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hJ_def]
    exact Ideal.mem_span_singleton_self (1 - e)
  have hmke : (Ideal.Quotient.mkₐ K J) e = 1 := by
    have hee : (1 : (B.obj : Type u)) - (1 - e) = e := by ring
    rw [← hee, map_sub, map_one, hmk1e, sub_zero]
  -- The splitting isomorphism `B ≃ₐ[K] A × C`.
  have hinj : Function.Injective (pA.prod (Ideal.Quotient.mkₐ K J)) := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    simp only [AlgHom.coe_prod, Pi.prod, Prod.mk_eq_zero] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hbI : b ∈ Ideal.span {e} := by rw [← heI, hI_def, RingHom.mem_ker]; exact hb1
    have hbJ : b ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk (R₁ := K)]
      exact hb2
    rw [Ideal.mem_span_singleton'] at hbI
    rw [hJ_def, Ideal.mem_span_singleton'] at hbJ
    obtain ⟨c, hc⟩ := hbI
    obtain ⟨d, hd⟩ := hbJ
    have hbe : b * e = 0 := by
      rw [← hd, mul_assoc, sub_mul, one_mul, he, sub_self, mul_zero]
    have hb1e : b * (1 - e) = 0 := by
      rw [← hc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero]
    have hsplit : b = b * e + b * (1 - e) := by ring
    rw [hbe, hb1e, add_zero] at hsplit
    exact hsplit
  have hsurjφ : Function.Surjective (pA.prod (Ideal.Quotient.mkₐ K J)) := by
    rintro ⟨a, y⟩
    obtain ⟨b1, rfl⟩ := hsurjpA a
    obtain ⟨b2, rfl⟩ := Ideal.Quotient.mkₐ_surjective K J y
    refine ⟨(1 - e) * b1 + e * b2, ?_⟩
    refine Prod.ext ?_ ?_
    · show pA ((1 - e) * b1 + e * b2) = pA b1
      rw [map_add, map_mul, map_mul, hpA1e, hpAe, one_mul, zero_mul, add_zero]
    · show (Ideal.Quotient.mkₐ K J) ((1 - e) * b1 + e * b2) = (Ideal.Quotient.mkₐ K J) b2
      rw [map_add, map_mul, map_mul, hmk1e, hmke, zero_mul, one_mul, zero_add]
  set φ := AlgEquiv.ofBijective (pA.prod (Ideal.Quotient.mkₐ K J)) ⟨hinj, hsurjφ⟩ with hφ_def
  have hφ_apply : ∀ z, φ z = (pA z, (Ideal.Quotient.mkₐ K J) z) := by
    intro z
    rw [hφ_def]
    simp only [AlgEquiv.coe_ofBijective, AlgHom.coe_prod, Pi.prod]
  have hpsA : ∀ w, pA (φ.symm w) = w.1 := by
    intro w
    have h := hφ_apply (φ.symm w)
    rw [φ.apply_symm_apply] at h
    exact (congrArg Prod.fst h).symm
  have hpsC : ∀ w, (Ideal.Quotient.mkₐ K J) (φ.symm w) = w.2 := by
    intro w
    have h := hφ_apply (φ.symm w)
    rw [φ.apply_symm_apply] at h
    exact (congrArg Prod.snd h).symm
  have hfstEq : pA.comp (φ.symm.toAlgHom) = AlgHom.fst K (A.obj : Type u) ((B.obj : Type u) ⧸ J) := by
    apply AlgHom.ext; intro w
    show pA (φ.symm w) = w.1
    exact hpsA w
  have hsndEq : (Ideal.Quotient.mkₐ K J).comp (φ.symm.toAlgHom)
      = AlgHom.snd K (A.obj : Type u) ((B.obj : Type u) ⧸ J) := by
    apply AlgHom.ext; intro w
    show (Ideal.Quotient.mkₐ K J) (φ.symm w) = w.2
    exact hpsC w
  -- Assemble the binary product limit.
  refine ⟨CC, ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K J)), ⟨?_⟩⟩
  refine BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk (CommAlgCat.ofHom
      ((φ.symm.toAlgHom).comp
        ((FiniteEtaleAlgCat.homAlg K s.fst).prod (FiniteEtaleAlgCat.homAlg K s.snd)))))
    (fun s => ?_) (fun s => ?_) (fun s m h1 h2 => ?_)
  · apply hom_ext'
    rw [FiniteEtaleAlgCat.homAlg_comp, homMk_homAlg, ← hpA, ← AlgHom.comp_assoc, hfstEq]
    exact AlgHom.fst_prod _ _
  · apply hom_ext'
    rw [FiniteEtaleAlgCat.homAlg_comp, homMk_homAlg, homMk_homAlg, ← AlgHom.comp_assoc, hsndEq]
    exact AlgHom.snd_prod _ _
  · apply hom_ext'
    rw [homMk_homAlg]
    have h1' : pA.comp (FiniteEtaleAlgCat.homAlg K m) = FiniteEtaleAlgCat.homAlg K s.fst := by
      have hh := congrArg (FiniteEtaleAlgCat.homAlg K) h1
      rw [FiniteEtaleAlgCat.homAlg_comp, ← hpA] at hh
      exact hh
    have h2' : (Ideal.Quotient.mkₐ K J).comp (FiniteEtaleAlgCat.homAlg K m)
        = FiniteEtaleAlgCat.homAlg K s.snd := by
      have hh := congrArg (FiniteEtaleAlgCat.homAlg K) h2
      rw [FiniteEtaleAlgCat.homAlg_comp, homMk_homAlg] at hh
      exact hh
    apply AlgHom.ext; intro x
    have e1 : pA (FiniteEtaleAlgCat.homAlg K m x) = FiniteEtaleAlgCat.homAlg K s.fst x := by
      have := DFunLike.congr_fun h1' x; rwa [AlgHom.comp_apply] at this
    have e2 : (Ideal.Quotient.mkₐ K J) (FiniteEtaleAlgCat.homAlg K m x)
        = FiniteEtaleAlgCat.homAlg K s.snd x := by
      have := DFunLike.congr_fun h2' x; rwa [AlgHom.comp_apply] at this
    have hx : φ (FiniteEtaleAlgCat.homAlg K m x)
        = (FiniteEtaleAlgCat.homAlg K s.fst x, FiniteEtaleAlgCat.homAlg K s.snd x) := by
      rw [hφ_apply, e1, e2]
    show (FiniteEtaleAlgCat.homAlg K m) x
        = φ.symm (FiniteEtaleAlgCat.homAlg K s.fst x, FiniteEtaleAlgCat.homAlg K s.snd x)
    rw [← hx, φ.symm_apply_apply]

/-- **A monomorphism in the Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` splits off a direct summand.**
Every mono `i : X ⟶ Y` fits into a binary coproduct decomposition `Y ≅ X ⊔ Z`, i.e. exhibits `X` as a
direct summand of `Y`.  Dually to `aux`: a surjection of finite étale algebras splits. -/
theorem monoInducesIsoOnDirectSummand_op {X Y : (FiniteEtaleAlgCat.{u} K)ᵒᵖ} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : (FiniteEtaleAlgCat.{u} K)ᵒᵖ) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  obtain ⟨C, q, ⟨hlim⟩⟩ := aux (K := K) i.unop
  refine ⟨Opposite.op C, q.op, ⟨?_⟩⟩
  have hop := BinaryFan.IsLimit.op hlim
  rw [BinaryFan.op_mk] at hop
  rwa [Quiver.Hom.op_unop] at hop

/-- **The category of finite étale `K`-algebras, opposite, is a Galois category** in the sense of
SGA1 (G1)–(G3): it has a terminal object, pullbacks, finite coproducts, quotients by finite groups,
and every monomorphism splits off a direct summand. -/
instance : PreGaloisCategory (FiniteEtaleAlgCat.{u} K)ᵒᵖ where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand i := monoInducesIsoOnDirectSummand_op i

end Rigidity.RET.Etale
