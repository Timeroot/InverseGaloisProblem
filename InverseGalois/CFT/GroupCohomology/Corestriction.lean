import Mathlib

/-!
# Corestriction (transfer) in group cohomology

Let `k` be a commutative ring, `G` a group, `S ≤ G` a subgroup of finite index and `A` a
`k`-linear `G`-representation. This file constructs the corestriction (transfer) map
`cor : Hⁿ(S, Res A) ⟶ Hⁿ(G, A)` in every degree, together with a restriction map going the
other way, and proves the fundamental relation `res ≫ cor = [G : S] • id`.

The construction is the conceptual one, via Shapiro's lemma. The coinduction functor
`Coind_S^G : Rep k S ⥤ Rep k G` is right adjoint to restriction, so there is a unit morphism
`η : A ⟶ Coind_S^G (Res A)`. When `S` has finite index there is also a *trace* morphism
`ε : Coind_S^G (Res A) ⟶ A`, given by summing `a ↦ A.ρ a (f a⁻¹)` over the coset space `G ⧸ S`,
and `η ≫ ε` is multiplication by the index `[G : S]`. Composing the maps induced on cohomology
with Shapiro's isomorphism `Hⁿ(G, Coind_S^G (Res A)) ≅ Hⁿ(S, Res A)` produces `cor` and `res`.

## Main results

* `InverseGalois.CFT.coindTrace`: the trace morphism `Coind_S^G (Res A) ⟶ A` attached to a
  finite-index subgroup.
* `InverseGalois.CFT.coindUnit_comp_coindTrace`: the composite of the adjunction unit with the
  trace morphism is multiplication by the index.
* `InverseGalois.CFT.cor`: the corestriction `Hⁿ(S, Res A) ⟶ Hⁿ(G, A)`.
* `InverseGalois.CFT.res`: the restriction `Hⁿ(G, A) ⟶ Hⁿ(S, Res A)` transported through
  Shapiro's isomorphism.
* `InverseGalois.CFT.res_comp_cor`: the fundamental relation `res ≫ cor = [G : S] • id`.
* `InverseGalois.CFT.map_subtype_id_eq`: the restriction map of `groupCohomology.map` factors as
  the unit followed by the Shapiro comparison `Hⁿ(G, Coind_S^G (Res A)) ⟶ Hⁿ(S, Res A)` induced
  by the adjunction counit.
* `InverseGalois.CFT.natCard_nsmul_eq_zero`: for a finite group `G` and `n > 0`, every element of
  `Hⁿ(G, A)` is killed by `|G|`.
* `InverseGalois.CFT.eq_zero_of_res_eq_zero_of_prime_pow`: if `p` is a prime not dividing
  `[G : S]`, then restriction is injective on the `p`-primary part of `Hⁿ(G, A)`.
* `InverseGalois.CFT.eq_zero_of_isUnit_natCard`: for a finite group `G` whose order is invertible
  in `k`, the higher cohomology of every `k`-linear `G`-representation vanishes.
* `InverseGalois.CFT.isMulCoboundary₂_pow_natCard`: the multiplicative `H²` form — for a finite
  group `Γ` acting on a commutative group `M`, the `|Γ|`-th power of a multiplicative `2`-cocycle
  is a multiplicative `2`-coboundary.

-/

universe u

open CategoryTheory Rep groupCohomology

namespace InverseGalois.CFT

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k G)

section Trace

/-- The `G`-representation coinduced from the restriction of `A` to a subgroup `S ≤ G`. Its
underlying module consists of the functions `f : G → A` with `f (s * g) = A.ρ s (f g)` for
`s ∈ S`. -/
noncomputable abbrev coindRes : Rep k G := coind S.subtype ((Action.res _ S.subtype).obj A)

/-- The `k`-linear map sending a vector `f` of the coinduced representation to
`A.ρ a (f a⁻¹)`. This depends only on the coset `a • S`. -/
noncomputable def coindTraceAux (a : G) : (coindRes S A) →ₗ[k] A where
  toFun f := A.ρ a (f.1 a⁻¹)
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The auxiliary evaluation maps `coindTraceAux` depend only on the left coset of the
group element. -/
theorem coindTraceAux_congr (a b : G) (h : a⁻¹ * b ∈ S) :
    coindTraceAux S A a = coindTraceAux S A b := by
  ext f
  have hf : f.1 ((a⁻¹ * b)⁻¹ * a⁻¹) = A.ρ (a⁻¹ * b)⁻¹ (f.1 a⁻¹) :=
    f.2 ⟨(a⁻¹ * b)⁻¹, S.inv_mem h⟩ a⁻¹
  simp only [coindTraceAux, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show b = a * (a⁻¹ * b) by group, show (a * (a⁻¹ * b))⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ by group, hf]
  simp [← Module.End.mul_apply, ← map_mul]

/-- The evaluation map `coindTraceAux`, descended to the coset space `G ⧸ S`. -/
noncomputable def coindTraceQuot (q : G ⧸ S) : (coindRes S A) →ₗ[k] A :=
  Quotient.liftOn' q (coindTraceAux S A) fun _ _ hab =>
    coindTraceAux_congr S A _ _ (QuotientGroup.leftRel_apply.mp hab)

/-- `coindTraceQuot` evaluated at the class of `a : G` is `coindTraceAux` at `a`. -/
@[simp]
theorem coindTraceQuot_mk (a : G) :
    coindTraceQuot S A (QuotientGroup.mk a) = coindTraceAux S A a := rfl

variable [S.FiniteIndex]

/-- The underlying `k`-linear map of the trace morphism: the sum of the evaluation maps
`coindTraceQuot` over the coset space `G ⧸ S`. -/
noncomputable def coindTraceLinear : (coindRes S A) →ₗ[k] A :=
  letI := S.fintypeQuotientOfFiniteIndex
  ∑ q : G ⧸ S, coindTraceQuot S A q

/-- The trace map is the sum over `G ⧸ S` of the coset evaluation maps. -/
theorem coindTraceLinear_apply (f : coindRes S A) :
    letI := S.fintypeQuotientOfFiniteIndex
    coindTraceLinear S A f = ∑ q : G ⧸ S, coindTraceQuot S A q f := by
  letI := S.fintypeQuotientOfFiniteIndex
  simp [coindTraceLinear]

/-- The trace map is `G`-equivariant. -/
theorem coindTraceLinear_comm (g : G) (f : coindRes S A) :
    coindTraceLinear S A ((coindRes S A).ρ g f) = A.ρ g (coindTraceLinear S A f) := by
  letI := S.fintypeQuotientOfFiniteIndex
  rw [coindTraceLinear_apply, coindTraceLinear_apply, map_sum]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ ?_).symm
  intro q
  induction q using Quotient.inductionOn' with
  | h a =>
    show A.ρ g (coindTraceAux S A a f) = coindTraceQuot S A (g • (QuotientGroup.mk a)) _
    rw [show g • (QuotientGroup.mk a : G ⧸ S) = QuotientGroup.mk (g * a) from rfl]
    simp only [coindTraceQuot_mk, coindTraceAux, LinearMap.coe_mk, AddHom.coe_mk]
    show A.ρ g (A.ρ a (f.1 a⁻¹)) = A.ρ (g * a) (f.1 ((g * a)⁻¹ * g))
    rw [show (g * a)⁻¹ * g = a⁻¹ by group]
    simp [← Module.End.mul_apply, ← map_mul]

/-- The trace morphism `Coind_S^G (Res A) ⟶ A` attached to a finite-index subgroup `S ≤ G`,
given by summing `a ↦ A.ρ a (f a⁻¹)` over the coset space `G ⧸ S`. -/
noncomputable def coindTrace : coindRes S A ⟶ A where
  hom := ModuleCat.ofHom (coindTraceLinear S A)
  comm g := by
    ext f
    exact coindTraceLinear_comm S A g f

/-- The unit of the restriction–coinduction adjunction at `A`, sending `x : A` to the function
`g ↦ A.ρ g x`. -/
noncomputable abbrev coindUnit : A ⟶ coindRes S A :=
  (Rep.resCoindAdjunction k S.subtype).unit.app A

/-- The composite of the adjunction unit with the trace morphism is multiplication by the
index `[G : S]`. -/
theorem coindUnit_comp_coindTrace :
    coindUnit S A ≫ coindTrace S A = (S.index : ℕ) • 𝟙 A := by
  letI := S.fintypeQuotientOfFiniteIndex
  ext x
  show coindTraceLinear S A ((coindUnit S A).hom x) = _
  rw [coindTraceLinear_apply]
  have hq : ∀ q : G ⧸ S, coindTraceQuot S A q ((coindUnit S A).hom x) = x := by
    intro q
    induction q using Quotient.inductionOn' with
    | h a =>
      show coindTraceAux S A a _ = x
      simp only [coindTraceAux, LinearMap.coe_mk, AddHom.coe_mk]
      rw [show (((coindUnit S A).hom x).1 a⁻¹) = A.ρ a⁻¹ x by simp [coindUnit]]
      simp [← Module.End.mul_apply, ← map_mul]
  rw [Finset.sum_congr rfl fun q _ => hq q]
  simp [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.index]

end Trace

section Cohomology

/-- The functor `A ↦ Hⁿ(G, A)` is additive, being the composite of the additive functor of
inhomogeneous cochains with the homology functor. -/
instance groupCohomologyFunctor_additive (n : ℕ) : (groupCohomology.functor k G n).Additive := by
  show (groupCohomology.cochainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).Additive
  infer_instance

variable [S.FiniteIndex]

/-- The corestriction (transfer) map `Hⁿ(S, Res A) ⟶ Hⁿ(G, A)` attached to a subgroup `S ≤ G`
of finite index: Shapiro's isomorphism followed by the map induced by the trace morphism. -/
noncomputable def cor (n : ℕ) :
    groupCohomology ((Action.res _ S.subtype).obj A) n ⟶ groupCohomology A n :=
  (groupCohomology.coindIso ((Action.res _ S.subtype).obj A) n).inv ≫
    (groupCohomology.functor k G n).map (coindTrace S A)

/-- The restriction map `Hⁿ(G, A) ⟶ Hⁿ(S, Res A)`, obtained from the adjunction unit followed by
Shapiro's isomorphism. -/
noncomputable def res (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology ((Action.res _ S.subtype).obj A) n :=
  (groupCohomology.functor k G n).map (coindUnit S A) ≫
    (groupCohomology.coindIso ((Action.res _ S.subtype).obj A) n).hom

/-- The fundamental relation between corestriction and restriction: their composite is
multiplication by the index `[G : S]`. -/
theorem res_comp_cor (n : ℕ) :
    res S A n ≫ cor S A n = (S.index : ℕ) • 𝟙 (groupCohomology A n) := by
  rw [res, cor, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    coindUnit_comp_coindTrace, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

omit [S.FiniteIndex] in
/-- The restriction map of `groupCohomology.map` along the inclusion `S ≤ G` factors as the map
induced by the adjunction unit followed by the map induced by the adjunction counit. -/
theorem map_subtype_id_eq (n : ℕ) :
    groupCohomology.map S.subtype (𝟙 ((Action.res _ S.subtype).obj A)) n =
      (groupCohomology.functor k G n).map (coindUnit S A) ≫
        groupCohomology.map S.subtype
          ((Rep.resCoindAdjunction k S.subtype).counit.app
            ((Action.res _ S.subtype).obj A)) n := by
  have h := groupCohomology.map_comp (MonoidHom.id G) S.subtype (coindUnit S A)
    ((Rep.resCoindAdjunction k S.subtype).counit.app ((Action.res _ S.subtype).obj A)) n
  rw [Adjunction.left_triangle_components] at h
  exact h

/-- An element of `Hⁿ(G, A)` killed by restriction to `S` is killed by the index `[G : S]`. -/
theorem index_nsmul_eq_zero_of_res_eq_zero (n : ℕ) (x : groupCohomology A n)
    (hx : res S A n x = 0) : S.index • x = 0 := by
  have h := res_comp_cor S A n
  have h' := congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f.hom x) h
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  rw [show (res S A n).hom x = 0 from hx] at h'
  simpa using h'.symm

end Cohomology

section Torsion

/-- An element of an additive commutative group killed by two coprime natural numbers
is zero. -/
theorem eq_zero_of_coprime_nsmul {M : Type*} [AddCommGroup M] {a b : ℕ} (h : Nat.Coprime a b)
    {x : M} (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) :=
    Int.isCoprime_iff_nat_coprime.2 (by simpa using h)
  have hx : ((u * a + v * b : ℤ)) • x = x := by rw [huv, one_zsmul]
  rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ha, hb] at hx
  simpa using hx.symm

variable [S.FiniteIndex]

/-- Restriction to a subgroup `S ≤ G` is injective on the elements of `Hⁿ(G, A)` killed by some
natural number coprime to the index `[G : S]`. -/
theorem eq_zero_of_res_eq_zero {n m : ℕ} (hm : Nat.Coprime S.index m)
    {x : groupCohomology A n} (hx : m • x = 0) (h : res S A n x = 0) : x = 0 :=
  eq_zero_of_coprime_nsmul hm (index_nsmul_eq_zero_of_res_eq_zero S A n x h) hx

/-- If `p` is a prime not dividing the index `[G : S]`, then restriction to `S` is injective on
the `p`-primary part of `Hⁿ(G, A)`. -/
theorem eq_zero_of_res_eq_zero_of_prime_pow {p : ℕ} (hp : p.Prime) (hdvd : ¬ p ∣ S.index)
    {n e : ℕ} {x : groupCohomology A n} (hx : p ^ e • x = 0) (h : res S A n x = 0) : x = 0 :=
  eq_zero_of_res_eq_zero S A
    (Nat.Coprime.pow_right e (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).2 hdvd))) hx h

end Torsion

section Finite

variable [Finite G]

/-- For a finite group `G` and `n > 0`, every element of `Hⁿ(G, A)` is killed by the order
of `G`. -/
theorem natCard_nsmul_eq_zero (n : ℕ) (x : groupCohomology A (n + 1)) : Nat.card G • x = 0 := by
  have hz : Limits.IsZero (groupCohomology
      ((Action.res _ (⊥ : Subgroup G).subtype).obj A) (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton _ _
  have h := res_comp_cor (⊥ : Subgroup G) A (n + 1)
  rw [hz.eq_of_tgt (res (⊥ : Subgroup G) A (n + 1)) 0, Limits.zero_comp,
    Subgroup.index_bot] at h
  have h' := congrArg
    (fun f : groupCohomology A (n + 1) ⟶ groupCohomology A (n + 1) => f.hom x) h
  simpa using h'.symm

/-- If the order of a finite group `G` is invertible in `k`, then the higher cohomology of every
`k`-linear `G`-representation vanishes. -/
theorem eq_zero_of_isUnit_natCard (hk : IsUnit (Nat.card G : k)) (n : ℕ)
    (x : groupCohomology A (n + 1)) : x = 0 := by
  obtain ⟨u, hu⟩ := hk
  have h : (Nat.card G : k) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact natCard_nsmul_eq_zero A n x
  have h' := congrArg (fun y => (↑u⁻¹ : k) • y) h
  simpa [smul_smul, ← hu] using h'

/-- If the order of a finite group `G` is invertible in `k`, then `Hⁿ⁺¹(G, A)` is a
subsingleton. -/
theorem subsingleton_of_isUnit_natCard (hk : IsUnit (Nat.card G : k)) (n : ℕ) :
    Subsingleton (groupCohomology A (n + 1)) :=
  ⟨fun x y => by
    rw [eq_zero_of_isUnit_natCard A hk n x, eq_zero_of_isUnit_natCard A hk n y]⟩

end Finite

section MulH2

/-- The multiplicative form of the statement that `H²(Γ, M)` is killed by `|Γ|`: for a finite
group `Γ` acting on a commutative group `M`, the `|Γ|`-th power of a multiplicative `2`-cocycle
is a multiplicative `2`-coboundary. -/
theorem isMulCoboundary₂_pow_natCard {Γ M : Type} [Group Γ] [Finite Γ] [CommGroup M]
    [MulDistribMulAction Γ M] {f : Γ × Γ → M} (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ (fun p : Γ × Γ => f p ^ Nat.card Γ) := by
  set B := Rep.ofMulDistribMulAction Γ M with hB
  set x : cocycles₂ B := cocyclesOfIsMulCocycle₂ hf with hx
  have h0 : Nat.card Γ • (H2π B x) = 0 := natCard_nsmul_eq_zero B 1 (H2π B x)
  rw [← map_nsmul] at h0
  exact isMulCoboundary₂_of_mem_coboundaries₂ (M := M) _
    ((H2π_eq_zero_iff (Nat.card Γ • x)).1 h0)

end MulH2

end InverseGalois.CFT
