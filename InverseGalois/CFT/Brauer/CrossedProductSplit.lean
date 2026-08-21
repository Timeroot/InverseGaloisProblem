import Mathlib
import InverseGalois.CFT.Brauer.CrossedProduct

/-!
# Split crossed products come from coboundaries

Let `L / K` be a finite Galois extension with group `G = Gal(L/K)` and let
`f : G × G → Lˣ` be a multiplicative `2`-cocycle.  Emmy Noether's theorem says that the crossed
product `(L, G, f)` is a matrix algebra over `K` exactly when `f` is a `2`-coboundary.  This file
proves the harder implication: if `CrossedProduct hf` is isomorphic, as a `K`-algebra, to the
endomorphism algebra of a finite-dimensional `K`-vector space (equivalently to a matrix algebra
over `K`), then `f` satisfies `groupCohomology.IsMulCoboundary₂`.  This is the injectivity of the
map `H²(Gal(L/K), Lˣ) → Br(K)`.

The proof is the classical one.  A `K`-algebra isomorphism `e : CrossedProduct hf ≃ₐ[K] End K V`
makes `V` a module over the copy of `L` inside the crossed product, by `c • w = e (incl hf c) w`.
Counting dimensions over `K` gives `finrank K V = finrank K L`, whence `finrank L V = 1`.  Fix
`v : V` nonzero; it is an `L`-basis.  The symbol `u g` acts `g`-semilinearly on `V`, so
`e (single hf g 1) v = h g • v` for a unique scalar `h g : L`, which is nonzero because `u g` has
a left inverse in the crossed product.  Reading the relation `u g * u g' = f (g, g') * u (g g')`
off at `v` turns into `g (h g') * h g = f (g, g') * h (g * g')`, which says precisely that `f` is
the coboundary of `h`.

## Main results

* `InverseGalois.CFT.CrossedProduct.isMulCoboundary₂_of_algEquivEnd`: if the crossed product of a
  `2`-cocycle `f` is `K`-isomorphic to `Module.End K V` for a finite-dimensional `K`-vector space
  `V`, then `f` is a `2`-coboundary.
* `InverseGalois.CFT.CrossedProduct.isMulCoboundary₂_of_algEquivMatrix`: the same conclusion from
  an isomorphism with a matrix algebra over `K`.

-/

namespace InverseGalois.CFT

open groupCohomology

namespace CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ} {hf : IsMulCocycle₂ f}

/-- The symbol `u 1` is the image of the value `f (1, 1)` under the embedding of `L`. -/
theorem single_one_one_eq_incl :
    (single hf 1 1 : CrossedProduct hf) = incl hf ((f (1, 1) : Lˣ) : L) := by
  rw [incl_eq_single]
  exact single_congr (val_mul_inv_val (f := f)).symm

/-- The product of two symbols is the value of the cocycle times the symbol of the product. -/
theorem single_one_mul_single_one (g g' : Gal(L/K)) :
    single hf g 1 * single hf g' 1
      = incl hf ((f (g, g') : Lˣ) : L) * single hf (g * g') 1 := by
  rw [single_mul_single, incl_mul, smul_single, map_one, one_mul, one_mul, mul_one]

/-- Every symbol `u g` has a left inverse up to the nonzero scalar `f (1, 1)`. -/
theorem single_inv_mul_single_one (g : Gal(L/K)) :
    single hf g⁻¹ ((((f (g⁻¹, g))⁻¹ : Lˣ)) : L) * single hf g 1
      = incl hf ((f (1, 1) : Lˣ) : L) := by
  rw [single_mul_single, inv_mul_cancel, ← single_one_one_eq_incl]
  refine single_congr ?_
  rw [map_one, mul_one]
  exact Units.inv_mul _

/-- **Noether's theorem**.  If the crossed product of a multiplicative `2`-cocycle
`f : Gal(L/K) × Gal(L/K) → Lˣ` is isomorphic, as a `K`-algebra, to the endomorphism algebra of a
finite-dimensional `K`-vector space, then `f` is a multiplicative `2`-coboundary. -/
theorem isMulCoboundary₂_of_algEquivEnd [FiniteDimensional K L] [IsGalois K L]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : CrossedProduct hf ≃ₐ[K] Module.End K V) :
    IsMulCoboundary₂ f := by
  -- Transport the copy of `L` inside the crossed product to a scalar action on `V`.
  letI : Module L V :=
    { smul := fun c w => e (incl hf c) w
      one_smul := fun w => by
        show e (incl hf 1) w = w
        rw [map_one, map_one, Module.End.one_apply]
      mul_smul := fun c c' w => by
        show e (incl hf (c * c')) w = e (incl hf c) (e (incl hf c') w)
        rw [map_mul, map_mul, Module.End.mul_apply]
      smul_zero := fun _ => map_zero _
      smul_add := fun _ _ _ => map_add _ _ _
      add_smul := fun c c' w => by
        show e (incl hf (c + c')) w = e (incl hf c) w + e (incl hf c') w
        rw [map_add, map_add, LinearMap.add_apply]
      zero_smul := fun w => by
        show e (incl hf 0) w = 0
        rw [map_zero, map_zero, LinearMap.zero_apply] }
  have hsmul : ∀ (c : L) (w : V), c • w = e (incl hf c) w := fun _ _ => rfl
  haveI : IsScalarTower K L V := by
    refine ⟨fun k c w => ?_⟩
    rw [hsmul, hsmul, Algebra.smul_def k c, map_mul, map_mul, Module.End.mul_apply,
      ← algebraMap_eq, AlgEquiv.commutes, Module.algebraMap_end_apply]
  -- Both sides have `K`-dimension the square of `[L : K]`, so `V` is an `L`-line.
  have hV : Module.finrank K V = Module.finrank K L := by
    have h1 : Module.finrank K (Module.End K V) = Module.finrank K V ^ 2 := by
      rw [Module.finrank_linearMap K K V V, sq]
    have h2 : Module.finrank K (CrossedProduct hf) = Module.finrank K (Module.End K V) :=
      e.toLinearEquiv.finrank_eq
    rw [finrank_eq, IsGalois.card_aut_eq_finrank, h1] at h2
    exact (Nat.pow_left_injective (by norm_num) h2).symm
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have hrank1 : Module.finrank L V = 1 := by
    have htower := Module.finrank_mul_finrank K L V
    rw [hV] at htower
    exact Nat.eq_of_mul_eq_mul_left hpos (htower.trans (mul_one _).symm)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := L) (by rw [hrank1]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hspan : ∀ w : V, ∃ c : L, c • v = w :=
    (finrank_eq_one_iff_of_nonzero' v hv).1 hrank1
  have hinj : ∀ c c' : L, c • v = c' • v → c = c' := by
    intro c c' hcc
    have hz : (c - c') • v = 0 := by rw [sub_smul, hcc, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 hz).resolve_right hv)
  -- The symbol `u g` acts `g`-semilinearly.
  have hsemi : ∀ (g : Gal(L/K)) (c : L) (w : V),
      e (single hf g 1) (c • w) = g c • e (single hf g 1) w := by
    intro g c w
    rw [hsmul, hsmul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      single_mul_incl]
  choose h hh using fun g : Gal(L/K) => hspan (e (single hf g 1) v)
  have hne : ∀ g, h g ≠ 0 := by
    intro g h0
    have h1 : e (single hf g⁻¹ ((((f (g⁻¹, g))⁻¹ : Lˣ)) : L)) (e (single hf g 1) v)
        = ((f (1, 1) : Lˣ) : L) • v := by
      rw [← Module.End.mul_apply, ← map_mul, single_inv_mul_single_one, hsmul]
    rw [← hh g, h0, zero_smul, map_zero] at h1
    exact hv ((smul_eq_zero.1 h1.symm).resolve_left (Units.ne_zero _))
  have key : ∀ g g' : Gal(L/K), g (h g') * h g = ((f (g, g') : Lˣ) : L) * h (g * g') := by
    intro g g'
    refine hinj _ _ ?_
    rw [← smul_smul, hh g, ← hsemi, hh g', ← Module.End.mul_apply, ← map_mul,
      single_one_mul_single_one, map_mul, Module.End.mul_apply, ← hsmul, ← hh (g * g'), smul_smul]
  refine ⟨fun g => Units.mk0 (h g) (hne g), fun g g' => ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff_eq_mul]
  refine Units.ext ?_
  push_cast
  simpa using key g g'

/-- **Noether's theorem**, matrix form.  If the crossed product of a multiplicative `2`-cocycle
`f : Gal(L/K) × Gal(L/K) → Lˣ` is isomorphic, as a `K`-algebra, to a matrix algebra over `K`,
then `f` is a multiplicative `2`-coboundary. -/
theorem isMulCoboundary₂_of_algEquivMatrix [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : CrossedProduct hf ≃ₐ[K] Matrix ι ι K) :
    IsMulCoboundary₂ f :=
  isMulCoboundary₂_of_algEquivEnd (e.trans Matrix.toLinAlgEquiv')

end CrossedProduct

end InverseGalois.CFT
