import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Separable
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure

/-!
# Subalgebras of finite étale algebras

A finite étale `K`-algebra is separable, and any `K`-subalgebra of one (presented as an injective
`K`-algebra hom) is again finite étale.  These are the algebraic facts underlying the closure of
`FiniteEtaleAlgCat K` under equalizers and the direct-summand splitting of surjections.
-/

open Polynomial

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

/-- Two distinct monic irreducible polynomials over a field are coprime. -/
private theorem coprime_of_ne_monic_irred {p q : K[X]} (hp : p.Monic) (hpi : Irreducible p)
    (hq : q.Monic) (hqi : Irreducible q) (hne : p ≠ q) : IsCoprime p q := by
  rw [hpi.coprime_iff_not_dvd]
  intro hdvd
  exact hne (eq_of_monic_of_associated hp hq (hpi.associated_of_dvd hqi hdvd))

/-- A finite étale `K`-algebra is a separable `K`-algebra (every element is separable). -/
theorem etale_isSeparable (A : Type u) [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    Algebra.IsSeparable K A := by
  classical
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  haveI : Fintype I := Fintype.ofFinite I
  haveI hfin : ∀ i, Module.Finite K (Ai i) := fun i => (hAi i).1
  haveI hsep : ∀ i, Algebra.IsSeparable K (Ai i) := fun i => (hAi i).2
  -- It suffices to show the product `∀ i, Ai i` is separable, then transport across `e`.
  haveI hpi : Algebra.IsSeparable K (∀ i, Ai i) := by
    refine ⟨fun y => ?_⟩
    show (minpoly K y).Separable
    have hInt : ∀ i, IsIntegral K (y i) := fun i => IsIntegral.of_finite (R := K) (y i)
    -- The finset of distinct minimal polynomials of the components.
    set T : Finset K[X] := Finset.univ.image (fun i => minpoly K (y i)) with hT
    -- The product over `T` is separable (distinct monic irreducibles are coprime).
    have hPsep : (∏ p ∈ T, p).Separable := by
      apply separable_prod'
      · intro p hp q hq hpq
        simp only [hT, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
        obtain ⟨i, rfl⟩ := hp
        obtain ⟨j, rfl⟩ := hq
        exact coprime_of_ne_monic_irred (minpoly.monic (hInt i)) (minpoly.irreducible (hInt i))
          (minpoly.monic (hInt j)) (minpoly.irreducible (hInt j)) hpq
      · intro p hp
        simp only [hT, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨i, rfl⟩ := hp
        exact Algebra.IsSeparable.isSeparable K (y i)
    -- `minpoly K y` divides the product because it vanishes at `y`.
    have haeval : (aeval y) (∏ p ∈ T, p) = 0 := by
      rw [aeval_pi_apply]
      funext j
      show (aeval (y j)) (∏ p ∈ T, p) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (minpoly.aeval K (y j))
    exact hPsep.of_dvd (minpoly.dvd K y haeval)
  exact AlgEquiv.Algebra.isSeparable e.symm

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-- A `K`-subalgebra of a finite étale `K`-algebra (given as an injective `K`-algebra hom) is
finite étale. -/
theorem etale_of_injective {A S : Type u} [CommRing A] [Algebra K A] [CommRing S] [Algebra K S]
    (ι : S →ₐ[K] A) (hι : Function.Injective ι) [Algebra.Etale K A] :
    Algebra.Etale K S := by
  haveI : Algebra.IsSeparable K A := etale_isSeparable A
  haveI : Module.Finite K A := etale_moduleFinite A
  -- `S` is separable: minimal polynomials are preserved by the injection.
  haveI : Algebra.IsSeparable K S := by
    refine ⟨fun x => ?_⟩
    show (minpoly K x).Separable
    rw [← minpoly.algHom_eq ι hι x]
    exact Algebra.IsSeparable.isSeparable K (ι x)
  -- `S` is module-finite: it embeds `K`-linearly into the finite module `A`.
  haveI : Module.Finite K S := Module.Finite.of_injective ι.toLinearMap hι
  -- `S` is reduced: `A` is reduced (a product of fields) and `S` embeds into `A`.
  haveI : IsReduced A := by
    obtain ⟨I, _, Ai, _, _, e, _⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
    haveI : IsReduced (∀ i, Ai i) :=
      ⟨fun x hx => funext fun i => by
        show x i = 0
        exact (hx.map (Pi.evalRingHom (fun i => Ai i) i)).eq_zero⟩
    exact isReduced_of_injective e e.injective
  haveI : IsReduced S := isReduced_of_injective ι hι
  -- `S` is Artinian: it is module-finite over the Artinian ring `K`.
  haveI : IsArtinianRing S := IsArtinianRing.of_finite K S
  -- Decompose `S` as a product of its residue fields and assemble étaleness.
  refine (Algebra.Etale.iff_exists_algEquiv_prod K S).mpr
    ⟨MaximalSpectrum S, inferInstance, fun J => S ⧸ J.asIdeal, inferInstance, inferInstance,
      (IsArtinianRing.equivPi S).restrictScalars K, ?_⟩
  intro J
  refine ⟨Module.Finite.of_surjective (Ideal.Quotient.mkₐ K J.asIdeal).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K J.asIdeal), ?_⟩
  refine ⟨fun z => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective K J.asIdeal z
  show (minpoly K _).Separable
  have hz : (aeval (Ideal.Quotient.mkₐ K J.asIdeal s)) (minpoly K s) = 0 := by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  exact Polynomial.Separable.of_dvd (Algebra.IsSeparable.isSeparable K s) (minpoly.dvd K _ hz)

end Rigidity.RET.Etale
