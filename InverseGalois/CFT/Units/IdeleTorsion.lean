/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.TorsionRep
import InverseGalois.CFT.Units.IdeleOrbitTate
import InverseGalois.CFT.Units.IdeleRep

/-!
# The elements of the ideles killed by an integer, place by place

An idele killed by a nonzero integer has every local component killed by it, and in particular has
local valuation zero at every finite place, since the valuation is an integer.  So the finiteness
condition that cuts the ideles out of the product of all the local unit groups is automatic for
those elements, and the elements of the ideles killed by an integer are exactly the elements of the
whole product killed by it: a root of unity at every place, with no restriction at all.

That product is a product of two halves, the infinite places and the finite ones, and each half is
the sections of a family of modules over the set of places of the extension, on which the Galois
group acts with one orbit for each place of the base field.  The general orbit decomposition of the
complete cohomology of such a family therefore applies to each half, and gives the description that
class field theory uses: **in every degree the complete cohomology of the elements of the ideles
killed by a nonzero integer is the product, over the places of the base field, of the complete
cohomology of the decomposition group of a place above it with coefficients in the elements killed
by that integer of the units of the completion there.**

No hypothesis is placed on the Galois group beyond finiteness, and the integer is arbitrary apart
from being nonzero.

## Main definitions

* `InverseGalois.CFT.fullIdeleAutHom`: the Galois action on the product of the local unit groups at
  all places, as a homomorphism.

## Main results

* `InverseGalois.CFT.mem_idele_of_zsmul_eq_zero`: an element of the product of the local unit groups
  killed by a nonzero integer is an idele.
* `InverseGalois.CFT.ideleTorsionIso`: **the elements of the ideles killed by a nonzero integer are
  the elements of the whole product of the local unit groups killed by it.**
* `InverseGalois.CFT.fullIdeleTorsionIso`: those elements split into the infinite places and the
  finite ones.
* `InverseGalois.CFT.adicIdeleTorsionTateEquiv`,
  `InverseGalois.CFT.infiniteIdeleTorsionTateEquiv`: each half is the product over the places of the
  base field of the local contributions.
* `InverseGalois.CFT.ideleTorsionTateEquiv`: **the complete cohomology of the elements of the ideles
  killed by a nonzero integer is the product over the places of the base field of the complete
  cohomology of a decomposition group with coefficients in the elements killed by that integer of
  the units of a completion.**
* `InverseGalois.CFT.isZero_tateModule_ideleTorsion`: those elements have no complete cohomology in
  a degree as soon as no local factor has any.

## Tags

number field, idele, root of unity, decomposition group, Tate cohomology, Shapiro's lemma
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### The action on the whole product of the local unit groups -/

section Full

variable (k K : Type) [Field k] [Field K] [NumberField K] [Algebra k K]

/-- **The Galois action on the product of the local unit groups at all places of a number field, as
a homomorphism.** -/
def fullIdeleAutHom : Gal(K/k) →* AddAut (FullIdele K) :=
  prodAutHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut

@[simp]
theorem fullIdeleAutHom_apply (σ : Gal(K/k)) :
    fullIdeleAutHom k K σ = fullIdeleAut (k := k) σ := rfl

variable {k K}

/-- **An element of the product of the local unit groups killed by a nonzero integer is an idele.**
Its local valuation at a finite place is an integer killed by a nonzero integer, hence zero, so the
finiteness condition holds for the trivial reason that it holds at every place at once. -/
theorem mem_idele_of_zsmul_eq_zero {m : ℤ} (hm : m ≠ 0) {x : FullIdele K} (hx : m • x = 0) :
    x ∈ idele K := by
  rw [mem_idele]
  refine Filter.Eventually.of_forall fun v => ?_
  have h : m • x.2 v = 0 := congrArg (fun y : FullIdele K => y.2 v) hx
  have h2 : m • unitVal (x.2 v) = (0 : ℤ) := by rw [← map_zsmul, h, map_zero]
  exact (smul_eq_zero.1 h2).resolve_left hm

variable (k K)

/-- **The elements of the ideles killed by a nonzero integer are the elements killed by it of the
whole product of the local unit groups**, as representations of the Galois group. -/
def ideleTorsionIso {m : ℤ} (hm : m ≠ 0) :
    torsionRep (ideleAutHom k K) m ≅ torsionRep (fullIdeleAutHom k K) m :=
  torsionSubIso m (fullIdeleAutHom k K) (ideleAutHom k K) (fun g x => coe_ideleAut (k := k) g x)
    fun _ hx => mem_idele_of_zsmul_eq_zero hm hx

/-- **The elements of the product of the local unit groups killed by an integer split into the
infinite places and the finite ones.** -/
def fullIdeleTorsionIso (m : ℤ) :
    torsionRep (fullIdeleAutHom k K) m ≅
      pairRep (torsionRep (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut m)
        (torsionRep (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut m) :=
  torsionProdIso (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut m

end Full

/-! ### The finite places -/

section Finite

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- **The action of the decomposition group of a finite place on the units of the completion
there**, read off from the family of all completions. -/
theorem stabAut_adicUnits_eq {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))}
    (v₀ : ω.orbit) :
    stabAut v₀ (smul_orbit_of_mem_stabilizer v₀)
        (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) :=
  MonoidHom.ext fun g => AddEquiv.ext (stabAut_orbitFamily_adicUnits v₀ g)

variable [Finite Gal(K/k)]
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit) (m : ℤ)

/-- **The complete cohomology of the elements killed by an integer of the finite part of the group
of ideles is the product over the finite places of the base field of the complete cohomology of the
decomposition group of a place above it with coefficients in the elements killed by that integer of
the units of the completion there.** -/
def adicIdeleTorsionTateEquiv (n : ℤ) :
    tateModule (torsionRep (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut m) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) m) n :=
  (tateTorsionEquiv (adicRingFamily (k := k) (K := K)).unitsFamily m v₀
      (H := fun ω => stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
      (fun ω g h => mem_stabilizer_of_smul_orbit (v₀ ω) g h)
      (fun ω g => smul_orbit_of_mem_stabilizer (v₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω => tateTorsionCast (stabAut_adicUnits_eq (v₀ ω)) m n

end Finite

/-! ### The infinite places -/

section Archimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- **The action of the decomposition group of an infinite place on the units of the completion
there**, read off from the family of all completions. -/
theorem stabAut_infiniteUnits_eq {ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K)}
    (w₀ : ω.orbit) :
    stabAut w₀ (smul_orbit_of_mem_stabilizer_infinite w₀)
        (orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
          (R := (w₀ : InfinitePlace K).Completion) :=
  MonoidHom.ext fun g => AddEquiv.ext (stabAut_orbitFamily_infiniteUnits w₀ g)

variable [Finite Gal(K/k)]
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit) (m : ℤ)

/-- **The complete cohomology of the elements killed by an integer of the infinite part of the group
of ideles is the product over the infinite places of the base field of the complete cohomology of
the decomposition group of a place above it with coefficients in the elements killed by that integer
of the units of the completion there.** -/
def infiniteIdeleTorsionTateEquiv (n : ℤ) :
    tateModule (torsionRep (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut m) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) m) n :=
  (tateTorsionEquiv (infiniteRingFamily (k := k) (K := K)).unitsFamily m w₀
      (H := fun ω => stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K))
      (fun ω g h => mem_stabilizer_of_smul_orbit_infinite (w₀ ω) g h)
      (fun ω g => smul_orbit_of_mem_stabilizer_infinite (w₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω => tateTorsionCast (stabAut_infiniteUnits_eq (w₀ ω)) m n

end Archimedean

/-! ### All the places at once -/

section Total

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit) {m : ℤ}

/-- **The complete cohomology of the elements of the ideles killed by a nonzero integer is the
product, over the places of the base field, of the complete cohomology of the decomposition group of
a place above it with coefficients in the elements killed by that integer of the units of the
completion there.**  Being killed by a nonzero integer forces the local valuations to vanish
everywhere, so the finiteness condition defining the ideles is no restriction on such elements, and
the product over all places splits into the infinite half and the finite half, each of which is the
sections of a family of modules over the places of the extension. -/
def ideleTorsionTateEquiv (hm : m ≠ 0) (n : ℤ) :
    tateModule (torsionRep (ideleAutHom k K) m) n ≃+
      (∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) m) n) ×
      (∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) m) n) :=
  (tateMapIso (ideleTorsionIso k K hm) n).toLinearEquiv.toAddEquiv.trans <|
    (tateMapIso (fullIdeleTorsionIso k K m) n).toLinearEquiv.toAddEquiv.trans <|
      (tatePairEquiv _ _ n).trans <|
        (infiniteIdeleTorsionTateEquiv w₀ m n).prodCongr (adicIdeleTorsionTateEquiv v₀ m n)

/-- **The elements of the ideles killed by a nonzero integer have no complete cohomology in a degree
as soon as no local factor has any.** -/
theorem isZero_tateModule_ideleTorsion (hm : m ≠ 0) (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Limits.IsZero (tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) m) n))
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Limits.IsZero (tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) m) n)) :
    Limits.IsZero (tateModule (torsionRep (ideleAutHom k K) m) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), Subsingleton
      ↥(tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) m) n) := fun ω =>
    ModuleCat.isZero_iff_subsingleton.1 (h₁ ω)
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Subsingleton
      ↥(tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) m) n) := fun ω =>
    ModuleCat.isZero_iff_subsingleton.1 (h₂ ω)
  exact (ideleTorsionTateEquiv w₀ v₀ hm n).injective.subsingleton

end Total

end

end InverseGalois.CFT
