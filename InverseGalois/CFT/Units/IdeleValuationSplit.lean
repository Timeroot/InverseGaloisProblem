/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyConst
import InverseGalois.CFT.Tate.FamilyTrunc
import InverseGalois.CFT.Tate.Isogeny
import InverseGalois.CFT.TateCohomology.TensorPExact
import InverseGalois.CFT.Units.IdeleTorsion
import InverseGalois.CFT.Units.InvariantUniformizer

/-!
# The ideles inside the product of all the local unit groups

The ideles are the elements of the product of the local unit groups whose valuation vanishes at all
but finitely many finite places, so the quotient of the whole product by the ideles is measured by
the vector of local valuations.  That vector is a section of the family with a copy of the integers
at every finite place, and it is carried along by the Galois action, an automorphism preserving the
valuation while moving the place.

The vector of valuations has a section: raising a chosen local unit at each place to the given power
produces an element of the product with prescribed valuations, and the choice can be made
Galois invariantly and to consist of uniformizers at all but finitely many places.  So the vector of
valuations of an element of the product may be subtracted off, up to finitely many places, and the
result is an idele.

## Main definitions

* `InverseGalois.CFT.placeIntRep`: **the representation on the vectors of integers indexed by the
  finite places.**
* `InverseGalois.CFT.fullIdeleVal`: **the vector of local valuations.**
* `InverseGalois.CFT.valSection`: **a right inverse of it**, built from a chosen local unit at each
  place.
* `InverseGalois.CFT.fullIdeleRep`, `InverseGalois.CFT.ideleDefectRep`: the product of all the local
  unit groups and its quotient by the ideles, as representations.
* `InverseGalois.CFT.ideleFullShortComplex`: the ideles, the whole product and the quotient,
  assembled into a short complex.

## Main results

* `InverseGalois.CFT.fullIdeleVal_equivariant`, `InverseGalois.CFT.valSection_equivariant`: **both
  maps are equivariant**, the second one for a Galois invariant choice of local units.
* `InverseGalois.CFT.sub_valSection_mem_idele`: **subtracting off the vector of valuations leaves an
  idele.**
* `InverseGalois.CFT.ideleFullShortComplex_shortExact`: **the ideles, the whole product and the
  quotient form a short exact sequence of representations.**
* `InverseGalois.CFT.injective_modNsmulHom_ideleToFullIdele`: **the inclusion of the ideles stays
  injective modulo a nonzero integer.**

## Tags

number field, idele, valuation, restricted product, short exact sequence, permutation module
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

noncomputable section

/-! ### The vectors of local valuations -/

section Val

variable {K : Type} [Field K] [NumberField K]

/-- **The vector of local valuations** of an element of the product of the local unit groups. -/
def fullIdeleVal : FullIdele K →+ (HeightOneSpectrum (𝓞 K) → ℤ) where
  toFun a v := unitVal (a.2 v)
  map_zero' := funext fun _ => _root_.map_zero _
  map_add' _ _ := funext fun _ => _root_.map_add _ _ _

theorem fullIdeleVal_apply (a : FullIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    fullIdeleVal a v = unitVal (a.2 v) := rfl

variable (s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ)

/-- **A right inverse of the vector of local valuations**, up to the valuations of the chosen local
units: the element of the product of the local unit groups with the given power of the chosen unit
at each finite place and nothing at the infinite ones. -/
def valSection : (HeightOneSpectrum (𝓞 K) → ℤ) →+ FullIdele K where
  toFun n := (0, fun v => n v • s v)
  map_zero' := Prod.ext rfl (funext fun v => zero_zsmul (s v))
  map_add' n m := Prod.ext (add_zero (0 : ∀ w : InfinitePlace K, Additive w.Completionˣ)).symm
    (funext fun v => add_zsmul (s v) (n v) (m v))

theorem valSection_apply_snd (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) :
    (valSection s n).2 v = n v • s v := rfl

theorem unitVal_valSection (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) :
    unitVal ((valSection s n).2 v) = n v * unitVal (s v) := by
  rw [valSection_apply_snd, _root_.map_zsmul, smul_eq_mul]

end Val

/-! ### The representation on the vectors of integers -/

section Rep

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The family with a copy of the integers at every finite place, the Galois group permuting the
places. -/
abbrev placeIntFamily : FamilyAction (fun _ : HeightOneSpectrum (𝓞 K) => ℤ) Gal(K/k) :=
  constFamily (HeightOneSpectrum (𝓞 K)) ℤ Gal(K/k)

/-- **The representation of the Galois group on the vectors of integers indexed by the finite
places.** -/
abbrev placeIntRep : Rep ℤ Gal(K/k) := orbitSectionsRep (placeIntFamily k K)

variable {k K}

omit [NumberField k] in
/-- **The vector of local valuations is equivariant**: an automorphism preserves the valuation while
moving the place. -/
theorem fullIdeleVal_equivariant (g : Gal(K/k)) (a : FullIdele K) :
    fullIdeleVal (fullIdeleAut (k := k) g a)
      = (placeIntFamily k K).familyAut g (fullIdeleVal a) := by
  funext v
  rw [constFamily_familyAut_apply]
  have h := unitVal_fullIdeleAut (k := k) g a (g⁻¹ • v)
  rwa [smul_inv_smul] at h

variable {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}

omit [NumberField k] in
/-- **A Galois invariant choice of local units makes the right inverse equivariant.** -/
theorem valSection_equivariant
    (hs : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s)
    (g : Gal(K/k)) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    fullIdeleAut (k := k) g (valSection s n)
      = valSection s ((placeIntFamily k K).familyAut g n) := by
  refine Prod.ext (_root_.map_zero _) ?_
  exact (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut_zsmul_of_familyAut_eq (hs g) n

end Rep

/-! ### Correcting an element of the product into an idele -/

section Correct

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}

/-- **Subtracting off the vector of valuations leaves an idele**: at every place carrying a chosen
uniformizer the valuation of the difference vanishes, and the other places are finite in number. -/
theorem sub_valSection_mem_idele (hs : ∀ v ∈ fixedUniformizerPlaces k K, unitVal (s v) = 1)
    (a : FullIdele K) : a - valSection s (fullIdeleVal a) ∈ idele K := by
  rw [mem_idele, Filter.eventually_cofinite]
  refine (finite_compl_fixedUniformizerPlaces k K).subset fun v hv hvmem => hv ?_
  show unitVal (a.2 v - (valSection s (fullIdeleVal a)).2 v) = 0
  rw [_root_.map_sub, unitVal_valSection, hs v hvmem, mul_one, fullIdeleVal_apply, sub_self]

omit [NumberField k] [Algebra k K] in
/-- The vector of valuations of an idele has finite support. -/
theorem fullIdeleVal_mem_finsuppSections (a : ↥(idele K)) :
    fullIdeleVal (a : FullIdele K) ∈ finsuppSections fun _ : HeightOneSpectrum (𝓞 K) => ℤ :=
  Filter.eventually_cofinite.1 a.2

omit [NumberField k] [Algebra k K] in
/-- A vector of integers of finite support gives an idele. -/
theorem valSection_mem_idele {n : HeightOneSpectrum (𝓞 K) → ℤ}
    (hn : n ∈ finsuppSections fun _ : HeightOneSpectrum (𝓞 K) => ℤ) :
    valSection s n ∈ idele K := by
  rw [mem_idele, Filter.eventually_cofinite]
  refine (mem_finsuppSections.1 hn).subset fun v hv hc => hv ?_
  rw [unitVal_valSection, hc, zero_mul]

end Correct

/-! ### The short exact sequence -/

section SES

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The representation of the Galois group on the product of all the local unit groups. -/
abbrev fullIdeleRep : Rep ℤ Gal(K/k) := repOfAddAut (fullIdeleAutHom k K)

/-- **The quotient of the product of all the local unit groups by the ideles.** -/
abbrev IdeleDefect : Type := FullIdele K ⧸ idele K

variable {k K}

omit [NumberField k] in
/-- The ideles are carried onto themselves by a Galois automorphism. -/
theorem map_idele_fullIdeleAut (g : Gal(K/k)) :
    (idele K).map (fullIdeleAut (k := k) g : FullIdele K →+ FullIdele K) = idele K := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact fullIdeleAut_mem_idele g hy
  · refine ⟨(fullIdeleAut (k := k) g).symm x, ?_, (fullIdeleAut (k := k) g).apply_symm_apply x⟩
    rw [fullIdeleAut_symm]
    exact fullIdeleAut_mem_idele g⁻¹ hx

variable (k K)

omit [NumberField k] in
/-- **The Galois action on the quotient of the product of all the local unit groups by the
ideles.** -/
def ideleDefectAutHom : Gal(K/k) →* AddAut (IdeleDefect K) where
  toFun g := quotAut (fullIdeleAut (k := k) g) (idele K) (map_idele_fullIdeleAut g)
  map_one' := AddEquiv.ext fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    show QuotientAddGroup.mk (fullIdeleAut (k := k) (1 : Gal(K/k)) a) = QuotientAddGroup.mk a
    rw [fullIdeleAut_one]
  map_mul' g h := AddEquiv.ext fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    show QuotientAddGroup.mk (fullIdeleAut (k := k) (g * h) a)
      = QuotientAddGroup.mk (fullIdeleAut (k := k) g (fullIdeleAut (k := k) h a))
    rw [fullIdeleAut_mul]

/-- The representation of the Galois group on the quotient of the product of all the local unit
groups by the ideles. -/
abbrev ideleDefectRep : Rep ℤ Gal(K/k) := repOfAddAut (ideleDefectAutHom k K)

/-- The inclusion of the ideles in the product of all the local unit groups, as a map of
representations. -/
def ideleToFullIdele : ideleRep k K ⟶ fullIdeleRep k K where
  hom := ModuleCat.ofHom (idele K).subtype.toIntLinearMap
  comm _ := by ext _; rfl

/-- The passage to the quotient by the ideles, as a map of representations. -/
def fullIdeleToDefect : fullIdeleRep k K ⟶ ideleDefectRep k K where
  hom := ModuleCat.ofHom (QuotientAddGroup.mk' (idele K)).toIntLinearMap
  comm _ := by ext _; rfl

/-- The ideles, the product of all the local unit groups and the quotient of the one by the other,
assembled into a short complex of representations of the Galois group. -/
def ideleFullShortComplex : ShortComplex (Rep ℤ Gal(K/k)) where
  X₁ := ideleRep k K
  X₂ := fullIdeleRep k K
  X₃ := ideleDefectRep k K
  f := ideleToFullIdele k K
  g := fullIdeleToDefect k K
  zero := by
    ext a
    exact (QuotientAddGroup.eq_zero_iff _).2 a.2

omit [NumberField k] in
/-- **The ideles, the product of all the local unit groups and the quotient of the one by the other
form a short exact sequence of representations of the Galois group.** -/
theorem ideleFullShortComplex_shortExact : (ideleFullShortComplex k K).ShortExact where
  exact := (forget₂ _ (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
      ⟨(⟨x, (QuotientAddGroup.eq_zero_iff _).1 hx⟩ : ↥(idele K)), rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (Rep.epi_iff_surjective _).2 QuotientAddGroup.mk_surjective

omit [NumberField k] in
/-- **The inclusion of the ideles in the product of all the local unit groups stays injective
modulo a nonzero integer**: a multiple of it whose valuations vanish at all but finitely many places
has itself valuations vanishing there, the integers having no torsion. -/
theorem injective_modNsmulHom_ideleToFullIdele {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (Tate.modNsmulHom (ideleToFullIdele k K) p).hom.hom := by
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun z hz => ?_)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (Tate.nsmulLinear ℤ p ↥(ideleRep k K).V)) z
  rw [Tate.modNsmulHom_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Tate.nsmulLinear_apply] at hb
  have hbv : ∀ v : HeightOneSpectrum (𝓞 K),
      unitVal (x.1.2 v) = (p : ℤ) * unitVal (b.2 v) := fun v => by
    have hv : p • b.2 v = x.1.2 v := congrArg (fun y : FullIdele K => y.2 v) hb
    rw [← hv, _root_.map_nsmul, nsmul_eq_mul]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨b, ?_⟩, ?_⟩
  · rw [mem_idele, Filter.eventually_cofinite]
    refine (Filter.eventually_cofinite.1 x.2).subset fun v hv hc => hv ?_
    have h0 : (p : ℤ) * unitVal (b.2 v) = 0 := by rw [← hbv v, hc]
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    exact (mul_eq_zero.1 h0).resolve_left hpz
  · refine Subtype.ext ?_
    rw [Tate.nsmulLinear_apply]
    exact hb

end SES

end

end InverseGalois.CFT
