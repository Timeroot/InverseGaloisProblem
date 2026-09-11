/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses

/-!
# A Galois equivariant family of lines carried by a free orbit of places

A prescription which is allowed to be ramified at a family of places is answered only when the
classes prescribed at one place all lie on a single line, and the lines at the places of one orbit
have to be carried into one another by the identification of the classes at a place with the
classes at its image.  A family of lines given at named places therefore has to be spread over the
orbits of those places, and for that to be unambiguous the orbits are asked to be free: no
automorphism other than the identity carries a named place to a named place.

Spreading a generator of a line by transporting it along the identification of the classes would
ask for the composition law of those identifications, whose two sides live at the two sides of the
associativity of the action and so differ by a transport of the classes along an equality of
places.  That is avoided here by carrying, instead of the classes themselves, elements of the
number field whose classes they are: a place enters the class of an element only as an index, so
the image of an element at the image of a place needs no transport, and the composition law
reduces to the associativity of the action on the units.

## Main definitions

* `InverseGalois.CFT.orbitLine`: the family of classes obtained by spreading a family of elements
  named at a free orbit of places over the whole orbit.

## Main statements

* `InverseGalois.CFT.orbitLine_smul`: **the spread family is Galois equivariant**, the class at the
  image of a place being the image of the class at the place.
* `InverseGalois.CFT.orbitLine_zpowers_smul`: the form the two-place construction asks for, that
  the line at the image of a place is the image of the line at the place.
* `InverseGalois.CFT.orbitLine_mem`: at a named place the spread family is the class of the element
  named there.
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Pointwise

section OrbitLine

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] {p : ℕ}
  {Tp : Finset (HeightOneSpectrum (𝓞 K))}

variable (k) in
/-- **A family of elements of the number field named at a family of places, spread over the orbits
of those places.**  At a place carried to a named place by an automorphism the class is that of the
image of the element named there; away from the orbits it is trivial. -/
noncomputable def orbitLine (Tp : Finset (HeightOneSpectrum (𝓞 K))) (a : ↥Tp → Kˣ) (p : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) : localClasses v p :=
  open Classical in
  if h : ∃ q : Gal(K/k) × ↥Tp, q.1 • (q.2 : HeightOneSpectrum (𝓞 K)) = v then
    localClassHom v p (galUnits h.choose.1 (a h.choose.2))
  else 1

omit [NumberField K] in
/-- Moving a unit of a number field by two automorphisms in turn moves it by their product. -/
theorem galUnits_mul_apply (σ τ : Gal(K/k)) (x : Kˣ) :
    galUnits σ (galUnits τ x) = galUnits (σ * τ) x := by
  ext
  exact (AlgEquiv.mul_apply σ τ (x : K)).symm

omit [NumberField K] in
/-- Moving a unit of a number field by the identity leaves it alone. -/
theorem galUnits_one_eq (x : Kˣ) : galUnits (1 : Gal(K/k)) x = x := by
  ext
  rfl

variable (hfree : ∀ σ : Gal(K/k), σ ≠ 1 → ∀ w ∈ Tp, σ • w ∉ Tp)

include hfree

omit [NumberField K] in
/-- **A place is carried to a named place by at most one automorphism, and from at most one named
place.**  Were two named places to have a common image, the automorphism carrying one to the other
would be an automorphism other than the identity carrying a named place to a named place. -/
theorem eq_of_smul_coe_eq_smul_coe {σ τ : Gal(K/k)} {w w' : ↥Tp}
    (h : σ • (w : HeightOneSpectrum (𝓞 K)) = τ • (w' : HeightOneSpectrum (𝓞 K))) :
    σ = τ ∧ w = w' := by
  have hw : (τ⁻¹ * σ) • (w : HeightOneSpectrum (𝓞 K)) = (w' : HeightOneSpectrum (𝓞 K)) := by
    rw [mul_smul, h, inv_smul_smul]
  have hστ : τ⁻¹ * σ = 1 := by
    by_contra hcon
    refine hfree _ hcon (w : HeightOneSpectrum (𝓞 K)) w.2 ?_
    rw [hw]
    exact w'.2
  refine ⟨?_, ?_⟩
  · rw [← one_mul σ, ← mul_inv_cancel τ, mul_assoc, hστ, mul_one]
  · rw [hστ, one_smul] at hw
    exact Subtype.ext hw

omit hfree in
/-- Away from the orbits of the named places the spread family is trivial. -/
theorem orbitLine_of_forall_ne (a : ↥Tp → Kˣ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ∀ (σ : Gal(K/k)) (w : ↥Tp), σ • (w : HeightOneSpectrum (𝓞 K)) ≠ v) :
    orbitLine k Tp a p v = 1 :=
  dif_neg fun ⟨q, hq⟩ => hv q.1 q.2 hq

/-- **On the orbits the spread family is the class of the image of the element named at the place
the orbit comes from.**  The automorphism and the named place are determined by the place, so the
choice the definition makes agrees with any other. -/
theorem orbitLine_of_smul_eq (a : ↥Tp → Kˣ) {σ : Gal(K/k)} {w : ↥Tp}
    {v : HeightOneSpectrum (𝓞 K)} (hv : σ • (w : HeightOneSpectrum (𝓞 K)) = v) :
    orbitLine k Tp a p v = localClassHom v p (galUnits σ (a w)) := by
  classical
  have hex : ∃ q : Gal(K/k) × ↥Tp, q.1 • (q.2 : HeightOneSpectrum (𝓞 K)) = v := ⟨(σ, w), hv⟩
  rw [orbitLine, dif_pos hex]
  obtain ⟨hσ, hw⟩ := eq_of_smul_coe_eq_smul_coe hfree (hex.choose_spec.trans hv.symm)
  rw [hσ, hw]

/-- At a named place the spread family is the class of the element named there. -/
theorem orbitLine_mem (a : ↥Tp → Kˣ) (w : ↥Tp) :
    orbitLine k Tp a p (w : HeightOneSpectrum (𝓞 K)) = localClassHom _ p (a w) := by
  rw [orbitLine_of_smul_eq hfree a (one_smul (Gal(K/k)) (w : HeightOneSpectrum (𝓞 K))),
    galUnits_one_eq]

/-- **The spread family is Galois equivariant.**  The class at the image of a place is the image of
the class at the place: on the orbits both are the class of the image of the element named at the
place the orbit comes from, by the two automorphisms differing by the one moving the place, and
away from the orbits both are trivial. -/
theorem orbitLine_smul (a : ↥Tp → Kˣ) (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    localClassesGalEquiv σ v p (orbitLine k Tp a p v) = orbitLine k Tp a p (σ • v) := by
  classical
  by_cases hv : ∃ q : Gal(K/k) × ↥Tp, q.1 • (q.2 : HeightOneSpectrum (𝓞 K)) = v
  · obtain ⟨⟨τ, w⟩, hτ⟩ := hv
    rw [orbitLine_of_smul_eq hfree a hτ, localClassesGalEquiv_localClassHom, galUnits_mul_apply,
      orbitLine_of_smul_eq hfree a (show (σ * τ) • (w : HeightOneSpectrum (𝓞 K)) = σ • v by
        rw [mul_smul, hτ])]
  · push_neg at hv
    have hv' : ∀ (ρ : Gal(K/k)) (w : ↥Tp), ρ • (w : HeightOneSpectrum (𝓞 K)) ≠ σ • v := by
      intro ρ w hcon
      refine hv (σ⁻¹ * ρ, w) ?_
      rw [mul_smul, hcon, inv_smul_smul]
    rw [orbitLine_of_forall_ne a fun ρ w hcon => hv (ρ, w) hcon,
      orbitLine_of_forall_ne a hv', _root_.map_one]

/-- **The line of the spread family at the image of a place is the image of the line at the
place**, which is the form the construction of a family of two places asks the lines in. -/
theorem orbitLine_zpowers_smul (a : ↥Tp → Kˣ) (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup.zpowers (orbitLine k Tp a p (σ • v))
      = Subgroup.zpowers (localClassesGalEquiv σ v p (orbitLine k Tp a p v)) := by
  rw [orbitLine_smul hfree]

end OrbitLine

end InverseGalois.CFT
