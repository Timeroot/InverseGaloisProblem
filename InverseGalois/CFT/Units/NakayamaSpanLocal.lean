/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.NakayamaSpan

/-!
# The span, read one degree at a time and one place at a time

The comparison of Tate and Nakayama for the idele classes, together with the classes coming from
the ideles, is asked to span; and the criteria for that span which are available so far are stated
for every coefficient module and every degree at once.  A single embedding problem uses the span at
one module and one degree, and the vanishing statements that discharge it are much easier to arrange
there than everywhere.  So the criteria are restated in that form.

Restated in that form they become genuinely local.  The elements of the ideles killed by a prime
are nothing but a root of unity at every place, with no restriction at all, so their complete
cohomology over a subgroup of the Galois group is the product, over the orbits of the subgroup on
the places of the extension, of the complete cohomology of the stabiliser there with coefficients in
the roots of unity of the completion.  Feeding that into the criterion leaves a condition which
mentions only the finite group and its subgroups: **the span holds in a degree as soon as, over a
Sylow subgroup for the prime, the stabiliser of every place has no complete cohomology of the roots
of unity of the completion tensored with the coefficients in that degree, and the roots of unity of
the whole field tensored with the coefficients have none one degree higher.**

That is the shape in which a construction which is free to modify the coefficient module can
discharge the span: both conditions are vanishing statements about the cohomology of a finite group
in a fixed degree, and there are only finitely many subgroups to worry about.

## Main results

* `InverseGalois.CFT.hasIdeleClassNakayamaSpanAt_of_isZero`: **the span holds at one module and one
  degree as soon as the idele classes killed by the prime, tensored with those coefficients, have no
  complete cohomology over a Sylow subgroup for the prime** in the degree the obstruction lands in.
* `InverseGalois.CFT.hasIdeleClassNakayamaSpanAt_of_isZero_idele`: **the same, from the vanishing of
  the ideles killed by the prime and of the roots of unity of the field**, each tensored with the
  coefficients, in the two relevant degrees.
* `InverseGalois.CFT.hasIdeleClassNakayamaSpanAt_of_isZero_local`: **the same, from vanishing at the
  stabiliser of each place of the extension in a Sylow subgroup**, together with the global
  condition on the roots of unity.  This is the form in which the span is a condition on the finite
  group alone.

## Tags

number field, idele class group, Tate-Nakayama, Sylow subgroup, decomposition group, local condition
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Limits MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p : ℕ} [Fact p.Prime]

/-! ### One module, one degree -/

/-- **The span holds at one choice of coefficients and one degree as soon as the idele classes
killed by the prime, tensored with those coefficients, have no complete cohomology over a Sylow
subgroup for the prime** in the degree the obstruction of Tate and Nakayama lands in.  There the
obstruction is the zero map, so the comparison is already surjective and the ideles are not needed;
this is the statement of `InverseGalois.CFT.hasIdeleClassNakayamaSpan_of_isZero` asked only where it
is used. -/
theorem hasIdeleClassNakayamaSpanAt_of_isZero (W : Rep ℤ Gal(K/k))
    (hW : ∀ w : ↥W.V, p • w = 0) (n : ℤ)
    (h : ∀ P : Sylow p Gal(K/k), IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
      (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) (n + 1 + 1 + 1 + 1))) :
    HasIdeleClassNakayamaSpanAt k K p W n := by
  intro P
  have hz : IsZero (tateModule (tensorObj
      (nsmulTorsion (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K)) p)
      (resObj (P : Subgroup Gal(K/k)) W)) (n + 1 + 1 + 1 + 1)) :=
    isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut
      ((ideleClassAutHom k K).comp (P : Subgroup Gal(K/k)).subtype) p
      (resObj (P : Subgroup Gal(K/k)) W) (n + 1 + 1 + 1 + 1) (h P)
  have hker : LinearMap.ker
      (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n) = ⊤ :=
    Submodule.eq_top_iff'.2 fun x => LinearMap.mem_ker.2 (eq_zero_of_isZero hz _)
  rw [← ker_resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n, hker, top_sup_eq]

/-- **The span holds at one choice of coefficients and one degree as soon as the ideles killed by
the prime and the roots of unity of the field, each tensored with those coefficients, have no
complete cohomology over a Sylow subgroup for the prime** in the two relevant degrees.  The idele
classes killed by the prime sit between those two groups, so their complete cohomology is squeezed
to nothing. -/
theorem hasIdeleClassNakayamaSpanAt_of_isZero_idele (W : Rep ℤ Gal(K/k))
    (hW : ∀ w : ↥W.V, p • w = 0) (n : ℤ)
    (hI : ∀ P : Sylow p Gal(K/k), IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
      (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) (n + 1 + 1 + 1 + 1)))
    (hU : ∀ P : Sylow p Gal(K/k), IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W))
        (n + 1 + 1 + 1 + 1 + 1))) :
    HasIdeleClassNakayamaSpanAt k K p W n :=
  hasIdeleClassNakayamaSpanAt_of_isZero W hW n fun P =>
    isZero_tateModule_tensor_ideleClassTorsionRes (Fact.out : p.Prime) W
      (P : Subgroup Gal(K/k)) (n + 1 + 1 + 1 + 1) (hI P) (hU P)

/-! ### One place at a time -/

/-- **The span holds at one choice of coefficients and one degree as soon as, over a Sylow subgroup
for the prime, the stabiliser of every place of the extension has no complete cohomology of the
roots of unity of the completion there tensored with the restricted coefficients** in the degree the
obstruction lands in, **and the roots of unity of the whole field tensored with the coefficients
have none** one degree higher.  Being killed by the prime forces the local valuations to vanish, so
the ideles killed by the prime are the sections of a family over the places and their complete
cohomology is computed orbit by orbit; a hypothesis asked at every place covers every orbit whatever
representatives are chosen. -/
theorem hasIdeleClassNakayamaSpanAt_of_isZero_local {d : ℕ} (W : Rep ℤ Gal(K/k))
    (hW : ∀ w : ↥W.V, p • w = 0) (e : ↥W.V ≃+ (Fin d → ZMod p)) (n : ℤ)
    (h₁ : ∀ (P : Sylow p Gal(K/k)) (w : InfinitePlace K), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) w)) (R := w.Completion)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(K/k)) w)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(K/k)) w) (resObj (P : Subgroup Gal(K/k)) W)))
        (n + 1 + 1 + 1 + 1)))
    (h₂ : ∀ (P : Sylow p Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) v)) (R := v.adicCompletion K)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(K/k)) v)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(K/k)) v) (resObj (P : Subgroup Gal(K/k)) W)))
        (n + 1 + 1 + 1 + 1)))
    (hU : ∀ P : Sylow p Gal(K/k), IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W))
        (n + 1 + 1 + 1 + 1 + 1))) :
    HasIdeleClassNakayamaSpanAt k K p W n := by
  classical
  refine hasIdeleClassNakayamaSpanAt_of_isZero_idele W hW n (fun P => ?_) hU
  exact isZero_tateModule_tensor_ideleTorsionRes (P : Subgroup Gal(K/k)) W e
    (fun ω => ⟨ω.nonempty_orbit.choose, ω.nonempty_orbit.choose_spec⟩)
    (fun ω => ⟨ω.nonempty_orbit.choose, ω.nonempty_orbit.choose_spec⟩)
    (n + 1 + 1 + 1 + 1) (fun ω => h₁ P _) (fun ω => h₂ P _)

end

end InverseGalois.CFT
