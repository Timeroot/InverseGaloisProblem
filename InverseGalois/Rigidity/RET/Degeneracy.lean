/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.SeparableUnramified

/-!
# The degeneracy polynomial of a family of equations

The resultant of a monic equation and its derivative is a polynomial in the parameter of the line
which vanishes exactly at the points where the specialized equation acquires a repeated root.  It
therefore locates the branch points of a cover presented by that equation: the branch locus lies
inside the zero set of the resultant, a finite set as soon as the generic equation is separable.

Over a field of characteristic zero a monic polynomial is separable exactly when the resultant of
the polynomial and its derivative is nonzero, the degree of the derivative being one less than the
degree of the polynomial; and the resultant commutes with specialization of the coefficients, the
degrees being unchanged because the equation is monic.  Both facts together turn the local
criterion of the previous file into a global, computable bound for the branch locus.

## Main results

* `Rigidity.RET.separable_iff_resultant_ne_zero` — over a field of characteristic zero, a monic
  polynomial is separable exactly when the resultant with its derivative is nonzero.
* `Rigidity.RET.separable_specialize_iff` — the specialized equation is separable exactly where the
  degeneracy polynomial does not vanish.
* `Rigidity.RET.degeneracy_ne_zero` — a separable generic equation has a nonzero degeneracy
  polynomial, so the degeneracy locus is finite.
* `Rigidity.RET.LineCover.branchLocus_subset_degeneracy` — the branch locus of a cover presented by
  the equation is contained in the degeneracy locus.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ### Separability and the resultant with the derivative -/

/-- **A monic polynomial over a field of characteristic zero is separable exactly when the
resultant of the polynomial with its derivative is nonzero.**  The derivative has degree one less
than the polynomial, which is what makes the resultant with those degrees the right invariant. -/
theorem separable_iff_resultant_ne_zero {K : Type*} [Field K] [CharZero K] {g : Polynomial K}
    (hg : g.Monic) (hdeg : 0 < g.natDegree) :
    g.Separable ↔ Polynomial.resultant g (derivative g) g.natDegree (g.natDegree - 1) ≠ 0 := by
  have hd : (derivative g).natDegree = g.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq g hdeg)
  rw [← hd, separable_def]
  constructor
  · intro hsep hzero
    exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hsep
  · intro hne
    by_contra hsep
    exact hne (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hg.ne_zero, hsep⟩)

/-! ### The degeneracy polynomial of a family -/

variable {K : Type*} [Field K] [CharZero K]

/-- The **degeneracy polynomial** of a monic family of equations over the line: the resultant of the
equation and its derivative in the fibre variable, a polynomial in the parameter of the line. -/
def degeneracy (f : Polynomial (Polynomial K)) : Polynomial K :=
  Polynomial.resultant f (derivative f) f.natDegree (f.natDegree - 1)

omit [CharZero K] in
/-- **The degeneracy polynomial specializes to the resultant of the specialized equation**: the
resultant is computed from the coefficients, so specializing them specializes it. -/
theorem degeneracy_eval (f : Polynomial (Polynomial K)) (t : K) :
    (degeneracy f).eval t
      = Polynomial.resultant (f.map (evalRingHom t)) (derivative (f.map (evalRingHom t)))
          f.natDegree (f.natDegree - 1) := by
  have hcoe : (degeneracy f).eval t = (evalRingHom t) (degeneracy f) := rfl
  rw [hcoe, degeneracy, ← Polynomial.resultant_map_map, Polynomial.derivative_map]

/-- **The specialized equation is separable exactly where the degeneracy polynomial does not
vanish.** -/
theorem separable_specialize_iff (f : Polynomial (Polynomial K)) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (t : K) :
    (f.map (evalRingHom t)).Separable ↔ (degeneracy f).eval t ≠ 0 := by
  have hmonic : (f.map (evalRingHom t)).Monic := hf.map _
  have hnat : (f.map (evalRingHom t)).natDegree = f.natDegree := hf.natDegree_map _
  rw [separable_iff_resultant_ne_zero hmonic (by rw [hnat]; exact hdeg), hnat, degeneracy_eval f t]

/-- **A separable generic equation has a nonzero degeneracy polynomial.**  Passing to the function
field of the line, the resultant specializes to the resultant of the generic equation, which is
nonzero precisely because that equation is separable. -/
theorem degeneracy_ne_zero (f : Polynomial (Polynomial K)) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (algebraMap (Polynomial K) (RatFunc K))).Separable) : degeneracy f ≠ 0 := by
  intro h0
  have hmonic : (f.map (algebraMap (Polynomial K) (RatFunc K))).Monic := hf.map _
  have hnat : (f.map (algebraMap (Polynomial K) (RatFunc K))).natDegree = f.natDegree :=
    hf.natDegree_map _
  have hres := (separable_iff_resultant_ne_zero hmonic (by rw [hnat]; exact hdeg)).mp hsep
  rw [hnat] at hres
  refine hres ?_
  have hmap : Polynomial.resultant (f.map (algebraMap (Polynomial K) (RatFunc K)))
      (derivative (f.map (algebraMap (Polynomial K) (RatFunc K)))) f.natDegree (f.natDegree - 1)
      = (algebraMap (Polynomial K) (RatFunc K)) (degeneracy f) := by
    rw [degeneracy, ← Polynomial.resultant_map_map, Polynomial.derivative_map]
  rw [hmap, h0, map_zero]

/-- **The generic equation is separable exactly when the degeneracy polynomial is nonzero.**  The
degeneracy polynomial is the resultant computed over the polynomial ring, and the function field of
the line contains that ring, so the two resultants determine each other. -/
theorem separable_generic_iff (f : Polynomial (Polynomial K)) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    (f.map (algebraMap (Polynomial K) (RatFunc K))).Separable ↔ degeneracy f ≠ 0 := by
  refine ⟨degeneracy_ne_zero f hf hdeg, fun h0 => ?_⟩
  have hmonic : (f.map (algebraMap (Polynomial K) (RatFunc K))).Monic := hf.map _
  have hnat : (f.map (algebraMap (Polynomial K) (RatFunc K))).natDegree = f.natDegree :=
    hf.natDegree_map _
  refine (separable_iff_resultant_ne_zero hmonic (by rw [hnat]; exact hdeg)).mpr ?_
  rw [hnat]
  have hmap : Polynomial.resultant (f.map (algebraMap (Polynomial K) (RatFunc K)))
      (derivative (f.map (algebraMap (Polynomial K) (RatFunc K)))) f.natDegree (f.natDegree - 1)
      = (algebraMap (Polynomial K) (RatFunc K)) (degeneracy f) := by
    rw [degeneracy, ← Polynomial.resultant_map_map, Polynomial.derivative_map]
  intro hc
  refine h0 (IsFractionRing.injective (Polynomial K) (RatFunc K) ?_)
  rw [← hmap, hc, map_zero]

/-- **A nonzero polynomial has at most `natDegree` many roots**, phrased for the set of roots. -/
theorem ncard_setOf_eval_eq_zero_le {F : Type*} [Field F] {p : Polynomial F} (hp : p ≠ 0) :
    {t : F | p.eval t = 0}.ncard ≤ p.natDegree := by
  have hfin : {t : F | p.eval t = 0}.Finite := Polynomial.finite_setOf_isRoot hp
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro a ha
  rw [Finset.mem_val, Set.Finite.mem_toFinset] at ha
  exact (Polynomial.mem_roots hp).mpr ha

/-- **The points where the specialized equation degenerates form a finite set**, as soon as the
generic equation is separable: they are the roots of a nonzero polynomial. -/
theorem finite_setOf_not_separable (f : Polynomial (Polynomial K)) (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (hsep : (f.map (algebraMap (Polynomial K) (RatFunc K))).Separable) :
    {t : K | ¬ (f.map (evalRingHom t)).Separable}.Finite := by
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot (degeneracy_ne_zero f hf hdeg hsep)) ?_
  intro t ht
  exact not_not.mp fun hne => ht ((separable_specialize_iff f hf hdeg t).mpr hne)

namespace LineCover

/-- **The branch locus of a cover presented by a monic equation is contained in the degeneracy
locus of that equation.** -/
theorem branchLocus_subset_degeneracy (L : LineCover) {x : L.M}
    (hgen : IntermediateField.adjoin (RatFunc k) {x} = ⊤)
    {f : Polynomial (Polynomial k)} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hroot : (Polynomial.aeval x) f = 0) :
    L.branchLocus ⊆ {t : k | (degeneracy f).eval t = 0} := by
  refine (L.branchLocus_subset_of_separable hgen hf hroot).trans ?_
  intro t ht
  exact not_not.mp fun hne => ht ((separable_specialize_iff f hf hdeg t).mpr hne)

/-- **A cover presented by a monic equation is unramified outside the roots of the degeneracy
polynomial.** -/
theorem isUnramifiedOutside_degeneracy (L : LineCover) {x : L.M}
    (hgen : IntermediateField.adjoin (RatFunc k) {x} = ⊤)
    {f : Polynomial (Polynomial k)} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hroot : (Polynomial.aeval x) f = 0) :
    L.IsUnramifiedOutside {t : k | (degeneracy f).eval t = 0} :=
  (L.isUnramifiedOutside_iff_branchLocus_subset _).mpr
    (L.branchLocus_subset_degeneracy hgen hf hdeg hroot)

end LineCover

end Rigidity.RET
