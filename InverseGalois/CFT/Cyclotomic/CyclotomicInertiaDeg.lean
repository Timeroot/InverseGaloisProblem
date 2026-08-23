import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.Cyclotomic.BuildingBlock

/-!
# Residue degree at the conductor in a cyclotomic field and its subfields

The prime `q` is totally ramified in the cyclotomic field `ℚ(ζ_q)` of prime conductor `q`, so the
unique prime of `ℚ(ζ_q)` above `q` has residue degree one.  Residue degrees are multiplicative in a
tower, and every prime of an intermediate field `F` of `ℚ(ζ_q)/ℚ` sits below a prime of `ℚ(ζ_q)`, so
the residue degree at `q` is one in every intermediate field as well.

## Main results

* `InverseGalois.CFT.inertiaDeg_eq_one_of_intermediateField_cyclotomic`: a prime of an intermediate
  field of `ℚ(ζ_q)/ℚ` lying over the rational prime `q` has residue degree one.
* `InverseGalois.CFT.inertiaDeg_under_eq_one_of_cyclotomic`: the same statement for the prime of an
  intermediate field lying under a given prime of `ℚ(ζ_q)`.
-/

open NumberField

namespace InverseGalois.CFT

/-- **The residue degree at the conductor is one in every subfield of `ℚ(ζ_q)`.**  For a prime
conductor `q`, a prime `Q` of an intermediate field `F` of `ℚ(ζ_q)/ℚ` lying over the rational prime
`q` has residue degree one over `ℚ`. -/
theorem inertiaDeg_eq_one_of_intermediateField_cyclotomic (q : ℕ) [hq : Fact q.Prime]
    (E : Type*) [Field E] [NumberField E] [IsCyclotomicExtension {q} ℚ E]
    (F : IntermediateField ℚ E) (Q : Ideal (𝓞 ↥F)) [Q.IsPrime]
    [hQover : Q.LiesOver (Ideal.span {(q : ℤ)})] :
    (Ideal.span {(q : ℤ)}).inertiaDeg Q = 1 := by
  haveI := isMaximal_span_prime hq.out
  haveI : Q.IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (ne_bot_of_liesOver_natCast hq.out hQover)
  haveI : Algebra.IsIntegral (𝓞 ↥F) (𝓞 E) := Algebra.IsIntegral.tower_top (R := ℤ)
  obtain ⟨P, hP⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 E)))
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver Q := hP.2
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.trans P Q _
  have htower := Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) Q P
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime q E P] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- **The residue degree at the conductor is one below any prime of `ℚ(ζ_q)`.**  The prime of an
intermediate field `F` lying under a prime `P` of `ℚ(ζ_q)` above the rational prime `q` has residue
degree one over `ℚ`. -/
theorem inertiaDeg_under_eq_one_of_cyclotomic (q : ℕ) [Fact q.Prime]
    (E : Type*) [Field E] [NumberField E] [IsCyclotomicExtension {q} ℚ E]
    (F : IntermediateField ℚ E) (P : Ideal (𝓞 E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    (Ideal.span {(q : ℤ)}).inertiaDeg (P.under (𝓞 ↥F)) = 1 :=
  inertiaDeg_eq_one_of_intermediateField_cyclotomic q E F (P.under (𝓞 ↥F))

end InverseGalois.CFT
