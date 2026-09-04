/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Additive
import InverseGalois.CFT.TateCohomology.SylowInjective

/-!
# Corestriction from a Sylow subgroup is onto the primary part

Corestriction after restriction is multiplication by the index of the subgroup.  Read in the other
direction from the injectivity of restriction, this says that a class killed by a natural number
prime to the index is already a corestriction: write one as a combination of the index and the
multiple that kills the class, and the second term disappears.

For a Sylow subgroup the index is prime to the prime, so corestriction reaches every class killed
by a power of that prime.  Coefficients killed by a power of a prime have complete cohomology
killed by the same power, because the multiple of the identity that kills them induces that
multiple on the cohomology.  Together these say that the complete cohomology of such coefficients
is entirely produced by the Sylow subgroup, which is the surjectivity that accompanies the
injectivity of restriction and completes the reduction to a Sylow subgroup.

## Main results

* `InverseGalois.CFT.Tate.mem_range_tateCor_of_coprime`: **a class killed by a natural number prime
  to the index of a subgroup is a corestriction from that subgroup.**
* `InverseGalois.CFT.Tate.nsmul_eq_zero_tateModule_of_nsmul`: **a multiple killing the coefficients
  kills their complete cohomology.**
* `InverseGalois.CFT.Tate.surjective_tateCor_sylow`: **corestriction from a Sylow subgroup is onto
  the complete cohomology of coefficients killed by a power of that prime.**

## Tags

Tate cohomology, corestriction, transfer, Sylow subgroup, primary component
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### A coprime multiple -/

/-- **An element killed by a natural number is an integer multiple of any coprime multiple of
itself.** -/
theorem exists_zsmul_nsmul_eq {M : Type*} [AddCommGroup M] {x : M} {a b : ℕ} (hb : b • x = 0)
    (hab : Nat.Coprime a b) : ∃ c : ℤ, c • (a • x) = x := by
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) :=
    Int.isCoprime_iff_nat_coprime.2 (by simpa using hab)
  refine ⟨u, ?_⟩
  have hx : ((u * a + v * b : ℤ)) • x = x := by rw [huv, one_zsmul]
  rwa [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, hb, smul_zero,
    add_zero] at hx

/-! ### Corestriction and the index -/

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A class killed by a natural number prime to the index of a subgroup is a corestriction from
that subgroup.** -/
theorem mem_range_tateCor_of_coprime {H : Subgroup G} {A : Rep k G} {n : ℤ} {x : tateModule A n}
    {m : ℕ} (hm : m • x = 0) (hcop : Nat.Coprime H.index m) :
    x ∈ LinearMap.range (tateCor H A n) := by
  obtain ⟨c, hc⟩ := exists_zsmul_nsmul_eq hm hcop
  refine LinearMap.mem_range.2 ⟨c • tateRes H A n x, ?_⟩
  rw [map_zsmul, tateCor_tateRes, hc]

/-- **Corestriction from a subgroup whose index is prime to a multiple killing the complete
cohomology is onto.** -/
theorem surjective_tateCor_of_coprime (H : Subgroup G) (A : Rep k G) (n : ℤ) {m : ℕ}
    (hm : ∀ x : tateModule A n, m • x = 0) (hcop : Nat.Coprime H.index m) :
    Function.Surjective (tateCor H A n) := fun x =>
  LinearMap.mem_range.1 (mem_range_tateCor_of_coprime (hm x) hcop)

/-! ### Coefficients killed by a multiple -/

/-- **A multiple killing the coefficients kills their complete cohomology.** -/
theorem nsmul_eq_zero_tateModule_of_nsmul {A : Rep k G} {m : ℕ} (hA : ∀ a : ↥A.V, m • a = 0)
    (n : ℤ) (x : tateModule A n) : m • x = 0 := by
  have hzero : (m • 𝟙 A) = (0 : A ⟶ A) :=
    Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun a => hA a))
  rw [← tateMap_nsmul_id_apply A m n x, hzero, tateMap_zero]
  rfl

/-! ### A Sylow subgroup -/

/-- **Corestriction from a Sylow subgroup is onto the complete cohomology of coefficients killed by
a power of that prime.** -/
theorem surjective_tateCor_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) (A : Rep k G) (n : ℤ)
    {j : ℕ} (hA : ∀ a : ↥A.V, p ^ j • a = 0) :
    Function.Surjective (tateCor (P : Subgroup G) A n) :=
  surjective_tateCor_of_coprime (P : Subgroup G) A n
    (fun x => nsmul_eq_zero_tateModule_of_nsmul hA n x)
    (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index).symm.pow_right j)

/-- **Corestriction from a Sylow subgroup is onto the complete cohomology of coefficients killed by
that prime.** -/
theorem surjective_tateCor_sylow_of_prime {p : ℕ} [Fact p.Prime] (P : Sylow p G) (A : Rep k G)
    (n : ℤ) (hA : ∀ a : ↥A.V, p • a = 0) :
    Function.Surjective (tateCor (P : Subgroup G) A n) :=
  surjective_tateCor_sylow P A n (j := 1) (fun a => by rw [pow_one]; exact hA a)

end

end InverseGalois.CFT.Tate
