/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalOrdBridge
import InverseGalois.CFT.PoitouTate.ShaKummerInflate
import InverseGalois.CFT.PoitouTate.TensorShrink

/-!
# The obstruction to inflating, as one class with coefficients in the units of a finite set

An everywhere locally trivial class of the second cohomology names a single obstruction to being
inflated from the Galois group of the extension splitting its coefficients, and twisted Kummer
theory puts that obstruction in the first cohomology of a finite group with the units of the
extension tensored with the homomorphisms of the roots of unity as coefficients.  Those coefficients
are still infinite.  This file cuts them down.

The local dictionary says the obstruction is everywhere locally trivial exactly when its
coordinates, read through a homomorphism recording the order at each place outside a finite set,
vanish; so the obstruction comes from the subgroup of units whose order at every such place is
zero — a finitely generated group.  Composing the two statements leaves the demand in the shape a
counting argument can meet: **an everywhere locally trivial class of the second cohomology names one
class of the first cohomology of a finite group with finitely generated coefficients, and any
homomorphism of the kernels annihilating that one class carries the class of the second cohomology
into the image of inflation.**

The ordering matters as much as the statement.  A counting argument fixes how many classes it can
annihilate before it sees any of them, so the class must be produced from the class of the second
cohomology alone, before the homomorphism of the kernels is named.  That is exactly the shape
proved here.

## Main results

* `InverseGalois.CFT.exists_forall_coeffH2_of_hasLocalOrdHom`: **an everywhere locally trivial class
  of the second cohomology names a single class of the first cohomology of the Galois group of the
  splitting extension with the units of a finite set as coefficients, and any homomorphism of the
  kernels annihilating that class carries the class into the image of inflation.**

## Tags

Galois cohomology, local-global principle, Kummer theory, inflation, units, representation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IntermediateField groupCohomology TensorProduct

section Shrink

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] [IsCyclic M] {ι : M →* (↥K)ˣ} {p : ℕ} [NeZero p]
variable {E E' : Type} [CommGroup E] [CommGroup E'] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction Gal(Ω/↥K) E] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
  [MulDistribMulAction Gal(Ω/k) E'] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E']
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
  (hπK : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = galRestrictScalarsHom k ↥K Ω g • e)
  (hπ' : ∀ (g : Gal(Ω/k)) (e : E'), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivE' : ∀ (x : ↥K.fixingSubgroup) (e : E'), x • e = e)
variable {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
variable (α : E ≃* (J → M)) (α' : E' ≃* (J' → M))
variable (hEp : ∀ e : E, e ^ p = 1) (hEp' : ∀ e : E', e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [ActsTrivially K.fixingSubgroup (M →* E')]
variable {X : Type} [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
variable (g : Additive (↥K)ˣ →+ (X →₀ ℤ))
variable (B : Subgroup (↥K)ˣ) [IsStableSubgroup (Gal(Ω/k) ⧸ K.fixingSubgroup) B]
variable [Finite (Gal(Ω/k) ⧸ K.fixingSubgroup)]

include hπ hπK hπ' htrivE' α' hEp' hfix in
/-- **An everywhere locally trivial class of the second cohomology names a single class of the first
cohomology of the Galois group of the splitting extension, with coefficients in the units whose
order vanishes at every place outside the finite set tensored with the homomorphisms of the roots of
unity, and every homomorphism of the kernels annihilating that one class carries the class of the
second cohomology into the image of inflation.**  Twisted Kummer theory turns the obstruction to
inflating into a class with the full units as coefficients; the local dictionary, read at every
place outside the finite set, shows that class comes from the subgroup of units of the set, which
is finitely generated.  The class is produced before the homomorphism of the kernels is chosen, so
a counting argument may fix in advance how many classes it must annihilate. -/
theorem exists_forall_coeffH2_of_hasLocalOrdHom
    (hg : Function.Surjective g)
    (hB : ∀ a : (↥K)ˣ, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hlocal : ∀ x : X, HasLocalOrdHom h htriv htrivE α hEp g (decompositionSubgroups k Ω) x)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ w : H1 (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive ↥B ⊗[ℤ] Additive (M →* E))),
      ∀ (ψ : E →* E') (hψ : ∀ (u : Gal(Ω/k)) (e : E), ψ (u • e) = u • ψ e),
        (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
            (A := Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
              (Additive ↥B ⊗[ℤ] Additive (M →* E)))
            (tensorCoeffRep (A := ↥B) (Gal(Ω/k) ⧸ K.fixingSubgroup) (MonoidHom.compHom ψ)
              (compHom_quotient_smul (M := M) ψ hψ)) 1).hom w = 0 →
          ∃ v : SmoothH2 (↥K ≃ₐ[k] ↥K) E', galInflH2 K hπ' v = coeffH2 ψ hψ z := by
  obtain ⟨y, hy, hforall⟩ := exists_kummerSha1_forall_coeffH2_of_mem_sha2 K hπ hπK hπ' h htriv
    htrivE htrivE' α α' hEp hEp' hfix z hz
  obtain ⟨w, hw⟩ := mem_range_tensorSubInclRep_of_mem_kummerSha1 h htriv htrivE α hEp hfix g B
    K.fixingSubgroup_isOpen (decompositionSubgroups k Ω) hg hB hgeq hlocal hy
  refine ⟨w, fun ψ hψ hkill => hforall ψ hψ ?_⟩
  rw [show kummerCoeffRepHom K M E E' ψ hψ
      = tensorCoeffRep (A := (↥K)ˣ) (Gal(Ω/k) ⧸ K.fixingSubgroup) (MonoidHom.compHom ψ)
        (compHom_quotient_smul (M := M) ψ hψ) from rfl]
  exact map_tensorCoeffRep_eq_zero_of_map_tensorSubInclRep B (MonoidHom.compHom ψ)
    (compHom_quotient_smul (M := M) ψ hψ) hw hkill

end Shrink

end InverseGalois.CFT
