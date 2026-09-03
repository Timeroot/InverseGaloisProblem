/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.CohomTrivial
import InverseGalois.CFT.TateCohomology.TensorPExact
import InverseGalois.CFT.TateCohomology.TorsionShift

/-!
# The vectors killed by a prime as the correction to a tensor product

Tensoring with coefficients killed by a prime does not see the difference between a representation
and its reduction modulo that prime, and it carries a short exact sequence whose middle term is
killed by the prime to a short exact sequence again.  So a presentation of a representation by one
on which the prime acts without torsion, read modulo the prime, splits into two such sequences: the
cycles of the reduced presentation sit between the reduced sub and the reduced middle term, and the
vectors of the reduced sub dying in those cycles sit below them.  The middle terms of the two
sequences are the reductions of the two terms of the presentation, so both stay short exact after
tensoring, and both connecting maps are bijective as soon as the presentation is acyclic after
tensoring.

What sits at the bottom is exactly the vectors of the represented quotient killed by the prime.  A
vector of the sub whose image is a multiple of the prime determines the vector of the middle term
it is the multiple of, uniquely, because the prime acts on the middle term without torsion; the
image of that vector in the quotient is killed by the prime; every vector of the quotient killed by
the prime arises this way; and the vectors of the sub sent to zero are on both sides the multiples
of the prime.

Running the two connecting maps one after the other, **the complete cohomology of a representation
tensored with coefficients killed by a prime, in a degree, is the complete cohomology of the
vectors it kills, tensored with the same coefficients, two degrees higher.**  That is the term
separating the theorem of Tate and Nakayama for coefficients killed by a prime from the theorem for
coefficients flat over the integers, and the free cover of a representation supplies a presentation
to run it on.

## Main definitions

* `InverseGalois.CFT.Tate.modCycleObj`, `InverseGalois.CFT.Tate.modTorObj`: the two kernels of a
  presentation read modulo a number.
* `InverseGalois.CFT.Tate.modCycleSeq`, `InverseGalois.CFT.Tate.modTorSeq`: the two short exact
  sequences into which the reduced presentation splits.
* `InverseGalois.CFT.Tate.preMultiples`: the vectors of the sub of a presentation whose image is a
  multiple of a number.

## Main results

* `InverseGalois.CFT.Tate.modTorTorsionIso`: **the lower kernel of a reduced presentation is the
  vectors of the quotient killed by the number**, when the number acts on the middle term without
  torsion.
* `InverseGalois.CFT.Tate.tensorPTorsionShiftEquiv`: **the complete cohomology of the quotient of a
  presentation tensored with coefficients killed by a prime, in a degree, is the complete
  cohomology of the vectors it kills tensored with the same coefficients two degrees higher.**
* `InverseGalois.CFT.Tate.tensorPTorsionShiftFreeEquiv`: the same for a representation whose
  restriction to every Sylow subgroup for the prime has no complete cohomology, presented by its
  free cover.

## Tags

Tate cohomology, torsion, dimension shifting, tensor product, Tate-Nakayama, presentation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Reducing a map of representations modulo a number -/

section Reduction

variable {k G : Type u} [CommRing k] [Group G]

/-- **The reduction of a surjection modulo a number is surjective.** -/
theorem modNsmulHom_surjective {A B : Rep k G} (Φ : A ⟶ B) (m : ℕ)
    (hΦ : Function.Surjective Φ.hom.hom) :
    Function.Surjective (modNsmulHom Φ m).hom.hom := by
  intro z
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥B.V)) z
  obtain ⟨a, rfl⟩ := hΦ b
  exact ⟨Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥A.V)) a, rfl⟩

/-- The class of a multiple of a number in the reduction modulo that number vanishes. -/
theorem mkQ_nsmul_eq_zero (A : Rep k G) (m : ℕ) (v : ↥A.V) :
    Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥A.V)) (m • v) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨v, rfl⟩

end Reduction

/-! ### The two kernels of a reduced presentation -/

section Presentation

variable {k G : Type u} [CommRing k] [Group G] (X : ShortComplex (Rep k G)) (m : ℕ)

/-- **The vectors of the reduced middle term of a presentation dying in the reduced quotient.** -/
def modCycleObj : Rep k G := kerObj (modNsmulHom X.g m)

/-- The reduction of the sub of a presentation lands in the vectors dying in the reduced
quotient. -/
theorem modNsmulHom_apply_mem_ker (x : ↥(modNsmul X.X₁ m).V) :
    (modNsmulHom X.f m).hom.hom x ∈ LinearMap.ker (modNsmulHom X.g m).hom.hom := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) x
  refine LinearMap.mem_ker.mpr ?_
  have h : X.g.hom.hom (X.f.hom.hom v) = 0 :=
    congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom.hom v) X.zero
  show Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₃.V)) (X.g.hom.hom (X.f.hom.hom v)) = 0
  rw [h, map_zero]

/-- The reduction of the sub of a presentation, seen in the vectors dying in the reduced
quotient. -/
def modCorestrictLinear : ↥(modNsmul X.X₁ m).V →ₗ[k] ↥(modCycleObj X m).V :=
  LinearMap.codRestrict (LinearMap.ker (modNsmulHom X.g m).hom.hom) (modNsmulHom X.f m).hom.hom
    (modNsmulHom_apply_mem_ker X m)

theorem modCorestrictLinear_equivariant (g : G) :
    modCorestrictLinear X m ∘ₗ (modNsmul X.X₁ m).ρ g
      = (modCycleObj X m).ρ g ∘ₗ modCorestrictLinear X m :=
  LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (hom_equivariant (modNsmulHom X.f m) g) x)

/-- **The reduced sub of a presentation, mapping onto the reduced cycles.** -/
def modCorestrict : modNsmul X.X₁ m ⟶ modCycleObj X m :=
  mkHom (modCorestrictLinear X m) (modCorestrictLinear_equivariant X m)

/-- **The vectors of the reduced sub of a presentation dying in the reduced cycles.** -/
def modTorObj : Rep k G := kerObj (modCorestrict X m)

/-- **The reduced cycles, the reduced middle term and the reduced quotient.** -/
def modCycleSeq : ShortComplex (Rep k G) := kerSeq (modNsmulHom X.g m)

/-- **The lower kernel, the reduced sub and the reduced cycles.** -/
def modTorSeq : ShortComplex (Rep k G) := kerSeq (modCorestrict X m)

/-- **The reduced sub of a presentation maps onto the reduced cycles.** -/
theorem modCorestrict_surjective (hX : X.ShortExact) :
    Function.Surjective (modCorestrict X m).hom.hom := by
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥X.X₂.V)) z
  have hz' : X.g.hom.hom y ∈ LinearMap.range (nsmulLinear k m ↥X.X₃.V) := by
    have h : Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₃.V)) (X.g.hom.hom y) = 0 :=
      LinearMap.mem_ker.mp hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact h
  obtain ⟨e, he⟩ := hz'
  obtain ⟨y₀, rfl⟩ := shortExact_surjective hX e
  simp only [nsmulLinear_apply] at he
  have hzero : X.g.hom.hom (y - m • y₀) = 0 := by
    rw [map_sub, map_nsmul, he, sub_self]
  obtain ⟨x, hx⟩ : y - m • y₀ ∈ LinearMap.range X.f.hom.hom := by
    rw [shortExact_range_eq_ker hX]
    exact LinearMap.mem_ker.mpr hzero
  refine ⟨Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) x, Subtype.ext ?_⟩
  show Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₂.V)) (X.f.hom.hom x) = _
  rw [hx, map_sub, mkQ_nsmul_eq_zero, sub_zero]

/-- **The reduced cycles sit in a short exact sequence.** -/
theorem modCycleSeq_shortExact (hX : X.ShortExact) : (modCycleSeq X m).ShortExact :=
  kerSeq_shortExact _ (modNsmulHom_surjective X.g m (shortExact_surjective hX))

/-- **The lower kernel sits in a short exact sequence.** -/
theorem modTorSeq_shortExact (hX : X.ShortExact) : (modTorSeq X m).ShortExact :=
  kerSeq_shortExact _ (modCorestrict_surjective X m hX)

end Presentation

/-! ### Dividing by a number acting without torsion -/

section Divide

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (m : ℕ)
  (htf : ∀ v : ↥A.V, m • v = 0 → v = 0)

/-- **Multiplication by a number acting without torsion, as an isomorphism onto its multiples.** -/
def nsmulRangeEquiv : ↥A.V ≃ₗ[k] ↥(LinearMap.range (nsmulLinear k m ↥A.V)) :=
  LinearEquiv.ofInjective (nsmulLinear k m ↥A.V) fun u v h =>
    sub_eq_zero.1 (htf _ (by rw [smul_sub]; exact sub_eq_zero.2 h))

theorem nsmulRangeEquiv_apply (v : ↥A.V) :
    ((nsmulRangeEquiv A m htf v : ↥(LinearMap.range (nsmulLinear k m ↥A.V))) : ↥A.V) = m • v :=
  rfl

theorem nsmul_nsmulRangeEquiv_symm (z : ↥(LinearMap.range (nsmulLinear k m ↥A.V))) :
    m • ((nsmulRangeEquiv A m htf).symm z) = (z : ↥A.V) := by
  rw [← nsmulRangeEquiv_apply A m htf, LinearEquiv.apply_symm_apply]

theorem nsmulRangeEquiv_symm_eq (z : ↥(LinearMap.range (nsmulLinear k m ↥A.V))) (v : ↥A.V)
    (hv : m • v = (z : ↥A.V)) : (nsmulRangeEquiv A m htf).symm z = v := by
  refine (LinearEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
  rw [nsmulRangeEquiv_apply, hv]

end Divide

/-! ### The lower kernel as the vectors killed by the number -/

section Kernel

variable {k G : Type u} [CommRing k] [Group G] (X : ShortComplex (Rep k G)) (m : ℕ)

/-- **The vectors of the sub of a presentation whose image is a multiple of a number.** -/
def preMultiples : Submodule k ↥X.X₁.V :=
  (LinearMap.range (nsmulLinear k m ↥X.X₂.V)).comap X.f.hom.hom

theorem mem_preMultiples_iff (v : ↥X.X₁.V) :
    v ∈ preMultiples X m ↔ X.f.hom.hom v ∈ LinearMap.range (nsmulLinear k m ↥X.X₂.V) :=
  Iff.rfl

theorem mkQ_mem_ker_modCorestrict (x : ↥(preMultiples X m)) :
    Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) (x : ↥X.X₁.V)
      ∈ LinearMap.ker (modCorestrict X m).hom.hom := by
  refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
  show Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₂.V)) (X.f.hom.hom (x : ↥X.X₁.V)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact x.2

/-- **The class in the lower kernel of a vector of the sub whose image is a multiple.** -/
def preClass : ↥(preMultiples X m) →ₗ[k] ↥(modTorObj X m).V :=
  LinearMap.codRestrict (LinearMap.ker (modCorestrict X m).hom.hom)
    ((Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V))).comp (preMultiples X m).subtype)
    (mkQ_mem_ker_modCorestrict X m)

theorem preClass_coe (x : ↥(preMultiples X m)) :
    (preClass X m x).1
      = Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) (x : ↥X.X₁.V) :=
  rfl

/-- **Every vector of the lower kernel is the class of a vector of the sub whose image is a
multiple.** -/
theorem preClass_surjective : Function.Surjective (preClass X m) := by
  rintro ⟨z, hz⟩
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) z
  have hv : v ∈ preMultiples X m := by
    have h : Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₂.V)) (X.f.hom.hom v) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact h
  exact ⟨⟨v, hv⟩, rfl⟩

/-- **A vector of the sub whose image is a multiple has trivial class exactly when it is itself a
multiple.** -/
theorem preClass_eq_zero_iff (x : ↥(preMultiples X m)) :
    preClass X m x = 0 ↔ (x : ↥X.X₁.V) ∈ LinearMap.range (nsmulLinear k m ↥X.X₁.V) := by
  constructor
  · intro h
    have h' : Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) (x : ↥X.X₁.V) = 0 :=
      congrArg Subtype.val h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
    exact h'
  · intro h
    refine Subtype.ext ?_
    show Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥X.X₁.V)) (x : ↥X.X₁.V) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h

/-- Moving a vector of the sub whose image is a multiple keeps its image a multiple. -/
theorem preMultiples_rho_mem (g : G) (x : ↥(preMultiples X m)) :
    X.X₁.ρ g (x : ↥X.X₁.V) ∈ preMultiples X m := by
  obtain ⟨y, hy⟩ : X.f.hom.hom (x : ↥X.X₁.V) ∈ LinearMap.range (nsmulLinear k m ↥X.X₂.V) := x.2
  simp only [nsmulLinear_apply] at hy
  show X.f.hom.hom (X.X₁.ρ g (x : ↥X.X₁.V)) ∈ LinearMap.range (nsmulLinear k m ↥X.X₂.V)
  refine ⟨X.X₂.ρ g y, ?_⟩
  show m • X.X₂.ρ g y = X.f.hom.hom (X.X₁.ρ g (x : ↥X.X₁.V))
  rw [← map_nsmul, hy]
  exact (LinearMap.congr_fun (hom_equivariant X.f g) (x : ↥X.X₁.V)).symm

theorem preClass_rho (g : G) (x : ↥(preMultiples X m)) :
    preClass X m ⟨X.X₁.ρ g (x : ↥X.X₁.V), preMultiples_rho_mem X m g x⟩
      = (modTorObj X m).ρ g (preClass X m x) :=
  Subtype.ext rfl

end Kernel

/-! ### The divisor of a vector of the sub -/

section Torsion

variable {k G : Type u} [CommRing k] [Group G] (X : ShortComplex (Rep k G)) (m : ℕ)
  (htf : ∀ y : ↥X.X₂.V, m • y = 0 → y = 0)

/-- **The vector of the middle term of a presentation whose multiple is the image of a vector of
the sub.** -/
def preDivide : ↥(preMultiples X m) →ₗ[k] ↥X.X₂.V :=
  (nsmulRangeEquiv X.X₂ m htf).symm.toLinearMap ∘ₗ
    LinearMap.restrict X.f.hom.hom (p := preMultiples X m)
      (q := LinearMap.range (nsmulLinear k m ↥X.X₂.V)) fun _ hv => hv

theorem nsmul_preDivide (x : ↥(preMultiples X m)) :
    m • preDivide X m htf x = X.f.hom.hom (x : ↥X.X₁.V) :=
  nsmul_nsmulRangeEquiv_symm X.X₂ m htf _

theorem preDivide_eq (x : ↥(preMultiples X m)) (y : ↥X.X₂.V)
    (hy : m • y = X.f.hom.hom (x : ↥X.X₁.V)) : preDivide X m htf x = y :=
  nsmulRangeEquiv_symm_eq X.X₂ m htf _ y hy

theorem preDivide_mem_ker (x : ↥(preMultiples X m)) :
    X.g.hom.hom (preDivide X m htf x) ∈ LinearMap.ker (nsmulLinear k m ↥X.X₃.V) := by
  refine LinearMap.mem_ker.mpr ?_
  show m • X.g.hom.hom (preDivide X m htf x) = 0
  rw [← map_nsmul, nsmul_preDivide]
  exact congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom.hom (x : ↥X.X₁.V)) X.zero

/-- **The vector of the quotient killed by the number attached to a vector of the sub whose image
is a multiple.** -/
def preTorsion : ↥(preMultiples X m) →ₗ[k] ↥(nsmulTorsion X.X₃ m).V :=
  LinearMap.codRestrict (LinearMap.ker (nsmulLinear k m ↥X.X₃.V))
    (X.g.hom.hom ∘ₗ preDivide X m htf) (preDivide_mem_ker X m htf)

theorem preTorsion_coe (x : ↥(preMultiples X m)) :
    (preTorsion X m htf x).1 = X.g.hom.hom (preDivide X m htf x) :=
  rfl

/-- **Every vector of the quotient killed by the number comes from a vector of the sub whose image
is a multiple.** -/
theorem preTorsion_surjective (hX : X.ShortExact) :
    Function.Surjective (preTorsion X m htf) := by
  rintro ⟨e, he⟩
  obtain ⟨y, rfl⟩ := shortExact_surjective hX e
  have h0 : X.g.hom.hom (m • y) = 0 := by
    rw [map_nsmul]
    exact LinearMap.mem_ker.mp he
  obtain ⟨x, hx⟩ : m • y ∈ LinearMap.range X.f.hom.hom := by
    rw [shortExact_range_eq_ker hX]
    exact LinearMap.mem_ker.mpr h0
  have hxmem : x ∈ preMultiples X m := by
    show X.f.hom.hom x ∈ LinearMap.range (nsmulLinear k m ↥X.X₂.V)
    rw [hx]
    exact ⟨y, rfl⟩
  refine ⟨⟨x, hxmem⟩, Subtype.ext ?_⟩
  rw [preTorsion_coe, preDivide_eq X m htf ⟨x, hxmem⟩ y hx.symm]

theorem preTorsion_rho (g : G) (x : ↥(preMultiples X m)) :
    preTorsion X m htf ⟨X.X₁.ρ g (x : ↥X.X₁.V), preMultiples_rho_mem X m g x⟩
      = (nsmulTorsion X.X₃ m).ρ g (preTorsion X m htf x) := by
  refine Subtype.ext ?_
  have hd : preDivide X m htf ⟨X.X₁.ρ g (x : ↥X.X₁.V), preMultiples_rho_mem X m g x⟩
      = X.X₂.ρ g (preDivide X m htf x) := by
    refine preDivide_eq X m htf _ _ ?_
    rw [← map_nsmul, nsmul_preDivide]
    exact (LinearMap.congr_fun (hom_equivariant X.f g) (x : ↥X.X₁.V)).symm
  rw [preTorsion_coe, hd]
  exact LinearMap.congr_fun (hom_equivariant X.g g) (preDivide X m htf x)

/-- A vector of the sub which is a multiple has trivial image in the vectors of the quotient killed
by the number. -/
theorem ker_preClass_le_ker_preTorsion (x : ↥(preMultiples X m)) (h : preClass X m x = 0) :
    preTorsion X m htf x = 0 := by
  rw [preClass_eq_zero_iff] at h
  obtain ⟨x', hx'⟩ := h
  simp only [nsmulLinear_apply] at hx'
  have hd : preDivide X m htf x = X.f.hom.hom x' := by
    refine preDivide_eq X m htf x _ ?_
    rw [← map_nsmul, hx']
  refine Subtype.ext ?_
  rw [preTorsion_coe, hd]
  exact congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom.hom x') X.zero

/-- A vector of the sub with trivial image in the vectors of the quotient killed by the number is
itself a multiple. -/
theorem ker_preTorsion_le_ker_preClass (hX : X.ShortExact) (x : ↥(preMultiples X m))
    (h : preTorsion X m htf x = 0) : preClass X m x = 0 := by
  have h1 : X.g.hom.hom (preDivide X m htf x) = 0 := congrArg Subtype.val h
  obtain ⟨x', hx'⟩ : preDivide X m htf x ∈ LinearMap.range X.f.hom.hom := by
    rw [shortExact_range_eq_ker hX]
    exact LinearMap.mem_ker.mpr h1
  have h2 : X.f.hom.hom ((x : ↥X.X₁.V) - m • x') = X.f.hom.hom 0 := by
    rw [map_sub, map_nsmul, hx', nsmul_preDivide, sub_self, map_zero]
  have h3 : (x : ↥X.X₁.V) = m • x' := sub_eq_zero.1 (shortExact_injective hX h2)
  rw [preClass_eq_zero_iff, h3]
  exact ⟨x', rfl⟩

/-- The lower kernel, presented by the vectors of the sub whose image is a multiple. -/
def modTorLift :
    (↥(preMultiples X m) ⧸ LinearMap.ker (preClass X m)) →ₗ[k] ↥(modTorObj X m).V :=
  Submodule.liftQ _ (preClass X m) le_rfl

theorem modTorLift_bijective : Function.Bijective (modTorLift X m) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (preClass X m)) z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hz
  · intro w
    obtain ⟨x, rfl⟩ := preClass_surjective X m w
    exact ⟨Submodule.mkQ (LinearMap.ker (preClass X m)) x, rfl⟩

/-- The vectors of the quotient killed by the number, presented by the vectors of the sub whose
image is a multiple. -/
def torsionLift :
    (↥(preMultiples X m) ⧸ LinearMap.ker (preClass X m)) →ₗ[k] ↥(nsmulTorsion X.X₃ m).V :=
  Submodule.liftQ _ (preTorsion X m htf) fun x hx =>
    LinearMap.mem_ker.mpr (ker_preClass_le_ker_preTorsion X m htf x (LinearMap.mem_ker.mp hx))

theorem torsionLift_bijective (hX : X.ShortExact) :
    Function.Bijective (torsionLift X m htf) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (preClass X m)) z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr (ker_preTorsion_le_ker_preClass X m htf hX x hz)
  · intro w
    obtain ⟨x, rfl⟩ := preTorsion_surjective X m htf hX w
    exact ⟨Submodule.mkQ (LinearMap.ker (preClass X m)) x, rfl⟩

/-- **The lower kernel of a reduced presentation is the vectors of the quotient killed by the
number**, when the number acts on the middle term without torsion. -/
def modTorTorsionEquiv (hX : X.ShortExact) :
    ↥(modTorObj X m).V ≃ₗ[k] ↥(nsmulTorsion X.X₃ m).V :=
  (LinearEquiv.ofBijective (modTorLift X m) (modTorLift_bijective X m)).symm.trans
    (LinearEquiv.ofBijective (torsionLift X m htf) (torsionLift_bijective X m htf hX))

theorem modTorTorsionEquiv_preClass (hX : X.ShortExact) (x : ↥(preMultiples X m)) :
    modTorTorsionEquiv X m htf hX (preClass X m x) = preTorsion X m htf x := by
  have h : (LinearEquiv.ofBijective (modTorLift X m) (modTorLift_bijective X m)).symm
      (preClass X m x) = Submodule.mkQ (LinearMap.ker (preClass X m)) x :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  show (LinearEquiv.ofBijective (torsionLift X m htf) (torsionLift_bijective X m htf hX))
      ((LinearEquiv.ofBijective (modTorLift X m) (modTorLift_bijective X m)).symm
        (preClass X m x)) = preTorsion X m htf x
  rw [h]
  rfl

theorem modTorTorsionEquiv_equivariant (hX : X.ShortExact) (g : G) :
    (modTorTorsionEquiv X m htf hX).toLinearMap ∘ₗ (modTorObj X m).ρ g
      = (nsmulTorsion X.X₃ m).ρ g ∘ₗ (modTorTorsionEquiv X m htf hX).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := preClass_surjective X m z
  show modTorTorsionEquiv X m htf hX ((modTorObj X m).ρ g (preClass X m x))
    = (nsmulTorsion X.X₃ m).ρ g (modTorTorsionEquiv X m htf hX (preClass X m x))
  rw [← preClass_rho, modTorTorsionEquiv_preClass, modTorTorsionEquiv_preClass]
  exact preTorsion_rho X m htf g x

/-- **The lower kernel of a reduced presentation is the vectors of the quotient killed by the
number**, as representations. -/
def modTorTorsionIso (hX : X.ShortExact) : modTorObj X m ≅ nsmulTorsion X.X₃ m :=
  Action.mkIso (modTorTorsionEquiv X m htf hX).toModuleIso fun g =>
    ModuleCat.hom_ext (modTorTorsionEquiv_equivariant X m htf hX g)

end Torsion

/-! ### The shift of the degree by two -/

section Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (X : ShortComplex (Rep ℤ G))
  (W : Rep ℤ G)

omit [Finite G] in
theorem tensorModCycleSeq_shortExact (hX : X.ShortExact) :
    (tensorSeq W (modCycleSeq X p)).ShortExact :=
  tensorSeq_shortExact_of_nsmul (modCycleSeq_shortExact X p hX) W (nsmul_modNsmul_eq_zero X.X₂ p)

omit [Finite G] in
theorem tensorModTorSeq_shortExact (hX : X.ShortExact) :
    (tensorSeq W (modTorSeq X p)).ShortExact :=
  tensorSeq_shortExact_of_nsmul (modTorSeq_shortExact X p hX) W (nsmul_modNsmul_eq_zero X.X₁ p)

omit [Fact p.Prime] in
/-- **A reduction modulo a prime tensored with coefficients killed by that prime has no complete
cohomology** as soon as the representation itself has none after tensoring. -/
theorem isZero_tateModule_tensorObj_modNsmul (A : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)
    (h : ∀ i : ℤ, Limits.IsZero (tateModule (tensorObj A W) i)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (modNsmul A p) W) n) :=
  isZero_tateModule_of_iso (tensorModNsmulIso A W p hW).symm n (h n)

/-- **The complete cohomology of the quotient of a presentation tensored with coefficients killed
by a prime, in a degree, is the complete cohomology of the vectors of the quotient killed by the
prime, tensored with the same coefficients, two degrees higher**, whenever the prime acts on the
middle term of the presentation without torsion and the two other terms have no complete cohomology
after tensoring. -/
def tensorPTorsionShiftEquiv (hX : X.ShortExact) (htf : ∀ y : ↥X.X₂.V, p • y = 0 → y = 0)
    (hW : ∀ w : ↥W.V, p • w = 0)
    (h₁ : ∀ i : ℤ, Limits.IsZero (tateModule (tensorObj X.X₁ W) i))
    (h₂ : ∀ i : ℤ, Limits.IsZero (tateModule (tensorObj X.X₂ W) i)) (n : ℤ) :
    ↥(tateModule (tensorObj X.X₃ W) n) ≃ₗ[ℤ]
      ↥(tateModule (tensorObj (nsmulTorsion X.X₃ p) W) (n + 1 + 1)) :=
  ((tateMapIso (tensorModNsmulIso X.X₃ W p hW) n).toLinearEquiv.trans
      (LinearEquiv.ofBijective (tateδ (tensorModCycleSeq_shortExact (p := p) X W hX) n).hom
        (bijective_tateδ (tensorModCycleSeq_shortExact (p := p) X W hX) n
          (isZero_tateModule_tensorObj_modNsmul W X.X₂ hW h₂ n)
          (isZero_tateModule_tensorObj_modNsmul W X.X₂ hW h₂ (n + 1))))).trans
    ((LinearEquiv.ofBijective (tateδ (tensorModTorSeq_shortExact (p := p) X W hX) (n + 1)).hom
        (bijective_tateδ (tensorModTorSeq_shortExact (p := p) X W hX) (n + 1)
          (isZero_tateModule_tensorObj_modNsmul W X.X₁ hW h₁ (n + 1))
          (isZero_tateModule_tensorObj_modNsmul W X.X₁ hW h₁ (n + 1 + 1)))).trans
      (tateMapIso (tensorIsoLeft W (modTorTorsionIso X p htf hX)) (n + 1 + 1)).toLinearEquiv)

end Assembly

/-! ### The presentation by the free cover -/

section Free

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The free cover of a representation still has no complete cohomology after restriction to a
subgroup.** -/
theorem isZero_tateModule_resObj_freeObj (H : Subgroup G) (A : Rep k G) (n : ℤ) :
    Limits.IsZero (tateModule (resObj H (freeObj A)) n) :=
  isZero_tateModule_resObj_indObj H (Rep.of (Representation.trivial k G (↥A.V →₀ k))) n

/-- **The free cover of a representation has no complete cohomology after tensoring with any
representation.** -/
theorem isZero_tateModule_tensorObj_freeObj (A W : Rep k G) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (freeObj A) W) n) :=
  isZero_tateModule_tensorObj_inducedRep (↥A.V →₀ k) W n

/-- **The kernel of the free cover of a representation with no complete cohomology on a subgroup
has none there either.** -/
theorem isZero_tateModule_resObj_kerObj_freeHom (A : Rep k G) (H : Subgroup G)
    (hA : ∀ i : ℤ, Limits.IsZero (tateModule (resObj H A) i)) (n : ℤ) :
    Limits.IsZero (tateModule (resObj H (kerObj (freeHom A))) n) := by
  have hS : (resSeq H (kerSeq (freeHom A))).ShortExact :=
    resSeq_shortExact (kerSeq_shortExact _ (freeHom_surjective A)) H
  refine isZero_tateModule_congr (show n - 1 + 1 = n by ring) ?_
  refine isZero_of_forall_eq_zero fun y => ?_
  obtain ⟨z, rfl⟩ := surjective_tateδ hS (n - 1)
    (isZero_tateModule_resObj_freeObj H A (n - 1 + 1)) y
  rw [eq_zero_of_isZero (hA (n - 1)) z, map_zero]

end Free

section FreeShift

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **The complete cohomology of a representation tensored with coefficients killed by a prime, in
a degree, is the complete cohomology of the vectors it kills, tensored with the same coefficients,
two degrees higher**, whenever the restriction of the representation to every Sylow subgroup for
the prime has no complete cohomology. -/
def tensorPTorsionShiftFreeEquiv (E W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)
    (hE : ∀ P : Sylow p G, ∀ i : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) E) i)) (n : ℤ) :
    ↥(tateModule (tensorObj E W) n) ≃ₗ[ℤ]
      ↥(tateModule (tensorObj (nsmulTorsion E p) W) (n + 1 + 1)) :=
  let hp : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  tensorPTorsionShiftEquiv (kerSeq (freeHom E)) W
    (kerSeq_shortExact _ (freeHom_surjective E)) (nsmul_eq_zero_freeObj E hp) hW
    (fun i => isZero_tateModule_tensorObj_of_torsionFree_nsmul (kerObj (freeHom E)) W hW
      (nsmul_eq_zero_kerObj _ (nsmul_eq_zero_freeObj E hp))
      (fun P j => isZero_tateModule_resObj_kerObj_freeHom E (P : Subgroup G) (hE P) j) i)
    (fun i => isZero_tateModule_tensorObj_freeObj E W i) n

end FreeShift

end

end InverseGalois.CFT.Tate
