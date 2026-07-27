/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamilyOdd
import InverseGalois.Hilbert.AlternatingFamilyAnalytic
import InverseGalois.Hilbert.AlternatingFamilyOddDescent

/-!
# The explicit `Aₙ`-family (Serre §4.5) — **odd-`n`** analytic (monodromy) half

Companion to `Hilbert/AlternatingFamilyOdd.lean` (the odd-`n` *algebraic* stack:
`serreAnFamilyOdd`, monic/degree/derivative, cofinite separability, and the square-discriminant
certificate `serreAnFamilyOdd_disc_isSquare_of_separable`) and a direct mirror of the even-`n`
`Hilbert/AlternatingFamilyAnalytic.lean`.

For odd `n` the base family `(n−1)Xⁿ − nX^{n-1} + T` has a *conic* discriminant
`∼ (−1)^{(n−1)/2}·n·T(T−1)`, rationally parametrised by `T = k/(k−U²)`; clearing denominators and
rescaling lands back in `ℚ[U][Y]` as the monic family `serreAnFamilyOdd n`.  The algebraic side is
already complete; this file supplies the odd-`n` analogues of the three analytic inputs of
`exists_alternating_resolvent_family`:

* `exists_altResolvent_odd` — the descended `Aₙ`-orbit resolvent `G` of `serreAnFamilyOdd n`
  (monic, `Y`-degree `n!/2`, coupled via `IsAltResolvent`, with a root in each specialised
  splitting field);
* `anResolvent_irreducible_odd` / `anResolvent_abs_irreducible_odd` — its irreducibility and
  **absolute** irreducibility (the odd-`n` geometric monodromy `= Aₙ`).

Each is the odd sibling of the correspondingly-named even lemma in `AlternatingFamilyAnalytic`; the
δ-descent and monodromy machinery that discharges the even versions
(`Hilbert/AlternatingFamilyDescent.lean`, `Resolvent/AlternatingResolventDescent.lean`,
`Hilbert/AlternatingFamilyMonodromy.lean`) has odd analogues still to be built, so these three sit
as `sorry` leaves — but the *assembly* of the odd branch of `exists_alternating_resolvent_family`
from them plus the (proved) odd algebraic lemmas is exactly parallel to the even branch.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

open AlternatingResolvent ResolventFamily

/-- **[odd resolvent core — descent, `sorry`]** For the odd-`n` conic family `serreAnFamilyOdd n`
there is a descended `Aₙ`-orbit resolvent `G ∈ ℚ[U][Y]`, monic of `Y`-degree `n!/2`, coupled to
`F = serreAnFamilyOdd n` via `IsAltResolvent`, with a root of `G(t)` inside the splitting field of
`F(t)` for every `t`.

Odd sibling of `AlternatingFamily.exists_altResolvent`.  The descent of the `Aₙ`-invariant
coefficients to `ℚ(U)` uses that they live in `ℚ[e₁,…,eₙ][δ]` with `δ = √disc F`, rational because
`disc F` is a square (the odd certificate `serreAnFamilyOdd_disc_isSquare_of_separable`, valid for
`Odd n`); the odd analogue of `Resolvent/AlternatingResolventDescent.lean` supplies the
polynomial-level `δ`-lift and the general-specialisation discriminant identity. -/
theorem exists_altResolvent_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    ∃ G : Polynomial (Polynomial ℚ), G.Monic ∧ G.natDegree = n.factorial / 2 ∧
      IsAltResolvent n (serreAnFamilyOdd n) G ∧
      (∀ t : ℤ, ∃ α : (specialize (serreAnFamilyOdd n) t).SplittingField,
        (aeval α) (specialize G t) = 0) := by
  obtain ⟨G, hm, hd, hres⟩ := exists_descended_altResolvent_odd n hn hodd
  exact ⟨G, hm, hd, hres, altResolvent_root_property_odd n hn G hres⟩

/-- **[odd monodromy core — geometric, `sorry`]** The descended resolvent `G` of
`serreAnFamilyOdd n` is **absolutely irreducible**: the geometric monodromy group over `ℚ̄(U)` is
exactly `Aₙ`.  Odd sibling of `AlternatingFamily.anResolvent_abs_irreducible`; the odd analogue of
the `AlternatingFamilyMonodromy` decomposition (geometric irreducibility + preprimitivity +
3-cycle inertia, all `≤ Aₙ` by the square-discriminant certificate) discharges it. -/
theorem anResolvent_abs_irreducible_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ))
    (hGmonic : G.Monic) (hG : IsAltResolvent n (serreAnFamilyOdd n) G) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  sorry

/-- **[odd monodromy core — arithmetic, proved from the absolute version]** The descended resolvent
`G` of `serreAnFamilyOdd n` is **irreducible** over `ℚ(U)`.  Odd sibling of
`AlternatingFamily.anResolvent_irreducible`; descends from absolute irreducibility along the base
change `ℚ[U] → ℚ̄[U]` by Gauss (`Monic.irreducible_of_irreducible_map`), exactly as in the even
case. -/
theorem anResolvent_irreducible_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ))
    (hGmonic : G.Monic) (hG : IsAltResolvent n (serreAnFamilyOdd n) G) :
    Irreducible G :=
  hGmonic.irreducible_of_irreducible_map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) G
    (anResolvent_abs_irreducible_odd n hn hodd G hGmonic hG)

end AlternatingFamily

end
