import PinnedUpstream316
import SignedMajorCharging
import Batteries.Tactic.OpenPrivate

open private GoldbachMajorArc.reindex_denominators from PinnedUpstream316

namespace GoldbachPartial
open Finset

/-- Decompose the weighted denominator sum into signed local prime factors. -/
theorem weightedCoefficient_powerset (P n : ℕ) (W : ℕ → ℝ)
    (hcut : ∀ q, P < q → W q = 0) :
    (∑ q ∈ Icc 1 P, (GoldbachMajorArc.coefficient q n).re * W q) =
      ∑ t ∈ ((range (P+1)).filter Nat.Prime).powerset,
        (∏ p ∈ t, majorPrimeLocal p n) * W (∏ p ∈ t,p) :=
  GoldbachMajorArc.reindex_denominators P n W hcut

end GoldbachPartial
