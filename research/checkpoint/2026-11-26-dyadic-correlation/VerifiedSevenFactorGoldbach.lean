import VerifiedMixedBrunFactorCount
import VerifiedSevenFactorParameters
import VerifiedFixedRatioSemiprimes
namespace GoldbachPartial
open Finset Filter
open scoped Classical

set_option exponentiation.threshold 500 in
/-- At each large even target, many distinct primes have a squarefree rough
complement with at most seven prime factors, counted with multiplicity. -/
theorem fixed_target_seven_factors :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (sevenBrunSmall n) 7
      (n:ℝ)/(25165824*Real.log n) ≤ ∑p∈S, Real.log p ∧
      (n:ℝ)/(25165824*(Real.log n)^2) ≤ (S.card:ℝ) := by
  have geo : ∀ᶠ n : ℕ in atTop, 2≤sevenBrunSmall n ∧ sevenBrunSmall n≤halfLevelBrunLarge n ∧
      halfLevelBrunLarge n≤n/4 ∧ n<(halfLevelBrunLarge n)^(2+1) ∧ n≤(sevenBrunSmall n)^432 := by
    filter_upwards [sevenBrun_geometry] with n h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2.1⟩
  have h := mixed_brunsieve_count sevenBrunIndex halfLevelBrunLarge 2 6 432 (519/100)
    (by decide) (by norm_num) sevenBrunSmall_tendsto geo (fun _ hε => sevenBrun_distribution hε) sevenBrun_medium_weight
  simpa only [sevenBrunSmall,show 2+6-1=7 by decide,Nat.cast_ofNat,show (4194304:ℝ)*6=25165824 by norm_num] using h

end GoldbachPartial