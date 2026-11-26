import TerminalMobiusPrimeMass
import PinnedLargeMobiusBudget

namespace GoldbachPartial
open Filter MeasureTheory Pinned316.GoldbachMajorArc
open scoped Topology

theorem terminalMobius_kernel_budget :
    ∀ᶠ n:ℕ in atTop, ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (terminalPrimeArcCutoff n) t)‖≤(n:ℝ)/32 := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop
      ((48000000:ℝ)^2)
  filter_upwards [fullRange_largeMobius_high_error,hl] with n hh hn
  change (48000000:ℝ)^2≤Real.log (n:ℝ) at hn
  have hp : 0 < 1+Real.log (n:ℝ) := by linarith [Real.log_natCast_nonneg n]
  have hs : 48000000≤Real.sqrt (1+Real.log (n:ℝ)) := Real.le_sqrt_of_sq_le (by linarith only [hn])
  apply hh.trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
  linarith only [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) n)]

/-- The high arcs use only d above their lower Farey cutoff. The two major-arc hypotheses
are the error comparison and the sublinear error theorem of the pinned major-arc proof. -/
theorem frozen_floor_from_terminal_mobius_tail
    (herr : ∀ {n : ℕ}, 2*(cutoff n)^2<n →
      ‖majorContribution n-modeledContribution n‖ ≤ totalArcError n)
    (hsmall : Tendsto (fun n : ℕ => totalArcError n/n) atTop (𝓝 0))
    (tail : ∀ᶠ n : ℕ in atTop,Even n → -(n:ℝ) ≤
      primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n +
        (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (terminalPrimeArcCutoff n) t).re) :
    ∃ N : ℕ, ∀ X n:ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      (1/16:ℝ)*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) :=
  pinned_dyadic_floor_of_largeMobius_budget terminalPrimeArcCutoff herr hsmall terminalMobius_kernel_budget tail

end GoldbachPartial