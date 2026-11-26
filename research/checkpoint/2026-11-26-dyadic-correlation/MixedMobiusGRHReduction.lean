import MixedMobiusTailBudget
import PinnedMajorGRHError

namespace GoldbachPartial
open Filter

/-- The GRH interface discharges the entire pinned major-arc comparison.
Only the pointwise signed bound on the remaining minor-arc expression is needed. -/
theorem frozen_floor_of_mixed_tail_of_grh (hψ : grhAllUniform)
    (tail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ) ≤ mixedMobiusTail n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) :=
  frozen_floor_from_mixed_mobius_tail
    (Pinned316.GoldbachMajorArc.GRHError.totalArcError_sublinear_of_grh hψ) tail

end GoldbachPartial