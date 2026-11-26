import PinnedUpstream316
import InteriorMobiusTailBudget

namespace GoldbachPartial
open Filter

/-- Fully replayed major-arc and Fourier estimates yield the frozen goal from this
single inequality on the still-uncontrolled signed expression for each even n. -/
theorem frozen_floor_of_interior_tail
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ) ≤ interiorMobiusTail n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hm := GoldbachMajorArc.verified_major_floor_below_nine_eighths (35/32) (by norm_num)
  obtain ⟨N,hN⟩ := dyadic_floor_from_interior_major_budget hm htail
  exact ⟨1/16,N,by norm_num,hN⟩

end GoldbachPartial
