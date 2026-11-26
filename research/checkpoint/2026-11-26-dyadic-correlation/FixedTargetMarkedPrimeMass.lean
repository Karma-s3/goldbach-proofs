import FixedTargetBrunBonferroni

namespace GoldbachPartial
open Finset
open scoped Classical

/-- Each medium prime factor of a real surviving complement is counted once. -/
noncomputable def fixedTargetMarkedPrimeMass (n y : ℕ) (R : Finset ℕ) : ℝ :=
  ∑ r∈R,∑k∈(fixedTargetBrunPrimeSurvivors n y).filter (fun k=>r∣n-k),Real.log k

theorem fixedTargetMarkedPrimeMass_by_complement (n y : ℕ) (R : Finset ℕ) :
    fixedTargetMarkedPrimeMass n y R =
    ∑ k∈fixedTargetBrunPrimeSurvivors n y,((R.filter (fun r=>r∣n-k)).card:ℝ)*Real.log k := by
  unfold fixedTargetMarkedPrimeMass
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [←sum_filter,sum_const,nsmul_eq_mul]

end GoldbachPartial