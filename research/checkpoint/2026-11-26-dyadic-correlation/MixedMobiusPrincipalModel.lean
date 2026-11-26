import MixedMobiusModelComparison
import ResonantHighArcModel
import PinnedMajorGRHError

namespace GoldbachPartial
open Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

noncomputable def resonantPrincipalModel (n q : ℕ) (β : ℝ) : ℂ :=
  (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*dirichletGeometricKernel n β

/-- Only the factor linear in the resonant wave is approximated here. -/
theorem terminalMixedTerm_model_bound (hψ : grhAllUniform) :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n;let Q := naturalTubeScale n
      ‖nonresonantMobiusRemainderMass n R R Q-modelMixedMobiusMass n R R Q (resonantPrincipalModel n)‖ ≤
        3000004*(n:ℝ)/(1+Real.log n) := by
  apply mixedMobiusModel_terminal_error resonantPrincipalModel
  · intro n q
    unfold resonantPrincipalModel dirichletGeometricKernel E
    fun_prop
  · filter_upwards [resonantMobius_geometric_high_pointwise hψ] with n h
    intro j hj β hβ
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hj
    apply h (j+1) (by omega) (by omega) β
    exact abs_le.mpr hβ

theorem terminalMixedTerm_model_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n;let Q := naturalTubeScale n
      ‖nonresonantMobiusRemainderMass n R R Q-modelMixedMobiusMass n R R Q (resonantPrincipalModel n)‖ ≤ ε*n := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (3000004/ε)
  filter_upwards [terminalMixedTerm_model_bound hψ,hl] with n h hn
  apply h.trans
  change 3000004/ε≤Real.log (n:ℝ) at hn
  apply (div_le_iff₀ (by positivity : 0<1+Real.log (n:ℝ))).mpr
  have hz := (div_le_iff₀ hε).mp hn
  nlinarith only [mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (α:=ℝ) n),mul_nonneg hε.le (Nat.cast_nonneg (α:=ℝ) n)]

end GoldbachPartial