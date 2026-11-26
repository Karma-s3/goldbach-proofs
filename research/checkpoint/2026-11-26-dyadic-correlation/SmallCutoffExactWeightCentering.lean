import WeightedTerminalCentering
import ExactRamanujanWeightBound

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

/-- Extending finite divisor weights by zero preserves the actual centered wave pointwise. -/
theorem weightedMangoldtKernel_extend_zero {P R : ℕ} (hPR : P≤R) (n : ℕ) (a : ℕ→ℂ) :
    weightedMangoldtKernel n R (fun d => if d≤P then a d else 0)=weightedMangoldtKernel n P a := by
  have heq (t : ℝ) : smallDivisorWave n (Icc 1 R) (fun d => if d≤P then a d else 0) t=
      smallDivisorWave n (Icc 1 P) a t := by
    have hi : (Icc 1 R).filter (fun d => d≤P)=Icc 1 P := by
      ext d
      simp only [mem_filter,mem_Icc];omega
    unfold smallDivisorWave
    simp only [ite_mul,zero_mul,←sum_filter,hi]
  unfold weightedMangoldtKernel
  simp_rw [heq]

/-- Uniformity in the weights is retained when the divisor cutoff is reduced. -/
theorem weighted_terminal_kernel_error_below_cutoff :
    ∀ᶠ n : ℕ in atTop,∀ P : ℕ, P≤terminalPrimeArcCutoff n →∀ a : ℕ→ℂ,
      (∀ d∈Icc 1 P, ‖a d‖≤8*(1+Real.log n)) →
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-(∫ t in highNaturalPrimeTubes n,
        weightedMangoldtKernel n P a t)‖≤95000000*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  filter_upwards [weighted_terminal_kernel_error] with n h
  intro P hP a ha
  let b := fun d : ℕ => if d≤P then a d else 0
  have hb (d : ℕ) (hd : d∈Icc 1 (terminalPrimeArcCutoff n)) : ‖b d‖≤8*(1+Real.log n) := by
    dsimp only [b]
    by_cases hdp : d≤P
    · rw [ite_eq_left hdp];exact ha d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,hdp⟩)
    · rw [ite_eq_right hdp,norm_zero];positivity
  have h' := h b hb
  rw [show weightedMangoldtKernel n _ b=weightedMangoldtKernel n P a from weightedMangoldtKernel_extend_zero hP n a] at h'
  exact h'

theorem medDeskQ_exactWeight_kernel_error :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,weightedMangoldtKernel n (medDeskQ n)
        (fun d => (exactRamanujanWeight (medDeskQ n) d:ℂ)) t)‖≤95000000*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  filter_upwards [weighted_terminal_kernel_error_below_cutoff,eventually_core_cutoffs,squareRootLogShell_geometry]
    with n h hc hg
  have hP : medDeskQ n≤medDeskD n := hc.1.trans (hc.2.1.trans hc.2.2.1)
  have hPR : medDeskQ n≤terminalPrimeArcCutoff n := hP.trans hg.2.1
  apply h _ hPR
  intro d hd
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply (exactRamanujanWeight_abs_le_log _ d).trans
  have hp0 : 0<medDeskQ n := (mem_Icc.mp hd).1.trans (mem_Icc.mp hd).2
  have hPn : medDeskQ n≤n := hPR.trans hg.2.2.2.1
  gcongr

theorem medDeskQ_exactWeight_kernel_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,weightedMangoldtKernel n (medDeskQ n)
        (fun d => (exactRamanujanWeight (medDeskQ n) d:ℂ)) t)‖≤ε*(n:ℝ) := by
  have hL : Tendsto (fun n : ℕ => 1+Real.log (n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim := (Real.tendsto_sqrt_atTop.comp hL).eventually_ge_atTop (95000000/ε)
  filter_upwards [medDeskQ_exactWeight_kernel_error,hlim] with n he hn
  apply he.trans
  have hpos : 0<Real.sqrt (1+Real.log (n:ℝ)) := by positivity
  apply (div_le_iff₀ hpos).mpr
  change 95000000/ε≤Real.sqrt (1+Real.log (n:ℝ)) at hn
  have hh := (div_le_iff₀ hε).mp hn
  nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) n)]

end GoldbachPartial
