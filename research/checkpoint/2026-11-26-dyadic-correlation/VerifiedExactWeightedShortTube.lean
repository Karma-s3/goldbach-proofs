import ExactWeightedShortTube
import ExactCenteredFrequencyEnergy
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

theorem phasedInterval_linear_error (h:ℤ) (r:ℝ) (hr:0≤r) :
    ‖(∫t in -r..r,E ((h:ℝ)*t))-((2*r:ℝ):ℂ)‖≤2*Real.pi*(h.natAbs:ℝ)*r^2 := by
  have hI : (∫_t in -r..r,(1:ℂ))=((2*r:ℝ):ℂ) := by
    rw [intervalIntegral.integral_const];simp only [Complex.real_smul,mul_one];congr 1;ring
  rw [←hI,←intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable;unfold E;fun_prop)
    (continuous_const.intervalIntegrable _ _)]
  have hpoint (t:ℝ) : ‖E ((h:ℝ)*t)-1‖≤(2*Real.pi*(h.natAbs:ℝ))*|t| := by
    unfold E;rw [mul_comm _ Complex.I]
    apply Real.norm_exp_I_mul_ofReal_sub_one_le.trans
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi),abs_mul,
      ←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast];apply le_of_eq;ring
  have hid (a b:ℝ) : (∫t in a..b,t)=b^2/2-a^2/2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x:ℝ=>x^2/2)
    · intro x _
      convert ((hasDerivAt_id x).pow 2).div_const (2:ℝ) using 1 <;> simp
    · exact continuous_id.intervalIntegrable _ _
  have hint : (∫t in -r..r,|t|)=r^2 := by
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (continuous_abs.intervalIntegrable (μ:=volume) (-r) 0)
      (continuous_abs.intervalIntegrable (μ:=volume) 0 r)]
    have h₁ : (∫t in -r..0,|t|)=(∫t in -r..0, -t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact abs_of_nonpos ht.2
    have h₂ : (∫t in (0:ℝ)..r,|t|)=(∫t in (0:ℝ)..r,t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hr] at ht
      exact abs_of_nonneg ht.1
    rw [h₁,h₂,intervalIntegral.integral_neg,hid,hid];ring
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : -r≤r)).trans
  calc _ ≤ ∫t in -r..r,(2*Real.pi*(h.natAbs:ℝ))*|t| := by
         apply intervalIntegral.integral_mono_on (by linarith)
           (by apply Continuous.intervalIntegrable;unfold E;fun_prop)
           (by apply Continuous.intervalIntegrable;fun_prop)
         intro t _;exact hpoint t
       _ = _ := by rw [intervalIntegral.integral_const_mul,hint]

theorem exactWeighted_high_short_eventually {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      ‖(∫t in highNaturalPrimeTubes n,exactWeightedOffTarget n (medDeskQ n) t)-
        (∫t in highNaturalPrimeTubes n,exactWeightedFarOffTarget n (medDeskQ n) (exactWeightedShortCutoff n) t)‖ ≤ ε*(n:ℝ) :=
  exactWeighted_high_short_small_of_energy medDeskQ (C:=28) (by norm_num) exactCentered_full_energy hε

theorem exactWeighted_high_short_integral_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,‖∫t in highNaturalPrimeTubes n,
      exactWeightedShortPolynomial n (medDeskQ n) (exactWeightedShortCutoff n) t‖ ≤ ε*(n:ℝ) := by
  filter_upwards [exactWeighted_high_short_eventually hε,highNaturalPrimeTubes_geometry] with n hn hg
  simpa only [exactWeightedOffTarget_integral_delete n _ _ hg.1] using hn

theorem exactWeighted_high_short_explicit :
    ∀ᶠ n:ℕ in atTop,‖∫t in highNaturalPrimeTubes n,
      exactWeightedShortPolynomial n (medDeskQ n) (exactWeightedShortCutoff n) t‖ ≤
        ((32+16*Real.pi)*28)*(n:ℝ)/(1+Real.log (terminalPrimeArcLog n)) := by
  filter_upwards [exactWeighted_high_short_rate 28 (by norm_num),exactCentered_full_energy,
    highNaturalPrimeTubes_geometry] with n hr he hg
  simpa only [exactWeightedOffTarget_integral_delete n _ _ hg.1] using hr (medDeskQ n) he
end GoldbachPartial
