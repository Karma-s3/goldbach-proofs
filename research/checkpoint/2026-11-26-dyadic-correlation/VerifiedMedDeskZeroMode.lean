import VerifiedMedDeskProgression
import ExactWeightedKernelZeroMode

namespace GoldbachPartial
open Finset Filter
open scoped Topology

noncomputable def exactWeightCrtError (n R : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
    exactRamanujanWeight R d * exactRamanujanWeight R e * crtRowError n d e

theorem exactWeightCrtError_abs_le (n R : ℕ) :
    |exactWeightCrtError n R| ≤ (R:ℝ)^2 * (8*(1+Real.log R))^2 := by
  let I := Icc 1 R
  let B := 8*(1+Real.log R)
  have hB : 0 ≤ B := by dsimp only [B]; linarith [Real.log_natCast_nonneg R]
  unfold exactWeightCrtError
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ d ∈ I, ∑ _e ∈ I, B^2 := by
      refine sum_le_sum fun d hd => (abs_sum_le_sum_abs ..).trans (sum_le_sum fun e he => ?_)
      rw [abs_mul,abs_mul,sq]
      exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (crtRowError_abs_le_one (mem_Icc.mp hd).1 (mem_Icc.mp he).1)).trans
          (mul_le_mul (exactRamanujanWeight_abs_le_log R d) (exactRamanujanWeight_abs_le_log R e)
            (abs_nonneg _) hB)
    _ = _ := by simp [I, B, sq, nsmul_eq_mul, mul_assoc]

theorem exactWeightCrtError_medDesk_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |exactWeightCrtError n (medDeskQ n)| ≤ ε*(n:ℝ) := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^8/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (8:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [h.eventually_lt_const (by positivity : (0:ℝ)<ε/4194304),
    eventually_ge_atTop (2:ℕ)] with n hp hn
  let R := medDeskQ n
  let L := Real.log n
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hR : 1≤R := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have hld : 1+Real.log R≤(R:ℝ) := by
    have h' := Real.log_le_sub_one_of_pos (show 0<(R:ℝ) by exact_mod_cast hR)
    linarith
  have hB : 0≤8*(1+Real.log R) := by linarith [Real.log_natCast_nonneg R]
  have hcut : (R:ℝ)≤16*L^2 := GoldbachMajorArc.cutoff_le_log_sq hn
  have hbig : (R:ℝ)^2*(8*(1+Real.log R))^2 ≤ 64*(R:ℝ)^4 := by
    calc _ ≤ (R:ℝ)^2*(8*(R:ℝ))^2 := by gcongr
         _ = _ := by ring
  have hnum := (div_lt_iff₀ hnpos).mp hp
  apply (exactWeightCrtError_abs_le n R).trans (hbig.trans _)
  calc
    _ ≤ 64*(16*L^2)^4 := by gcongr
    _ = 4194304*L^8 := by ring
    _ ≤ _ := by linarith only [hnum]

theorem crtLambdaConvolution_eventually_approx_corr {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |crtLambdaConvolution n - corr n|≤ε*(n:ℝ) := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^2/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [h.eventually_lt_const (by positivity : (0:ℝ)<ε/4),
    eventually_ge_atTop (1:ℕ)] with n hu hn
  obtain ⟨hl,hr⟩ := crtLambdaConvolution_prime_error hn
  rw [abs_of_nonneg hl]
  apply hr.trans
  have hS : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h' := (div_lt_iff₀ hS).mp hu
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith only [mul_le_mul_of_nonneg_left h'.le hS.le,
    congrArg (fun x : ℝ => ε*x) hsq]

/-- Uniform at the fixed major-arc cutoff. All inputs use the original
verified progression estimate at logarithmic moduli. -/
theorem exactWeightedZeroMode_medDesk_approx_corr {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      |exactWeightedZeroMode n (medDeskQ n) -
        (corr n - ((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n (medDeskQ n))| ≤ ε*(n:ℝ) := by
  filter_upwards [crtLambdaConvolution_eventually_approx_corr (ε:=ε/4) (by positivity),
    exactWeightCrtError_medDesk_small (ε:=ε/4) (by positivity),
    exactRamanujanWeight_medDeskProgression_small (ε:=ε/4) (by positivity)] with n hΛ hcrt hprog
  let R := medDeskQ n
  let A := ∑ d ∈ Icc 1 R, exactRamanujanWeight R d * primeSmallProgressionError n d
  have ha : |A| ≤ ε/4*(n:ℝ) := (abs_sum_le_sum_abs ..).trans hprog
  have hid : exactWeightedZeroMode n R -
      (corr n - ((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n R) =
      (crtLambdaConvolution n - corr n) + exactWeightCrtError n R - 2*A := by
    rw [exactWeightedZeroMode_arithmetic, exactRamanujanZeroCorrection_eq]
    unfold exactWeightCrtError A
    ring
  rw [hid]
  rw [abs_le] at ha hcrt hΛ ⊢
  change - (ε/4*(n:ℝ)) ≤ exactWeightCrtError n R ∧ _ at hcrt
  constructor <;> linarith only [ha.1,ha.2,hcrt.1,hcrt.2,hΛ.1,hΛ.2]

end GoldbachPartial