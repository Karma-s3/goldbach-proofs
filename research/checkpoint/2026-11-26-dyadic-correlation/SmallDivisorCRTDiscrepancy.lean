import TruncatedRamanujanSquare
import Mathlib.Data.Int.CardIntervalMod
namespace GoldbachPartial
open Finset Filter
open scoped Topology

private theorem crt_residue_discrepancy (N r z:ℕ) (hr:0<r) :
    |(((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℝ)-(N:ℝ)/r|≤1 := by
  let b := ((N:ℚ)-z)/r
  let a := (-(z:ℚ))/r
  have hr' : (0:ℚ)<r := by exact_mod_cast hr
  have hab : a≤b := by dsimp [a,b];gcongr;linarith
  have hcard := Nat.Ioc_filter_modEq_card 0 N hr z
  change (((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℤ) = max (⌊b⌋-⌊((0:ℚ)-z)/r⌋) 0 at hcard
  rw [zero_sub,max_eq_left (sub_nonneg.mpr (Int.floor_mono hab))] at hcard
  have hcardQ := congrArg ((↑):ℤ→ℚ) hcard
  push_cast at hcardQ
  have hd : b-a=(N:ℚ)/r := by dsimp [a,b];ring
  have hrat : |(((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℚ)-(N:ℚ)/r|≤1 := by
    rw [←hd]
    apply abs_le.mpr
    constructor <;> linarith [Int.floor_le a,Int.lt_floor_add_one a,Int.floor_le b,Int.lt_floor_add_one b]
  have hc := (Rat.cast_le (K:=ℝ)).mpr hrat
  push_cast at hc
  exact hc

theorem crtRowError_abs_le_one {n d e:ℕ} (hd:0<d) (he:0<e) : |crtRowError n d e|≤1 := by
  have hInt : Ioo 0 n=Ioc 0 (n-1) := by ext k;simp only [mem_Ioo,mem_Ioc];omega
  have hnk (k:ℕ) (hk:k∈Ioo 0 n) : (e∣n-k) ↔ k ≡ n [MOD e] := by
    have hkn := (mem_Ioo.mp hk).2.le
    exact (Nat.modEq_iff_dvd' hkn).symm
  rw [crtRowError,crtCompleteCount_eq hd he]
  by_cases hn : d.gcd e∣n
  · let z := Nat.chineseRemainder' (Nat.modEq_zero_iff_dvd.mpr hn).symm
    have hsol (k:ℕ) (hk:k∈Ioo 0 n) : (d∣k ∧ e∣n-k) ↔ k ≡ (z:ℕ) [MOD d.lcm e] := by
      rw [hnk k hk,←Nat.modEq_and_modEq_iff_modEq_lcm]
      constructor
      · rintro ⟨h₁,h₂⟩;exact ⟨(Nat.modEq_zero_iff_dvd.mpr h₁).trans z.2.1.symm,h₂.trans z.2.2.symm⟩
      · rintro ⟨h₁,h₂⟩;exact ⟨Nat.modEq_zero_iff_dvd.mp (h₁.trans z.2.1),h₂.trans z.2.2⟩
    have hcnt : crtEndpointCount n d e=(((Ioc 0 (n-1)).filter (fun k=>k ≡ (z:ℕ) [MOD d.lcm e])).card:ℝ) := by
      unfold crtEndpointCount
      rw [←hInt,←sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
      congr 2
      ext k
      simp only [mem_filter]
      constructor
      · rintro ⟨hk,hs⟩;exact ⟨hk,(hsol k hk).mp hs⟩
      · rintro ⟨hk,hs⟩;exact ⟨hk,(hsol k hk).mpr hs⟩
    simp only [hn,ite_true,Nat.cast_one,mul_one,hcnt]
    exact crt_residue_discrepancy _ _ _ (Nat.lcm_pos hd he)
  · have hz : crtEndpointCount n d e=0 := by
      apply sum_eq_zero
      intro k hk
      apply ite_eq_right
      rintro ⟨h₁,h₂⟩
      have hz := (Nat.modEq_zero_iff_dvd.mpr h₁).of_dvd (Nat.gcd_dvd_left d e)
      exact hn (Nat.modEq_zero_iff_dvd.mp ((((hnk k hk).mp h₂).of_dvd (Nat.gcd_dvd_right d e)).symm.trans hz))
    simp [hn,hz]

noncomputable def crtSmallEndpointError (n R:ℕ) : ℝ :=
  ∑d∈Icc 1 R,∑e∈Icc 1 R,crtLambdaCoefficient d*crtLambdaCoefficient e*crtRowError n d e

theorem crtSmallEndpointError_abs (n R:ℕ) :
    |crtSmallEndpointError n R|≤(R:ℝ)^2*(Real.log R)^2 := by
  let I := Icc 1 R
  have hcoef (d:ℕ) (hd:d∈I) : |crtLambdaCoefficient d|≤Real.log R := by
    obtain ⟨hd0,hdu⟩ := mem_Icc.mp hd
    rw [crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg _)]
    have hmu : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    apply (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hmu).trans
    exact Real.log_le_log (by exact_mod_cast hd0) (by exact_mod_cast hdu)
  unfold crtSmallEndpointError
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑d∈I,∑_e∈I,(Real.log R)^2 := by
      apply sum_le_sum;intro d hd
      apply (abs_sum_le_sum_abs ..).trans
      apply sum_le_sum;intro e he
      rw [abs_mul,abs_mul,pow_two]
      apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (crtRowError_abs_le_one (mem_Icc.mp hd).1 (mem_Icc.mp he).1)).trans
      exact mul_le_mul (hcoef d hd) (hcoef e he) (abs_nonneg _) (Real.log_natCast_nonneg R)
    _ = _ := by simp [I,nsmul_eq_mul,pow_two,mul_assoc]

theorem crtSmallEndpointError_terminal_bound (n:ℕ) (hn:1≤n) :
    |crtSmallEndpointError n (terminalPrimeArcCutoff n)| ≤ (n:ℝ)/(terminalPrimeArcLog n)^8 := by
  let R := terminalPrimeArcCutoff n
  let L := terminalPrimeArcLog n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hR : (R:ℝ)≤Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hrootn : Real.sqrt n≤(n:ℝ) := by
    have h := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    nlinarith [sq_nonneg (Real.sqrt n-1)]
  have hrn : (R:ℝ)≤n := hR.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)).trans hrootn)
  have hll : Real.log R≤L := by
    by_cases h : R=0
    · simp [h];linarith
    · have hr : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      exact (Real.log_le_log hr hrn).trans (by dsimp only [L,terminalPrimeArcLog];linarith)
  apply (crtSmallEndpointError_abs n R).trans
  calc _ ≤ (Real.sqrt n/L^5)^2*L^2 := by gcongr
       _ = _ := by
         change _=(n:ℝ)/L^8
         rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
         field_simp

theorem crtSmallEndpointError_terminal_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, |crtSmallEndpointError n (terminalPrimeArcCutoff n)|≤ε*(n:ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually_ge_atTop (1/ε)] with n hn hh
  apply (crtSmallEndpointError_terminal_bound n hn).trans
  let L := terminalPrimeArcLog n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hL : 0<L := by linarith
  have he : 1≤ε*L^8 := by
    have h₁ : 1/ε≤L := hh.trans (by change Real.log n≤1+Real.log n;linarith)
    exact ((div_le_iff₀ hε).mp h₁).trans ((mul_comm L ε).le.trans
      (mul_le_mul_of_nonneg_left (le_self_pow₀ hL1 (by decide:8≠0)) hε.le))
  change (n:ℝ)/L^8≤ε*n
  apply (div_le_iff₀ (pow_pos hL 8)).mpr
  simpa only [one_mul,mul_one,mul_comm,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) n)

theorem truncatedLambda_self_ramanujan_error (n R:ℕ) :
    |(∑k∈Ioo 0 n,truncatedLambdaDivisors R k*truncatedLambdaDivisors R (n-k)) -
      ((n-1:ℕ):ℝ)*(∑r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r)^2)|
      ≤ (R:ℝ)^2*(Real.log R)^2 := by
  rw [truncatedLambda_self_ramanujan,add_sub_cancel_left]
  exact crtSmallEndpointError_abs n R

theorem truncatedLambda_self_terminal_ramanujan_error (n:ℕ) (hn:1≤n) :
    let R := terminalPrimeArcCutoff n
    |(∑k∈Ioo 0 n,truncatedLambdaDivisors R k*truncatedLambdaDivisors R (n-k)) -
      ((n-1:ℕ):ℝ)*(∑r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r)^2)|
      ≤ (n:ℝ)/(terminalPrimeArcLog n)^8 := by
  dsimp only
  rw [truncatedLambda_self_ramanujan,add_sub_cancel_left]
  exact crtSmallEndpointError_terminal_bound n hn
end GoldbachPartial
