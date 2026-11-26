import PinnedUpstream316
import WeightedSmallProgression
import ExactRamanujanWeightBound

namespace GoldbachPartial
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

private theorem pinned_progression_prefix_eq (X d a:ℕ) :
    OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt X d (a%d) -
      (X:ℝ)/d.totient = grhUnitResidueError X d a := by
  unfold OAI.LargePrimeGaps.residuePrefix OAI.LargePrimeGaps.residueSlice grhUnitResidueError
  congr 2

private theorem sw_natLog_le {X:ℕ} (_hX:1≤X) : (Nat.log 2 X:ℝ)≤2*Real.log X := by
  have h := Real.natLog_le_logb X 2
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h₂
  have hu := Real.log_natCast_nonneg X
  simp only [Nat.cast_ofNat,Real.logb] at h
  exact h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr (by
    nlinarith only [mul_nonneg hu (show 0≤2*Real.log 2-1 by linarith)]))

theorem medDeskSmallProgression_rows :
    ∃C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀d∈Icc 1 (medDeskQ n),
      |primeSmallProgressionError n d|≤C*(n:ℝ)/(Real.log n)^8 := by
  obtain ⟨M,hM,x₀,_hx₀,hAP⟩ := GoldbachMajorArc.progression_error 8 4 (by norm_num) (by norm_num)
  refine ⟨256*M+8,by positivity,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow 10 (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop (⌈x₀⌉₊+3),hlog.eventually_ge_atTop 16,hpow] with n hn hu hpn
  intro d hd
  let X := n-1
  let u := Real.log n
  let t := Real.log X
  have hthr : ⌈x₀⌉₊≤X := by dsimp [X];omega
  have hx : x₀≤(X:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hthr)
  have hX1 : 1≤X := by dsimp [X];omega
  have hX1r : (1:ℝ)≤X := by exact_mod_cast hX1
  have hXn : (X:ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
  have hn0 : (0:ℝ)<n := by linarith
  have hnX : (n:ℝ)≤(X:ℝ)^2 := by
    have hh : n=X+1 := by dsimp [X];omega
    have h2 : 2≤X := by dsimp [X];omega
    exact_mod_cast (show n≤X^2 by nlinarith [Nat.mul_le_mul h2 h2,Nat.mul_le_mul_right X h2])
  change 16≤u at hu
  have hu1 : 1≤u := by linarith
  have hu0 : 0<u := by linarith
  have htu : t≤u := Real.log_le_log (by linarith) hXn
  have hut : u≤2*t := by simpa only [Real.log_pow,Nat.cast_ofNat,t,u] using Real.log_le_log hn0 hnX
  have ht8 : 8≤t := by linarith
  have ht1 : 1≤t := by linarith
  have ht : 0<t := by linarith
  have h10 : u^10≤(n:ℝ) := by simpa only [u,Function.comp_def,Real.rpow_one,Real.rpow_ofNat] using hpn
  have huB : u^2 ≤(n:ℝ)/u^8 := (le_div_iff₀ (pow_pos hu0 8)).mpr (by convert h10 using 1;ring)
  have h8 : u^8≤256*t^8 := by simpa only [mul_pow,show (2:ℝ)^8=256 by norm_num] using pow_le_pow_left₀ hu0.le hut 8
  obtain ⟨hd1,hdQ⟩ := mem_Icc.mp hd
  have hdr : (0:ℝ)<d := by exact_mod_cast hd1
  have hdcut : (d:ℝ)≤16*u^2 := (by exact_mod_cast hdQ : (d:ℝ)≤medDeskQ n).trans
    (GoldbachMajorArc.cutoff_le_log_sq (by omega : 2≤n))
  have ht2 : 64≤t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht8) (show 0≤t+8 by linarith)]
  have hd4 : (d:ℝ)≤t^4 := calc
    _ ≤ 16*(2*t)^2 := hdcut.trans (by gcongr)
    _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)]
  have hlg : Real.log d≤4*u := by
    have hh := Real.log_le_log hdr hd4
    rw [Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos ht
    norm_num at hh
    linarith
  by_cases hc : d.Coprime n
  · have hb : (n%d).Coprime d := by
      rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm];exact hc.symm.gcd_eq_one
    have hclass := hAP (X:ℝ) hx d (n%d) hd1 (by simpa only [Real.rpow_ofNat] using hd4)
      (Nat.mod_lt _ hd1) hb
    rw [Nat.floor_natCast,pinned_progression_prefix_eq] at hclass
    have hrp : (Real.log (X:ℝ))^(-(8:ℝ)) = (t^8)⁻¹ := by
      rw [Real.rpow_neg ht.le,Real.rpow_ofNat]
    rw [hrp] at hclass
    rw [primeSmallProgressionError_unit hc]
    apply hclass.trans
    have hrec : (X:ℝ)*(t^8)⁻¹≤256*((n:ℝ)/u^8) := by
      rw [←div_eq_mul_inv,mul_div_assoc',div_le_div_iff₀ (pow_pos ht 8) (pow_pos hu0 8)]
      calc _ ≤ (n:ℝ)*(256*t^8) := mul_le_mul hXn h8 (pow_nonneg hu0.le 8) (Nat.cast_nonneg _)
           _ = _ := by ring
    have hlog2 : (Nat.log 2 X:ℝ)≤2*u := (sw_natLog_le hX1).trans (by linarith)
    have hlogsum := mul_le_mul hlog2 hlg (Real.log_natCast_nonneg d) (by positivity)
    have hmain := mul_le_mul_of_nonneg_left hrec hM.le
    have htail := mul_le_mul_of_nonneg_left huB (by norm_num : (0:ℝ)≤8)
    change _≤(256*M+8)*(n:ℝ)/u^8
    apply (add_le_add (show M*(X:ℝ)*(t^8)⁻¹≤(256*M)*((n:ℝ)/u^8) by linear_combination hmain)
      (show (Nat.log 2 X:ℝ)*Real.log d≤8*((n:ℝ)/u^8) by nlinarith only [hlogsum,htail])).trans_eq
    ring
  · apply (primeSmallProgressionError_nonunit_log n d (by omega) hc).trans
    have hmu : 1≤256*M+8 := by linarith
    have hh : u≤u^2 := le_self_pow₀ hu1 (by decide)
    calc u ≤ (n:ℝ)/u^8 := hh.trans huB
         _ ≤ _ := by rw [mul_div_assoc];exact le_mul_of_one_le_left (by positivity) hmu

theorem weightedMedDeskProgression_bound :
    ∃A:ℝ,0<A ∧ ∀ᶠ n:ℕ in atTop,∀a:ℕ→ℝ,
      (∀d∈Icc 1 (medDeskQ n),|a d|≤8*terminalPrimeArcLog n) →
      (∑d∈Icc 1 (medDeskQ n),|a d*primeSmallProgressionError n d|) ≤
        A*(n:ℝ)/(Real.log n)^5 := by
  obtain ⟨C,hC,hrow⟩ := medDeskSmallProgression_rows
  refine ⟨256*C,by positivity,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hrow,eventually_ge_atTop (2:ℕ),hlog.eventually_ge_atTop 1] with n hr hn hu
  intro a ha
  let u := Real.log n
  change 1≤u at hu
  have hu0 : 0<u := by linarith
  have hL : terminalPrimeArcLog n≤2*u := by change 1+u≤_;linarith
  let B := 16*u*(C*(n:ℝ)/u^8)
  have hB : 0≤B := by dsimp [B];positivity
  calc _ ≤ ∑_d∈Icc 1 (medDeskQ n),B := by
         apply sum_le_sum;intro d hd
         rw [abs_mul]
         apply mul_le_mul ((ha d hd).trans (by linarith only [hL] : 8*terminalPrimeArcLog n≤16*u))
           (hr d hd) (abs_nonneg _) (by positivity)
       _ ≤ (16*u^2)*B := by
         simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right (GoldbachMajorArc.cutoff_le_log_sq hn) hB
       _ = _ := by change _=(256*C)*(n:ℝ)/u^5;dsimp only [B];field_simp;ring

theorem weightedMedDeskProgression_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀a:ℕ→ℝ,
      (∀d∈Icc 1 (medDeskQ n),|a d|≤8*terminalPrimeArcLog n) →
      (∑d∈Icc 1 (medDeskQ n),|a d*primeSmallProgressionError n d|) ≤ ε*(n:ℝ) := by
  obtain ⟨A,_hA,h⟩ := weightedMedDeskProgression_bound
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h,hlog.eventually_ge_atTop (max 1 (A/ε))] with n hn hln
  intro a ha
  apply (hn a ha).trans
  let u := Real.log n
  have hu := (le_max_left 1 (A/ε)).trans hln
  change 1≤u at hu
  have hu0 : 0<u := by linarith
  have hA := (div_le_iff₀ hε).mp ((le_max_right 1 (A/ε)).trans hln)
  have he : A≤ε*u^5 := hA.trans ((mul_comm u ε).le.trans
    (mul_le_mul_of_nonneg_left (le_self_pow₀ hu (by decide:5≠0)) hε.le))
  apply (div_le_iff₀ (pow_pos hu0 5)).mpr
  simpa only [mul_comm,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) n)

theorem exactRamanujanWeight_medDeskProgression_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      (∑d∈Icc 1 (medDeskQ n),|exactRamanujanWeight (medDeskQ n) d*primeSmallProgressionError n d|)
        ≤ ε*(n:ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow 4 (by norm_num : (0:ℝ)<1))
  filter_upwards [weightedMedDeskProgression_small hε,eventually_ge_atTop (2:ℕ),
    hlog.eventually_ge_atTop 4,hpow] with n h hn hu hp
  apply h
  intro d _
  have hl : 4≤Real.log (n:ℝ) := hu
  have h4 : (Real.log (n:ℝ))^4≤n := by simpa only [Function.comp_def,Real.rpow_one,Real.rpow_ofNat] using hp
  let u := Real.log n
  have hu2 : 16≤u^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0≤Real.log n+4 by linarith)]
  have hcut : (medDeskQ n:ℝ)≤n := (GoldbachMajorArc.cutoff_le_log_sq hn).trans
    ((show 16*u^2≤u^4 by nlinarith only [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]).trans h4)
  apply (exactRamanujanWeight_abs_le_log _ _).trans
  by_cases hQ : medDeskQ n=0
  · simp only [hQ,Nat.cast_zero,Real.log_zero,add_zero,mul_one]
    change (8:ℝ)≤8*(1+Real.log n);linarith
  · have hr : (0:ℝ)<medDeskQ n := by exact_mod_cast Nat.pos_of_ne_zero hQ
    change _≤8*(1+Real.log n)
    gcongr
end GoldbachPartial
