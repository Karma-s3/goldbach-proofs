import SmallDivisorGRHProgression
namespace GoldbachPartial
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

/-- A nonunit residue class supports von Mangoldt only on powers of one prime. -/
theorem primeSmallProgressionError_nonunit_log (n d:ℕ) (hn:0<n) (hc:¬d.Coprime n) :
    |primeSmallProgressionError n d|≤Real.log n := by
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hc
  obtain ⟨hpd,hpn⟩ := Nat.dvd_gcd_iff.mp hpg
  let I := (Ioo 0 n).filter (fun k=>d∣n-k)
  let m := p^(Nat.log p n)
  have hm : 0<m := pow_pos hp.pos _
  have hmn : m≤n := Nat.pow_log_le_self _ hn.ne'
  unfold primeSmallProgressionError
  rw [ite_eq_right hc,sub_zero,←sum_filter]
  change |∑k∈I,Λ k|≤_
  rw [abs_of_nonneg (sum_nonneg fun _ _=>ArithmeticFunction.vonMangoldt_nonneg),
    ←sum_filter_of_ne (p:=fun k=>Λ k≠0) (fun _ _ h=>h)]
  apply le_trans _ (Real.log_le_log (by exact_mod_cast hm : (0:ℝ)<m) (by exact_mod_cast hmn))
  rw [←ArithmeticFunction.vonMangoldt_sum]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _=>ArithmeticFunction.vonMangoldt_nonneg)
  intro k hk
  obtain ⟨hi,hne⟩ := mem_filter.mp hk
  obtain ⟨hk,hd⟩ := mem_filter.mp hi
  have hkn := (mem_Ioo.mp hk).2.le
  have hpk : p∣k := by
    simpa only [Nat.sub_sub_self hkn] using Nat.dvd_sub hpn (hpd.trans hd)
  obtain ⟨b,j,hb,_hj,rfl⟩ := (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne)
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hb).mp (hp.dvd_of_dvd_pow hpk)
  exact Nat.mem_divisors.mpr ⟨pow_dvd_pow _ (Nat.le_log_of_pow_le hp.one_lt hkn),hm.ne'⟩

theorem primeSmallProgression_uniform_rows (hψ:grhAllUniform) :
    ∃C:ℝ,0<C ∧ ∀n d:ℕ, 3≤n → 0<d → d≤n →
      |primeSmallProgressionError n d|≤C*Real.sqrt n*(terminalPrimeArcLog n)^2 := by
  obtain ⟨K,hK,h⟩ := grhUnitResidueError_bound_of_uniform hψ
  let C := 9*K+1
  have hC1 : 1≤C := by dsimp [C];linarith
  refine ⟨C,by linarith,?_⟩
  intro n d hn hd hdn
  let L := terminalPrimeArcLog n
  let X := n-1
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hX : 2≤X := by dsimp [X];omega
  have hXn : (X:ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
  have hX1 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have hn1 : (1:ℝ)≤n := hX1.trans hXn
  have hs1 : 1≤Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hdn' : (d:ℝ)≤n := by exact_mod_cast hdn
  have hln : Real.log n≤L := by dsimp [L,terminalPrimeArcLog];linarith
  by_cases hc : d.Coprime n
  · have hr := h X d n hX hd hc.symm
    have harg : 1≤2*(d:ℝ)*X := by nlinarith [mul_le_mul hd1 hX1 (by norm_num) (Nat.cast_nonneg (α:=ℝ) d)]
    have hlg0 := Real.log_nonneg harg
    have hlog : Real.log (2*(d:ℝ)*X)≤3*L := by
      rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity)]
      have h₁ := Real.log_le_log (by linarith : (0:ℝ)<X) hXn
      have h₂ := Real.log_le_log (by positivity : (0:ℝ)<d) hdn'
      have h₃ := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      dsimp only [L,terminalPrimeArcLog];linarith
    rw [primeSmallProgressionError_unit hc]
    apply hr.trans
    calc _ ≤ K*Real.sqrt n*(3*L)^2 := by gcongr
         _ ≤ _ := by
           change _≤(9*K+1)*Real.sqrt n*L^2
           nlinarith only [mul_nonneg (Real.sqrt_nonneg (n:ℝ)) (sq_nonneg L)]
  · apply (primeSmallProgressionError_nonunit_log n d (by omega) hc).trans
    apply hln.trans
    calc L ≤ 1*1*L^2 := by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hL1)]
         _ ≤ C*Real.sqrt n*L^2 := by gcongr

theorem weightedSmallProgression_terminal_bound (hψ:grhAllUniform) :
    ∃A:ℝ,0<A ∧ ∀n:ℕ,3≤n → ∀a:ℕ→ℝ,
      (∀d∈Icc 1 (terminalPrimeArcCutoff n),|a d|≤8*terminalPrimeArcLog n) →
      (∑d∈Icc 1 (terminalPrimeArcCutoff n),|a d*primeSmallProgressionError n d|) ≤
        A*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  obtain ⟨C,hC,hr⟩ := primeSmallProgression_uniform_rows hψ
  refine ⟨8*C,by positivity,?_⟩
  intro n hn a ha
  let L := terminalPrimeArcLog n
  let R := terminalPrimeArcCutoff n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hR : (R:ℝ)≤Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hrootn : Real.sqrt n≤(n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  have hrn : R≤n := by
    exact_mod_cast hR.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)).trans hrootn)
  let B := (8*L)*(C*Real.sqrt n*L^2)
  have hB : 0≤B := by dsimp [B];positivity
  calc _ ≤ ∑ _d∈Icc 1 R,B := by
         apply sum_le_sum;intro d hd
         rw [abs_mul]
         have hd' := mem_Icc.mp hd
         exact mul_le_mul (ha d hd) (hr n d hn hd'.1 (hd'.2.trans hrn)) (abs_nonneg _) (by positivity)
       _ ≤ (Real.sqrt n/L^5)*B := by
         simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right hR hB
       _ = _ := by
         change _=(8*C)*(n:ℝ)/L^2
         dsimp only [B]
         calc _ = (8*C)*(Real.sqrt n)^2/L^2 := by field_simp
              _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem weightedSmallProgression_terminal_small (hψ:grhAllUniform) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀a:ℕ→ℝ,
      (∀d∈Icc 1 (terminalPrimeArcCutoff n),|a d|≤8*terminalPrimeArcLog n) →
      |∑d∈Icc 1 (terminalPrimeArcCutoff n),a d*primeSmallProgressionError n d|≤ε*(n:ℝ) := by
  obtain ⟨A,hA,h⟩ := weightedSmallProgression_terminal_bound hψ
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (3:ℕ),hlog.eventually_ge_atTop (A/ε)] with n hn hh
  intro a ha
  apply (abs_sum_le_sum_abs ..).trans
  apply (h n hn a ha).trans
  let L := terminalPrimeArcLog n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hL : 0<L := by linarith
  have hk : A/ε≤L := hh.trans (by change Real.log n≤1+Real.log n;linarith)
  have he : A≤ε*L^2 := ((div_le_iff₀ hε).mp hk).trans ((mul_comm L ε).le.trans
    (mul_le_mul_of_nonneg_left (le_self_pow₀ hL1 (by decide:2≠0)) hε.le))
  change A*(n:ℝ)/L^2≤ε*n
  apply (div_le_iff₀ (pow_pos hL 2)).mpr
  simpa only [mul_comm,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) n)

theorem crtSmallProgression_terminal_small (hψ:grhAllUniform) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      |∑d∈Icc 1 (terminalPrimeArcCutoff n),crtLambdaCoefficient d*primeSmallProgressionError n d|
        ≤ ε*(n:ℝ) := by
  filter_upwards [weightedSmallProgression_terminal_small hψ hε,eventually_ge_atTop (1:ℕ)] with n hh hn
  apply hh crtLambdaCoefficient
  intro d hd
  let L := terminalPrimeArcLog n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hr := Nat.floor_le (by positivity : 0≤Real.sqrt n/L^5)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hrootn : Real.sqrt n≤(n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  obtain ⟨hd0,hdr⟩ := mem_Icc.mp hd
  have hdn := (by exact_mod_cast hdr : (d:ℝ)≤terminalPrimeArcCutoff n).trans
    (hr.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)).trans hrootn))
  have hmu : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  rw [crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg _)]
  apply (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hmu).trans
  apply (Real.log_le_log (by exact_mod_cast hd0) hdn).trans
  change Real.log n≤8*(1+Real.log n)
  linarith [Real.log_natCast_nonneg n]

theorem truncatedLambda_mixed_terminal_small (hψ:grhAllUniform) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      let R := terminalPrimeArcCutoff n
      |(∑ k∈Ioo 0 n,Λ k*truncatedLambdaDivisors R (n-k)) -
        ((n-1:ℕ):ℝ)*(∑r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*
          ((ArithmeticFunction.moebius r:ℝ)/r.totient)*crtRamanujanTruncation R r)|≤ε*(n:ℝ) := by
  filter_upwards [crtSmallProgression_terminal_small hψ hε] with n hn
  dsimp only
  rw [truncatedLambda_mixed_ramanujan,add_sub_cancel_left]
  exact hn
end GoldbachPartial
