import VerifiedFiniteBonferroni
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
namespace GoldbachPartial
open Filter
open scoped Topology

noncomputable def brunNearPowerIndex (n:ℕ) : ℕ := Nat.log 2 ⌊Real.log (n:ℝ)⌋₊
noncomputable def brunNearPowerRank (n:ℕ) : ℕ := 16*(Nat.log 2 (brunNearPowerIndex n+1)+1)+15
noncomputable def brunNearPowerExponent (n:ℕ) : ℕ := brunNearPowerIndex n/brunNearPowerRank n
noncomputable def brunNearPowerCutoff (n:ℕ) : ℕ := 2^brunNearPowerExponent n

private theorem brun_logtwo : (1/2:ℝ)≤Real.log 2 ∧ Real.log 2≤1 := by
  constructor
  · have h:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    linarith
  · simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)

private theorem brun_natlog_le (s:ℕ) : (Nat.log 2 s:ℝ)≤2*Real.log s := by
  have h:=Real.natLog_le_logb s 2
  simp only [Real.logb,Nat.cast_ofNat] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith [brun_logtwo.1] : 0<Real.log 2)).mpr
  nlinarith only [mul_nonneg (Real.log_natCast_nonneg s) (show 0≤2*Real.log 2-1 by linarith [brun_logtwo.1])]

theorem brunNearPowerIndex_tendsto : Tendsto brunNearPowerIndex atTop atTop := by
  have h := tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [h.eventually_ge_atTop (2^m)] with n hn
  change 2^m≤⌊Real.log (n:ℝ)⌋₊ at hn
  have h1 := (Nat.one_le_pow _ _ (by decide : 1≤2)).trans hn
  exact (Nat.le_log_iff_pow_le (by decide) (by omega : ⌊Real.log (n:ℝ)⌋₊≠0)).mpr hn

theorem brunNearPowerRank_odd (n:ℕ) : Odd (brunNearPowerRank n) := by
  refine ⟨8*(Nat.log 2 (brunNearPowerIndex n+1)+1)+7,?_⟩
  unfold brunNearPowerRank;omega

theorem brunNearPower_cutoff_rank_bound (n:ℕ) (hn:1≤⌊Real.log (n:ℝ)⌋₊) :
    (brunNearPowerCutoff n)^(brunNearPowerRank n)≤⌊Real.log (n:ℝ)⌋₊ := by
  unfold brunNearPowerCutoff brunNearPowerExponent
  rw [←pow_mul]
  exact (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self ..)).trans (Nat.pow_log_le_self 2 (by omega))

theorem brunNearPower_rank_dominates (n:ℕ) :
    (2:ℝ)^22*(1+Real.log (brunNearPowerCutoff n))^3 ≤ (2:ℝ)^(brunNearPowerRank n) := by
  let s:=brunNearPowerIndex n
  let b:=Nat.log 2 (s+1)+1
  let j:=brunNearPowerExponent n
  have hj : j≤s := Nat.div_le_self .. 
  have hb : s+1≤2^b := (Nat.lt_pow_succ_log_self (by decide : 1<2) (s+1)).le
  have hlog : Real.log (brunNearPowerCutoff n)=(j:ℝ)*Real.log 2 := by
    simp only [brunNearPowerCutoff,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,j]
  have hjr : (j:ℝ)≤s := by exact_mod_cast hj
  have hbr : (s:ℝ)+1≤(2:ℝ)^b := by exact_mod_cast hb
  have h1 : 1+Real.log (brunNearPowerCutoff n)≤(2:ℝ)^b := by
    rw [hlog]
    linarith only [hjr,hbr,mul_le_mul_of_nonneg_left brun_logtwo.2 (Nat.cast_nonneg (α:=ℝ) j)]
  have hK : 22+b*3≤brunNearPowerRank n := by dsimp only [b,s,brunNearPowerRank];omega
  calc _ ≤ (2:ℝ)^22*((2:ℝ)^b)^3 := by gcongr
       _ = (2:ℝ)^(22+b*3) := by rw [←pow_mul,←pow_add]
       _ ≤ _ := pow_le_pow_right₀ (by norm_num) hK

theorem brunNearPower_parameters : ∀ᶠ n:ℕ in atTop,
    Odd (brunNearPowerRank n) ∧ 1≤brunNearPowerCutoff n ∧
    (brunNearPowerCutoff n)^(brunNearPowerRank n)≤⌊Real.log (n:ℝ)⌋₊ ∧
    (2:ℝ)^22*(1+Real.log (brunNearPowerCutoff n))^3≤(2:ℝ)^(brunNearPowerRank n) := by
  have h := tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [h.eventually_ge_atTop 1] with n hn
  exact ⟨brunNearPowerRank_odd n,Nat.one_le_pow _ _ (by decide),brunNearPower_cutoff_rank_bound n hn,brunNearPower_rank_dominates n⟩

private theorem brun_rank_le {n:ℕ} (h:1≤brunNearPowerIndex n) :
    (brunNearPowerRank n:ℝ) ≤64*(1+Real.log (brunNearPowerIndex n)) := by
  let s:=brunNearPowerIndex n
  have hs : (1:ℝ)≤s := by exact_mod_cast h
  have hss : Real.log ((s+1:ℕ):ℝ) ≤ 1+Real.log s := by
    rw [Nat.cast_add,Nat.cast_one]
    have hh:=Real.log_le_log (by positivity : (0:ℝ)<s+1) (show (s:ℝ)+1≤2*s by linarith only [hs])
    rw [Real.log_mul (by norm_num) (by linarith only [hs] : (s:ℝ)≠0)] at hh
    linarith only [hh,brun_logtwo.2]
  have hh:=brun_natlog_le (s+1)
  change ((16*(Nat.log 2 (s+1)+1)+15:ℕ):ℝ)≤64*(1+Real.log s)
  push_cast at hh hss ⊢
  linarith only [hh,hss,Real.log_natCast_nonneg s]

theorem brunNearPowerExponent_tendsto : Tendsto brunNearPowerExponent atTop atTop := by
  let s:=brunNearPowerIndex
  have hS : Tendsto (fun n:ℕ=>(s n:ℝ)) atTop atTop := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp brunNearPowerIndex_tendsto
  have h0 : Tendsto (fun n:ℕ=>1/(s n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hS
  have hlog : Tendsto (fun n:ℕ=>Real.log (s n)/(s n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp hS)
  have hsum : Tendsto (fun n:ℕ=>(1+Real.log (s n))/(s n:ℝ)) atTop (𝓝 0) := by
    simpa only [add_div,zero_add] using h0.add hlog
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [brunNearPowerIndex_tendsto.eventually_ge_atTop 1,
    hsum.eventually_lt_const (show (0:ℝ)<1/(64*((m:ℝ)+1)) by positivity)] with n hn ht
  have hs : (0:ℝ)<s n := by exact_mod_cast hn
  have hk : 0<brunNearPowerRank n := by unfold brunNearPowerRank;omega
  apply (Nat.le_div_iff_mul_le hk).mpr
  have hpre := brun_rank_le hn
  change (brunNearPowerRank n:ℝ)≤64*(1+Real.log (s n)) at hpre
  have hpos : (0:ℝ)<64*((m:ℝ)+1) := by positivity
  have hin : (1+Real.log (s n))*(64*((m:ℝ)+1)) < s n := by
    have hh := (div_lt_div_iff₀ hs hpos).mp ht
    simpa only [one_mul] using hh
  have hh : (m:ℝ)*(brunNearPowerRank n:ℝ) ≤ (s n:ℝ) := by
    nlinarith only [hin,mul_le_mul_of_nonneg_left hpre (Nat.cast_nonneg (α:=ℝ) m),Real.log_natCast_nonneg (s n)]
  exact_mod_cast hh

theorem brunNearPowerCutoff_tendsto : Tendsto brunNearPowerCutoff atTop atTop := by
  apply tendsto_atTop.mpr;intro m
  filter_upwards [brunNearPowerExponent_tendsto.eventually_ge_atTop m] with n hn
  exact (show m<2^m from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) hn)

theorem brunNearPower_log_lower : ∀ᶠ n:ℕ in atTop,
    Real.log (Real.log n)/(1024*(1+Real.log (Real.log (Real.log n)))) ≤
      Real.log (brunNearPowerCutoff n) := by
  let x (n:ℕ):ℝ:=Real.log n
  let u (n:ℕ):ℝ:=Real.log (x n)
  have hx : Tendsto x atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hu : Tendsto u atTop atTop := Real.tendsto_log_atTop.comp hx
  filter_upwards [hx.eventually_ge_atTop 2,hu.eventually_ge_atTop 1,brunNearPowerIndex_tendsto.eventually_ge_atTop 1,
    brunNearPowerExponent_tendsto.eventually_ge_atTop 1] with n hx2 hu1 hs1 hj1
  let s:=brunNearPowerIndex n
  let k:=brunNearPowerRank n
  let j:=brunNearPowerExponent n
  let W:=1+Real.log (u n)
  have hx0 : 0<x n := by linarith only [hx2]
  have hu0 : 0<u n := by linarith only [hu1]
  have hlU : 0≤Real.log (u n) := Real.log_nonneg hu1
  have hs : (1:ℝ)≤s := by exact_mod_cast hs1
  have hs0 : (0:ℝ)<s := by linarith
  have hfloor : (1:ℕ)≤⌊x n⌋₊ := Nat.le_floor (by push_cast;linarith only [hx2])
  have hnat : ⌊x n⌋₊ +1 ≤2^(s+1) := Nat.lt_pow_succ_log_self (by decide) _
  have hnat' : (⌊x n⌋₊:ℝ)+1 ≤(2:ℝ)^(s+1) := by exact_mod_cast hnat
  have hxl := Real.log_le_log hx0 ((Nat.lt_floor_add_one (x n)).le.trans hnat')
  rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at hxl
  have hus : u n≤2*s := by
    change Real.log (x n)≤2*s
    nlinarith only [hxl,mul_le_mul_of_nonneg_left brun_logtwo.2 (show 0≤(s:ℝ)+1 by positivity),hs]
  have hlogsf : Real.log ((⌊x n⌋₊:ℕ):ℝ) ≤ u n := Real.log_le_log
    (by exact_mod_cast (show (0:ℕ)<⌊x n⌋₊ by omega)) (Nat.floor_le hx0.le)
  have hsu : (s:ℝ)≤2*u n := (brun_natlog_le _).trans (by linarith only [hlogsf])
  have hls := Real.log_le_log hs0 hsu
  rw [Real.log_mul (by norm_num) hu0.ne'] at hls
  have hk : (k:ℝ)≤128*W := by
    have hh := brun_rank_le hs1
    change (k:ℝ)≤64*(1+Real.log s) at hh
    dsimp [W]
    linarith only [hh,hls,brun_logtwo.2,hlU]
  have hk0 : 0<k := by dsimp [k,brunNearPowerRank];omega
  have hmod := Nat.div_add_mod s k
  have hrem := Nat.mod_lt s hk0
  have hsj : s≤2*k*j := by
    change 1≤s/k at hj1
    change s≤2*k*(s/k)
    nlinarith only [hmod,hrem,Nat.mul_le_mul_left k hj1]
  have hsj' : (s:ℝ)≤2*(k:ℝ)*j := by exact_mod_cast hsj
  have hj : (0:ℝ)≤j := Nat.cast_nonneg _
  have hw : 0<W := by dsimp only [W];linarith
  have hlogz : Real.log (brunNearPowerCutoff n)=(j:ℝ)*Real.log 2 := by
    simp only [brunNearPowerCutoff,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,j]
  change u n/(1024*W)≤_
  apply (div_le_iff₀ (by positivity)).mpr
  rw [hlogz]
  have hj2 : (j:ℝ)≤2*(j:ℝ)*Real.log 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left brun_logtwo.1 hj]
  nlinarith only [hus,hsj',mul_le_mul_of_nonneg_right hk hj,mul_le_mul_of_nonneg_left hj2 hw.le]

end GoldbachPartial
