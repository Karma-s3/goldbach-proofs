import FarShortPairModes
import NaturalTubeShortModes

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient Filter
open scoped Topology

theorem farShortOffTargetKernel_naturalTube_bound (n H R Q M : ℕ)
    (hR : 0<R) (hsep : 2*Q<M) :
    ‖∫ t in naturalTubeUnion R Q M, farShortOffTargetKernel n H t‖ ≤
      (((n:ℝ)+1)*Real.log n^2)*((4/(M:ℝ))*(H:ℝ)*(1+Real.log Q)^2) := by
  have hV := naturalTubeUnion_inside_unit (B:=R) (R:=Q) hR (by omega : 0<M)
  apply (farPairKernelAtModes_fourier_l1 n H (shortNonzeroModes H) hV).trans
  exact mul_le_mul_of_nonneg_left (naturalTubeFourier_shortNonzeroModes_l1 R Q M H hsep) (by positivity)

theorem farShortOffTargetKernel_eventually_pow_bound :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in highNaturalPrimeTubes n,
      farShortOffTargetKernel n (closePrimeGapCutoff n) t‖ ≤ (64/3)*(n:ℝ)^(7/8:ℝ) := by
  let t (n : ℕ) := (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n / t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn htwo hlog
  let T := t n
  let H := closePrimeGapCutoff n
  let Q := naturalTubeScale n
  let R := terminalPrimeArcCutoff n
  change 2≤T at htwo
  have hT0 : 0<T := by linarith
  have hT1 : 1≤T := by linarith
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hpow (k : ℕ) : T^k=(n:ℝ)^((1/32:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le]
  have h8 : T^8=(n:ℝ)^(1/4:ℝ) := by rw [hpow]; norm_num
  have h16 : T^16=Real.sqrt n := by rw [hpow,Real.sqrt_eq_rpow]; norm_num
  have h28 : T^28=(n:ℝ)^(7/8:ℝ) := by rw [hpow]; norm_num
  have h32 : T^32=(n:ℝ) := by rw [hpow]; norm_num
  have hH : (H:ℝ)≤T^8 := by rw [h8]; exact Nat.floor_le (by positivity)
  have hQu : (Q:ℝ)≤T^16 := by rw [h16]; exact Nat.floor_le (by positivity)
  have hfloor : T^16<(Q:ℝ)+1 := by rw [h16]; exact Nat.lt_floor_add_one _
  have hT16 : T≤T^16 := by simpa only [pow_one] using pow_le_pow_right₀ hT1 (by decide : 1≤16)
  have hQl : T^16/2≤(Q:ℝ) := by linarith
  have hQr : (0:ℝ)<Q := by linarith
  have hQ : 0<Q := by exact_mod_cast hQr
  have hln : Real.log n≤T := by
    change Real.log n/T<1 at hlog
    linarith [(div_lt_iff₀ hT0).mp hlog]
  have hQn : (Q:ℝ)≤n :=
    hQu.trans ((pow_le_pow_right₀ hT1 (by decide : 16≤32)).trans_eq h32)
  have hlnQ : 1+Real.log Q≤2*T := by linarith [Real.log_le_log hQr hQn]
  have hnc : (n:ℝ)+1 ≤ 2*T^32 := by rw [h32]; linarith
  have hden : 4/(3*(Q:ℝ)) ≤ 8/(3*T^16) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith only [hQl]
  have hbound := farShortOffTargetKernel_naturalTube_bound n H R Q (3*Q)
    (hg.1.trans_le hg.2.1) (by omega)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hbound
  apply hbound.trans
  rw [←h28]
  calc
    _ ≤ ((2*T^32)*T^2)*((8/(3*T^16))*T^8*(2*T)^2) := by gcongr
    _ = (64/3)*T^28 := by field_simp; ring

theorem farShortOffTargetKernel_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in highNaturalPrimeTubes n,
      farShortOffTargetKernel n (closePrimeGapCutoff n) t‖ ≤ ε*(n:ℝ) := by
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hdec : Tendsto (fun n : ℕ => (64/3)*(n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=(64/3:ℝ))).mul hu
  filter_upwards [farShortOffTargetKernel_eventually_pow_bound,eventually_ge_atTop (1:ℕ),
    hdec.eventually (gt_mem_nhds hε)] with n h hn he
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_right he.le hn0.le
  change ((64/3)*(n:ℝ)^(-(1/8:ℝ)))*(n:ℝ) ≤ _ at hmul
  rw [mul_assoc,←Real.rpow_add_one hn0.ne',show -(1/8:ℝ)+1=7/8 by norm_num] at hmul
  exact hmul

end GoldbachPartial