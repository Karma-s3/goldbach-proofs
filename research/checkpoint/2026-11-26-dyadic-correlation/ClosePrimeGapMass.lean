import NaturalPrimeGapTubeUnion

namespace GoldbachPartial

open Finset MeasureTheory Filter ExtendedArcCoefficient
open scoped Topology

noncomputable def closePrimeGapKernel (n H : ℕ) (t : ℝ) : ℂ :=
  (∑ d∈range (H+1), primeGapKernel n d t) +
  (∑ d∈Icc 1 H, primeGapKernel n d t)

noncomputable abbrev closePrimeGapCutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/4:ℝ)⌋₊

theorem closePrimeGapKernel_finite_bound (n H R Q : ℕ) (hR : 0<R) (hQ : 0<Q) :
    ‖∫ t in naturalTubeUnion R Q (3*Q), closePrimeGapKernel n H t‖ ≤
      (2*(H:ℝ)+1)*(4*Real.log n^2/(3*(Q:ℝ))*((n:ℝ)*(1+Real.log Q)^2+Q)) := by
  let Ω := naturalTubeUnion R Q (3*Q)
  let A := 4*Real.log n^2/(3*(Q:ℝ))*((n:ℝ)*(1+Real.log Q)^2+Q)
  have hsub := naturalTubeUnion_inside_unit (B:=R) (R:=Q) hR (by omega : 0<3*Q)
  have hi (s : Finset ℕ) : IntegrableOn (fun t => ∑ d∈s,primeGapKernel n d t) Ω := by
    have hc : Continuous (fun t => ∑ d∈s,primeGapKernel n d t) :=
      continuous_finsetSum s fun d _ => by unfold primeGapKernel E; fun_prop
    exact hc.integrableOn_Icc.mono_set hsub
  have hs (s : Finset ℕ) : ‖∫ t in Ω, ∑ d∈s, primeGapKernel n d t‖ ≤ (s.card:ℝ)*A :=
    primeGapKernel_disjoint_natural_band n R Q s hR hQ
  change ‖∫ t in Ω, (∑ d∈range (H+1), primeGapKernel n d t)+(∑ d∈Icc 1 H,primeGapKernel n d t)‖ ≤ _
  rw [integral_add (hi _) (hi _)]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hs (range (H+1))) (hs (Icc 1 H))).trans_eq
  simp only [card_range,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_add_one]
  dsimp only [A]
  ring

theorem closePrimeGapKernel_eventually_pow_bound :
    ∀ᶠ n : ℕ in atTop,
      ‖∫ t in naturalTubeUnion (terminalPrimeArcCutoff n) (naturalTubeScale n) (3*naturalTubeScale n),
        closePrimeGapKernel n (closePrimeGapCutoff n) t‖ ≤ 40*(n:ℝ)^(7/8:ℝ) := by
  let t (n : ℕ) := (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n / t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht2 hlog
  let T := t n
  let Q := naturalTubeScale n
  let H := closePrimeGapCutoff n
  let R := terminalPrimeArcCutoff n
  change 2≤T at ht2
  have ht0 : 0<T := by linarith
  have ht1 : 1≤T := by linarith
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hR : 0<R := hg.1.trans_le hg.2.1
  have hpow (k : ℕ) : T^k=(n:ℝ)^((1/32:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le]
  have h8 : T^8=(n:ℝ)^(1/4:ℝ) := by rw [hpow]; norm_num
  have h16 : T^16=Real.sqrt n := by rw [hpow,Real.sqrt_eq_rpow]; norm_num
  have h28 : T^28=(n:ℝ)^(7/8:ℝ) := by rw [hpow]; norm_num
  have h32 : T^32=(n:ℝ) := by rw [hpow]; norm_num
  have hH : (H:ℝ)≤T^8 := by rw [h8]; exact Nat.floor_le (by positivity)
  have hQu : (Q:ℝ)≤T^16 := by rw [h16]; exact Nat.floor_le (by positivity)
  have hfloor : T^16<(Q:ℝ)+1 := by rw [h16]; exact Nat.lt_floor_add_one _
  have hT16 : T≤T^16 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1≤16)
  have hQl : T^16/2≤(Q:ℝ) := by linarith
  have hQr : (0:ℝ)<Q := by linarith
  have hQ : 0<Q := by exact_mod_cast hQr
  have hln : Real.log n≤T := by
    change Real.log n/T < 1 at hlog
    linarith [(div_lt_iff₀ ht0).mp hlog]
  have hQn : (Q:ℝ)≤n :=
    hQu.trans ((pow_le_pow_right₀ ht1 (by decide : 16≤32)).trans_eq h32)
  have hlnQ : 1+Real.log Q ≤ 2*T := by linarith [Real.log_le_log hQr hQn]
  have hcard : 2*(H:ℝ)+1 ≤ 3*T^8 := by linarith [one_le_pow₀ ht1 (n:=8)]
  have hbracket : (n:ℝ)*(1+Real.log Q)^2+Q ≤ 5*T^34 := calc
    _ ≤ T^32*(2*T)^2+T^34 := by
      rw [h32]
      gcongr
      exact hQu.trans (pow_le_pow_right₀ ht1 (by decide))
    _ = _ := by ring
  have hcoef : 4*Real.log n^2/(3*(Q:ℝ)) ≤ 8*T^2/(3*T^16) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs : (Real.log n)^2 ≤ T^2 := pow_le_pow_left₀ (Real.log_natCast_nonneg _) hln 2
    have hb := mul_le_mul_of_nonneg_right hQl (sq_nonneg T)
    have ha := mul_le_mul_of_nonneg_right hs (pow_nonneg ht0.le 16)
    linarith only [hb,ha]
  apply (closePrimeGapKernel_finite_bound n H R Q hR hQ).trans
  rw [←h28]
  calc
    _ ≤ (3*T^8)*(8*T^2/(3*T^16)*(5*T^34)) := by gcongr
    _ = 40*T^28 := by field_simp; ring

theorem closePrimeGapKernel_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖∫ t in naturalTubeUnion (terminalPrimeArcCutoff n) (naturalTubeScale n) (3*naturalTubeScale n),
        closePrimeGapKernel n (closePrimeGapCutoff n) t‖ ≤ ε*(n:ℝ) := by
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hdec : Tendsto (fun n : ℕ => 40*(n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=(40:ℝ))).mul hu
  filter_upwards [closePrimeGapKernel_eventually_pow_bound,eventually_ge_atTop (1:ℕ),
    hdec.eventually (gt_mem_nhds hε)] with n h hn he
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_right he.le hn0.le
  change (40*(n:ℝ)^(-(1/8:ℝ)))*(n:ℝ) ≤ _ at hmul
  rw [mul_assoc,←Real.rpow_add_one hn0.ne',show -(1/8:ℝ)+1=7/8 by norm_num] at hmul
  exact hmul

end GoldbachPartial