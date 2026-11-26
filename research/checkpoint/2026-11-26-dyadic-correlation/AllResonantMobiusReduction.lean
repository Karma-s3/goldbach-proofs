import ResonantMobiusHighMass

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient

theorem allResonantMobiusSignedRow_band_bound {n : ℕ} (hn : 0<n) (D R Q : ℕ) (hQ : 0<Q) :
    ‖∑ j∈Ico R Q,resonantMobiusSignedRow n D n (j+1) (naturalTubeRadius (3*Q) (j+1))‖ ≤
    (2/(3*(Q:ℝ)))*((n:ℝ)*Real.log n*(1+Real.log n)/((R:ℝ)+1))^2*
      (1+Real.log Q)*(n.divisors.card:ℝ) := by
  let A := (n:ℝ)*Real.log n*(1+Real.log n)
  let B := A/((R:ℝ)+1)
  let C := (2/(3*(Q:ℝ)))*B^2
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hA : 0≤A := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
    (by linarith [Real.log_natCast_nonneg n])
  have hC : 0≤C := mul_nonneg (by positivity) (sq_nonneg _)
  have hrow (j : ℕ) (hj : j∈Ico R Q) :
      ‖resonantMobiusSignedRow n D n (j+1) (naturalTubeRadius (3*Q) (j+1))‖ ≤
        C*(|(dyadicRamanujanDivisor n (j+1):ℝ)|/((j+1:ℕ):ℝ)) := by
    let q := j+1
    let ρ := naturalTubeRadius (3*Q) q
    have hq : 0<q := Nat.succ_pos _
    have hq' : (0:ℝ)<q := by exact_mod_cast hq
    have hρ : 0≤ρ := by dsimp [ρ,naturalTubeRadius]; positivity
    have hjR : (R:ℝ)+1 ≤ q := by exact_mod_cast Nat.succ_le_succ (mem_Ico.mp hj).1
    have hbound (t : ℝ) : ‖resonantMobiusWave n D n q t‖ ≤ B :=
      (resonantMobiusWave_bound n D n q hq t).trans
        (div_le_div_of_nonneg_left hA (by positivity) hjR)
    have hi : ‖∫ β in -ρ..ρ, resonantMobiusWave n D n q β^2*E (-(n:ℝ)*β)‖ ≤ B^2*(2*ρ) := by
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=B^2) (fun t _ => ?_)).trans_eq
      · rw [sub_neg_eq_add,abs_of_nonneg (add_nonneg hρ hρ)]
        ring
      · rw [norm_mul,norm_pow,show ‖E (-(n:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2
    rw [resonantMobiusSignedRow_exact _ _ _ _ hq,norm_mul]
    have hcast : ‖(dyadicRamanujanDivisor n q:ℂ)‖ = |(dyadicRamanujanDivisor n q:ℝ)| := by
      norm_cast
    apply (mul_le_mul_of_nonneg_left hi (norm_nonneg (dyadicRamanujanDivisor n q:ℂ))).trans_eq
    rw [hcast]
    change |(dyadicRamanujanDivisor n q:ℝ)| * (B^2*(2*(1/((q:ℝ)*(3*Q:ℕ))))) =
      C*(|(dyadicRamanujanDivisor n q:ℝ)|/(q:ℝ))
    dsimp only [C]
    push_cast
    ring
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ j∈Ico R Q,C*(|(dyadicRamanujanDivisor n (j+1):ℝ)|/((j+1:ℕ):ℝ)) :=
      sum_le_sum hrow
    _ = C*∑ j∈Ico R Q,|(dyadicRamanujanDivisor n (j+1):ℝ)|/((j+1:ℕ):ℝ) := (mul_sum ..).symm
    _ ≤ C*((1+Real.log Q)*(n.divisors.card:ℝ)) := mul_le_mul_of_nonneg_left
      (resonantRamanujan_harmonic n R Q hn) hC
    _ = _ := by dsimp only [C,B,A]; ring

noncomputable def allResonantMobiusHighMass (n D : ℕ) : ℂ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  ∑ j∈Ico R Q,resonantMobiusSignedRow n D n (j+1) (naturalTubeRadius (3*Q) (j+1))

set_option maxRecDepth 20000 in
theorem allResonantMobiusHighMass_power :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, ‖allResonantMobiusHighMass n D‖ ≤ 2^27*(n:ℝ)^(7/8:ℝ) := by
  let t := fun n : ℕ => (n:ℝ)^(1/128:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/128)).comp tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/128)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 2,hl.eventually (gt_mem_nhds zero_lt_one),eventually_ge_atTop (1:ℕ)] with n hT hlog hn
  intro D
  let T := t n
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let L := 1+Real.log n
  change 2≤T at hT
  have hT0 : 0<T := by linarith
  have hT1 : 1≤T := by linarith
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hp (k : ℕ) : T^k=(n:ℝ)^((1/128:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul hn'.le]
  have h128 : T^128=(n:ℝ) := by rw [hp]; norm_num
  have h64 : T^64=Real.sqrt n := by rw [hp,Real.sqrt_eq_rpow]; norm_num
  have h112 : T^112=(n:ℝ)^(7/8:ℝ) := by rw [hp]; norm_num
  have hT64 : T≤T^64 := by simpa only [pow_one] using pow_le_pow_right₀ hT1 (by decide : 1≤64)
  have hQfloor : T^64<(Q:ℝ)+1 := by rw [h64]; exact Nat.lt_floor_add_one _
  have hQl : T^64/2≤(Q:ℝ) := by linarith
  have hQp : (0:ℝ)<Q := by linarith
  have hQn : 0<Q := by exact_mod_cast hQp
  have hQu : (Q:ℝ)≤T^64 := by rw [h64]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hnlog : Real.log n≤T := by
    change Real.log n/T<1 at hlog
    linarith only [(div_lt_iff₀ hT0).mp hlog]
  have hlogQ : Real.log Q ≤ T :=
    (Real.log_le_log hQp (hQu.trans ((pow_le_pow_right₀ hT1 (by decide : 64≤128)).trans_eq h128))).trans hnlog
  have hL : 0<L := by dsimp [L]; linarith [Real.log_natCast_nonneg n]
  have hLu : L≤2*T := by dsimp [L]; linarith
  have hqlog : 1+Real.log Q≤2*T := by linarith
  have hRf : T^64/L^5 < (R:ℝ)+1 := by rw [h64]; exact Nat.lt_floor_add_one _
  have hRmul := (div_lt_iff₀ (pow_pos hL 5)).mp hRf
  have hRl : T^64 ≤ ((R:ℝ)+1)*(2*T)^5 :=
    hRmul.le.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hLu 5) (by positivity))
  have hnum : (n:ℝ)*Real.log n*(1+Real.log n) ≤ T^128*T*(2*T) := by
    rw [h128]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hnlog hn'.le) hLu hL.le (by positivity)
  have hratio : (n:ℝ)*Real.log n*(1+Real.log n)/((R:ℝ)+1) ≤ 64*T^71 := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply hnum.trans
    have h := mul_le_mul_of_nonneg_left hRl (show 0≤2*T^66 by positivity)
    linarith only [h]
  have hcoef : 2/(3*(Q:ℝ)) ≤ 2/T^64 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hQl,hQp])
  have hcnt : (n.divisors.card:ℝ) ≤ 4096*T^32 := by
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
    have h : (n.divisors.card:ℝ)^4 ≤ (2:ℝ)^48*n := by exact_mod_cast divisor_count_fourth_le n
    apply h.trans
    rw [←h128]; ring_nf; exact le_rfl
  apply (allResonantMobiusSignedRow_band_bound hn D R Q hQn).trans
  rw [←h112]
  calc
    _ ≤ (2/T^64)*(64*T^71)^2*(2*T)*(4096*T^32) := by
      gcongr
    _ = 2^26*T^111 := by field_simp; ring
    _ ≤ 2^27*T^112 := by
      exact mul_le_mul (by norm_num) (pow_le_pow_right₀ hT1 (by decide : 111≤112)) (by positivity) (by positivity)

theorem allResonantMobiusHighMass_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, ‖allResonantMobiusHighMass n D‖ ≤ ε*(n:ℝ) := by
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/8:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hdec : Tendsto (fun n : ℕ => 2^27*(n:ℝ)^(-(1/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=((2:ℝ)^27))).mul hu
  filter_upwards [allResonantMobiusHighMass_power,eventually_ge_atTop (1:ℕ),
    hdec.eventually (gt_mem_nhds hε)] with n h hn he
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  intro D
  apply (h D).trans
  have hmul := mul_le_mul_of_nonneg_right he.le hn0.le
  change (2^27*(n:ℝ)^(-(1/8:ℝ)))*(n:ℝ) ≤ _ at hmul
  rw [mul_assoc,←Real.rpow_add_one hn0.ne',show -(1/8:ℝ)+1=7/8 by norm_num] at hmul
  exact hmul

noncomputable def nonresonantMobiusWave (n D q : ℕ) (t : ℝ) : ℂ :=
  smallDivisorWave n ((Ioc D n).filter (fun d => ¬q∣d)) (fun d => (crtLambdaCoefficient d:ℂ)) t

theorem largeMobiusWave_split (n D q : ℕ) (t : ℝ) :
    smallDivisorWave n (Ioc D n) (fun d => (crtLambdaCoefficient d:ℂ)) t =
      resonantMobiusWave n D n q t + nonresonantMobiusWave n D q t := by
  unfold resonantMobiusWave nonresonantMobiusWave smallDivisorWave
  exact (sum_filter_add_sum_filter_not _ _ _).symm

noncomputable def nonresonantMobiusRemainderKernel (n D q : ℕ) (t : ℝ) : ℂ :=
  let N := nonresonantMobiusWave n D q t
  let T := resonantMobiusWave n D n q t
  (N^2 + 2*N*T)*E (-(n:ℝ)*t)

noncomputable def nonresonantMobiusRemainderMass (n D R Q : ℕ) : ℂ :=
  ∑ j∈Ico R Q, ∑ a∈(range (j+1)).filter (fun a => a.Coprime (j+1)),
    ∫ β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),
      nonresonantMobiusRemainderKernel n D (j+1) (β+(a:ℝ)/((j+1:ℕ):ℝ))

private theorem resonance_center_sum {q : ℕ} [NeZero q] (f : ℕ→ℂ) :
    (∑ a : (ZMod q)ˣ, f (a:ZMod q).val) =
      ∑ a∈(range q).filter (fun a => a.Coprime q), f a := by
  apply sum_bij (fun (a : (ZMod q)ˣ) _ => (a:ZMod q).val)
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ he
    exact Units.ext (ZMod.val_injective q he)
  · intro a ha
    obtain ⟨har,hac⟩ := mem_filter.mp ha
    exact ⟨ZMod.unitOfCoprime a hac,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp har)⟩
  · intro _ _
    rfl

theorem largeMobiusKernel_union_split (n D R Q : ℕ) (hQ : 0<Q) :
    (∫ t in naturalTubeUnion R Q (3*Q),largeMobiusKernel n D t) =
      nonresonantMobiusRemainderMass n D R Q +
      ∑ j∈Ico R Q,resonantMobiusSignedRow n D n (j+1) (naturalTubeRadius (3*Q) (j+1)) := by
  have hG : Continuous (largeMobiusKernel n D) := by
    unfold largeMobiusKernel smallDivisorWave positiveDivisorRow E
    fun_prop
  rw [naturalTubeUnion_integral_rows R Q (3*Q) (by omega) _ hG]
  unfold nonresonantMobiusRemainderMass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  let q := j+1
  let ρ := naturalTubeRadius (3*Q) q
  let f (a : ℕ) := ∫ β in -ρ..ρ,largeMobiusKernel n D (β+(a:ℝ)/(q:ℝ))
  change (∑ a : (ZMod (j+1))ˣ, f (a:ZMod (j+1)).val) = _
  rw [resonance_center_sum]
  unfold resonantMobiusSignedRow
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  let c := (a:ℝ)/(q:ℝ)
  have hid (β : ℝ) :
      largeMobiusKernel n D (β+c) = nonresonantMobiusRemainderKernel n D q (β+c) +
      resonantMobiusWave n D n q (β+c)^2*E (-(n:ℝ)*(β+c)) := by
    unfold largeMobiusKernel nonresonantMobiusRemainderKernel
    rw [largeMobiusWave_split n D q]
    ring
  change (∫ β in -ρ..ρ,largeMobiusKernel n D (β+c)) = _
  simp_rw [hid]
  apply intervalIntegral.integral_add
  · apply Continuous.intervalIntegrable
    unfold nonresonantMobiusRemainderKernel nonresonantMobiusWave resonantMobiusWave smallDivisorWave positiveDivisorRow E
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold resonantMobiusWave smallDivisorWave positiveDivisorRow E
    fun_prop

theorem largeMobiusHighMass_sub_remainder {n : ℕ} (hQ : 0<naturalTubeScale n) (D : ℕ) :
    (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n D t) -
      nonresonantMobiusRemainderMass n D (terminalPrimeArcCutoff n) (naturalTubeScale n) =
      allResonantMobiusHighMass n D := by
  rw [highNaturalPrimeTubes,largeMobiusKernel_union_split _ _ _ _ hQ]
  exact add_sub_cancel_left .. 

theorem largeMobiusHighMass_remainder_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ,
      ‖(∫ t in highNaturalPrimeTubes n,largeMobiusKernel n D t) -
        nonresonantMobiusRemainderMass n D (terminalPrimeArcCutoff n) (naturalTubeScale n)‖ ≤ ε*n := by
  filter_upwards [allResonantMobiusHighMass_eventually_small hε,naturalTube_eventual_budget] with n h hn
  intro D
  rw [largeMobiusHighMass_sub_remainder hn.2.2.1]
  exact h D

end GoldbachPartial