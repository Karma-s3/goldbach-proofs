import LargeDivisorPrimeMass
import NaturalTubeSingleFrequency
import DivisorCountFourth

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient

noncomputable def resonantMobiusWave (n R Q q : ℕ) (t : ℝ) : ℂ :=
  smallDivisorWave n ((Ioc R Q).filter (fun d => q∣d)) (fun d => (crtLambdaCoefficient d:ℂ)) t

theorem positiveDivisorRow_at_resonant_center {q d : ℕ} (hq : 0<q) (hqd : q∣d)
    (n a : ℕ) (β : ℝ) : positiveDivisorRow n d (β+a/(q:ℝ)) = positiveDivisorRow n d β := by
  have hn (k : ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I)=(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  unfold positiveDivisorRow
  apply sum_congr rfl
  intro k hk
  obtain ⟨v,hv⟩ := hqd.trans (mem_filter.mp hk).2
  rw [mul_add,phase_add,show (k:ℝ)*((a:ℝ)/q)=(v*a:ℕ) by
    rw [hv]; push_cast; field_simp,hn,mul_one]

theorem resonantMobiusWave_at_center {q : ℕ} (hq : 0<q) (n R Q a : ℕ) (β : ℝ) :
    resonantMobiusWave n R Q q (β+a/(q:ℝ)) = resonantMobiusWave n R Q q β := by
  unfold resonantMobiusWave smallDivisorWave
  exact sum_congr rfl fun d hd => congrArg (_ * ·) (positiveDivisorRow_at_resonant_center hq (mem_filter.mp hd).2 n a β)

noncomputable def resonantMobiusSignedRow (n R Q q : ℕ) (ρ : ℝ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), ∫ β in -ρ..ρ,
    resonantMobiusWave n R Q q (β+a/(q:ℝ))^2 * E (-(n:ℝ)*(β+a/(q:ℝ)))

theorem resonantMobiusSignedRow_exact (n R Q q : ℕ) (hq : 0<q) (ρ : ℝ) :
    resonantMobiusSignedRow n R Q q ρ =
    (dyadicRamanujanDivisor n q:ℂ)*(∫ β in -ρ..ρ, resonantMobiusWave n R Q q β^2*E (-(n:ℝ)*β)) := by
  have h (a : ℕ) (β : ℝ) :
      resonantMobiusWave n R Q q (β+a/(q:ℝ))^2*E (-(n:ℝ)*(β+a/(q:ℝ))) =
      E (-((n:ℝ)*a/q))*(resonantMobiusWave n R Q q β^2 * E (-(n:ℝ)*β)) := by
    rw [resonantMobiusWave_at_center hq,mul_add,phase_add,show -(n:ℝ)*(a/q) = -(n*a/q) by ring]
    ring
  unfold resonantMobiusSignedRow
  simp_rw [h,intervalIntegral.integral_const_mul]
  rw [←sum_mul,actualRamanujan_neg_eq_divisor n q hq]

private theorem resonant_harmonic (R : ℕ) :
    (∑ j ∈ range R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    by_cases h : R=0
    · subst R; norm_num
    · have hR : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(R:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hR)
      rw [Real.log_div hp.ne' hR.ne',inv_div] at hl
      have he : 1-(R:ℝ)/(R+1) = ((R:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]


private theorem resonant_multiple_reciprocals (R Q d : ℕ) (hd : 0<d) :
    ∑ j ∈ Ico R Q, (if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0) ≤ 1+Real.log Q := by
  rw [←sum_filter]
  apply le_trans _ (resonant_harmonic Q)
  let s := (Ico R Q).filter (fun j => d∣j+1)
  let u (j:ℕ) := (j+1)/d-1
  have hdiv (j:ℕ) (hj:j∈s) :
      0<(j+1)/d ∧ d*((j+1)/d)=j+1 ∧ j<Q := by
    obtain ⟨hj,hjd⟩ := mem_filter.mp hj
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hjd) hd,Nat.mul_div_cancel' hjd,(mem_Ico.mp hj).2⟩
  apply sum_le_sum_of_injOn u
  · intro i hi j hj he
    obtain ⟨hi',him,_⟩ := hdiv _ hi
    obtain ⟨hj',hjm,_⟩ := hdiv _ hj
    dsimp only [u] at he
    have hh : (i+1)/d=(j+1)/d := by omega
    rw [hh] at him
    omega
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    obtain ⟨hpos,_,hQ⟩ := hdiv _ hj
    have hle := Nat.div_le_self (j+1) d
    exact mem_range.mpr (by dsimp only [u]; omega)
  · intro j hj
    obtain ⟨hj0,he,_⟩ := hdiv _ hj
    dsimp only [u]
    rw [Nat.sub_add_cancel (by omega : 1≤(j+1)/d)]
    have hd' : (0:ℝ)<d := by exact_mod_cast hd
    have hk' : (0:ℝ)<((j+1)/d:ℕ) := by exact_mod_cast hj0
    have hprod : (d:ℝ)*(((j+1)/d:ℕ):ℝ) = ((j+1:ℕ):ℝ) := by exact_mod_cast he
    rw [←hprod]
    field_simp
    exact le_rfl
  · intro k _ _
    positivity

theorem resonantRamanujan_harmonic (n R Q : ℕ) (hn : 0<n) :
    (∑ j∈Ico R Q, |(dyadicRamanujanDivisor n (j+1):ℝ)|/((j+1:ℕ):ℝ)) ≤
      (1+Real.log Q)*(n.divisors.card:ℝ) := by
  have hrow (q:ℕ) (hq:0<q) : |(dyadicRamanujanDivisor n q:ℝ)|/(q:ℝ) ≤
      ∑ d ∈ n.divisors, if d∣q then (d:ℝ)/(q:ℝ) else 0 := by
    have he : (q.gcd n).divisors = n.divisors.filter (fun d => d∣q) := by
      ext d
      simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
      simp [hn.ne',(Nat.gcd_pos_of_pos_left _ hq).ne',and_comm]
    unfold dyadicRamanujanDivisor
    push_cast
    rw [←sum_filter,←sum_div,he]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [abs_mul,show |(d:ℝ)|=(d:ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q/d)))
  calc
    _ ≤ ∑ j ∈ Ico R Q, ∑ d ∈ n.divisors, if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0 :=
      sum_le_sum fun j _ => hrow (j+1) (Nat.succ_pos j)
    _ = ∑ d ∈ n.divisors, ∑ j ∈ Ico R Q, if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ n.divisors, (1+Real.log Q) :=
      sum_le_sum fun d hd => resonant_multiple_reciprocals R Q d (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp [nsmul_eq_mul,mul_comm,mul_add]


private theorem resonant_index_shift (R Q : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ→A) :
    (∑ d∈Ioc R Q,f d) = ∑ j∈Ico R Q,f (j+1) := by
  symm
  apply sum_bij (fun j _ => j+1)
  · intro j hj
    obtain ⟨hl,hu⟩ := mem_Ico.mp hj
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro i hi j hj h
    omega
  · intro d hd
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hd
    exact ⟨d-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro j _
    rfl

theorem positiveDivisorRow_trivial_bound (n d : ℕ) (hd : 0<d) (t : ℝ) :
    ‖positiveDivisorRow n d t‖ ≤ (n:ℝ)/d := by
  let S := (Icc 1 n).filter (fun k => d∣k)
  have hsub : S ⊆ (range n.succ).filter (fun k => k≠0 ∧ d∣k) := by
    intro k hk
    obtain ⟨hi,hk⟩ := mem_filter.mp hk
    obtain ⟨hk1,hkn⟩ := mem_Icc.mp hi
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,hk⟩
  have hcard := card_le_card hsub
  rw [Nat.card_multiples'] at hcard
  calc
    _ ≤ ∑ k∈S, ‖E ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = S.card := by simp [show ∀ x : ℝ, ‖E x‖=1 from fun _ => Complex.norm_exp_ofReal_mul_I _]
    _ ≤ ((n/d:ℕ):ℝ) := by exact_mod_cast hcard
    _ ≤ _ := (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ)<d)).mpr (by exact_mod_cast Nat.div_mul_le_self n d)

theorem resonantMobiusWave_bound (n R Q q : ℕ) (hq : 0<q) (t : ℝ) :
    ‖resonantMobiusWave n R Q q t‖ ≤
      (n:ℝ)*(Real.log Q)*(1+Real.log Q)/(q:ℝ) := by
  let I := (Ioc R Q).filter (fun d => q∣d)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  let C := (n:ℝ)*(Real.log Q)/(q:ℝ)
  have hC : 0≤C := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) hq'.le
  have hterm (d : ℕ) (hd : d∈I) :
      ‖(crtLambdaCoefficient d:ℂ)*positiveDivisorRow n d t‖ ≤ C*((q:ℝ)/d) := by
    obtain ⟨hdI,_⟩ := mem_filter.mp hd
    obtain ⟨hRd,hdQ⟩ := mem_Ioc.mp hdI
    have hdp : 0<d := by omega
    have hdn : (0:ℝ)<d := by exact_mod_cast hdp
    have hc : ‖(crtLambdaCoefficient d:ℂ)‖ ≤ Real.log Q := by
      rw [Complex.norm_real,Real.norm_eq_abs,crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg d)]
      have hm : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
      exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hm).trans
        (Real.log_le_log hdn (by exact_mod_cast hdQ))
    rw [norm_mul]
    apply (mul_le_mul hc (positiveDivisorRow_trivial_bound n d hdp t) (norm_nonneg _) (Real.log_natCast_nonneg _)).trans
    dsimp [C]
    apply le_of_eq
    field_simp
  have hsum : (∑ d∈I,(q:ℝ)/d) ≤ 1+Real.log Q := by
    change (∑ d∈(Ioc R Q).filter (fun d => q∣d),(q:ℝ)/d) ≤ _
    rw [sum_filter,resonant_index_shift]
    exact resonant_multiple_reciprocals R Q q hq
  calc
    _ ≤ ∑ d∈I,‖(crtLambdaCoefficient d:ℂ)*positiveDivisorRow n d t‖ := norm_sum_le _ _
    _ ≤ ∑ d∈I,C*((q:ℝ)/d) := sum_le_sum hterm
    _ = C*∑ d∈I, (q:ℝ)/d := (mul_sum ..).symm
    _ ≤ C*(1+Real.log Q) := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by dsimp [C]; ring

theorem resonantMobiusSignedRow_band_bound {n : ℕ} (hn : 0<n) (R Q : ℕ) (hQ : 0<Q) :
    ‖∑ j∈Ico R Q,resonantMobiusSignedRow n R Q (j+1) (naturalTubeRadius (3*Q) (j+1))‖ ≤
    (2/(3*(Q:ℝ)))*((n:ℝ)*Real.log Q*(1+Real.log Q)/((R:ℝ)+1))^2*
      (1+Real.log Q)*(n.divisors.card:ℝ) := by
  let A := (n:ℝ)*Real.log Q*(1+Real.log Q)
  let B := A/((R:ℝ)+1)
  let C := (2/(3*(Q:ℝ)))*B^2
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hA : 0≤A := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
    (by linarith [Real.log_natCast_nonneg Q])
  have hC : 0≤C := mul_nonneg (by positivity) (sq_nonneg _)
  have hrow (j : ℕ) (hj : j∈Ico R Q) :
      ‖resonantMobiusSignedRow n R Q (j+1) (naturalTubeRadius (3*Q) (j+1))‖ ≤
        C*(|(dyadicRamanujanDivisor n (j+1):ℝ)|/((j+1:ℕ):ℝ)) := by
    let q := j+1
    let ρ := naturalTubeRadius (3*Q) q
    have hq : 0<q := Nat.succ_pos _
    have hq' : (0:ℝ)<q := by exact_mod_cast hq
    have hρ : 0≤ρ := by dsimp [ρ,naturalTubeRadius]; positivity
    have hjR : (R:ℝ)+1 ≤ q := by exact_mod_cast Nat.succ_le_succ (mem_Ico.mp hj).1
    have hbound (t : ℝ) : ‖resonantMobiusWave n R Q q t‖ ≤ B :=
      (resonantMobiusWave_bound n R Q q hq t).trans
        (div_le_div_of_nonneg_left hA (by positivity) hjR)
    have hi : ‖∫ β in -ρ..ρ, resonantMobiusWave n R Q q β^2*E (-(n:ℝ)*β)‖ ≤ B^2*(2*ρ) := by
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

noncomputable def resonantMobiusHighMass (n : ℕ) : ℂ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  ∑ j∈Ico R Q,resonantMobiusSignedRow n R Q (j+1) (naturalTubeRadius (3*Q) (j+1))

set_option maxRecDepth 20000 in
theorem resonantMobiusHighMass_power :
    ∀ᶠ n : ℕ in atTop, ‖resonantMobiusHighMass n‖ ≤ 2^27*(n:ℝ)^(7/8:ℝ) := by
  let t := fun n : ℕ => (n:ℝ)^(1/128:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/128)).comp tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/128)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 2,hl.eventually (gt_mem_nhds zero_lt_one),eventually_ge_atTop (1:ℕ)] with n hT hlog hn
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
  have hnum : (n:ℝ)*Real.log Q*(1+Real.log Q) ≤ T^128*T*(2*T) := by
    rw [←h128]
    gcongr
  have hratio : (n:ℝ)*Real.log Q*(1+Real.log Q)/((R:ℝ)+1) ≤ 64*T^71 := by
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
  apply (resonantMobiusSignedRow_band_bound hn R Q hQn).trans
  rw [←h112]
  calc
    _ ≤ (2/T^64)*(64*T^71)^2*(2*T)*(4096*T^32) := by
      gcongr
    _ = 2^26*T^111 := by field_simp; ring
    _ ≤ 2^27*T^112 := by
      exact mul_le_mul (by norm_num) (pow_le_pow_right₀ hT1 (by decide : 111≤112)) (by positivity) (by positivity)

theorem resonantMobiusHighMass_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖resonantMobiusHighMass n‖ ≤ ε*(n:ℝ) := by
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/8:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hdec : Tendsto (fun n : ℕ => 2^27*(n:ℝ)^(-(1/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=((2:ℝ)^27))).mul hu
  filter_upwards [resonantMobiusHighMass_power,eventually_ge_atTop (1:ℕ),
    hdec.eventually (gt_mem_nhds hε)] with n h hn he
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_right he.le hn0.le
  change (2^27*(n:ℝ)^(-(1/8:ℝ)))*(n:ℝ) ≤ _ at hmul
  rw [mul_assoc,←Real.rpow_add_one hn0.ne',show -(1/8:ℝ)+1=7/8 by norm_num] at hmul
  exact hmul

end GoldbachPartial