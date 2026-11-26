import DistantPrimePairReduction

namespace GoldbachPartial
open Finset Filter MeasureTheory
open scoped Topology

theorem farOnTargetWeight_single_sum (n H : ℕ) :
    farOnTargetWeight n H = ∑ p ∈ range (n+1),
      if p+H<n-p ∨ n-p+H<p then weight p*weight (n-p) else 0 := by
  let F := fun p r : ℕ => if p+r=n then (weight p:ℂ)*(weight r:ℂ) else 0
  have hs : ∀ p r, F p r=F r p := by
    intro p r
    simp only [F,Nat.add_comm r p,mul_comm (weight r:ℂ) (weight p:ℂ)]
  have he := ordered_far_gap_sum n H F hs
  apply Complex.ofReal_injective
  simp only [farOnTargetWeight,targetGapWeight,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_sum,apply_ite,Complex.ofReal_zero]
  change 2*(∑ d ∈ Ioc H n,∑ p ∈ (range (n+1)).filter (fun p => p+d≤n),F p (p+d)) = _
  rw [he]
  apply sum_congr rfl
  intro p hp
  have hp' := mem_range.mp hp
  rw [sum_eq_single (n-p)]
  · have hit : p+(n-p)=n := by omega
    simp [F,hit]
  · intro r _ hr
    have hmiss : p+r≠n := by omega
    simp [F,hmiss]
  · intro hn
    exact (hn (mem_range.mpr (by omega))).elim

private theorem centerWeight_nonneg (p : ℕ) : 0≤weight p := by
  unfold weight
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

private theorem centerWeight_le {n p : ℕ} (hn : 1≤n) (hp : p≤n) :
    weight p ≤ Real.log n := by
  unfold weight
  split_ifs with h
  · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem corr_sub_farOnTargetWeight {n H : ℕ} (hn : 1≤n) :
    0≤corr n-farOnTargetWeight n H ∧
      corr n-farOnTargetWeight n H ≤ (H+1:ℕ)*(Real.log n)^2 := by
  let I := (range (n+1)).filter (fun p => ¬(p+H<n-p ∨ n-p+H<p))
  have hsplit : corr n-farOnTargetWeight n H = ∑ p ∈ I,weight p*weight (n-p) := by
    rw [farOnTargetWeight_single_sum,corr,←sum_sub_distrib]
    dsimp only [I]
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp_all
  rw [hsplit]
  constructor
  · exact sum_nonneg fun p _ => mul_nonneg (centerWeight_nonneg p) (centerWeight_nonneg _)
  have hsub : I⊆Icc ((n-H+1)/2) ((n+H)/2) := by
    intro p hp
    have h := mem_filter.mp hp
    have h' := mem_range.mp h.1
    have h'' := h.2
    exact mem_Icc.mpr (by omega)
  have hcard : I.card≤H+1 := (card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _p ∈ I,(Real.log n)^2 := by
      apply sum_le_sum
      intro p hp
      have hl : p≤n := by have ht := mem_range.mp (mem_filter.mp hp).1; omega
      rw [sq]
      exact mul_le_mul (centerWeight_le hn hl) (centerWeight_le hn (Nat.sub_le ..))
        (centerWeight_nonneg _) (Real.log_natCast_nonneg _)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

theorem close_target_eventually_sqrt :
    ∀ᶠ n : ℕ in atTop, corr n-farOnTargetWeight n (closePrimeGapCutoff n) ≤ 2*Real.sqrt n := by
  let t := fun n : ℕ => (n:ℝ)^(1/8:ℝ)
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/8)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hl.eventually (gt_mem_nhds zero_lt_one)] with n hn hlog
  let T := t n
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have h1 : 1≤T := Real.one_le_rpow hn1 (by norm_num)
  have h0 : 0<T := by linarith
  change Real.log n/T<1 at hlog
  have hL : Real.log n≤T := by linarith [(div_lt_iff₀ h0).mp hlog]
  have hpow (k : ℕ) : T^k=(n:ℝ)^((1/8:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤(n:ℝ))]
  have h2 : T^2=(n:ℝ)^(1/4:ℝ) := by rw [hpow]; norm_num
  have h4 : T^4=Real.sqrt n := by rw [hpow,Real.sqrt_eq_rpow]; norm_num
  have hH : (closePrimeGapCutoff n:ℝ)≤T^2 := by rw [h2]; exact Nat.floor_le (by positivity)
  apply (corr_sub_farOnTargetWeight hn).2.trans
  push_cast
  rw [←h4]
  calc
    _ ≤ (T^2+1)*T^2 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (T^2-1),sq_nonneg (T-1)]

theorem high_tube_volume_upper {n : ℕ} (hn : 1≤n) :
    volume.real (highNaturalPrimeTubes n) ≤ 2/3 := by
  let Q := naturalTubeScale n
  let R := terminalPrimeArcCutoff n
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hQ : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  change volume.real (naturalTubeUnion R Q (3*Q))≤_
  rw [naturalTubeUnion_realVolume_eq R Q (3*Q) (by omega)]
  have hs : (∑ j ∈ Ico R Q, ((j+1).totient:ℝ)/((j+1:ℕ):ℝ))≤(Q:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Ico R Q,(1:ℝ) := by
        apply sum_le_sum
        intro j _
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.totient_le _
      _ ≤ (Q:ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Ico]; exact_mod_cast Nat.sub_le Q R
  push_cast at hs ⊢
  calc
    _ ≤ (2/(3*(Q:ℝ)))*(Q:ℝ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (2/3:ℝ) := by
      have : (0:ℝ)<Q := by exact_mod_cast hQ
      field_simp

open ExtendedArcCoefficient

private theorem centered_integral_identity {n H : ℕ} (hH : H≤n) {V : Set ℝ}
    (hm : MeasurableSet V) (hi : V⊆Set.Icc 0 1) :
    primeArcMass V n =
      ((∫ t in V,closePrimeGapKernel n H t) + ∫ t in V,farShortOffTargetKernel n H t).re +
      (∫ t in V,distantPrimePairKernel n H t).re + volume.real V*farOnTargetWeight n H := by
  have hc : Continuous (closePrimeGapKernel n H) := by
    unfold closePrimeGapKernel primeGapKernel E
    fun_prop
  have hs : Continuous (farShortOffTargetKernel n H) := by
    unfold farShortOffTargetKernel farPairKernelAtModes
    apply continuous_finsetSum
    intro p _
    apply continuous_finsetSum
    intro r _
    split_ifs <;> first | exact continuous_const | dsimp [primePairMode,E]; fun_prop
  have hd : Continuous (distantPrimePairKernel n H) := by
    unfold distantPrimePairKernel
    apply continuous_finsetSum
    intro p _
    apply continuous_finsetSum
    intro r _
    split_ifs <;> first | exact continuous_const | dsimp [primePairMode,E]; fun_prop
  have hcI : IntegrableOn (closePrimeGapKernel n H) V := hc.continuousOn.integrableOn_Icc.mono_set hi
  have hsI : IntegrableOn (farShortOffTargetKernel n H) V := hs.continuousOn.integrableOn_Icc.mono_set hi
  have hdI : IntegrableOn (distantPrimePairKernel n H) V := hd.continuousOn.integrableOn_Icc.mono_set hi
  have hwI : IntegrableOn (fun _ : ℝ => (farOnTargetWeight n H:ℂ)) V :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set hi
  rw [primeArcMass_eq_setIntegral_re_of_subset_Icc n hm hi]
  change (∫ t in V,primeSquareKernel n t).re=_
  simp_rw [primeSquareKernel_double_partition hH]
  rw [integral_add (f:=fun t => closePrimeGapKernel n H t + farShortOffTargetKernel n H t +
    distantPrimePairKernel n H t) (g:=fun _ : ℝ => (farOnTargetWeight n H:ℂ))
    ((hcI.add hsI).add hdI) hwI,
    integral_add (f:=fun t => closePrimeGapKernel n H t + farShortOffTargetKernel n H t)
      (g:=distantPrimePairKernel n H) (hcI.add hsI) hdI,
    integral_add hcI hsI,setIntegral_const,Complex.real_smul]
  simp [Complex.mul_re]

/-- The complement arc and the distant frequencies on the high arcs give one signed statistic. -/
noncomputable def centeredDistantMass (n : ℕ) : ℝ :=
  primeArcMass (highNaturalPrimeTubes n)ᶜ n +
    (∫ t in highNaturalPrimeTubes n,distantPrimePairKernel n (closePrimeGapCutoff n) t).re

theorem centeredDistantMass_error :
    ∀ᶠ n : ℕ in atTop,
      |centeredDistantMass n-(1-volume.real (highNaturalPrimeTubes n))*corr n| ≤
        (184/3:ℝ)*(n:ℝ)^(7/8:ℝ)+2*Real.sqrt n := by
  filter_upwards [high_tubes_two_error_power,highNaturalPrimeTubes_geometry,
    close_target_eventually_sqrt,eventually_ge_atTop (1:ℕ)] with n he hg ht hn
  let V := highNaturalPrimeTubes n
  let H := closePrimeGapCutoff n
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hH : H≤n := Nat.floor_le_of_le (by
    change (n:ℝ)^(1/4:ℝ)≤n
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/4:ℝ)≤1))
  have hm : MeasurableSet V := naturalTubeUnion_measurable ..
  have hsplit := corr_eq_primeArcMass n V hm
  have hid := centered_integral_identity hH hm hg.1
  let z := (∫ t in V,closePrimeGapKernel n H t) + ∫ t in V,farShortOffTargetKernel n H t
  change primeArcMass V n = z.re + _ + volume.real V*farOnTargetWeight n H at hid
  have hz : |z.re|≤(184/3:ℝ)*(n:ℝ)^(7/8:ℝ) := (Complex.abs_re_le_norm _).trans he
  have hv : volume.real V≤1 := (high_tube_volume_upper hn).trans (by norm_num)
  have hnneg := (corr_sub_farOnTargetWeight (H:=H) hn).1
  have heq : centeredDistantMass n-(1-volume.real V)*corr n =
      volume.real V*(corr n-farOnTargetWeight n H)-z.re := by
    unfold centeredDistantMass
    change primeArcMass Vᶜ n + (∫ t in V,distantPrimePairKernel n H t).re - _ = _
    linarith only [hsplit,hid]
  change |centeredDistantMass n-(1-volume.real V)*corr n|≤_
  rw [heq]
  have hnn := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=V)) hnneg
  have htop := (mul_le_mul_of_nonneg_right hv hnneg).trans (by simpa only [one_mul] using ht)
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hz).2,Real.sqrt_nonneg (n:ℝ)],
    by linarith [(abs_le.mp hz).1]⟩

theorem centeredDistantMass_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      |centeredDistantMass n-(1-volume.real (highNaturalPrimeTubes n))*corr n| ≤ ε*(n:ℝ) := by
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hv : Tendsto (fun n : ℕ => (190/3:ℝ)*(n:ℝ)^(-(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=(190/3:ℝ))).mul hu
  filter_upwards [centeredDistantMass_error,eventually_ge_atTop (1:ℕ),
    hv.eventually (gt_mem_nhds hε)] with n he hn hd
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have h0 : (0:ℝ)<n := by linarith
  have hs : Real.sqrt n ≤ (n:ℝ)^(7/8:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hd.le h0.le
  change ((190/3:ℝ)*(n:ℝ)^(-(1/8:ℝ)))*(n:ℝ)≤_ at hm
  rw [mul_assoc,←Real.rpow_add_one h0.ne',show -(1/8:ℝ)+1=7/8 by norm_num] at hm
  linarith only [he,hs,hm]

/-- A two-way criterion for the frozen dyadic prime-correlation floor. -/
theorem dyadic_floor_iff_centeredDistantMass :
    (∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p))) ↔
    (∃ d : ℝ, 0<d ∧ ∀ᶠ n : ℕ in atTop, Even n → d*(n:ℝ)≤centeredDistantMass n) := by
  constructor
  · rintro ⟨c,N,hc,hfloor⟩
    refine ⟨c/6,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),
      centeredDistantMass_eventually_small (ε:=c/6) (by positivity)] with n hn hn1 he
    intro heven
    have hcor : c*(n:ℝ)≤corr n := hfloor n n hn le_rfl (by omega) heven
    have hs : 1/3≤1-volume.real (highNaturalPrimeTubes n) := by
      linarith only [high_tube_volume_upper hn1]
    have hnon : (0:ℝ)≤c*n := by positivity
    have hlow := mul_le_mul hs hcor hnon (by linarith only [hs])
    linarith only [(abs_le.mp he).1,hlow]
  · rintro ⟨d,hd,hrest⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hrest.and
      (centeredDistantMass_eventually_small (ε:=d/2) (by positivity)))
    refine ⟨d/2,N,by positivity,?_⟩
    intro X n hX hXn _ heven
    change _≤corr n
    obtain ⟨hm,he⟩ := hN n (hX.trans hXn)
    have hc : 0≤corr n := sum_nonneg fun p _ => mul_nonneg (centerWeight_nonneg p) (centerWeight_nonneg _)
    have hv := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hc
    linarith only [hm heven,(abs_le.mp he).2,hv]

end GoldbachPartial