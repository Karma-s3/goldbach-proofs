import QuarterEndpointWing
import OddPrimeHalfPeriod
import HalfPeriodWings

namespace GoldbachPartial

open Finset MeasureTheory Filter Set ExtendedArcCoefficient
open scoped Topology

private theorem even_fourier_half_periodic {m : ℤ} (he : Even m) :
    Function.Periodic (fun t : ℝ => E ((m:ℝ)*t)) (1/2) := by
  obtain ⟨a,ha⟩ := he
  have hE : E (a:ℝ)=1 := by
    unfold E
    convert Complex.exp_int_mul_two_pi_mul_I a using 2; push_cast; ring
  intro t
  change E ((m:ℝ)*(t+1/2)) = _
  rw [show (m:ℝ)*(t+1/2) = m*t+a by rw [ha]; push_cast; ring,phase_add,hE,mul_one]

private theorem full_prime_wave_split {n : ℕ} (hn : 2≤n) (t : ℝ) :
    (∑ k ∈ range (n+1), (weight k:ℂ)*E ((k:ℝ)*t)) =
       oddPrimeWave n t + (Real.log 2:ℂ)*E (2*t) := by
  calc
    _ = ∑ k ∈ range (n+1), ((oddPrimeWeight k:ℂ)*E ((k:ℝ)*t) +
       if k=2 then (Real.log 2:ℂ)*E (2*t) else 0) := by
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : k=2
      · subst k; simp [weight,oddPrimeWeight,Nat.prime_two]
      · simp [oddPrimeWeight,hk]
    _ = _ := by rw [sum_add_distrib]; simp [oddPrimeWave,show 2<n+1 by omega]


theorem oddPrimeWave_norm_le_primorial (n : ℕ) (t : ℝ) :
    ‖oddPrimeWave n t‖ ≤ (n:ℝ)*Real.log 4 := by
  have hw (k : ℕ) : 0≤weight k := by
    by_cases hp : k.Prime <;> simp [weight,hp,Real.log_natCast_nonneg]
  have hs (k : ℕ) : 0≤oddPrimeWeight k := by unfold oddPrimeWeight; split <;> simp_all only [le_refl]
  have hle (k : ℕ) : oddPrimeWeight k ≤ weight k := by unfold oddPrimeWeight; split <;> simp_all only [le_refl]
  have hweight : (∑ p ∈ range (n+1), weight p) = Real.log (primorial n : ℝ) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    · simp [sum_filter,weight]
    · intro p hp; exact_mod_cast (mem_filter.mp hp).2.ne_zero
  unfold oddPrimeWave
  calc
    _ ≤ ∑ k∈range (n+1), ‖(oddPrimeWeight k:ℂ)*E ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ ≤ ∑ k∈range (n+1), weight k := by
      apply sum_le_sum
      intro k _
      rw [norm_mul,show ‖E ((k:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,
        mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs k)]
      exact hle k
    _ ≤ _ := by
      rw [hweight]
      have h := Real.log_le_log (show 0<(primorial n:ℝ) by exact_mod_cast primorial_pos n)
        (show (primorial n:ℝ) ≤ (4:ℝ)^n by exact_mod_cast primorial_le_four_pow n)
      simpa using h

theorem primeSquareKernel_half_shift_bound {n : ℕ} (hn : 2≤n) (he : Even n) (t : ℝ) :
    ‖primeSquareKernel n (t+1/2)-primeSquareKernel n t‖ ≤
      4*Real.log 2*Real.log 4*(n:ℝ) := by
  have hphase : E (-(n:ℝ)*(t+1/2))=E (-(n:ℝ)*t) := by
    have hnz : Even (-(n:ℤ)) := (show Even (n:ℤ) by exact_mod_cast he).neg
    simpa only [Int.cast_neg,Int.cast_natCast] using even_fourier_half_periodic hnz t
  have htwo : E (2*(t+1/2))=E (2*t) := by
    simpa using even_fourier_half_periodic (show Even (2:ℤ) by decide) t
  have hsplit : primeSquareKernel n (t+1/2)-primeSquareKernel n t =
      -(4:ℂ)*(Real.log 2:ℂ)*E (2*t)*oddPrimeWave n t*E (-(n:ℝ)*t) := by
    unfold primeSquareKernel
    rw [full_prime_wave_split hn (t+1/2),full_prime_wave_split hn t,hphase,htwo,oddPrimeWave_add_half]
    ring
  rw [hsplit]
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)),
    show ‖E (2*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,
    show ‖E (-(n:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
  norm_num only [Complex.norm_ofNat]
  linarith only [mul_le_mul_of_nonneg_left (oddPrimeWave_norm_le_primorial n t)
    (show 0≤4*Real.log 2 by positivity)]

private theorem two_translated_wings_mass (n : ℕ) {a b c d : ℝ} (hab : a≤b)
    (hdis : Disjoint (Set.Ioc (c+a) (c+b)) (Set.Ico (d-b) (d-a)))
    (hc₁ : 0≤c+a) (hc₂ : c+b≤1) (hd₁ : 0≤d-b) (hd₂ : d-a≤1) :
    primeArcMass (Set.Ioc (c+a) (c+b) ∪ Set.Ico (d-b) (d-a)) n =
      (∫ t in a..b, primeSquareKernel n (c+t)+primeSquareKernel n (d-t)).re := by
  let f := primeSquareKernel n
  have hc : Continuous f := by change Continuous (primeSquareKernel n); unfold primeSquareKernel E; fun_prop
  have hsub : Set.Ioc (c+a) (c+b) ∪ Set.Ico (d-b) (d-a) ⊆ Set.Icc 0 1 := by
    rintro x (h|h)
    · exact ⟨hc₁.trans h.1.le,h.2.trans hc₂⟩
    · exact ⟨hd₁.trans h.1,h.2.le.trans hd₂⟩
  have hleft := intervalIntegral.integral_comp_add_left (a:=a) (b:=b) f c
  have hright := intervalIntegral.integral_comp_sub_left (a:=a) (b:=b) f d
  have hl : Continuous (fun t => f (c+t)) := hc.comp (continuous_const.add continuous_id)
  have hr : Continuous (fun t => f (d-t)) := hc.comp (continuous_const.sub continuous_id)
  unfold primeArcMass
  change (∫ t in (0:ℝ)..1, (Set.Ioc (c+a) (c+b) ∪ Set.Ico (d-b) (d-a)).indicator f t).re =
    (∫ t in a..b, f (c+t)+f (d-t)).re
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (measurableSet_Ioc.union measurableSet_Ico),Set.inter_eq_right.mpr hsub,
    setIntegral_union hdis measurableSet_Ico (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self),
    integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : c+a≤c+b),
    ← intervalIntegral.integral_of_le (by linarith : d-b≤d-a),
    intervalIntegral.integral_add (hl.intervalIntegrable _ _) (hr.intervalIntegrable _ _),hleft,hright]

theorem halfPeriodWings_endpoint_transfer {n : ℕ} (hn : 2≤n) (he : Even n) {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hb : b≤1/3) :
    |primeArcMass (Set.Ioc (1/2+a) (1/2+b) ∪ Set.Ico (1/2-b) (1/2-a)) n -
      primeArcMass (Set.Ioc a b ∪ Set.Ico (1-b) (1-a)) n| ≤
      8*Real.log 2*Real.log 4*(n:ℝ)*(b-a) := by
  let f := primeSquareKernel n
  let B := 4*Real.log 2*Real.log 4*(n:ℝ)
  have hc : Continuous f := by change Continuous (primeSquareKernel n); unfold primeSquareKernel E; fun_prop
  have hd₁ : Disjoint (Set.Ioc (1/2+a) (1/2+b)) (Set.Ico (1/2-b) (1/2-a)) := by
    apply Set.disjoint_left.mpr
    intro t h h'; linarith [h.1,h'.2]
  have hd₂ : Disjoint (Set.Ioc (0+a) (0+b)) (Set.Ico (1-b) (1-a)) := by
    apply Set.disjoint_left.mpr
    intro t h h'; linarith [h.2,h'.1]
  have hmid := two_translated_wings_mass n hab hd₁ (by linarith) (by linarith) (by linarith) (by linarith)
  have hend := two_translated_wings_mass n hab hd₂ (by linarith) (by linarith) (by linarith) (by linarith)
  simp only [zero_add] at hend
  rw [hmid,hend,←Complex.sub_re]
  let g := fun t : ℝ => f (1/2+t)+f (1/2-t)
  let h := fun t : ℝ => f t+f (1-t)
  change |((∫ t in a..b, g t) - ∫ t in a..b, h t).re| ≤ _
  have hg : Continuous g := (hc.comp (continuous_const.add continuous_id)).add (hc.comp (continuous_const.sub continuous_id))
  have hh : Continuous h := hc.add (hc.comp (continuous_const.sub continuous_id))
  rw [←intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  have hp (t : ℝ) : ‖g t-h t‖ ≤ B+B := by
    have h₁ : ‖f (1/2+t)-f t‖ ≤ B := by simpa only [add_comm t (1/2)] using primeSquareKernel_half_shift_bound hn he t
    have h₂ : ‖f (1/2-t)-f (1-t)‖ ≤ B := by
      rw [norm_sub_rev]
      have hh' := primeSquareKernel_half_shift_bound hn he (1/2-t)
      rwa [show (1/2-t)+(1/2:ℝ)=1-t by ring] at hh'
    have hid : g t-h t=(f (1/2+t)-f t)+(f (1/2-t)-f (1-t)) := by dsimp only [g,h]; ring
    exact hid ▸ (norm_add_le _ _).trans (add_le_add h₁ h₂)
  apply (Complex.abs_re_le_norm _).trans
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (fun t _ => hp t)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact hi.trans_eq (by dsimp only [B]; ring)


private theorem halfWing_outerRadius_tendsto_zero :
    Tendsto (fun n : ℕ => (n:ℝ)^(1/4:ℝ)/n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hpos : (0:ℝ)<n := by exact_mod_cast hn
  change (n:ℝ)^(-(3/4:ℝ))=(n:ℝ)^(1/4:ℝ)/n
  rw [show -(3/4:ℝ)=1/4-1 by norm_num,Real.rpow_sub_one hpos.ne']

theorem halfPeriodWings_mass_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n → |primeArcMass (halfPeriodWings n) n| ≤ ε*(n:ℝ) := by
  let K := 8*Real.log 2*Real.log 4
  have hK : 0≤K := by dsimp only [K]; positivity
  have hKb : Tendsto (fun n : ℕ => K*((n:ℝ)^(1/4:ℝ)/n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=K)).mul halfWing_outerRadius_tendsto_zero
  have he2 : 0<ε/2 := half_pos hε
  filter_upwards [quarterEndpointStrips_mass_small hψ he2,quarterEndpointStrips_geometry,
    eventually_ge_atTop (2:ℕ),halfWing_outerRadius_tendsto_zero.eventually (gt_mem_nhds
      (by norm_num : (0:ℝ)<1/3)),hKb.eventually (gt_mem_nhds he2)] with n hend hg hn hb hsb
  intro he
  let a := (medDeskQ n:ℝ)/n
  let b := (n:ℝ)^(1/4:ℝ)/n
  have ha : 0≤a := by dsimp only [a]; positivity
  have hab : a≤b := hg.1.le
  have ht := halfPeriodWings_endpoint_transfer hn he ha hab (show b≤1/3 from hb.le)
  change |primeArcMass (halfPeriodWings n) n-primeArcMass (quarterEndpointStrips n) n| ≤
    K*(n:ℝ)*(b-a) at ht
  have hs : K*b ≤ ε/2 := hsb.le
  have he' : K*(n:ℝ)*(b-a) ≤ ε/2*(n:ℝ) := calc
    _ ≤ K*(n:ℝ)*b := by gcongr; linarith
    _ = (K*b)*(n:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)
  have htri := abs_add_le (primeArcMass (halfPeriodWings n) n-primeArcMass (quarterEndpointStrips n) n)
    (primeArcMass (quarterEndpointStrips n) n)
  rw [sub_add_cancel] at htri
  linarith only [htri,ht,he',hend]

theorem halfPeriodWings_mass_floor (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n → -(ε*(n:ℝ)) ≤ primeArcMass (halfPeriodWings n) n := by
  filter_upwards [halfPeriodWings_mass_small hψ hε] with n hn
  intro he
  exact (abs_le.mp (hn he)).1

end GoldbachPartial