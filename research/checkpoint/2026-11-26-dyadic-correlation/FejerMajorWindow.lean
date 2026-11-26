import PrimeArcModelBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient
noncomputable section

abbrev fejerWindowEnergy (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in -r..r, ‖dirichletGeometricKernel n t‖^2

private theorem geometricKernel_even_norm (n : ℕ) (t : ℝ) :
    ‖dirichletGeometricKernel n (-t)‖=‖dirichletGeometricKernel n t‖ := by
  have he (z : ℝ) : E (-z)=(starRingEnd ℂ) (E z) := by
    unfold E
    rw [←Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  unfold dirichletGeometricKernel
  simp_rw [mul_neg,he]
  rw [←map_sum]
  exact Complex.norm_conj _

theorem fejer_kernel_pointwise (n : ℕ) {t : ℝ} (ht : 0<t) (hb : t≤1/2) :
    ‖dirichletGeometricKernel n t‖ ≤ 1/(2*t) := by
  have hs := Real.mul_le_sin (x:=Real.pi*t) (mul_nonneg Real.pi_pos.le ht.le)
    (by linarith [mul_le_mul_of_nonneg_left hb Real.pi_pos.le])
  rw [show 2/Real.pi*(Real.pi*t)=2*t by field_simp] at hs
  have hh : 4*t ≤ ‖E t - 1‖ := by
    unfold E
    rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,
      show 2*Real.pi*t/2=Real.pi*t by ring,abs_of_nonneg (by linarith : 0≤2*Real.sin (Real.pi*t))]
    linarith
  have hcancel : ‖dirichletGeometricKernel n t‖*‖E t-1‖ ≤ 2 := by
    have he (k : ℕ) : E ((k:ℝ)*t)=(E t)^k := by
      unfold E
      rw [←Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [←norm_mul]
    unfold dirichletGeometricKernel
    simp_rw [he]
    rw [geom_sum_mul]
    simpa only [norm_pow,show ‖E t‖=1 from Complex.norm_exp_ofReal_mul_I _,one_pow,norm_one,
      one_add_one_eq_two] using norm_sub_le ((E t)^(n+1)) 1
  exact (le_div_iff₀ (by positivity)).mpr
    (by nlinarith only [hcancel,mul_le_mul_of_nonneg_left hh (norm_nonneg (dirichletGeometricKernel n t))])

theorem fejer_window_lower (n : ℕ) {r : ℝ} (hr : 0<r) (hh : r≤1/2) :
    (n:ℝ)+2-1/(2*r) ≤ fejerWindowEnergy n r := by
  let f := fun t : ℝ => ‖dirichletGeometricKernel n t‖^2
  have hf : Continuous f := by unfold f dirichletGeometricKernel E; fun_prop
  have hhalf : (0:ℝ)<1/2 := by norm_num
  have hI : ContinuousOn (fun t:ℝ => (t^2)⁻¹) (Set.Icc r (1/2)) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro t ht; exact pow_ne_zero _ (hr.trans_le ht.1).ne'
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=-(fun t:ℝ => t⁻¹))
    (f':=fun t:ℝ => (t^2)⁻¹) (a:=r) (b:=1/2) (fun t ht => by
        rw [Set.uIcc_of_le hh] at ht
        simpa using (hasDerivAt_inv (hr.trans_le ht.1).ne').neg) (hI.intervalIntegrable_of_Icc hh)
  have hi : (∫ t in r..(1/2:ℝ), (t^2)⁻¹) = r⁻¹-2 := by
    norm_num only [Pi.neg_apply,neg_sub_neg,one_div,inv_inv] at hF
    exact hF
  have htail : (∫ t in r..(1/2:ℝ), f t) ≤ 1/4*(r⁻¹-2) := by
    calc _ ≤ ∫ t in r..(1/2:ℝ), (1/4:ℝ)*(t^2)⁻¹ := by
           apply intervalIntegral.integral_mono_on hh (hf.intervalIntegrable _ _) ((continuousOn_const.mul hI).intervalIntegrable_of_Icc hh)
           intro t ht
           have ht0 := hr.trans_le ht.1
           calc f t ≤ (1/(2*t))^2 := pow_le_pow_left₀ (norm_nonneg _) (fejer_kernel_pointwise n ht0 ht.2) 2
                _ = _ := by change (1/(2*t))^2 = 1/4*(t^2)⁻¹; ring
         _ = _ := by rw [intervalIntegral.integral_const_mul,hi]
  have href : (∫ t in -(1/2:ℝ)..-r, f t) = ∫ t in r..(1/2:ℝ), f t := by
    rw [←intervalIntegral.integral_comp_neg f]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [f]
    rw [geometricKernel_even_norm]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ:=volume) (-(1/2):ℝ) (-r)) (hf.intervalIntegrable (-r) r)
  have hadd' := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ:=volume) (-(1/2):ℝ) r) (hf.intervalIntegrable r (1/2))
  rw [href] at hadd
  have htotal : (∫ t in -(1/2:ℝ)..(1/2:ℝ), f t) = (n:ℝ)+1 := geometricKernel_unit_energy n
  change (n:ℝ)+2-1/(2*r) ≤ ∫ t in -r..r, f t
  rw [show 1/(2*r)=r⁻¹/2 by ring]
  linarith only [hadd,hadd',htail,htotal]

theorem fejer_denominator_window_lower {n q : ℕ} {Q : ℝ} (hn : 0<n) (hq : 0<q)
    (hQ : 0<Q) (hwin : Q/((q:ℝ)*n) ≤ 1/2) :
    (n:ℝ)+2-(q:ℝ)*n/(2*Q) ≤ fejerWindowEnergy n (Q/((q:ℝ)*n)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have h := fejer_window_lower n (r:=Q/((q:ℝ)*n)) (by positivity) hwin
  convert h using 1; field_simp

/-- Splitting off the prime 2 keeps both applications of the signed powerset estimate.
The hypothesis is the one-third floor at shifts 1 and 2 on the remaining primes. -/
theorem major_powerset_keep_two (S : Finset ℕ) (h₂ : 2 ∉ S) (c W : ℕ → ℝ) (hc : c 2=1)
    (hfloor : ∀ d ∈ ({1,2} : Finset ℕ),
      W d/3 ≤ ∑ U ∈ S.powerset, (∏ p ∈ U,c p)*W (d*∏ p ∈ U,p)) :
    (W 1 + W 2)/3 ≤ ∑ U ∈ (insert 2 S).powerset, (∏ p ∈ U,c p)*W (∏ p ∈ U,p) := by
  classical
  rw [sum_powerset_insert h₂]
  have he : (∑ U ∈ S.powerset, (∏ p ∈ insert 2 U,c p)*W (∏ p ∈ insert 2 U,p)) =
      ∑ U ∈ S.powerset, (∏ p ∈ U,c p)*W (2*∏ p ∈ U,p) := by
    apply sum_congr rfl
    intro U hU
    have h₂' : 2∉U := fun h => h₂ (mem_powerset.mp hU h)
    rw [prod_insert h₂',prod_insert h₂',hc,one_mul]
  rw [he]
  have h₁ := hfloor 1 (by simp)
  simp only [one_mul] at h₁
  have h₂'' := hfloor 2 (by simp)
  linarith only [h₁,h₂'']

theorem major_two_window_floor {n : ℕ} {Q : ℝ} (hn : 0<n) (hQ : 0<Q)
    (hqhalf : Q/(n:ℝ) ≤ 1/2) :
    (2/3:ℝ)*((n:ℝ)+2)-(n:ℝ)/(2*Q) ≤
       (fejerWindowEnergy n (Q/n)+fejerWindowEnergy n (Q/(2*n)))/3 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h₁ := fejer_denominator_window_lower (n:=n) (q:=1) hn (by decide) hQ (by simpa using hqhalf)
  have h₂half : Q/(2*(n:ℝ)) ≤ 1/2 := (div_le_div_of_nonneg_left hQ.le hn' (by linarith)).trans hqhalf
  have h₂ := fejer_denominator_window_lower (n:=n) (q:=2) hn (by decide) hQ (by simpa using h₂half)
  simp only [Nat.cast_one,one_mul,Nat.cast_ofNat] at h₁ h₂
  rw [show 2*(n:ℝ)/(2*Q)=2*((n:ℝ)/(2*Q)) by ring] at h₂
  linarith only [h₁,h₂]

end
end GoldbachPartial
