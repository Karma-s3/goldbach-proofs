import OddWheelHighArc
import VerifiedPrimeQuarterDistribution

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient
open scoped ComplexConjugate

/-- Fourier extraction with a common truncation N for all target frequencies m≤N. -/
theorem fixed_truncation_coefficient (w : ℕ → ℝ) (N m : ℕ) (hm : m≤N) :
    (∫ t in (0:ℝ)..1, (∑ k ∈ range (N+1), (w k:ℂ)*E ((k:ℝ)*t))^2*E (-(m:ℝ)*t)) =
      ((∑ k∈range (m+1), w k*w (m-k):ℝ):ℂ) := by
  let I := range (N+1)
  let term (k j : ℕ) (t : ℝ) :=
    ((w k:ℂ)*(w j:ℂ))*E (((((k:ℤ)+j-m):ℤ):ℝ)*t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term,E];fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I,(w k:ℂ)*E ((k:ℝ)*t))^2*E (-(m:ℝ)*t) =
      ∑ k∈I,∑j∈I,term k j t := by
    simp only [sq,sum_mul,mul_sum]
    refine sum_congr rfl (fun k _ => sum_congr rfl (fun j _ => ?_))
    dsimp [term];push_cast
    rw [show ((k:ℝ)+j-m)*t = ((k:ℝ)*t+j*t) + -(m:ℝ)*t by ring,phase_add,phase_add]
    ring
  have hrow (k : ℕ) : (∫ t in (0:ℝ)..1,∑j∈I,term k j t) =
      if k≤m then (w k:ℂ)*(w (m-k):ℂ) else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [term,intervalIntegral.integral_const_mul,fourier_mode]
    split_ifs with hk
    · rw [sum_eq_single_of_mem (m-k) (show m-k∈I from mem_range.mpr (by omega))]
      · simp [show (k:ℤ)+(m-k:ℕ)-m=0 by omega]
      · intro j _ hne
        simp [show (k:ℤ)+j-m≠0 by omega]
    · apply sum_eq_zero
      intro j _
      simp [show (k:ℤ)+j-m≠0 by omega]
  change (∫ t in (0:ℝ)..1,(∑ k∈I,(w k:ℂ)*E ((k:ℝ)*t))^2*E (-(m:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  simp_rw [hrow]
  rw [←sum_filter,show I.filter (fun k => k≤m) = range (m+1) by ext k; simp [I];omega]
  push_cast
  rfl

noncomputable def commonKernel (N m : ℕ) (t : ℝ) : ℂ :=
  (dirichletGeometricKernel N t)^2*E (-(m:ℝ)*t)

private theorem commonKernel_cont (N m : ℕ) : Continuous (commonKernel N m) := by
  unfold commonKernel dirichletGeometricKernel E
  fun_prop

private theorem commonKernel_periodic (N m : ℕ) : Function.Periodic (commonKernel N m) 1 := by
  have hp : Function.Periodic (fun t:ℝ => E (-(m:ℝ)*t)) 1 := by
    intro t
    change E (-(m:ℝ)*(t+1)) = E (-(m:ℝ)*t)
    rw [mul_add,mul_one,phase_add]
    have h : E (-(m:ℝ))=1 := by
      unfold E
      rw [show (((2*Real.pi*(-(m:ℝ)):ℝ):ℂ)*Complex.I) = ((-(m:ℤ):ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) by
        push_cast;ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h,mul_one]
  intro t
  change (dirichletGeometricKernel N (t+1))^2*E (-(m:ℝ)*(t+1)) = _
  have ht := hp t
  dsimp only at ht
  rw [wheelGeometricKernel_period N t,ht]
  rfl

theorem commonKernel_unit_integral (N m : ℕ) (hm : m≤N) :
    (∫ t in (0:ℝ)..1, commonKernel N m t) = (m:ℂ)+1 := by
  simpa [commonKernel,dirichletGeometricKernel] using fixed_truncation_coefficient (fun _ => 1) N m hm

theorem commonKernel_window_error (N m : ℕ) (hm : m≤N) {ρ : ℝ} (hρ : 0<ρ) (hh : ρ≤1/2) :
    ‖(∫ t in -ρ..ρ, commonKernel N m t) - ((m:ℂ)+1)‖ ≤ 8/ρ := by
  have hc := commonKernel_cont N m
  have hp := (commonKernel_periodic N m).intervalIntegral_add_eq (-ρ) 0
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (a:= -ρ) (b:=ρ) (c:=1-ρ)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have he : (∫ t in -ρ..1-ρ,commonKernel N m t) = (m:ℂ)+1 := by
    simpa only [neg_add_eq_sub,zero_add,commonKernel_unit_integral N m hm] using hp
  rw [he] at hi
  rw [←hi,sub_add_cancel_left, norm_neg]
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : ρ ≤ 1-ρ)).trans
  have hn (t : ℝ) : ‖commonKernel N m t‖=‖dirichletGeometricKernel N t‖^2 := by
    rw [commonKernel,norm_mul,norm_pow,E,Complex.norm_exp_ofReal_mul_I,mul_one]
  simp_rw [hn]
  exact geometricKernel_single_period_tail N hρ hh

private theorem commonKernel_conj (N m : ℕ) (t : ℝ) :
    conj (commonKernel N m t) = commonKernel N m (-t) := by
  have hE (x : ℝ) : conj (E x) = E (-x) := by
    unfold E
    rw [←Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  unfold commonKernel dirichletGeometricKernel
  simp only [map_mul,map_pow,map_sum,hE,mul_neg]

theorem commonKernel_window_im (N m : ℕ) (ρ : ℝ) :
    (∫ t in -ρ..ρ, commonKernel N m t).im = 0 := by
  have h : conj (∫ t in -ρ..ρ, commonKernel N m t) = ∫ t in -ρ..ρ, commonKernel N m t := by
    calc _ = ∫ t in -ρ..ρ, conj (commonKernel N m t) := by
           exact (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm (commonKernel N m)).symm
         _ = ∫ t in -ρ..ρ, commonKernel N m (-t) := by simp_rw [commonKernel_conj]
         _ = _ := by rw [intervalIntegral.integral_comp_neg,neg_neg]
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem common_width_model_floor (N m Q : ℕ) (hm : m≤N) (he : Even m) (hQ : 1≤Q)
    {ρ : ℝ} (hρ : 0<ρ) (hh : ρ≤1/2) (hsize : 16/ρ≤(m:ℝ)) :
    (m:ℝ)/6 ≤ ((∑q∈Icc 1 Q,GoldbachMajorArc.coefficient q m) *
      (∫ t in -ρ..ρ,commonKernel N m t)).re := by
  let W (q : ℕ) : ℝ := if q ≤ Q then 1 else 0
  have hw := GoldbachMajorArc.arithmetic_floor (Q:=Q) he W
    (fun q => by dsimp [W];split <;> norm_num) (by
      intro i j _ hij
      dsimp [W];split_ifs <;> grind)
    (fun q hq => ite_eq_right (not_le.mpr hq))
  simp only [W,ite_eq_left hQ] at hw
  have hs : (1:ℝ)/3 ≤ ∑ q∈Icc 1 Q,(GoldbachMajorArc.coefficient q m).re := by
    refine hw.trans_eq ?_
    apply sum_congr rfl
    intro q hq
    rw [ite_eq_left (mem_Icc.mp hq).2,mul_one]
  let V := ∫ t in -ρ..ρ,commonKernel N m t
  have htail : ‖((m:ℂ)+1)-V‖ ≤ 8/ρ := (norm_sub_rev _ _).le.trans (commonKernel_window_error N m hm hρ hh)
  have hdist := (Complex.re_le_norm (((m:ℂ)+1)-V)).trans htail
  simp only [Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re] at hdist
  have hV : (m:ℝ)/2 ≤ V.re := by
    simp only [div_eq_mul_inv] at hsize hdist
    linarith only [hdist,hsize]
  rw [Complex.mul_re,Complex.re_sum,commonKernel_window_im,mul_zero,sub_zero]
  change _ ≤ _*V.re
  have h := mul_le_mul hs hV (by positivity) (by linarith only [hs] : 0≤∑q∈Icc 1 Q,(GoldbachMajorArc.coefficient q m).re)
  linarith only [h]

end GoldbachPartial