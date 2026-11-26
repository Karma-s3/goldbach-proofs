import NaturalPrimeTubeVolume
import QuarterEndpointWing

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

noncomputable def normalizedOddWave (m : ℕ) (t : ℝ) : ℂ :=
  2*E t*dirichletGeometricKernel m (2*t)

noncomputable def normalizedOddKernel (m : ℕ) (t : ℝ) :=
  (normalizedOddWave m t)^2 * E (-((2*m+2:ℕ):ℝ)*t)

theorem normalizedOddWave_eq (m:ℕ) (t:ℝ) :
    normalizedOddWave m t = ∑ k ∈ range (m+1), (2:ℂ)*E (((2*k+1:ℕ):ℝ)*t) := by
  unfold normalizedOddWave dirichletGeometricKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [show (2*(k:ℝ)+1)*t=t+(k:ℝ)*(2*t) by ring,phase_add]
  ring

theorem normalizedOddKernel_eq_norm_sq (m:ℕ) (t:ℝ) :
    normalizedOddKernel m t = ((4*‖dirichletGeometricKernel m (2*t)‖^2:ℝ):ℂ) := by
  unfold normalizedOddKernel normalizedOddWave
  push_cast
  rw [←Complex.ofReal_pow,←geometricKernel_sq_phase]
  rw [show -(2*(m:ℝ)+2)*t= -(m:ℝ)*(2*t)+(-t + -t) by ring,phase_add,phase_add]
  have he : E t * E (-t)=1 := by rw [←phase_add,add_neg_cancel]; simp [E]
  linear_combination (norm:=ring) (4*(dirichletGeometricKernel m (2*t))^2*E (-(m:ℝ)*(2*t))*(E t*E (-t)+1))*he

private theorem wheel_kernel_chord (n : ℕ) (t : ℝ) :
    ‖dirichletGeometricKernel n t‖ * ‖E t-1‖ ≤ 2 := by
  have he (k : ℕ) : E ((k:ℝ)*t) = (E t)^k := by
    unfold E
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← norm_mul]
  unfold dirichletGeometricKernel
  simp_rw [he]
  rw [geom_sum_mul]
  have h := norm_sub_le ((E t)^(n+1)) 1
  simpa only [norm_pow,show ‖E t‖=1 from Complex.norm_exp_ofReal_mul_I _,one_pow,norm_one,
    one_add_one_eq_two] using h

private theorem wheel_kernel_neg (n : ℕ) (t : ℝ) :
    ‖dirichletGeometricKernel n (-t)‖ = ‖dirichletGeometricKernel n t‖ := by
  have hc (z : ℝ) : E (-z) = (starRingEnd ℂ) (E z) := by
    unfold E
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast; ring
  unfold dirichletGeometricKernel
  simp_rw [mul_neg,hc]
  rw [← map_sum]
  exact Complex.norm_conj _

private theorem wheel_inv_sq_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, (t^2)⁻¹) = a⁻¹-b⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro t ht
    exact pow_ne_zero _ (ha.trans_le ht.1).ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := -(fun t:ℝ => t⁻¹))
    (f' := fun t:ℝ => (t^2)⁻¹) (a:=a) (b:=b) (fun t ht => by
      rw [Set.uIcc_of_le hab] at ht
      simpa using (hasDerivAt_inv (ha.trans_le ht.1).ne').neg) (hc.intervalIntegrable_of_Icc hab)
  simpa only [Pi.neg_apply,neg_sub_neg] using h


private theorem wheelKernel_positive_half (m:ℕ) {t:ℝ} (ht:0<t) (hb:t≤1/2) :
    ‖dirichletGeometricKernel m t‖ ≤ 2/t := by
  by_cases ha : t≤1/3
  · simpa only [abs_of_pos ht] using centralKernel_small_tail (t:=t) (by simpa only [abs_of_pos ht]) (by simpa only [abs_of_pos ht]) m
  have hsin : 1/2 ≤ Real.sin (Real.pi*t) := by
    rw [←Real.sin_pi_div_six]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [mul_le_mul_of_nonneg_left hb Real.pi_pos.le]
    · nlinarith only [mul_nonneg Real.pi_pos.le (show 0≤t-1/6 by linarith)]
  have hch : 1≤‖E t-1‖ := by
    unfold E
    rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,
      show (2*Real.pi*t)/2=Real.pi*t by ring,abs_of_nonneg (by linarith : 0≤2*Real.sin (Real.pi*t))]
    linarith
  have hk := wheel_kernel_chord m t
  exact (le_div_iff₀ ht).mpr ((mul_le_mul_of_nonneg_left (by linarith : t≤‖E t-1‖) (norm_nonneg _)).trans hk)

private theorem wheelKernel_period (m:ℕ) : Function.Periodic (dirichletGeometricKernel m) 1 := by
  have hn (k:ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  intro t
  unfold dirichletGeometricKernel
  simp_rw [mul_add,mul_one,phase_add,hn,mul_one]

private theorem wheelKernel_two_sided_tail (m:ℕ) {a:ℝ} (ha:0<a) (ha':a≤1/2) :
    (∫ t in a..(1-a), ‖dirichletGeometricKernel m t‖^2) ≤ 8/a := by
  let F (t : ℝ) := ‖dirichletGeometricKernel m t‖^2
  have hF : Continuous F := by dsimp [F,dirichletGeometricKernel,E]; fun_prop
  have href (t:ℝ) : F (1-t) = F t := by
    dsimp only [F]
    rw [show 1-t= -t+1 by ring,wheelKernel_period m,wheel_kernel_neg]
  have he := intervalIntegral.integral_comp_sub_left (a:=a) (b:=(1/2:ℝ)) F (1:ℝ)
  simp_rw [href] at he
  norm_num at he
  have hg : ContinuousOn (fun t:ℝ => (t^2)⁻¹) (Set.Icc a (1/2)) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro t ht
    exact pow_ne_zero _ (ha.trans_le ht.1).ne'
  have hint := hg.intervalIntegrable_of_Icc ha' («μ»:=volume)
  have hp : (∫ t in a..(1/2:ℝ), F t) ≤ 4/a := calc
    _ ≤ ∫ t in a..(1/2:ℝ), 4*(t^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on ha' (hF.intervalIntegrable _ _) (hint.const_mul 4)
      intro t ht
      exact (pow_le_pow_left₀ (norm_nonneg _) (wheelKernel_positive_half m (ha.trans_le ht.1) ht.2) 2).trans_eq (by rw [div_pow]; ring)
    _ ≤ _ := by rw [intervalIntegral.integral_const_mul,wheel_inv_sq_integral ha ha']; ring_nf; linarith
  change (∫ t in a..(1-a), F t) ≤ _
  rw [←intervalIntegral.integral_add_adjacent_intervals (b:=1/2) (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),←he]
  calc _ ≤ 4/a+4/a := add_le_add hp hp
       _ = _ := by ring


private theorem oddWheel_strip_geometry {R Q:ℕ} (hR:2≤R) (hRQ:R≤Q) :
    let a : ℝ := 1/(12*(Q:ℝ))
    naturalTubeUnion R Q (3*Q) ⊆ Set.Icc (a/2) ((1-a)/2) ∪ Set.Icc ((1+a)/2) (1-a/2) := by
  let a : ℝ := 1/(12*(Q:ℝ))
  have hQ : 0<Q := by omega
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hM : 0<3*Q := by omega
  have hR' : (R:ℝ)≤Q := by exact_mod_cast hRQ
  have hs : (Q:ℝ)*(1:ℕ)/(12*Q:ℕ)+(R:ℝ)/(3*Q:ℕ)<1 := by
    push_cast
    field_simp
    linarith
  have hd := naturalTubeUnion_outside_core (n:=12*Q) (B:=R) (R:=Q) (M:=3*Q) (H:=1) (by omega) hM hs
  have hu := naturalTubeUnion_inside_unit (B:=R) (R:=Q) (by omega) hM
  have ha : 0<a := by dsimp only [a]; positivity
  change naturalTubeUnion R Q (3*Q) ⊆ Set.Icc (a/2) ((1-a)/2) ∪ Set.Icc ((1+a)/2) (1-a/2)
  intro t ht
  have h0 : 0≤t := (hu ht).1
  have h1 : t≤1 := (hu ht).2
  have ex (d b:ℕ) (hd0:0<d) (hdR:d≤R) (hbd:b≤d) (hcop:b.Coprime d) :
      1/((d:ℝ)*(12*Q:ℕ)) < |t-(b:ℝ)/d| := by
    by_contra! hx
    exact hd ht ⟨d,b,hd0,hdR,hbd,hcop,by exact_mod_cast hx⟩
  have hx0 := ex 1 0 (by decide) (by omega) (by decide) (by decide)
  have hx1 := ex 1 1 (by decide) (by omega) (by decide) (by decide)
  have hx2 := ex 2 1 (by decide) hR (by decide) (by decide)
  have et : a<t := by simpa [a,abs_of_nonneg h0] using hx0
  have eu : a<1-t := by
    simpa [a,abs_of_nonpos (by linarith : t-1≤0),neg_sub] using hx1
  have em : a/2 < |t-1/2| := by
    push_cast at hx2
    convert hx2 using 1
    dsimp only [a]
    ring
  rcases lt_or_ge t (1/2:ℝ) with hl|hr
  · rw [abs_of_nonpos (by linarith : t-1/2≤0)] at em
    exact Or.inl ⟨by change a/2≤t; linarith,by change t≤(1-a)/2; linarith⟩
  · rw [abs_of_nonneg (by linarith : 0≤t-1/2)] at em
    exact Or.inr ⟨by change (1+a)/2≤t; linarith,by change t≤1-a/2; linarith⟩

theorem normalizedOddKernel_naturalTube_mass (m R Q : ℕ) (hR : 2≤R) (hRQ : R≤Q) :
    0 ≤ (∫ t in naturalTubeUnion R Q (3*Q), normalizedOddKernel m t).re ∧
      (∫ t in naturalTubeUnion R Q (3*Q), normalizedOddKernel m t).re ≤ 384*(Q:ℝ) := by
  let U := naturalTubeUnion R Q (3*Q)
  let a : ℝ := 1/(12*(Q:ℝ))
  let F (t:ℝ) := ‖dirichletGeometricKernel m t‖^2
  let G (t:ℝ) := F (2*t)
  let I := Set.Icc (a/2) ((1-a)/2)
  let J := Set.Icc ((1+a)/2) (1-a/2)
  have hQ0 : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast (show 1≤Q by omega)
  have ha : 0<a := by dsimp only [a]; positivity
  have ha' : a≤1/2 := by dsimp only [a]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hF : Continuous F := by dsimp [F,dirichletGeometricKernel,E]; fun_prop
  have hG : Continuous G := hF.comp (continuous_const.mul continuous_id)
  have hfpos (t:ℝ) : 0≤G t := sq_nonneg _
  have hI : IntegrableOn G I := hG.integrableOn_Icc
  have hJ : IntegrableOn G J := hG.integrableOn_Icc
  have hd : Disjoint I J := by
    apply Set.disjoint_left.mpr
    intro t ht hs
    have h1 := ht.2
    have h2 := hs.1
    linarith
  have hU : U ⊆ I ∪ J := oddWheel_strip_geometry hR hRQ
  have hmono := setIntegral_mono_set (hI.union hJ)
    (Filter.Eventually.of_forall hfpos) hU.eventuallySubset
  have hper (t:ℝ) : F (t+1)=F t := congrArg (fun z:ℂ => ‖z‖^2) (wheelKernel_period m t)
  have he := intervalIntegral.integral_comp_add_right (a:=a) (b:=1-a) F (1:ℝ)
  simp_rw [hper] at he
  have hto (b c:ℝ) (h:b≤c) : (∫ t in Set.Icc b c, G t) = (2:ℝ)⁻¹*(∫ t in 2*b..2*c, F t) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le h]
    exact intervalIntegral.integral_comp_mul_left F (by norm_num : (2:ℝ)≠0)
  have hIp : (∫ t in I, G t)=(2:ℝ)⁻¹*∫ t in a..(1-a), F t := by
    rw [hto _ _ (by linarith : a/2≤(1-a)/2)]
    ring_nf
  have hJp : (∫ t in J, G t)=(2:ℝ)⁻¹*∫ t in a..(1-a), F t := by
    rw [hto _ _ (by linarith : (1+a)/2≤1-a/2),he]
    ring_nf
  have hupper : (∫ t in U, G t) ≤ 8/a := by
    rw [setIntegral_union hd measurableSet_Icc hI hJ,hIp,hJp] at hmono
    have ht := wheelKernel_two_sided_tail m ha ha'
    change (∫ t in a..(1-a), F t)≤8/a at ht
    linarith only [hmono,ht]
  have hlower : 0≤∫ t in U,G t := setIntegral_nonneg_of_ae (Filter.Eventually.of_forall hfpos)
  have hEq : (∫ t in U, normalizedOddKernel m t).re = 4*(∫ t in U,G t) := by
    have hfun : normalizedOddKernel m = (fun t:ℝ => ((4*G t:ℝ):ℂ)) := funext (normalizedOddKernel_eq_norm_sq m)
    rw [hfun,integral_complex_ofReal (f:=fun t:ℝ => 4*G t),Complex.ofReal_re,integral_const_mul]
  change 0 ≤ (∫ t in U, normalizedOddKernel m t).re ∧ (∫ t in U, normalizedOddKernel m t).re ≤ _
  rw [hEq]
  refine ⟨by positivity,?_⟩
  exact (mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℝ)≤4)).trans_eq (by dsimp only [a]; field_simp; norm_num)

/-- All noncentral ordered pairs of odd terms, with both logarithmic-model weights equal to two. -/
noncomputable def oddWheelOffTarget (m:ℕ) (t:ℝ) : ℂ :=
  ∑ k ∈ range (m+1), ∑ l ∈ (range (m+1)).erase (m-k),
    (4:ℂ)*E ((2*((k:ℤ)+l-m):ℤ)*t)

theorem normalizedOddKernel_off_target (m:ℕ) (t:ℝ) :
    normalizedOddKernel m t = 4*((m:ℂ)+1)+oddWheelOffTarget m t := by
  let s := range (m+1)
  let term (k l : ℕ) := (4:ℂ)*E ((2*((k:ℤ)+l-m):ℤ)*t)
  have hker : normalizedOddKernel m t=∑ k ∈ s, ∑ l ∈ s, term k l := by
    unfold normalizedOddKernel
    rw [normalizedOddWave_eq,sq]
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    dsimp only [term]
    push_cast
    rw [show 2*((k:ℝ)+l-m)*t = ((2*k+1)*t+(2*l+1)*t)+ -(2*m+2)*t by ring,phase_add,phase_add]
    ring
  have hrow (k:ℕ) (hk:k∈s) : ∑ l ∈ s, term k l = 4+ ∑ l ∈ s.erase (m-k), term k l := by
    have hkm : k≤m := Nat.le_of_lt_succ (mem_range.mp hk)
    have hmem : m-k∈s := mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase s (term k) (a:=m-k) hmem]
    congr 1
    dsimp only [term]
    rw [show 2*((k:ℤ)+(m-k:ℕ)-m)=0 by omega]
    simp [E]
  rw [hker,Finset.sum_congr rfl hrow,Finset.sum_add_distrib]
  change (∑ _k ∈ s, (4:ℂ)) + oddWheelOffTarget m t = _
  simp [s,nsmul_eq_mul,mul_comm]

theorem oddWheelOffTarget_naturalTube_bound (m R Q:ℕ) (hR:2≤R) (hRQ:R≤Q) :
    let U := naturalTubeUnion R Q (3*Q);
    -(4*((m:ℝ)+1)*volume.real U) ≤ (∫ t in U, oddWheelOffTarget m t).re ∧
      (∫ t in U, oddWheelOffTarget m t).re ≤ 384*(Q:ℝ)-4*((m:ℝ)+1)*volume.real U := by
  let U := naturalTubeUnion R Q (3*Q)
  have hQ : 0<Q := by omega
  have hu := naturalTubeUnion_inside_unit (B:=R) (R:=Q) (by omega) (by omega : 0<3*Q)
  have hc : Continuous (oddWheelOffTarget m) := by unfold oddWheelOffTarget E; fun_prop
  have hi : IntegrableOn (oddWheelOffTarget m) U := hc.integrableOn_Icc.mono_set hu
  have hconst : IntegrableOn (fun _:ℝ => 4*((m:ℂ)+1)) U :=
    continuous_const.integrableOn_Icc.mono_set hu
  have hfun : normalizedOddKernel m = fun t:ℝ => 4*((m:ℂ)+1)+oddWheelOffTarget m t := funext (normalizedOddKernel_off_target m)
  have hs := normalizedOddKernel_naturalTube_mass m R Q hR hRQ
  change 0≤(∫ t in U,normalizedOddKernel m t).re ∧ (∫ t in U,normalizedOddKernel m t).re≤_ at hs
  rw [hfun,MeasureTheory.integral_add hconst hi,MeasureTheory.setIntegral_const] at hs
  have hcast : (4*((m:ℂ)+1)).re = 4*((m:ℝ)+1) := by norm_num [Complex.mul_re]
  simp only [Complex.add_re,Complex.real_smul,Complex.re_ofReal_mul,hcast] at hs
  change -(4*((m:ℝ)+1)*volume.real U) ≤ (∫ t in U, oddWheelOffTarget m t).re ∧
    (∫ t in U, oddWheelOffTarget m t).re ≤ 384*(Q:ℝ)-4*((m:ℝ)+1)*volume.real U
  constructor <;> nlinarith only [hs.1,hs.2]

theorem oddWheelOffTarget_negative_on_naturalTube (m R Q:ℕ) (hR:2≤R) (hRQ:8*R≤Q) :
    (∫ t in naturalTubeUnion R Q (3*Q), oddWheelOffTarget m t).re ≤ 384*(Q:ℝ)-((m:ℝ)+1)/3 := by
  have hQ : 0<Q := by omega
  have hv := naturalTubeUnion_realVolume_ge_twelfth hQ hRQ
  have hs := (oddWheelOffTarget_naturalTube_bound m R Q hR (by omega)).2
  exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hv (by positivity : 0≤4*((m:ℝ)+1))])

/-- Unnormalized geometric-kernel energy away from both endpoints of a single period. -/
theorem geometricKernel_single_period_tail (m:ℕ) {a:ℝ} (ha:0<a) (ha':a≤1/2) :
    (∫ t in a..(1-a), ‖dirichletGeometricKernel m t‖^2) ≤ 8/a :=
  wheelKernel_two_sided_tail m ha ha'

theorem geometricKernel_single_period_Icc_tail (m:ℕ) {a:ℝ} (ha:0<a) (ha':a≤1/2) :
    (∫ t in Set.Icc a (1-a), ‖dirichletGeometricKernel m t‖^2) ≤ 8/a := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : a≤1-a)]
  exact geometricKernel_single_period_tail m ha ha'

theorem wheelGeometricKernel_period (m:ℕ) : Function.Periodic (dirichletGeometricKernel m) 1 :=
  wheelKernel_period m

theorem wheelGeometricKernel_positive_half (m:ℕ) {t:ℝ} (ht:0<t) (hb:t≤1/2) :
    ‖dirichletGeometricKernel m t‖ ≤ 2/t :=
  wheelKernel_positive_half m ht hb

theorem wheelGeometricKernel_neg_norm (m:ℕ) (t:ℝ) :
    ‖dirichletGeometricKernel m (-t)‖ = ‖dirichletGeometricKernel m t‖ :=
  wheel_kernel_neg m t

end GoldbachPartial