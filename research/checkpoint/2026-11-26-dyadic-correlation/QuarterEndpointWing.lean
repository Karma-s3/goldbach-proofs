import PrimeArcModelBounds
import GRHTruePrimePrefix
import QuarterEndpointGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GoldbachPartial

open MeasureTheory Finset ExtendedArcCoefficient Filter

noncomputable def centralPrimeWave (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (weight k : ℂ)*E ((k:ℝ)*t)

theorem centralPrimeWave_abel (n : ℕ) (t D : ℝ)
    (h : ∀ j≤n, ‖centeredPrimeArcTransform 1 j 0 ((j:ℂ)+1) 1‖ ≤ D) :
    ‖centralPrimeWave n t-dirichletGeometricKernel n t‖ ≤ D*(1+2*Real.pi*n*|t|) := by
  have hb := centeredPrimeArcTransform_abel_of_prefix 1 n t D 1 h
  have hu (k : ℕ) : (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 :=
    MulChar.one_apply (by rw [Subsingleton.elim (k : ZMod 1) 1]; exact isUnit_one)
  simpa only [centeredPrimeArcTransform,weightedArcCharacterSum,ite_true,hu,star_one,mul_one,
    centralPrimeWave,dirichletGeometricKernel] using hb

private theorem wing_chord {t : ℝ} (ht : 0<t) (hh : t ≤ 1/3) :
    t ≤ ‖E t - 1‖ := by
  let x := Real.pi*t
  have hx : 0<x := mul_pos Real.pi_pos ht
  have hu : x ≤ Real.pi/3 := by dsimp [x]; linarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
  obtain ⟨c,hc,hs⟩ := exists_deriv_eq_slope Real.sin hx Real.continuous_sin.continuousOn
    Real.differentiable_sin.differentiableOn
  rw [Real.deriv_sin,Real.sin_zero,sub_zero,sub_zero] at hs
  have hcos : 1/2 ≤ Real.cos c := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hc.1.le (by linarith [Real.pi_pos]) (hc.2.le.trans hu)
  have hsx : x/2 ≤ Real.sin x := by
    have he := (eq_div_iff hx.ne').mp hs
    nlinarith [mul_le_mul_of_nonneg_right hcos hx.le]
  have hπ : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have ht' : t ≤ x := by simpa [x] using mul_le_mul_of_nonneg_right hπ ht.le
  unfold E
  rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,
    show (2*Real.pi*t)/2=x by dsimp [x]; ring, abs_of_nonneg (by linarith : 0≤2*Real.sin x)]
  linarith

private theorem wing_kernel_chord (n : ℕ) (t : ℝ) :
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

private theorem centralKernel_neg (n : ℕ) (t : ℝ) :
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

theorem centralKernel_small_tail {t : ℝ} (ht : 0 < abs t) (hb : abs t ≤ 1/3) (n : ℕ) :
    ‖dirichletGeometricKernel n t‖ ≤ 2 / abs t := by
  have h := (mul_le_mul_of_nonneg_left (wing_chord ht hb) (norm_nonneg (dirichletGeometricKernel n (abs t)))).trans
    (wing_kernel_chord n (abs t))
  have hz : ‖dirichletGeometricKernel n (abs t)‖=‖dirichletGeometricKernel n t‖ := by
    rcases le_total 0 t with ht' | ht'
    · rw [abs_of_nonneg ht']
    · rw [abs_of_nonpos ht',centralKernel_neg]
  exact (le_div_iff₀ ht).mpr (hz ▸ h)

private theorem central_inv_sq_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
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

theorem centralWing_piece_budget (n : ℕ) {a b D η : ℝ} (ha : 0<a) (hab : a≤b)
    (hb : b≤1/3) (hη : |η|=1) (hD : 0≤D)
    (hp : ∀ j≤n, ‖centeredPrimeArcTransform 1 j 0 ((j:ℂ)+1) 1‖ ≤ D) :
    ‖∫ t in a..b, primeSquareKernel n (η*t)‖ ≤ 2*(b-a)*(D*(1+2*Real.pi*n*b))^2+8/a := by
  let B := D*(1+2*Real.pi*n*b)
  have hi : Continuous (fun t : ℝ => primeSquareKernel n (η*t)) := by unfold primeSquareKernel E; fun_prop
  have hg : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro t ht
    exact pow_ne_zero _ (ha.trans_le ht.1).ne'
  have hg' := hg.intervalIntegrable_of_Icc hab (μ := volume)
  have hB : 0≤B := by dsimp [B]; have hb0 := ha.trans_le hab; positivity
  have hs (t : ℝ) (ht : t∈Set.Icc a b) :
      ‖primeSquareKernel n (η*t)‖ ≤ 2*B^2 + 8*(t^2)⁻¹ := by
    have ht0 : 0<t := ha.trans_le ht.1
    have hnorm : |η*t|=t := by rw [abs_mul,hη,one_mul,abs_of_pos ht0]
    have herr := centralPrimeWave_abel n (η*t) D hp
    rw [hnorm] at herr
    have hK := centralKernel_small_tail (t:=η*t) (by rwa [hnorm]) (by rw [hnorm]; exact ht.2.trans hb) n
    rw [hnorm] at hK
    have htriangle : ‖centralPrimeWave n (η*t)‖ ≤ ‖centralPrimeWave n (η*t)-dirichletGeometricKernel n (η*t)‖ +
        ‖dirichletGeometricKernel n (η*t)‖ := by
      simpa using norm_add_le (centralPrimeWave n (η*t)-dirichletGeometricKernel n (η*t)) (dirichletGeometricKernel n (η*t))
    have hE : D*(1+2*Real.pi*n*t) ≤ B := by dsimp [B]; gcongr; exact ht.2
    have hW := htriangle.trans (add_le_add (herr.trans hE) hK)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hW 2
    change ‖(centralPrimeWave n (η*t))^2*E (-(n:ℝ)*(η*t))‖ ≤ _
    rw [norm_mul,norm_pow,show ‖E (-(n:ℝ)*(η*t))‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
    calc
      _ ≤ (B+2/t)^2 := hsq
      _ ≤ 2*B^2+2*(2/t)^2 := by nlinarith [sq_nonneg (B-2/t)]
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ∫ t in a..b, ‖primeSquareKernel n (η*t)‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, (2*B^2+8*(t^2)⁻¹) := intervalIntegral.integral_mono_on hab
      (hi.norm.intervalIntegrable _ _) (intervalIntegrable_const.add (hg'.const_mul 8)) hs
    _ = (b-a)*(2*B^2)+8*(a⁻¹-b⁻¹) := by rw [intervalIntegral.integral_add
          intervalIntegrable_const (hg'.const_mul 8),intervalIntegral.integral_const_mul (r:=8),
          central_inv_sq_integral ha hab,intervalIntegral.integral_const,smul_eq_mul]
    _ ≤ _ := by dsimp [B]; rw [div_eq_mul_inv]; linarith [inv_nonneg.mpr (ha.trans_le hab).le]


private theorem centralWing_periodic (n : ℕ) : Function.Periodic (primeSquareKernel n) 1 := by
  have hnat (k : ℕ) : E k = 1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hneg : E (-(n:ℝ))=1 := by
    have h := phase_add (n:ℝ) (-(n:ℝ))
    rw [hnat, one_mul, add_neg_cancel, show E 0=1 by simp [E]] at h
    exact h.symm
  intro t
  unfold primeSquareKernel
  simp_rw [mul_add,mul_one,phase_add,hnat,hneg,mul_one]

private theorem centralWing_two_pieces (n : ℕ) {a b : ℝ} (hab : a≤b) (hb : b≤1/3)
    (hsub : Set.Ioc a b ∪ Set.Ico (1-b) (1-a) ⊆ Set.Icc (0:ℝ) 1) :
    primeArcMass (Set.Ioc a b ∪ Set.Ico (1-b) (1-a)) n =
      ((∫ t in a..b, primeSquareKernel n (1*t)) +
        ∫ t in a..b, primeSquareKernel n ((-1)*t)).re := by
  have hc : Continuous (primeSquareKernel n) := by unfold primeSquareKernel E; fun_prop
  have hd : Disjoint (Set.Ioc a b) (Set.Ico (1-b) (1-a)) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    linarith [ht.2,ht'.1]
  have hs : MeasurableSet (Set.Ioc a b ∪ Set.Ico (1-b) (1-a)) := measurableSet_Ioc.union measurableSet_Ico
  have hr : 1-b≤1-a := by linarith
  have href := intervalIntegral.integral_comp_sub_left (a:=a) (b:=b) (primeSquareKernel n) (1:ℝ)
  have he (t:ℝ) : primeSquareKernel n (1-t) = primeSquareKernel n (-t) := by
    rw [show 1-t = -t + 1 by ring, centralWing_periodic n]
  simp_rw [he] at href
  unfold primeArcMass
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator hs,Set.inter_eq_right.mpr hsub,
    setIntegral_union hd measurableSet_Ico ((hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
      ((hc.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self),
    integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,← intervalIntegral.integral_of_le hr,
    ←href]
  simp


/-- The combined signed prime coefficient on both endpoint strips is o(n), uniformly in n. -/
theorem quarterEndpointStrips_mass_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |primeArcMass (quarterEndpointStrips n) n| ≤ ε*(n:ℝ) := by
  obtain ⟨C,hC,hpre⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  let K : ℝ := 1+2*Real.pi
  obtain ⟨k,hk⟩ := exists_nat_ge (32/ε)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(1/48:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp tendsto_natCast_atTop_atTop
  filter_upwards [medDesk_composite_shell_thresholds C hC,quarterEndpointStrips_geometry,
    eventually_ge_atTop (2:ℕ),eventually_ge_atTop (2^k : ℕ),ht.eventually_ge_atTop 3,
    ht.eventually_ge_atTop (8*K^2/ε)] with n hh hg hn hk' ht3 hTK
  let T := (n:ℝ)^(1/48:ℝ)
  let a := (medDeskQ n:ℝ)/n
  let b := (n:ℝ)^(1/4:ℝ)/n
  obtain ⟨h1,h48,_,_,_,hD,_,_,_⟩ := hh
  change 1≤T at h1
  change T^48=(n:ℝ) at h48
  change _≤T^28 at hD
  change 3≤T at ht3
  change 8*K^2/ε≤T at hTK
  have hT : 0<T := by linarith
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hQ1 : 1≤medDeskQ n := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have hQ : (0:ℝ)<medDeskQ n := by exact_mod_cast (show 0<medDeskQ n by omega)
  have hak : 32/ε ≤ (medDeskQ n:ℝ) := by
    have hx : k ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
    have hx' : k≤medDeskQ n := hx.trans (le_self_pow₀ (Nat.log_pos (by decide) (by omega)) (by decide : 2≠0))
    exact hk.trans (by exact_mod_cast hx')
  have ha : 0<a := div_pos hQ hn'
  have hab : a≤b := hg.1.le
  have hpow : T^12=(n:ℝ)^(1/4:ℝ) := by
    dsimp only [T]
    rw [←Real.rpow_natCast,←Real.rpow_mul hn'.le]
    norm_num
  have hb : b=(T^36)⁻¹ := by dsimp only [b]; rw [←hpow,←h48]; field_simp
  have h3 : 3≤T^36 := ht3.trans (le_self_pow₀ h1 (by decide))
  have hb' : b ≤ 1/3 := by rw [hb,←one_div]; gcongr
  have hnb : (n:ℝ)*b=T^12 := by dsimp only [b]; rw [←hpow]; field_simp
  have hp : ∀ j≤n, ‖centeredPrimeArcTransform 1 j 0 ((j:ℂ)+1) 1‖ ≤ T^28 :=
    fun j hj => (hpre n hn 1 (by omega) 1 j hj).trans hD
  let Z (η:ℝ) := ∫ t in a..b, primeSquareKernel n (η*t)
  have hrow (η : ℝ) (hη : |η|=1) : ‖Z η‖ ≤ 2*(b-a)*(T^28*(1+2*Real.pi*n*b))^2+8/a :=
    centralWing_piece_budget n ha hab hb' hη (by positivity) hp
  have hboth := (Complex.abs_re_le_norm (Z 1+Z (-1))).trans
    ((norm_add_le _ _).trans (add_le_add (hrow 1 (by norm_num)) (hrow (-1) (by norm_num))))
  have heq := centralWing_two_pieces n hab hb' hg.2.1
  change primeArcMass (quarterEndpointStrips n) n=(Z 1+Z (-1)).re at heq
  rw [heq]
  have hf : 1+2*Real.pi*n*b ≤ K*T^12 := by
    rw [mul_assoc (2*Real.pi),hnb]
    dsimp only [K]
    nlinarith only [one_le_pow₀ (n:=12) h1]
  have hx : (b-a)*(T^28*(1+2*Real.pi*n*b))^2 ≤ K^2*T^44 := by
    calc
      _ ≤ b*(T^28*(K*T^12))^2 := by
        gcongr
        · linarith
      _ = _ := by rw [hb]; field_simp
  have hy : 8/a ≤ ε*(n:ℝ)/4 := by
    have hkQ := (div_le_iff₀ hε).mp hak
    dsimp only [a]
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hQ).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hkQ hn'.le]
  have hz : K^2*T^44 ≤ ε*(n:ℝ)/8 := by
    have htk := (div_le_iff₀ hε).mp (hTK.trans (le_self_pow₀ h1 (by decide : 4≠0)))
    rw [←h48]
    nlinarith only [mul_le_mul_of_nonneg_right htk (pow_nonneg hT.le 44)]
  linarith only [hboth,hx,hy,hz]

theorem quarterEndpointStrips_mass_floor (hψ : grhAllUniform) :
    ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ)/14400 ≤ primeArcMass (quarterEndpointStrips n) n := by
  filter_upwards [quarterEndpointStrips_mass_small hψ (ε:=1/14400) (by norm_num)] with n hn
  intro _
  linarith only [(abs_le.mp hn).1]
end GoldbachPartial
