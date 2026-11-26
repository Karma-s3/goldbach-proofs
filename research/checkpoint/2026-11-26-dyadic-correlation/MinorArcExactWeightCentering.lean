import MinorArcExactWeightEnergy

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private theorem minor_weighted_kernel_transfer {n D : ℕ} (a : ℕ→ℂ) {V : Set ℝ} (hi : V⊆Set.Icc 0 1)
    {M s : ℝ} (hs : 0<s)
    (hM : (∫ t in V,‖smallDivisorWave n (Icc 1 D) a t‖^2)≤M) :
    ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,weightedMangoldtKernel n D a t)‖ ≤
      s*(Real.log 4*(n:ℝ)*Real.log n)+(1+s⁻¹)*(2*M+4*Real.sqrt n*(Real.log n)^2) := by
  let S := smallDivisorWave n (Icc 1 D) a
  let P := properPrimePowerWave n
  let B := fun t => S t-P t
  have hS : Continuous S := by unfold S smallDivisorWave positiveDivisorRow E; fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E; fun_prop
  have hB : Continuous B := hS.sub hP
  have he := truePrime_centering_young_chebyshev n hi B hB hs
  apply he.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hI {f:ℝ→ℝ} (hf:Continuous f) : IntegrableOn f V := hf.integrableOn_Icc.mono_set hi
  have h (t : ℝ) : ‖B t‖^2≤2*‖S t‖^2+2*‖P t‖^2 := by
    have h' := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (S t) (P t)) 2
    dsimp only [B]
    nlinarith only [h',sq_nonneg (‖S t‖-‖P t‖)]
  apply (integral_mono (hI (hB.norm.pow 2)) (hI ((continuous_const.mul (hS.norm.pow 2)).add
    (continuous_const.mul (hP.norm.pow 2)))) h).trans
  change (∫ t in V,2*‖S t‖^2+2*‖P t‖^2)≤_
  rw [integral_add (f:=fun t => 2*‖S t‖^2) (g:=fun t => 2*‖P t‖^2)
    (hI (continuous_const.mul (hS.norm.pow 2))) (hI (continuous_const.mul (hP.norm.pow 2))),
    integral_const_mul,integral_const_mul]
  change (∫ t in V,‖S t‖^2)≤M at hM
  have hp := properPrimePowerWave_energy n hi
  change (∫ t in V,‖P t‖^2)≤_ at hp
  linarith only [hM,hp]

/-- Uniform signed-square transfer on any measurable part of the original minor arcs. -/
theorem minorArc_exactWeight_kernel_bound :
    ∀ᶠ n : ℕ in atTop,∀ V : Set ℝ,MeasurableSet V → V⊆Set.Icc 0 1 →
      V⊆(rationalArcSet (medDeskQ n) n)ᶜ →
      ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,weightedMangoldtKernel n (minorRamanujanCutoff n)
        (fun d => (exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t)‖≤
        32780*(n:ℝ)/((Real.log n)^(1/8:ℝ))^2 := by
  filter_upwards [minorArc_exactWeight_energy,minorRamanujan_geometry_eventually] with n henergy hgeom
  intro V hm hv ho
  obtain ⟨hn,ht,h8,h32,_,_,_,_,_,_⟩ := hgeom
  let T := (Real.log (n:ℝ))^(1/8:ℝ)
  have ht0 : 0<T := by linarith only [ht]
  have h1 : 1≤T := by linarith only [ht]
  have hx : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hp : 4*Real.sqrt n*(Real.log n)^2 ≤ 4*(n:ℝ)/T^12 := by
    apply (le_div_iff₀ (pow_pos ht0 _)).mpr
    have h28 : T^28≤Real.sqrt n := (pow_le_pow_right₀ h1 (by decide : 28≤32)).trans h32
    rw [←h8]
    calc
      _ = 4*Real.sqrt n*T^28 := by dsimp only [T];ring
      _ ≤ 4*Real.sqrt n*Real.sqrt n := by gcongr
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hx]
  have hl4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hh := minor_weighted_kernel_transfer _ hv (s:=(T^10)⁻¹) (by positivity) (henergy V hm hv ho)
  apply hh.trans
  rw [inv_inv]
  change (T^10)⁻¹*(Real.log 4*n*Real.log n)+(1+T^10)*(2*(8192*(n:ℝ)/T^12)+_)≤32780*(n:ℝ)/T^2
  have hadd : 1+T^10≤2*T^10 := by linarith only [one_le_pow₀ h1 (n:=10)]
  calc
    _ ≤ (T^10)⁻¹*(4*(n:ℝ)*T^8)+(2*T^10)*(2*(8192*(n:ℝ)/T^12)+4*(n:ℝ)/T^12) := by
      apply add_le_add
      · rw [h8]
        gcongr
      · apply mul_le_mul hadd (add_le_add le_rfl hp) (by positivity) (by positivity)
    _ = _ := by field_simp;ring

theorem minorArc_exactWeight_kernel_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ V : Set ℝ,MeasurableSet V → V⊆Set.Icc 0 1 →
      V⊆(rationalArcSet (medDeskQ n) n)ᶜ →
      ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,weightedMangoldtKernel n (minorRamanujanCutoff n)
        (fun d => (exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t)‖≤ε*(n:ℝ) := by
  let T := fun n : ℕ => (Real.log (n:ℝ))^(1/8:ℝ)
  have ht : Tendsto T atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hs := ((tendsto_pow_atTop (α:=ℝ) (by decide : 2≠0)).comp ht).eventually_ge_atTop (32780/ε)
  filter_upwards [hs,minorArc_exactWeight_kernel_bound,minorRamanujan_geometry_eventually] with n hs hh hgeom
  intro V hm hv ho
  apply (hh V hm hv ho).trans
  have ht0 : 0<T n := by linarith only [hgeom.2.1]
  apply (div_le_iff₀ (pow_pos ht0 2)).mpr
  change 32780/ε≤(T n)^2 at hs
  have he := (div_le_iff₀ hε).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) n)]

/-- Real centered mass over the part of s in the original unit integration interval. -/
noncomputable def minorExactCenteredMass (s : Set ℝ) (n : ℕ) : ℝ :=
  (∫ t in Set.Icc 0 1 ∩ s, weightedMangoldtKernel n (minorRamanujanCutoff n)
    (fun d => (exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t).re

theorem primeArcMass_minorExactCenteredMass_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ s : Set ℝ, MeasurableSet s → s⊆(rationalArcSet (medDeskQ n) n)ᶜ →
      |primeArcMass s n-minorExactCenteredMass s n|≤ε*(n:ℝ) := by
  filter_upwards [minorArc_exactWeight_kernel_small hε] with n hh
  intro s hm hs
  have h := hh (Set.Icc 0 1 ∩ s) (measurableSet_Icc.inter hm) Set.inter_subset_left (Set.inter_subset_right.trans hs)
  unfold primeArcMass minorExactCenteredMass
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,setIntegral_indicator hm,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-- The uncovered portion of the original minor arc admits the same sublinear replacement. -/
theorem primeArcMass_originalMinorOutsideHigh_centered {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let s := (rationalArcSet (medDeskQ n) n)ᶜ \ highNaturalPrimeTubes n
      |primeArcMass s n-minorExactCenteredMass s n|≤ε*(n:ℝ) := by
  filter_upwards [primeArcMass_minorExactCenteredMass_small hε] with n h
  exact h _ ((measurable_rational_arcs _ _).compl.diff (naturalTubeUnion_measurable ..)) Set.sdiff_subset

/-- The leakage is little-o of n/log n, uniformly over all measurable minor-arc subsets. -/
theorem minorArc_exactWeight_energy_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ V : Set ℝ, MeasurableSet V → V⊆Set.Icc 0 1 →
      V⊆(rationalArcSet (medDeskQ n) n)ᶜ →
      (∫ t in V,‖smallDivisorWave n (Icc 1 (minorRamanujanCutoff n))
        (fun d => (exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t‖^2) ≤
        ε*(n:ℝ)/Real.log n := by
  let T := fun n : ℕ => (Real.log (n:ℝ))^(1/8:ℝ)
  have ht : Tendsto T atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hs := ((tendsto_pow_atTop (α:=ℝ) (by decide : 4≠0)).comp ht).eventually_ge_atTop (8192/ε)
  filter_upwards [hs,minorArc_exactWeight_energy,minorRamanujan_geometry_eventually] with n hs hh hg
  intro V hm hv ho
  have ht0 : 0<T n := by linarith only [hg.2.1]
  have h8 : (T n)^8=Real.log n := hg.2.2.1
  change 8192/ε≤(T n)^4 at hs
  have hle := (div_le_iff₀ hε).mp hs
  apply (hh V hm hv ho).trans
  conv_rhs => rw [←h8]
  apply (div_le_div_iff₀ (pow_pos ht0 12) (pow_pos ht0 8)).mpr
  calc
    _ = 8192*((n:ℝ)*(T n)^8) := by ring
    _ ≤ ((T n)^4*ε)*((n:ℝ)*(T n)^8) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = _ := by ring

end GoldbachPartial
