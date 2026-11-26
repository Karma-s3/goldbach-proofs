import DeepPrimeShell
import GRHTruePrimePrefix
import GrowingPrimeArcChange

/-!
The uniform Dirichlet Chebyshev estimate supplies every character prefix used in the
deep shell. The analytic inputs to that estimate are made explicit below. The original
GRH project and this research desk use different toolchains.
-/

namespace GoldbachPartial
open Filter MeasureTheory
open scoped Topology

theorem dyadicCharacterPrefix_of_uniform_psi (hψ : grhAllUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ dyadicCharacterPrefixBound C := by
  obtain ⟨C,hC,h⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  refine ⟨C,hC,?_⟩
  filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget] with n hn
  obtain ⟨hbig,hy,hcu,_,_⟩ := hn
  let Y := medDeskD n
  change 192^4 ≤ Y at hy
  change Y^3 ≤ n at hcu
  have h2 : 2 ≤ Y := by omega
  have ha := Nat.mul_le_mul_left Y h2
  have hb := Nat.mul_le_mul_left (Y*Y) (show 1≤Y by omega)
  have hs : 2*Y ≤ n := by nlinarith only [ha,hb,hcu]
  intro j hj χ k hk
  exact h n (by omega) (j+1) ((Finset.mem_Ico.mp hj).2.trans_le hs) χ k hk

theorem frozen_shell_integral_power_of_uniform_psi (hψ : grhAllUniform) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in allDenominatorTubeUnion n (medDeskD n), primeSquareKernel n t‖ ≤
      (4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12)*(n:ℝ)^(23/24:ℝ) := by
  obtain ⟨C,hC,h⟩ := dyadicCharacterPrefix_of_uniform_psi hψ
  exact frozen_shell_integral_power hC h

theorem frozen_shell_power_of_dirichlet_inputs
    (Lfun : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℂ)
    (m : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℕ)
    (hline : grhStripInput Lfun) (hfinite : grhFiniteInput Lfun)
    (hcount : grhZeroCountInput Lfun m) (hformula : grhExplicitInput Lfun m) (hind : grhInductionInput) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in allDenominatorTubeUnion n (medDeskD n), primeSquareKernel n t‖ ≤
      (4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12)*(n:ℝ)^(23/24:ℝ) :=
  frozen_shell_integral_power_of_uniform_psi (uniform_all_psi_of_primitive
    (uniform_primitive_psi_of_GRH_inputs Lfun m hline hfinite hcount hformula) hind)

theorem dyadic_floor_from_uniform_psi_and_remaining_arcs
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      ((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ allDenominatorTubeUnion n (medDeskD n)) n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n := by
  obtain ⟨C,hc,h⟩ := dyadicCharacterPrefix_of_uniform_psi hψ
  exact dyadic_floor_after_denominator_shell hm h₁ h₂ h₃ major hc h rest

open Filter
open scoped Topology

theorem threeEighths_shell_geometry :
    ∀ᶠ n : ℕ in atTop, let T := (n:ℝ)^(1/48:ℝ); let Y := medDeskD n; let R := growingPrimeArcCutoff n
      4 ≤ Y ∧ Y ≤ R ∧ R^2 ≤ n ∧ R ≤ n ∧
      R*(256*Y*medDeskQ n+Y)<n ∧ ((Nat.log 2 R:ℕ):ℝ)+1 ≤ T := by
  let t := fun n : ℕ => (n:ℝ)^(1/48:ℝ)
  have htlim : Tendsto t atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp
    tendsto_natCast_atTop_atTop
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/48)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget,
    medDesk_composite_shell_thresholds 0 le_rfl,htlim.eventually_ge_atTop 300,
    hlog.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/10))] with n hb hc htbig hsmall
  let T := t n
  let Y := medDeskD n
  let R := growingPrimeArcCutoff n
  obtain ⟨ht,h48,hy,h16,_,_,_,_,_⟩ := hc
  change 1 ≤ T at ht
  change T^48=(n:ℝ) at h48
  change (Y:ℝ) ≤ T^16 at h16
  change 300 ≤ T at htbig
  have ht0 : 0<T := by linarith
  have hn2 : 2≤n := (by decide : 2 ≤ 2*192^4).trans hb.1
  have hn : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hr : (R:ℝ) ≤ T^18 := by
    have he : T^18=(n:ℝ)^(3/8:ℝ) := by dsimp [T,t]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num
    rw [he]; exact Nat.floor_le (by positivity)
  have hyr : Y ≤ R := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1/3:ℝ)≤3/8))
  have hrn : R ≤ n := by
    exact_mod_cast hr.trans ((pow_le_pow_right₀ ht (by decide : 18≤48)).trans_eq h48)
  have hlogn : Real.log n < T/10 := by
    change Real.log (n:ℝ)/T < 1/10 at hsmall
    linarith [(div_lt_iff₀ ht0).mp hsmall]
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hlog2
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax : ((Nat.log 2 (n+2):ℕ):ℝ)+1 ≤ T := by
    have h := Real.natLog_le_logb (n+2) 2
    simp only [Real.logb,Nat.cast_add,Nat.cast_ofNat] at h
    have he : 2≤(n:ℝ) := by exact_mod_cast hn2
    have hn2n : (n:ℝ)+2 ≤ 2*n := by linarith
    have hlogarg := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hn2n
    rw [Real.log_mul (by norm_num) (by positivity)] at hlogarg
    have hlogU := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have coef : Real.log ((n:ℝ)+2)/Real.log 2 ≤ T-1 := by
      apply (div_le_iff₀ hlog2p).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ Real.log 2-1/2 by linarith)]
    linarith
  have hQ : ((medDeskQ n):ℝ) ≤ T^2 := by
    dsimp only [medDeskQ]; push_cast
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hmax]) 2
  refine ⟨(by decide : 4≤192^4).trans hb.2.1,hyr,?_,hrn,?_,?_⟩
  · have he : (R:ℝ)^2 ≤ (n:ℝ) := calc
      _ ≤ (T^18)^2 := pow_le_pow_left₀ (by positivity) hr 2
      _ = T^36 := by ring
      _ ≤ _ := (pow_le_pow_right₀ ht (by decide : 36≤48)).trans_eq h48
    exact_mod_cast he
  · have he : (R:ℝ)*(256*(Y:ℝ)*(medDeskQ n:ℝ)+Y)<(n:ℝ) := calc
      _ ≤ T^18*(256*T^16*T^2+T^18) := by
        have hy18 := h16.trans (pow_le_pow_right₀ ht (by decide : 16≤18))
        gcongr
      _ = 257*T^36 := by ring
      _ < T*T^36 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = T^37 := by ring
      _ ≤ _ := (pow_le_pow_right₀ ht (by decide : 37≤48)).trans_eq h48
    exact_mod_cast he
  · exact (add_le_add_left (by exact_mod_cast Nat.log_mono_right (by omega : R ≤ n+2) :
      ((Nat.log 2 R:ℕ):ℝ) ≤ ((Nat.log 2 (n+2):ℕ):ℝ)) 1).trans hmax

theorem threeEighths_model_cost :
    ∀ᶠ n : ℕ in atTop, ((n:ℝ)+1)*((((Nat.log 2 (growingPrimeArcCutoff n):ℕ):ℝ)+1)^2*
      (2*(n.divisors.card:ℝ)/(medDeskD n:ℝ))) ≤
      (8*2^12:ℝ)*(n:ℝ)^(23/24:ℝ) := by
  filter_upwards [threeEighths_shell_geometry,medDesk_composite_shell_thresholds 0 le_rfl] with n hg hc
  let T := (n:ℝ)^(1/48:ℝ)
  let Y := medDeskD n
  let K : ℝ := ((Nat.log 2 (growingPrimeArcCutoff n):ℕ):ℝ)+1
  obtain ⟨ht,h48,hy,_,hlo,_,_,_,_⟩ := hc
  change 1 ≤ T at ht
  change T^48 = (n:ℝ) at h48
  change T^16/2 ≤ (Y:ℝ) at hlo
  have ht0 : 0<T := by linarith
  have hyr : 0<(Y:ℝ) := by exact_mod_cast hy
  have hk : K≤T := hg.2.2.2.2.2
  have hk0 : 0≤K := by dsimp [K]; positivity
  have hτ : (n.divisors.card:ℝ) ≤ (2:ℝ)^12*T^12 := by
    apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by positivity)
    have h : (n.divisors.card:ℝ)^4 ≤ (2:ℝ)^48*n := by exact_mod_cast divisor_count_fourth_le n
    refine h.trans_eq ?_
    rw [← h48]; ring
  have hI : 1/(Y:ℝ) ≤ 2/T^16 := (div_le_div_iff₀ hyr (by positivity)).mpr (by linarith)
  have h1 : T^48+1 ≤ 2*T^48 := by linarith [one_le_pow₀ (n:=48) ht]
  have h46 : T^46=(n:ℝ)^(23/24:ℝ) := by
    dsimp [T]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num
  calc
    _ = (T^48+1)*(K^2*(2*(n.divisors.card:ℝ))*(1/(Y:ℝ))) := by rw [h48]; dsimp [K,Y]; ring
    _ ≤ (2*T^48)*(T^2*(2*((2:ℝ)^12*T^12))*(2/T^16)) := by gcongr
    _ = (8*2^12:ℝ)*T^46 := by field_simp; ring
    _ = _ := by rw [h46]


noncomputable def growingDeepTubes (n : ℕ) : Set ℝ :=
  allDenominatorIntervalTubeUnion n (medDeskD n) (growingPrimeArcCutoff n)

theorem growingDeepTubes_geometry :
    ∀ᶠ n : ℕ in atTop, growingDeepTubes n ⊆ Set.Icc 0 1 ∧
      growingDeepTubes n ⊆ (coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n))ᶜ ∧
      growingDeepTubes n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ := by
  filter_upwards [threeEighths_shell_geometry] with n hn
  obtain ⟨hy,_,hs,_,hsep,_⟩ := hn
  have hy0 : 0 < medDeskD n := (by decide : 0<4).trans_le hy
  have hd := allDenominatorIntervalTubeUnion_inside_deep hsep
  refine ⟨allDenominatorIntervalTubeUnion_inside_unit hy0 hs,hd,?_⟩
  intro t ht hh
  apply hd ht
  obtain ⟨q,a,hq,hu,ha,hcop,hw⟩ := hh
  refine ⟨q,a,hq,hu,ha,hcop,hw.trans ?_⟩
  have hmul : 1 ≤ 256*medDeskD n := by omega
  have he : medDeskQ n ≤ (256*medDeskD n)*medDeskQ n := by
    simpa using Nat.mul_le_mul_right (medDeskQ n) hmul
  exact div_le_div_of_nonneg_right (by exact_mod_cast he) (by positivity)

theorem growingPrimeArcPrefix_of_uniform_psi (hψ : grhAllUniform) : ∃ C : ℝ, 0≤C ∧ growingPrimeArcPrefix C := by
  obtain ⟨C,hC,h⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  refine ⟨C,hC,?_⟩
  filter_upwards [threeEighths_shell_geometry,eventually_ge_atTop (2:ℕ)] with n hn hn2
  intro j hj χ k hk
  exact h n hn2 (j+1) ((Finset.mem_Ico.mp hj).2.trans_le hn.2.2.2.1) χ k hk

/-- A single signed coefficient estimate on the actual union through n^(3/8). -/
theorem growingDeepTubes_power_of_prefix {C : ℝ} (hC : 0≤C) (hP : growingPrimeArcPrefix C) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in growingDeepTubes n, primeSquareKernel n t‖ ≤
      ((2/5:ℝ)*((9*C)^2*(1+Real.pi/10)^2+1)+12+8*2^12)*(n:ℝ)^(23/24:ℝ) := by
  filter_upwards [threeEighths_shell_geometry,threeEighths_model_cost,growingPrimeArcChange_power_bound C hC hP,
    eventually_ge_atTop (1:ℕ)] with n hg hm hc hn
  let I := ∫ t in growingDeepTubes n, primeSquareKernel n t
  have hy : 0 < medDeskD n := (by decide : 0<4).trans_le hg.1
  have he : ‖I-growingPrimeArcChange n‖ ≤ (8*2^12:ℝ)*(n:ℝ)^(23/24:ℝ) :=
    (allDenominatorIntervalTubeUnion_model_bound hn hy hg.2.2.1).trans hm
  have hpow : (n:ℝ)^(15/16:ℝ) ≤ (n:ℝ)^(23/24:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  have hcompare := norm_add_le (I-growingPrimeArcChange n) (growingPrimeArcChange n)
  rw [sub_add_cancel] at hcompare
  refine hcompare.trans ?_
  rw [add_mul]
  exact (add_le_add he (hc.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))).trans_eq (add_comm ..)

theorem growingDeepTubes_integral_small {C : ℝ} (hC : 0≤C) (hP : growingPrimeArcPrefix C) :
    Tendsto (fun n : ℕ => ‖∫ t in growingDeepTubes n, primeSquareKernel n t‖/(n:ℝ)) atTop (𝓝 0) := by
  let A : ℝ := (2/5:ℝ)*((9*C)^2*(1+Real.pi/10)^2+1)+12+8*2^12
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/24)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun n : ℕ => A*(n:ℝ)^(-(1/24:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hpow.const_mul A
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)
  · filter_upwards [growingDeepTubes_power_of_prefix hC hP,eventually_ge_atTop (1:ℕ)] with n h hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    refine (div_le_div_of_nonneg_right h hnR.le).trans_eq ?_
    change A*(n:ℝ)^(23/24:ℝ)/n = _
    rw [mul_div_assoc,show (n:ℝ)^(23/24:ℝ)/(n:ℝ) = (n:ℝ)^(-(1/24:ℝ)) by
      conv_lhs => rhs; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_sub hnR]; norm_num]

theorem dyadic_floor_after_growing_deep_tubes
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      ((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ growingDeepTubes n) n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n := by
  obtain ⟨C,hc,h⟩ := growingPrimeArcPrefix_of_uniform_psi hψ
  exact dyadic_floor_from_narrow_core_after_deletion hm h₁ h₂ h₃ major growingDeepTubes
    (fun _ => measurableSet_allDenominatorIntervalTubeUnion ..)
    (growingDeepTubes_geometry.mono fun _ h => h.1) (growingDeepTubes_geometry.mono fun _ h => h.2.2)
    (growingDeepTubes_integral_small hc h) rest



/-- Without character estimates, the part of the signed coefficient predicted by
the Ramanujan model already satisfies an explicit power saving. -/
theorem growingDeepTubes_model_power :
    ∀ᶠ n : ℕ in atTop, ‖(∫ t in growingDeepTubes n, primeSquareKernel n t) -
      growingPrimeArcChange n‖ ≤ (8*2^12:ℝ)*(n:ℝ)^(23/24:ℝ) := by
  filter_upwards [threeEighths_shell_geometry,threeEighths_model_cost,eventually_ge_atTop (1:ℕ)] with n hg hm hn
  have hy : 0 < medDeskD n := (by decide : 0<4).trans_le hg.1
  exact (allDenominatorIntervalTubeUnion_model_bound hn hy hg.2.2.1).trans hm

theorem growingDeepTubes_power_of_uniform_psi (hψ : grhAllUniform) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      ‖∫ t in growingDeepTubes n, primeSquareKernel n t‖ ≤ A*(n:ℝ)^(23/24:ℝ) := by
  obtain ⟨C,hC,h⟩ := growingPrimeArcPrefix_of_uniform_psi hψ
  exact ⟨_,by positivity,growingDeepTubes_power_of_prefix hC h⟩


end GoldbachPartial
