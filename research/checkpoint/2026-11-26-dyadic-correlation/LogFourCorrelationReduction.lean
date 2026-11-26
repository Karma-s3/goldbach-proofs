import VariableDenominatorTubes
import QuarterEndpointNaturalGeometry
import EndpointCorrelationReduction
import ParsevalLogPrimeArc

namespace GoldbachPartial
open Filter MeasureTheory
open scoped Topology

noncomputable def logFourPrimeTubes (n : ℕ) : Set ℝ :=
  variableDenominatorTubes (medDeskD n) (terminalPrimeArcCutoff n) (logFourDirichletRadius n)

theorem logFourPrimeTubes_model {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖(∫ t in logFourPrimeTubes n, primeSquareKernel n t) -
      parsevalLogArcChange n‖ ≤ ε*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  filter_upwards [logFourDirichletShell_geometry,squareRootLogShell_geometry,
    eventually_interval_model_budget_log_sq hε,eventually_ge_atTop (4:ℕ)] with n hg hc hm hn
  have hS : (2:ℝ) ≤ Real.sqrt n := calc
    (2:ℝ) = Real.sqrt 4 := by rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hL : (1:ℝ) ≤ terminalPrimeArcLog n := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hρ (q : ℕ) (hq : q ∈ Finset.Ioc (medDeskD n) (terminalPrimeArcCutoff n)) :
      0 ≤ logFourDirichletRadius n q ∧ logFourDirichletRadius n q ≤ 1/2 := by
    have hq' : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by have := (Finset.mem_Ioc.mp hq).1; omega)
    have hden : (2:ℝ) ≤ q*Real.sqrt n*(terminalPrimeArcLog n)^4 := calc
      (2:ℝ) = (1:ℝ)*2*1^4 := by norm_num
      _ ≤ _ := by gcongr
    exact ⟨by dsimp [logFourDirichletRadius]; positivity,
      one_div_le_one_div_of_le (by norm_num) hden⟩
  exact (variableDenominatorTubes_model_bound (by omega) hc.1 (logFourDirichletRadius n) hρ hg.1).trans
    (hm _ hc.2.2.2.1)

/-- The true integral on the union of the enlarged intervals is uniformly o(n). -/
theorem logFourPrimeTubes_signed_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in logFourPrimeTubes n, primeSquareKernel n t‖ ≤ ε*(n:ℝ) := by
  filter_upwards [logFourPrimeTubes_model (half_pos hε),
    parsevalLogArcChange_small hψ (half_pos hε)] with n hm he
  have hL : (1:ℝ) ≤ terminalPrimeArcLog n := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hm' := hm.trans (div_le_self (by positivity) (one_le_pow₀ (n:=2) hL))
  let I := ∫ t in logFourPrimeTubes n, primeSquareKernel n t
  have h : ‖I‖ ≤ ‖I-parsevalLogArcChange n‖+‖parsevalLogArcChange n‖ := by
    simpa only [sub_add_cancel] using norm_add_le (I-parsevalLogArcChange n) (parsevalLogArcChange n)
  exact h.trans ((add_le_add hm' he).trans_eq (by ring))



theorem logFourPrimeTubes_rate_of_uniform_psi (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ n : ℕ in atTop,
      ‖∫ t in logFourPrimeTubes n, primeSquareKernel n t‖ ≤ K*(n:ℝ)/Real.sqrt (terminalPrimeArcLog n) := by
  obtain ⟨C,hC,hp⟩ := nearRoot_prefix_of_uniform_psi hψ
  refine ⟨2*parsevalLogArcConstant C+5,by dsimp only [parsevalLogArcConstant]; positivity,?_⟩
  filter_upwards [logFourPrimeTubes_model (ε:=1) zero_lt_one,hp,eventually_ge_atTop (4:ℕ)] with n hm he hn
  have hL : (1:ℝ) ≤ terminalPrimeArcLog n := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hpos : 0<terminalPrimeArcLog n := zero_lt_one.trans_le hL
  have h2 : Real.sqrt (terminalPrimeArcLog n) ≤ (terminalPrimeArcLog n)^2 := by
    have hP : terminalPrimeArcLog n ≤ (terminalPrimeArcLog n)^2 := by
      nlinarith only [mul_nonneg hpos.le (sub_nonneg.mpr hL)]
    have hS := Real.sqrt_le_sqrt hP
    rw [Real.sqrt_sq hpos.le] at hS
    exact hS.trans hP
  have hm' := hm.trans (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hpos) h2)
  let I := ∫ t in logFourPrimeTubes n, primeSquareKernel n t
  have h : ‖I‖ ≤ ‖I-parsevalLogArcChange n‖+‖parsevalLogArcChange n‖ := by
    simpa only [sub_add_cancel] using norm_add_le (I-parsevalLogArcChange n) (parsevalLogArcChange n)
  exact h.trans ((add_le_add hm' (parsevalLogArcChange_bound_at hn hC he)).trans_eq (by ring))

theorem logFourPrimeTubes_rate_of_dirichlet_inputs
    (Lfun : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℂ)
    (m : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℕ)
    (hline : grhStripInput Lfun) (hfinite : grhFiniteInput Lfun)
    (hcount : grhZeroCountInput Lfun m) (hformula : grhExplicitInput Lfun m) (hind : grhInductionInput) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ n : ℕ in atTop,
      ‖∫ t in logFourPrimeTubes n, primeSquareKernel n t‖ ≤ K*(n:ℝ)/Real.sqrt (terminalPrimeArcLog n) :=
  logFourPrimeTubes_rate_of_uniform_psi (uniform_all_psi_of_primitive
    (uniform_primitive_psi_of_GRH_inputs Lfun m hline hfinite hcount hformula) hind)

/-- Every reduced fraction in the band gains at least a factor 20(1+log n)
in radius over the fixed 1/(20n) family. -/
theorem logFour_radius_lower {n q : ℕ} (hn : 0<n) (hq : 0<q) (hr : q≤terminalPrimeArcCutoff n) :
    terminalPrimeArcLog n / (n:ℝ) ≤ logFourDirichletRadius n q := by
  let L := terminalPrimeArcLog n
  have hL : 0<L := by dsimp only [L,terminalPrimeArcLog]; linarith [Real.log_natCast_nonneg n]
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hS : 0<Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hr' : (q:ℝ) ≤ Real.sqrt n/L^5 :=
    (show (q:ℝ) ≤ (terminalPrimeArcCutoff n:ℝ) by exact_mod_cast hr).trans (Nat.floor_le (by positivity))
  change L/n ≤ 1/((q:ℝ)*Real.sqrt n*L^4)
  apply (div_le_div_iff₀ hn' (by positivity)).mpr
  calc
    _ ≤ L*((Real.sqrt n/L^5)*Real.sqrt n*L^4) := by gcongr
    _ = (Real.sqrt n)^2 := by field_simp
    _ = _ := by rw [Real.sq_sqrt hn'.le,one_mul]

private theorem narrowCore_measurable (n : ℕ) :
    MeasurableSet (coreArcBand n (medDeskQ n) 0 (medDeskD n)) := by
  simp only [coreArcBand, Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  exact measurableSet_le
    (show Continuous (fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|) by fun_prop).measurable measurable_const


/-- After removing the enlarged tube family and the two endpoint intervals,
a one-sided estimate on the remainder suffices for the frozen target. -/
theorem dyadic_floor_after_log_four_tubes_and_endpoints
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      (((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n) \ quarterEndpointStrips n) n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  apply dyadic_floor_from_narrow_core_budget hm h₁ h₂ h₃ major
  obtain ⟨N,hN⟩ := rest
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,logFourDirichletShell_geometry,quarterEndpointStrips_geometry,
    quarterEndpointStrips_mass_floor hψ,logFourPrimeTubes_signed_small hψ (ε:=1/14400) (by norm_num)]
    with n hn hg hends hwing hsmall
  intro he
  have hu : MeasurableSet (logFourPrimeTubes n) := measurableSet_variableDenominatorTubes .. 
  have hw : quarterEndpointStrips n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n := by
    intro t ht
    exact ⟨(hends.2.2 ht).1,fun hu => Set.disjoint_left.mp hg.2.2.2 hu ht⟩
  have hl := (abs_le.mp (Complex.abs_re_le_norm (∫ t in logFourPrimeTubes n, primeSquareKernel n t))).1
  have hpart := primeArcMass_partition (measurableSet_quarterEndpointStrips n)
    ((narrowCore_measurable n).compl.diff hu) hw n
  rw [primeArcMass_partition hu (narrowCore_measurable n).compl hg.2.2.1,
    primeArcMass_eq_setIntegral_re_of_subset_Icc n hu hg.2.1,hpart]
  linarith only [hsmall,hl,hwing he,hN n hn he]

end GoldbachPartial
