import GRHDeepShell
import TerminalPrimeArcChange
import SquareRootLogShellGeometry
import TerminalIntervalModelBudget

namespace GoldbachPartial
open Filter MeasureTheory
open scoped Topology

/-- Fixed-width intervals around every reduced fraction in the indicated denominator range. -/
noncomputable def nearRootTubes (n : ℕ) : Set ℝ :=
  allDenominatorIntervalTubeUnion n (medDeskD n) (terminalPrimeArcCutoff n)

theorem nearRootTubes_geometry :
    ∀ᶠ n : ℕ in atTop, nearRootTubes n ⊆ Set.Icc 0 1 ∧
      nearRootTubes n ⊆ (coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n))ᶜ ∧
      nearRootTubes n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ := by
  filter_upwards [squareRootLogShell_geometry] with n hg
  obtain ⟨hy,_,hs,_,hsep⟩ := hg
  have hd := allDenominatorIntervalTubeUnion_inside_deep hsep
  refine ⟨allDenominatorIntervalTubeUnion_inside_unit hy hs,hd,?_⟩
  intro t ht hh
  apply hd ht
  obtain ⟨q,a,hq,hu,ha,hcop,hw⟩ := hh
  refine ⟨q,a,hq,hu,ha,hcop,hw.trans ?_⟩
  have hm : 1 ≤ 256*medDeskD n := by omega
  have he : medDeskQ n ≤ (256*medDeskD n)*medDeskQ n := by
    simpa using Nat.mul_le_mul_right (medDeskQ n) hm
  exact div_le_div_of_nonneg_right (by exact_mod_cast he) (by positivity)

theorem nearRoot_prefix_of_uniform_psi (hψ : grhAllUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ terminalPrimeArcPrefix C := by
  obtain ⟨C,hC,h⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  refine ⟨C,hC,?_⟩
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (2:ℕ)] with n hg hn
  intro j hj χ k hk
  exact h n hn (j+1) ((Finset.mem_Ico.mp hj).2.trans_le hg.2.2.2.1) χ k hk

/-- The model contribution alone is little-oh of n/(1+log n)^2. -/
theorem nearRootTubes_model {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖(∫ t in nearRootTubes n, primeSquareKernel n t) -
      terminalPrimeArcChange n‖ ≤ ε*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  filter_upwards [squareRootLogShell_geometry,eventually_interval_model_budget_log_sq hε,
    eventually_ge_atTop (1:ℕ)] with n hg hm hn
  exact (allDenominatorIntervalTubeUnion_model_bound hn hg.1 hg.2.2.1).trans
    (hm _ hg.2.2.2.1)

theorem nearRootTubes_signed_of_prefix {C : ℝ} (hC : 0≤C) (hp : terminalPrimeArcPrefix C) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in nearRootTubes n, primeSquareKernel n t‖ ≤
      (1+terminalPrimeArcConstant C)*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  filter_upwards [nearRootTubes_model (ε:=1) zero_lt_one,terminalPrimeArcChange_log_bound C hC hp]
    with n hm he
  let I := ∫ t in nearRootTubes n, primeSquareKernel n t
  have ht := norm_add_le (I-terminalPrimeArcChange n) (terminalPrimeArcChange n)
  rw [sub_add_cancel] at ht
  exact ht.trans ((add_le_add hm he).trans_eq (by ring))

theorem nearRootTubes_signed_of_uniform_psi (hψ : grhAllUniform) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ n : ℕ in atTop,
      ‖∫ t in nearRootTubes n, primeSquareKernel n t‖ ≤ A*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  obtain ⟨C,hC,h⟩ := nearRoot_prefix_of_uniform_psi hψ
  exact ⟨_,by dsimp only [terminalPrimeArcConstant]; positivity,nearRootTubes_signed_of_prefix hC h⟩

theorem nearRootTubes_signed_of_dirichlet_inputs
    (Lfun : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℂ)
    (m : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℕ)
    (hline : grhStripInput Lfun) (hfinite : grhFiniteInput Lfun)
    (hcount : grhZeroCountInput Lfun m) (hformula : grhExplicitInput Lfun m) (hind : grhInductionInput) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ n : ℕ in atTop,
      ‖∫ t in nearRootTubes n, primeSquareKernel n t‖ ≤ A*(n:ℝ)/(terminalPrimeArcLog n)^2 :=
  nearRootTubes_signed_of_uniform_psi (uniform_all_psi_of_primitive
    (uniform_primitive_psi_of_GRH_inputs Lfun m hline hfinite hcount hformula) hind)

theorem nearRootTubes_integral_small (hψ : grhAllUniform) :
    Tendsto (fun n : ℕ => ‖∫ t in nearRootTubes n, primeSquareKernel n t‖/(n:ℝ))
      atTop (𝓝 0) := by
  obtain ⟨A,_,hA⟩ := nearRootTubes_signed_of_uniform_psi hψ
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto terminalPrimeArcLog atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [terminalPrimeArcLog]; linarith) hlog
  have hpow : Tendsto (fun n : ℕ => (terminalPrimeArcLog n)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp hL
  have hdec : Tendsto (fun n : ℕ => A/(terminalPrimeArcLog n)^2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x:=A)).div_atTop hpow
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hdec
  filter_upwards [hA,eventually_ge_atTop (1:ℕ)] with n h hn
  apply (div_le_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr
  exact h.trans_eq (by ring)

/-- Suffices to bound the signed mass of the remaining complement for every large even n. -/
theorem dyadic_floor_after_near_root_tubes
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      ((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ nearRootTubes n) n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n := by
  exact dyadic_floor_from_narrow_core_after_deletion hm h₁ h₂ h₃ major nearRootTubes
    (fun _ => measurableSet_allDenominatorIntervalTubeUnion ..)
    (nearRootTubes_geometry.mono fun _ h => h.1) (nearRootTubes_geometry.mono fun _ h => h.2.2)
    (nearRootTubes_integral_small hψ) rest

end GoldbachPartial
