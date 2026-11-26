import NearRootShell

namespace GoldbachPartial
open Filter MeasureTheory
open scoped Topology

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

/-- A second region only needs a one-sided lower bound. The residual budget remains n/300. -/
theorem dyadic_floor_after_near_root_and_one_sided_arcs
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform) (W : ℕ → Set ℝ) (hw : ∀ n, MeasurableSet (W n))
    (hd : ∀ᶠ n : ℕ in atTop, W n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ nearRootTubes n)
    (wing : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ)/14400 ≤ primeArcMass (W n) n)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      (((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ nearRootTubes n) \ W n) n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  apply dyadic_floor_from_narrow_core_budget hm h₁ h₂ h₃ major
  obtain ⟨N,hN⟩ := rest
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1:ℕ), hd, wing,
    nearRootTubes_geometry, (nearRootTubes_integral_small hψ).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/14400))] with n hn hpos hW hwing hg hsmall
  intro he
  have hp : (0:ℝ)<n := by exact_mod_cast hpos
  have hu : MeasurableSet (nearRootTubes n) := measurableSet_allDenominatorIntervalTubeUnion ..
  have ht := (div_lt_iff₀ hp).mp hsmall
  have hl := (abs_le.mp (Complex.abs_re_le_norm (∫ t in nearRootTubes n, primeSquareKernel n t))).1
  have hpart := primeArcMass_partition (hw n) ((narrowCore_measurable n).compl.diff hu) hW n
  rw [primeArcMass_partition hu (narrowCore_measurable n).compl hg.2.2,
    primeArcMass_eq_setIntegral_re_of_subset_Icc n hu hg.1,hpart]
  linarith only [ht,hl,hwing he,hN n hn he]

end GoldbachPartial
