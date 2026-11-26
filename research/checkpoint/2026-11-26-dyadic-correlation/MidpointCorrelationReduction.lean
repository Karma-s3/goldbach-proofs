import HalfPeriodWingGeometry
import HalfPeriodWingMass

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


/-- After removing the enlarged tube family and the endpoint and midpoint intervals,
a one-sided estimate on the remainder suffices for the frozen target. -/
theorem dyadic_floor_after_tubes_endpoints_and_midpoint
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      ((((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n) \ quarterEndpointStrips n) \ halfPeriodWings n) n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  apply dyadic_floor_from_narrow_core_budget hm h₁ h₂ h₃ major
  obtain ⟨N,hN⟩ := rest
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,logFourDirichletShell_geometry,quarterEndpointStrips_geometry,
    quarterEndpointStrips_mass_small hψ (ε:=1/21600) (by norm_num),
    logFourPrimeTubes_signed_small hψ (ε:=1/21600) (by norm_num),halfPeriodWings_geometry,
    halfPeriodWings_mass_floor hψ (ε:=1/21600) (by norm_num)] with n hn hg hends hwing hsmall hg₂ hm₂
  intro he
  have hu : MeasurableSet (logFourPrimeTubes n) := measurableSet_variableDenominatorTubes .. 
  have hw : quarterEndpointStrips n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n := by
    intro t ht
    exact ⟨(hends.2.2 ht).1,fun hu => Set.disjoint_left.mp hg.2.2.2 hu ht⟩
  have hl := (abs_le.mp (Complex.abs_re_le_norm (∫ t in logFourPrimeTubes n, primeSquareKernel n t))).1
  have hpart := primeArcMass_partition (measurableSet_quarterEndpointStrips n)
    ((narrowCore_measurable n).compl.diff hu) hw n
  have hpart₂ := primeArcMass_partition (measurableSet_halfPeriodWings n)
    (((narrowCore_measurable n).compl.diff hu).diff (measurableSet_quarterEndpointStrips n)) hg₂.2.1 n
  rw [primeArcMass_partition hu (narrowCore_measurable n).compl hg.2.2.1,
    primeArcMass_eq_setIntegral_re_of_subset_Icc n hu hg.2.1,hpart,hpart₂]
  linarith only [hsmall,hl,(abs_le.mp hwing).1,hm₂ he,hN n hn he]

end GoldbachPartial
