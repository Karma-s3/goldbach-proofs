import ClosePrimeGapMass
import NaturalPrimeTubeVolume
import HighDenominatorGeometry

namespace GoldbachPartial
open Finset ExtendedArcCoefficient

theorem gap_sum_upper_triangle (n : ℕ) (J : Finset ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ d ∈ J, ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n), F p (p+d)) =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), if p≤r ∧ r-p∈J then F p r else 0 := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun d _ => p+d)
  · intro d hd
    obtain ⟨hd,he⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa using hd⟩
  · intro d hd d' hd' he; omega
  · intro r hr
    obtain ⟨hr',hpr,hrJ⟩ := mem_filter.mp hr
    have h := mem_range.mp hr'
    exact ⟨r-p,mem_filter.mpr ⟨hrJ,by omega⟩,by omega⟩
  · simp

noncomputable def primePairMode (n p r : ℕ) (t : ℝ) : ℂ :=
  (((weight p:ℂ)*E ((p:ℝ)*t))*((weight r:ℂ)*E ((r:ℝ)*t)))*E (-(n:ℝ)*t)

private theorem primePairMode_swap (n p r : ℕ) (t : ℝ) :
    primePairMode n p r t = primePairMode n r p t := by dsimp [primePairMode]; ring

private theorem primePairMode_at_target {n p r : ℕ} (h : p+r=n) (t : ℝ) :
    primePairMode n p r t = (weight p:ℂ)*(weight r:ℂ) := by
  dsimp [primePairMode]
  rw [show (((weight p:ℂ)*E ((p:ℝ)*t))*((weight r:ℂ)*E ((r:ℝ)*t)))*E (-(n:ℝ)*t) =
      ((weight p:ℂ)*(weight r:ℂ))*(E ((p:ℝ)*t)*E ((r:ℝ)*t)*E (-(n:ℝ)*t)) by ring,
    ← phase_add,← phase_add,← h,Nat.cast_add,
    show (p:ℝ)*t+r*t+-((p:ℝ)+r)*t=0 by ring]
  simp [E]

theorem primeSquareKernel_all_gaps (n : ℕ) (t : ℝ) :
    primeSquareKernel n t = (∑ d ∈ range (n+1), primeGapKernel n d t) +
      ∑ d ∈ Icc 1 n, primeGapKernel n d t := by
  classical
  let I := range (n+1)
  let F := fun p r => primePairMode n p r t
  have hsum : primeSquareKernel n t = ∑ p ∈ I,∑ r ∈ I, F p r := by
    dsimp only [primeSquareKernel,I,F,primePairMode]
    rw [sq,Finset.sum_mul]; simp_rw [Finset.mul_sum,Finset.sum_mul]
  have hgap (J : Finset ℕ) : (∑ d ∈ J, primeGapKernel n d t) =
      ∑ p ∈ I,∑ r ∈ I, if p≤r ∧ r-p∈J then F p r else 0 :=
    gap_sum_upper_triangle n J F
  rw [hsum,hgap,hgap]
  rw [Finset.sum_comm (s:=I) (t:=I) (f:=fun p r => if p≤r ∧ r-p∈Icc 1 n then F p r else 0)]
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  have hpr := mem_range.mp hp
  have hrr := mem_range.mp hr
  by_cases h : p≤r
  · have h₁ : p≤r ∧ r-p ∈ range (n+1) := ⟨h,mem_range.mpr (by omega)⟩
    have h₂ : ¬(r≤p ∧ p-r∈Icc 1 n) := by simp only [mem_Icc]; omega
    rw [ite_eq_left h₁,ite_eq_right h₂,add_zero]
  · have h₁ : ¬(p≤r ∧ r-p∈range (n+1)) := fun x => h x.1
    have h₂ : r≤p ∧ p-r∈Icc 1 n := ⟨by omega,mem_Icc.mpr ⟨by omega,by omega⟩⟩
    rw [ite_eq_right h₁,ite_eq_left h₂,zero_add]
    exact primePairMode_swap n p r t

noncomputable def offTargetGapKernel (n d : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n),
    if p+(p+d)=n then 0 else primePairMode n p (p+d) t

noncomputable def targetGapWeight (n d : ℕ) : ℝ :=
  ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n),
    if p+(p+d)=n then weight p*weight (p+d) else 0

theorem targetGapWeight_nonneg (n d : ℕ) : 0≤targetGapWeight n d := by
  apply sum_nonneg
  intro p _
  have hw (k : ℕ) : 0≤weight k := by
    dsimp [weight]; split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  split_ifs <;> first | exact mul_nonneg (hw _) (hw _) | exact le_rfl


private theorem gap_target_term (n p d : ℕ) (t : ℝ) :
    primePairMode n p (p+d) t =
      (if p+(p+d)=n then 0 else primePairMode n p (p+d) t) +
      ((if p+(p+d)=n then weight p*weight (p+d) else 0 : ℝ):ℂ) := by
  by_cases h : p+(p+d)=n
  · simpa only [ite_eq_left h,zero_add,Complex.ofReal_mul] using primePairMode_at_target h t
  · simp only [ite_eq_right h,Complex.ofReal_zero,add_zero]

theorem primeGapKernel_eq_offTarget_add_weight (n d : ℕ) (t : ℝ) :
    primeGapKernel n d t = offTargetGapKernel n d t+(targetGapWeight n d:ℂ) := by
  let S := (range (n+1)).filter (fun p => p+d≤n)
  let w := fun p => if p+(p+d)=n then weight p*weight (p+d) else 0
  let f := fun p => if p+(p+d)=n then (0:ℂ) else primePairMode n p (p+d) t
  have hc : ((∑ p ∈ S, w p : ℝ):ℂ) = ∑ p ∈ S, (w p:ℂ) := Complex.ofReal_sum ..
  change (∑ p ∈ S, primePairMode n p (p+d) t) = (∑ p ∈ S, f p) + ((∑ p ∈ S,w p:ℝ):ℂ)
  rw [hc,← sum_add_distrib]
  exact sum_congr rfl fun p _ => gap_target_term n p d t


noncomputable def farOffTargetKernel (n H : ℕ) (t : ℝ) : ℂ :=
  2*∑ d ∈ Ioc H n, offTargetGapKernel n d t

noncomputable def farOnTargetWeight (n H : ℕ) : ℝ :=
  2*∑ d ∈ Ioc H n, targetGapWeight n d

theorem farOnTargetWeight_nonneg (n H : ℕ) : 0≤farOnTargetWeight n H :=
  mul_nonneg (by norm_num) (sum_nonneg fun d _ => targetGapWeight_nonneg n d)

private theorem split_gap_ranges {n H : ℕ} (h : H≤n) (f : ℕ → ℂ) :
    (∑ d ∈ range (n+1), f d) + (∑ d ∈ Icc 1 n, f d) =
    ((∑ d ∈ range (H+1), f d)+(∑ d ∈ Icc 1 H, f d))+2*(∑ d ∈ Ioc H n, f d) := by
  classical
  have ha : range (H+1) ∪ Ioc H n = range (n+1) := by ext x; simp only [mem_union,mem_range,mem_Ioc]; omega
  have hb : Icc 1 H ∪ Ioc H n = Icc 1 n := by ext x; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have hc : Disjoint (range (H+1)) (Ioc H n) := by simp only [Finset.disjoint_left,mem_range,mem_Ioc]; omega
  have hd : Disjoint (Icc 1 H) (Ioc H n) := by simp only [Finset.disjoint_left,mem_Icc,mem_Ioc]; omega
  rw [← ha,← hb,sum_union hc,sum_union hd]
  ring

/-- Complete ordered square, with every close gap, the far off-target pairs
and the nonnegative constant coming from far pairs that sum to n. -/
theorem primeSquareKernel_gap_partition {n H : ℕ} (hH : H≤n) (t : ℝ) :
    primeSquareKernel n t = closePrimeGapKernel n H t+farOffTargetKernel n H t+(farOnTargetWeight n H:ℂ) := by
  rw [primeSquareKernel_all_gaps,split_gap_ranges hH]
  change closePrimeGapKernel n H t+2*(∑ d ∈ Ioc H n, primeGapKernel n d t) = _
  have hf : (∑ d ∈ Ioc H n, primeGapKernel n d t) =
      (∑ d ∈ Ioc H n, offTargetGapKernel n d t) + ((∑ d ∈ Ioc H n,targetGapWeight n d:ℝ):ℂ) := by
    rw [Complex.ofReal_sum,←sum_add_distrib]
    exact sum_congr rfl fun d _ => primeGapKernel_eq_offTarget_add_weight n d t
  rw [hf]
  dsimp only [farOffTargetKernel,farOnTargetWeight]
  push_cast; ring

open MeasureTheory Filter
open scoped Topology

private theorem continuous_farOffTargetKernel (n H : ℕ) : Continuous (farOffTargetKernel n H) := by
  unfold farOffTargetKernel offTargetGapKernel
  apply continuous_const.mul
  apply continuous_finsetSum
  intro d _
  apply continuous_finsetSum
  intro p _
  by_cases h : p+(p+d)=n
  · simpa only [ite_eq_left h] using (continuous_const : Continuous (fun _ : ℝ => (0:ℂ)))
  · simp only [ite_eq_right h,primePairMode,E]; fun_prop

private theorem continuous_closePrimeGapKernel (n H : ℕ) : Continuous (closePrimeGapKernel n H) := by
  unfold closePrimeGapKernel primeGapKernel E
  fun_prop

theorem highNaturalPrimeTubes_volume_lower :
    ∀ᶠ n : ℕ in atTop, (1:ℝ)/12 ≤ volume.real (highNaturalPrimeTubes n) :=
  terminalNaturalTube_realVolume_ge_twelfth

/-- On a set of length at least 1/12, it suffices to retain the well-separated
off-target pairs for a one-sided estimate. This inequality is unconditional. -/
theorem highNaturalPrimeTubes_far_lower {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (∫ t in highNaturalPrimeTubes n, farOffTargetKernel n (closePrimeGapCutoff n) t).re - ε*(n:ℝ) ≤
      primeArcMass (highNaturalPrimeTubes n) n := by
  filter_upwards [closePrimeGapKernel_eventually_small hε,highNaturalPrimeTubes_geometry,
    eventually_ge_atTop (1:ℕ)] with n hc hg hn
  let V := highNaturalPrimeTubes n
  let H := closePrimeGapCutoff n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hH : H ≤ n := Nat.floor_le_of_le (by
    change (n:ℝ)^(1/4:ℝ) ≤ (n:ℝ)
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/4:ℝ)≤1))
  have hmeas : MeasurableSet V := naturalTubeUnion_measurable ..
  have hcI : IntegrableOn (closePrimeGapKernel n H) V := (continuous_closePrimeGapKernel n H).continuousOn.integrableOn_Icc.mono_set hg.1
  have hfI : IntegrableOn (farOffTargetKernel n H) V := (continuous_farOffTargetKernel n H).continuousOn.integrableOn_Icc.mono_set hg.1
  have hwI : IntegrableOn (fun _ : ℝ => (farOnTargetWeight n H:ℂ)) V :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set hg.1
  rw [primeArcMass_eq_setIntegral_re_of_subset_Icc n hmeas hg.1]
  change _ ≤ (∫ t in V, primeSquareKernel n t).re
  simp_rw [primeSquareKernel_gap_partition hH]
  rw [integral_add (f:=fun t => closePrimeGapKernel n H t+farOffTargetKernel n H t)
    (g:=fun _ : ℝ => (farOnTargetWeight n H:ℂ)) (hcI.add hfI) hwI,
    integral_add hcI hfI,setIntegral_const,Complex.real_smul]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hpositive := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=V)) (farOnTargetWeight_nonneg n H)
  have hneg := (abs_le.mp (Complex.abs_re_le_norm (∫ t in V,closePrimeGapKernel n H t))).1
  change ‖∫ t in V, closePrimeGapKernel n H t‖ ≤ ε*n at hc
  change (∫ t in V, farOffTargetKernel n H t).re - ε*(n:ℝ) ≤ _
  linarith only [hneg,hc,hpositive]

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


/-- Only far off-target pairs need to be handled on the high-denominator tubes. -/
theorem dyadic_floor_of_far_remainder_budget
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (δ : ℝ) (hδ : δ < 1/288)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(δ*(n:ℝ)) ≤
      primeArcMass (remainingPrimeArcs n \ highNaturalPrimeTubes n) n +
      (∫ t in highNaturalPrimeTubes n, farOffTargetKernel n (closePrimeGapCutoff n) t).re) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  let η : ℝ := (1/288-δ)/4
  have hη : 0<η := by dsimp [η]; linarith
  apply dyadic_floor_from_narrow_core_budget hm h₁ h₂ h₃ major
  obtain ⟨N,hN⟩ := rest
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,logFourDirichletShell_geometry,quarterEndpointStrips_geometry,
    quarterEndpointStrips_mass_small hψ (ε:=η) hη,
    logFourPrimeTubes_signed_small hψ (ε:=η) hη,halfPeriodWings_geometry,
    halfPeriodWings_mass_floor hψ (ε:=η) hη,highNaturalPrimeTubes_geometry,
    highNaturalPrimeTubes_far_lower (ε:=η) hη]
    with n hn hg hends hwing hsmall hg₂ hm₂ hhigh hoff
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
  have hrem : MeasurableSet (remainingPrimeArcs n) :=
    (((narrowCore_measurable n).compl.diff hu).diff (measurableSet_quarterEndpointStrips n)).diff
      (measurableSet_halfPeriodWings n)
  have hpart₃ := primeArcMass_partition (naturalTubeUnion_measurable ..) hrem hhigh.2 n
  rw [primeArcMass_partition hu (narrowCore_measurable n).compl hg.2.2.1,
    primeArcMass_eq_setIntegral_re_of_subset_Icc n hu hg.2.1,hpart,hpart₂]
  change _ ≤ _ + (_ + (_ + primeArcMass (remainingPrimeArcs n) n))
  have hsum : -(δ*(n:ℝ))-η*n ≤ primeArcMass (remainingPrimeArcs n) n := by
    rw [hpart₃]
    change _ ≤ primeArcMass (highNaturalPrimeTubes n) n +
      primeArcMass (remainingPrimeArcs n \ highNaturalPrimeTubes n) n
    linarith only [hoff,hN n hn he]
  have hb : δ*(n:ℝ)+4*η*n=(n:ℝ)/288 := by dsimp [η]; ring
  linarith only [hsmall,hl,(abs_le.mp hwing).1,hm₂ he,hsum,hb]



theorem dyadic_floor_from_far_off_target_remainder
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤
      primeArcMass (remainingPrimeArcs n \ highNaturalPrimeTubes n) n +
      (∫ t in highNaturalPrimeTubes n, farOffTargetKernel n (closePrimeGapCutoff n) t).re) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  apply dyadic_floor_of_far_remainder_budget hm h₁ h₂ h₃ major hψ (1/300) (by norm_num)
  obtain ⟨N,hN⟩ := rest
  refine ⟨N,fun n hn he => ?_⟩
  linarith only [hN n hn he]

end GoldbachPartial
