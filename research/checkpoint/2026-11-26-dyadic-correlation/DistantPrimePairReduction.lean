import FarShortModeMass

namespace GoldbachPartial
open Finset

theorem ordered_far_gap_sum (n H : ℕ) (F : ℕ → ℕ → ℂ) (hs : ∀ p r, F p r=F r p) :
    2*(∑ d ∈ Ioc H n, ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n), F p (p+d)) =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), if p+H<r ∨ r+H<p then F p r else 0 := by
  classical
  let I := range (n+1)
  let G := fun p r => if p≤r ∧ r-p∈Ioc H n then F p r else 0
  have ha := gap_sum_upper_triangle n (Ioc H n) F
  change _ = ∑ p ∈ I,∑ r ∈ I,G p r at ha
  have hb : (∑ p ∈ I,∑ r ∈ I,G p r) = ∑ p ∈ I,∑ r ∈ I,G r p := sum_comm
  rw [two_mul,ha]
  calc
    _ = (∑ p ∈ I,∑ r ∈ I,G p r) + ∑ p ∈ I,∑ r ∈ I,G r p := congrArg (_ + ·) hb
    _ = _ := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro r hr
      have hp' : p<n+1 := mem_range.mp hp
      have hr' : r<n+1 := mem_range.mp hr
      have h₁ : (p≤r ∧ r-p∈Ioc H n) ↔ p+H<r := by simp only [mem_Ioc]; omega
      have h₂ : (r≤p ∧ p-r∈Ioc H n) ↔ r+H<p := by simp only [mem_Ioc]; omega
      dsimp only [G]
      rw [if_congr h₁ rfl rfl,if_congr h₂ rfl rfl]
      by_cases hl : p+H<r
      · have hnl : ¬r+H<p := by omega
        simp [hl,hnl]
      · by_cases hr : r+H<p
        · simp [hl,hr,hs r p]
        · simp [hl,hr]

theorem farOffTargetKernel_ordered (n H : ℕ) (t : ℝ) :
    farOffTargetKernel n H t =
      ∑ p ∈ range (n+1),∑ r ∈ range (n+1),
        if p+H<r ∨ r+H<p then (if p+r=n then 0 else primePairMode n p r t) else 0 := by
  apply ordered_far_gap_sum n H (fun p r => if p+r=n then 0 else primePairMode n p r t)
  intro p r
  rw [Nat.add_comm p r]
  by_cases h : r+p=n
  · simp [h]
  · simp only [ite_eq_right h,primePairMode]; ring


/-- Both the prime gap and the distance of the sum from n exceed H. -/
noncomputable def distantPrimePairKernel (n H : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    if (p+H<r ∨ r+H<p) ∧ H<(farPairFrequency n p r).natAbs then primePairMode n p r t else 0

theorem farOffTargetKernel_frequency_partition (n H : ℕ) (t : ℝ) :
    farOffTargetKernel n H t = farShortOffTargetKernel n H t + distantPrimePairKernel n H t := by
  rw [farOffTargetKernel_ordered]
  unfold farShortOffTargetKernel farPairKernelAtModes distantPrimePairKernel
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  simp only [mem_shortNonzeroPairModes]
  by_cases hg : p+H<r ∨ r+H<p
  · have hz : farPairFrequency n p r=0 ↔ p+r=n := by unfold farPairFrequency; omega
    by_cases h0 : p+r=n
    · simp [hg,h0,hz.mpr h0]
    · have hneq : farPairFrequency n p r≠0 := fun he => h0 (hz.mp he)
      by_cases h : (farPairFrequency n p r).natAbs≤H
      · simp [hg,h0,hneq,h,not_lt.mpr h]
      · simp [hg,h0,hneq,h,lt_of_not_ge h]
  · simp [hg]

open Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology


def distantPairModes (n H : ℕ) : Finset ℤ :=
  (Icc (-(n:ℤ)) (n:ℤ)).filter (fun m => H<m.natAbs)

theorem distantPrimePairKernel_at_modes (n H : ℕ) (t : ℝ) :
    distantPrimePairKernel n H t = farPairKernelAtModes n H (distantPairModes n H) t := by
  unfold distantPrimePairKernel farPairKernelAtModes
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro r hr
  have hP := mem_range.mp hp
  have hR := mem_range.mp hr
  have hmem : farPairFrequency n p r ∈ Icc (-(n:ℤ)) (n:ℤ) := by
    apply mem_Icc.mpr
    unfold farPairFrequency
    omega
  simp only [distantPairModes,mem_filter,hmem,true_and]

theorem distantPrimePairKernel_integral_frequencies (n H : ℕ) {V : Set ℝ} (hV : V⊆Set.Icc 0 1) :
    (∫ t in V, distantPrimePairKernel n H t).re =
      ∑ m ∈ distantPairModes n H, farPairModeWeight n H m*(∫ t in V,E ((m:ℝ)*t)).re := by
  simp_rw [distantPrimePairKernel_at_modes]
  rw [farPairKernelAtModes_integral n H (distantPairModes n H) hV]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

private theorem distantPrimePairKernel_continuous (n H : ℕ) : Continuous (distantPrimePairKernel n H) := by
  unfold distantPrimePairKernel
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro r _
  split_ifs <;> first | exact continuous_const | dsimp [primePairMode,E]; fun_prop

private theorem shortFarKernel_continuous (n H : ℕ) : Continuous (farShortOffTargetKernel n H) := by
  unfold farShortOffTargetKernel farPairKernelAtModes
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro r _
  split_ifs <;> first | exact continuous_const | dsimp [primePairMode,E]; fun_prop



theorem primeSquareKernel_double_partition {n H : ℕ} (hH : H≤n) (t : ℝ) :
    primeSquareKernel n t = closePrimeGapKernel n H t + farShortOffTargetKernel n H t +
      distantPrimePairKernel n H t + (farOnTargetWeight n H:ℂ) := by
  rw [primeSquareKernel_gap_partition hH,farOffTargetKernel_frequency_partition]
  abel

/-- The two discarded, disjoint classes of ordered pairs have jointly sublinear signed mass. -/
theorem high_tubes_two_error_power :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n, closePrimeGapKernel n (closePrimeGapCutoff n) t) +
        (∫ t in highNaturalPrimeTubes n, farShortOffTargetKernel n (closePrimeGapCutoff n) t)‖ ≤
        (184/3:ℝ)*(n:ℝ)^(7/8:ℝ) := by
  filter_upwards [closePrimeGapKernel_eventually_pow_bound,
    farShortOffTargetKernel_eventually_pow_bound] with n h₁ h₂
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

private theorem distant_arc_mass_split (n : ℕ) (hi : highNaturalPrimeTubes n ⊆ Set.Icc 0 1) :
    (∫ t in highNaturalPrimeTubes n, farOffTargetKernel n (closePrimeGapCutoff n) t).re =
    (∫ t in highNaturalPrimeTubes n, farShortOffTargetKernel n (closePrimeGapCutoff n) t).re +
    (∫ t in highNaturalPrimeTubes n, distantPrimePairKernel n (closePrimeGapCutoff n) t).re := by
  have hs : IntegrableOn (farShortOffTargetKernel n (closePrimeGapCutoff n)) (highNaturalPrimeTubes n) := (shortFarKernel_continuous n (closePrimeGapCutoff n)).continuousOn.integrableOn_Icc.mono_set hi
  have hd : IntegrableOn (distantPrimePairKernel n (closePrimeGapCutoff n)) (highNaturalPrimeTubes n) := (distantPrimePairKernel_continuous n (closePrimeGapCutoff n)).continuousOn.integrableOn_Icc.mono_set hi
  simp_rw [farOffTargetKernel_frequency_partition]
  rw [integral_add hs hd,Complex.add_re]

/-- The pointwise remaining inequality only uses pairs with |p-r|>floor(n^(1/4))
and |p+r-n|>floor(n^(1/4)) inside the high-denominator region. -/
theorem dyadic_floor_from_distant_pairs
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤
      primeArcMass (remainingPrimeArcs n \ highNaturalPrimeTubes n) n +
      (∫ t in highNaturalPrimeTubes n, distantPrimePairKernel n (closePrimeGapCutoff n) t).re) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ) ≤ Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hfar : ∃ N : ℕ, ∀ n ≥ N, Even n → -((1/299:ℝ)*(n:ℝ)) ≤
      primeArcMass (remainingPrimeArcs n \ highNaturalPrimeTubes n) n +
      (∫ t in highNaturalPrimeTubes n, farOffTargetKernel n (closePrimeGapCutoff n) t).re := by
    obtain ⟨N,hN⟩ := rest
    apply eventually_atTop.mp
    filter_upwards [eventually_ge_atTop N,highNaturalPrimeTubes_geometry,farShortOffTargetKernel_eventually_small (ε:=1/89700) (by norm_num)] with n hn hg hs
    intro he
    have heps := (abs_le.mp (Complex.abs_re_le_norm
      (∫ t in highNaturalPrimeTubes n, farShortOffTargetKernel n (closePrimeGapCutoff n) t))).1
    rw [distant_arc_mass_split n hg.1]
    change ‖∫ t in highNaturalPrimeTubes n, farShortOffTargetKernel n (closePrimeGapCutoff n) t‖ ≤
      (1/89700)*(n:ℝ) at hs
    linarith only [hN n hn he,hs,heps]
  obtain ⟨N,h⟩ := dyadic_floor_of_far_remainder_budget hm h₁ h₂ h₃ major hψ (1/299) (by norm_num) hfar
  refine ⟨1/576,N,by norm_num,fun X n hx hn hu he => ?_⟩
  change (1/576)*(n:ℝ) ≤ corr n
  linarith only [h X n hx hn hu he]

end GoldbachPartial
