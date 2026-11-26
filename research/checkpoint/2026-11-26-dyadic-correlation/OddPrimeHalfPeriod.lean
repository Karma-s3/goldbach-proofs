import DyadicCorrelationReduction

namespace GoldbachPartial

open MeasureTheory Finset ExtendedArcCoefficient

noncomputable def oddPrimeWeight (p : ℕ) : ℝ := if p=2 then 0 else weight p

noncomputable def oddPrimeWave (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (oddPrimeWeight k:ℂ)*E ((k:ℝ)*t)

noncomputable def oddPrimeSquareKernel (n : ℕ) (t : ℝ) : ℂ :=
  (oddPrimeWave n t)^2*E (-(n:ℝ)*t)

theorem corr_eq_oddPrime_convolution {n : ℕ} (hn : 4<n) (he : Even n) :
    corr n = ∑ k ∈ range (n+1), oddPrimeWeight k*oddPrimeWeight (n-k) := by
  obtain ⟨u,hu⟩ := he
  apply sum_congr rfl
  intro k _
  by_cases hk : k=2
  · subst k
    have hnp : ¬(n-2).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with ht | ho <;> omega
    simp [oddPrimeWeight,weight,hnp]
  · by_cases hnk : n-k=2
    · have hnp : ¬k.Prime := by
        intro hp
        rcases hp.eq_two_or_odd with ht | ho <;> omega
      simp [oddPrimeWeight,weight,hk,hnk,hnp]
    · simp [oddPrimeWeight,hk,hnk]

theorem oddPrimeSquareKernel_full_coefficient {n : ℕ} (hn : 4<n) (he : Even n) :
    (∫ t in (0:ℝ)..1, oddPrimeSquareKernel n t) = (corr n:ℂ) := by
  rw [corr_eq_oddPrime_convolution hn he]
  exact coefficient oddPrimeWeight n

private theorem phase_nat_half (k : ℕ) : E ((k:ℝ)/2) = (-1:ℂ)^k := by
  unfold E
  have h : ((2*Real.pi*((k:ℝ)/2):ℝ):ℂ)*Complex.I = (k:ℂ)*(Real.pi*Complex.I) := by
    push_cast
    ring
  rw [h,Complex.exp_nat_mul,Complex.exp_pi_mul_I]

theorem oddPrimeWave_add_half (n : ℕ) (t : ℝ) :
    oddPrimeWave n (t+1/2) = -oddPrimeWave n t := by
  unfold oddPrimeWave
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro k _
  rw [show (k:ℝ)*(t+1/2)=k*t+(k:ℝ)/2 by ring,phase_add,phase_nat_half]
  by_cases hp : k.Prime
  · by_cases hk : k=2
    · simp [oddPrimeWeight,hk]
    · rw [(hp.odd_of_ne_two hk).neg_one_pow]
      ring
  · simp [oddPrimeWeight,weight,hp]

theorem oddPrimeSquareKernel_half_periodic {n : ℕ} (he : Even n) :
    Function.Periodic (oddPrimeSquareKernel n) (1/2) := by
  intro t
  have hphase : E (-(n:ℝ)/2) = 1 := by
    obtain ⟨m,hm⟩ := he
    have he' : -(n:ℝ)/2 = ((-(m:ℤ):ℤ):ℝ) := by rw [hm]; push_cast; ring
    rw [he']
    unfold E
    convert Complex.exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 2; push_cast; ring
  unfold oddPrimeSquareKernel
  rw [oddPrimeWave_add_half,show -(n:ℝ)*(t+1/2)=-(n:ℝ)*t+(-(n:ℝ)/2) by ring,
    phase_add,hphase]
  ring

private theorem integral_eq_twice_half_of_periodic {f : ℝ → ℂ} (hp : Function.Periodic f (1/2))
    (hi : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ t in (0:ℝ)..1, f t) = 2*(∫ t in (0:ℝ)..(1/2), f t) := by
  have hh := hp.intervalIntegral_add_zsmul_eq (2:ℤ) (0:ℝ) hi
  norm_num [zsmul_eq_mul] at hh
  exact hh

theorem corr_eq_twice_oddPrime_half_integral {n : ℕ} (hn : 4<n) (he : Even n) :
    corr n = (2*(∫ t in (0:ℝ)..(1/2), oddPrimeSquareKernel n t)).re := by
  have hc : Continuous (oddPrimeSquareKernel n) := by unfold oddPrimeSquareKernel oddPrimeWave E; fun_prop
  have hh := integral_eq_twice_half_of_periodic (oddPrimeSquareKernel_half_periodic he)
    (fun a b => hc.intervalIntegrable a b)
  rw [← hh,oddPrimeSquareKernel_full_coefficient hn he,Complex.ofReal_re]

theorem oddPrimeSquareKernel_half_integral_on_set {n : ℕ} (he : Even n) {s : Set ℝ}
    (hs : MeasurableSet s) (hperiod : ∀ t, t+1/2 ∈ s ↔ t∈s) :
    (∫ t in (0:ℝ)..1, s.indicator (oddPrimeSquareKernel n) t) =
      2*(∫ t in (0:ℝ)..(1/2), s.indicator (oddPrimeSquareKernel n) t) := by
  apply integral_eq_twice_half_of_periodic
  · intro t
    by_cases ht : t∈s
    · rw [Set.indicator_of_mem ((hperiod t).mpr ht),Set.indicator_of_mem ht]
      exact oddPrimeSquareKernel_half_periodic he t
    · rw [Set.indicator_of_notMem (mt (hperiod t).mp ht),Set.indicator_of_notMem ht]
  · intro a b
    have hc : Continuous (oddPrimeSquareKernel n) := by unfold oddPrimeSquareKernel oddPrimeWave E; fun_prop
    have hi := hc.intervalIntegrable (μ:=volume) a b
    exact ⟨hi.1.indicator hs,hi.2.indicator hs⟩

end GoldbachPartial