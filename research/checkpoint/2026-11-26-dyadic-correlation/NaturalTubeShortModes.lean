import NaturalPrimeTubeVolume
import ShortNonzeroModes

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

noncomputable def naturalTubeFourierMode (R Q M : ℕ) (h : ℤ) : ℂ :=
  ∫ t in naturalTubeUnion R Q M, E ((h:ℝ)*t)

theorem naturalTubeFourierMode_eq (R Q M : ℕ) (hsep : 2*Q<M) (h:ℤ) :
    naturalTubeFourierMode R Q M h =
      ∑ j ∈ Ico R Q, (dyadicRamanujanDivisor h.natAbs (j+1):ℂ)*
        ∫ t in -(naturalTubeRadius M (j+1))..(naturalTubeRadius M (j+1)), E ((h:ℝ)*t) := by
  unfold naturalTubeFourierMode
  rw [naturalTubeUnion_integral_rows R Q M hsep _ (by unfold E; fun_prop)]
  exact sum_congr rfl fun j _ => signedModeRow_exact (j+1) h _

theorem naturalTubeFourierMode_ramanujan_bound (R Q M : ℕ) (hsep : 2*Q<M) (h : ℤ) :
    ‖naturalTubeFourierMode R Q M h‖ ≤ (2/(M:ℝ))*∑ j ∈ Ico R Q,
      |(dyadicRamanujanDivisor h.natAbs (j+1):ℝ)|/((j+1:ℕ):ℝ) := by
  rw [naturalTubeFourierMode_eq R Q M hsep]
  apply (norm_sum_le ..).trans
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  let r := naturalTubeRadius M (j+1)
  have hr : 0≤r := by dsimp [r,naturalTubeRadius]; positivity
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f:=fun t:ℝ => E ((h:ℝ)*t)) (C:=1) (fun _ _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [abs_of_nonneg (by linarith : 0≤r- -r),one_mul] at hi
  rw [norm_mul,Complex.norm_intCast]
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg _)).trans_eq (by dsimp only [r,naturalTubeRadius]; ring)

theorem naturalTubeFourierMode_short_l1 (R Q M H : ℕ) (hsep : 2*Q<M) (f : ℕ→ℤ)
    (hf : ∀ k∈range H, (f k).natAbs=k+1) :
    ∑ k ∈ range H, ‖naturalTubeFourierMode R Q M (f k)‖ ≤
      (2/(M:ℝ))*(H:ℝ)*(1+Real.log Q)^2 := by
  let J := Ico R Q
  let C (k j:ℕ) := |(dyadicRamanujanDivisor (k+1) (j+1):ℝ)|/((j+1:ℕ):ℝ)
  have hsum : ∑ j ∈ J, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ) ≤ (1+Real.log Q)^2 :=
    (sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
        (fun _ _ _ => by positivity)).trans (signedFiber_divisor_harmonic Q)
  have hcol (j:ℕ) : ∑ k ∈ range H, C k j ≤ (H:ℝ)*(((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) := by
    dsimp only [C]
    rw [←sum_div,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (ramanujan_frequency_mass (j+1) H (Nat.succ_pos j)) (by positivity)
  calc
    _ ≤ ∑ k ∈ range H, (2/(M:ℝ))*∑ j ∈ J, C k j := by
      apply sum_le_sum
      intro k hk
      simpa only [hf k hk,C,J] using naturalTubeFourierMode_ramanujan_bound R Q M hsep (f k)
    _ = (2/(M:ℝ))*∑ j ∈ J, ∑ k ∈ range H, C k j := by rw [←mul_sum,Finset.sum_comm]
    _ ≤ (2/(M:ℝ))*∑ j ∈ J, (H:ℝ)*(((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hcol j) (by positivity)
    _ ≤ _ := by rw [←mul_sum,mul_assoc]; gcongr

theorem naturalTubeFourierMode_short_weighted (R Q M H : ℕ) (hsep : 2*Q<M)
    (f : ℕ→ℤ) (hf : ∀ k∈range H, (f k).natAbs=k+1) (c : ℕ→ℂ) {A : ℝ}
    (hA : 0≤A) (hc : ∀ k∈range H, ‖c k‖≤A) :
    ‖∑ k ∈ range H, c k*naturalTubeFourierMode R Q M (f k)‖ ≤
      A*((2/(M:ℝ))*(H:ℝ)*(1+Real.log Q)^2) := by
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ k ∈ range H, A*‖naturalTubeFourierMode R Q M (f k)‖ := by
      apply sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc k hk) (norm_nonneg _)
    _ ≤ _ := by
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (naturalTubeFourierMode_short_l1 R Q M H hsep f hf) hA

theorem naturalTubeFourier_shortNonzeroModes_l1 (R Q M H : ℕ) (hsep : 2*Q<M) :
    ∑ h ∈ shortNonzeroModes H, ‖naturalTubeFourierMode R Q M h‖ ≤
      (4/(M:ℝ))*(H:ℝ)*(1+Real.log Q)^2 := by
  have hp := naturalTubeFourierMode_short_l1 R Q M H hsep (fun k => ((k+1:ℕ):ℤ))
    (fun _ _ => rfl)
  have hm := naturalTubeFourierMode_short_l1 R Q M H hsep (fun k => -((k+1:ℕ):ℤ))
    (fun k _ => by rw [Int.natAbs_neg]; rfl)
  rw [sum_shortNonzeroModes,sum_add_distrib]
  exact (add_le_add hp hm).trans_eq (by ring)

theorem naturalTubeFourier_short_polynomial_bound (R Q M H : ℕ) (hR : 0<R) (hsep : 2*Q<M)
    (c : ℤ→ℂ) {A : ℝ} (hA : 0≤A) (hc : ∀ h∈shortNonzeroModes H, ‖c h‖≤A) :
    ‖∫ t in naturalTubeUnion R Q M, ∑ h ∈ shortNonzeroModes H, c h*E ((h:ℝ)*t)‖ ≤
      A*((4/(M:ℝ))*(H:ℝ)*(1+Real.log Q)^2) := by
  have hU := naturalTubeUnion_inside_unit (B:=R) (R:=Q) hR (by omega : 0<M)
  have hi (h:ℤ) : IntegrableOn (fun t:ℝ => c h * E ((h:ℝ)*t)) (naturalTubeUnion R Q M) := by
    have hh : Continuous (fun t:ℝ => c h*E ((h:ℝ)*t)) := by unfold E; fun_prop
    exact hh.integrableOn_Icc.mono_set hU
  rw [integral_finsetSum _ (fun h _ => hi h)]
  simp_rw [integral_const_mul]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ h ∈ shortNonzeroModes H, A*‖naturalTubeFourierMode R Q M h‖ := by
      apply sum_le_sum
      intro h hh
      exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_right (hc h hh) (norm_nonneg _))
    _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (naturalTubeFourier_shortNonzeroModes_l1 R Q M H hsep) hA

end GoldbachPartial