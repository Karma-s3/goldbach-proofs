import SignedRamanujanReciprocal
import ResonantMobiusHighMass
import GcdDilationFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

theorem signedMode_interval_error (h:ℤ) (r:ℝ) (hr:0≤r) :
    ‖(∫t in -r..r,E ((h:ℝ)*t))-((2*r:ℝ):ℂ)‖≤4*Real.pi*(h.natAbs:ℝ)*r^2 := by
  have hI : (∫_t in -r..r,(1:ℂ))=((2*r:ℝ):ℂ) := by
    rw [intervalIntegral.integral_const];simp only [Complex.real_smul,mul_one];congr 1;ring
  rw [←hI,←intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable;unfold E;fun_prop)
    (continuous_const.intervalIntegrable _ _)]
  have hpoint (t:ℝ) (ht:t∈Set.uIoc (-r) r) :
      ‖E ((h:ℝ)*t)-1‖≤2*Real.pi*(h.natAbs:ℝ)*r := by
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hat : |t|≤r := abs_le.mpr ⟨ht.1.le,ht.2⟩
    unfold E
    rw [mul_comm _ Complex.I]
    apply (Real.norm_exp_I_mul_ofReal_sub_one_le).trans
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi),abs_mul,
      ←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg _)) (by positivity)).trans_eq (by ring)
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans_eq
  rw [abs_of_nonneg (by linarith : 0≤r- -r)];ring

theorem signedTube_mode_bound (R Q M:ℕ) (hsep:2*Q<M) (h:ℤ) (hne:h≠0)
    (hcap:(h.natAbs:ℝ)*(1+Real.log Q)≤M) :
    ‖naturalTubeFourierMode R Q M h‖ ≤ ((8+4*Real.pi)/(M:ℝ))*(h.natAbs.divisors.card:ℝ) := by
  let J := Ico R Q
  let c (j:ℕ) : ℝ := dyadicRamanujanDivisor h.natAbs (j+1)
  let r (j:ℕ) := naturalTubeRadius M (j+1)
  let I (j:ℕ) := ∫t in -(r j)..r j,E ((h:ℝ)*t)
  let D : ℝ := h.natAbs.divisors.card
  let S : ℝ := ∑j∈J,c j/((j+1:ℕ):ℝ)
  let F : ℝ := 4*Real.pi*(h.natAbs:ℝ)/(M:ℝ)^2
  have hM : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hD : 0≤D := Nat.cast_nonneg _
  have hF : 0≤F := by dsimp [F];positivity
  have hS : |S|≤4*D := signedRamanujan_reciprocal_band _ _ _ (Int.natAbs_pos.mpr hne)
  have hx : naturalTubeFourierMode R Q M h =
      (∑j∈J,(c j:ℂ)*(I j-((2*r j:ℝ):ℂ))) + (((2/(M:ℝ))*S:ℝ):ℂ) := by
    rw [naturalTubeFourierMode_eq R Q M hsep]
    dsimp only [S]
    rw [mul_sum,Complex.ofReal_sum,←sum_add_distrib]
    apply sum_congr rfl;intro j _
    change (c j:ℂ)*I j=(c j:ℂ)*(I j-((2*r j:ℝ):ℂ))+(((2/(M:ℝ))*(c j/((j+1:ℕ):ℝ)):ℝ):ℂ)
    have he : (2/(M:ℝ))*(c j/((j+1:ℕ):ℝ))=c j*(2*r j) := by
      dsimp only [r,naturalTubeRadius];simp only [div_eq_mul_inv,mul_inv_rev];ring
    rw [he];simp only [Complex.ofReal_mul];ring
  have herror : ‖∑j∈J,(c j:ℂ)*(I j-((2*r j:ℝ):ℂ))‖ ≤(4*Real.pi/(M:ℝ))*D := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑j∈J,F*(|c j|/((j+1:ℕ):ℝ)) := by
           apply sum_le_sum;intro j _
           have hj : (1:ℝ)≤((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos j
           have hr : 0≤r j := by dsimp [r,naturalTubeRadius];positivity
           have hr' : r j≤1/(M:ℝ) := by
             apply one_div_le_one_div_of_le hM
             change (M:ℝ)≤((j+1:ℕ):ℝ)*M
             exact le_mul_of_one_le_left hM.le hj
           rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
           apply (mul_le_mul_of_nonneg_left (signedMode_interval_error h _ hr) (abs_nonneg _)).trans
           calc _ ≤ |c j| *(4*Real.pi*(h.natAbs:ℝ)*(r j*(1/(M:ℝ)))) := by rw [sq];gcongr
                _ = _ := by dsimp only [F,r,naturalTubeRadius];simp only [div_eq_mul_inv,mul_inv_rev];ring
         _ ≤ F*((1+Real.log Q)*D) := by
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left (resonantRamanujan_harmonic _ _ _ (Int.natAbs_pos.mpr hne)) hF
         _ ≤ _ := by
           calc F*((1+Real.log Q)*D) = (4*Real.pi/(M:ℝ)^2)*
                  ((h.natAbs:ℝ)*(1+Real.log Q))*D := by dsimp only [F];ring
                _ ≤ (4*Real.pi/(M:ℝ)^2)*(M:ℝ)*D := by gcongr
                _ = _ := by field_simp
  rw [hx]
  apply (norm_add_le ..).trans
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤2/(M:ℝ))]
  exact (add_le_add herror (mul_le_mul_of_nonneg_left hS (by positivity))).trans_eq (by ring)

theorem signedTube_shortFourier_l1 (R Q M H:ℕ) (hsep:2*Q<M)
    (hcap:(H:ℝ)*(1+Real.log Q)≤M) :
    (∑h∈shortNonzeroModes H,‖naturalTubeFourierMode R Q M h‖) ≤
      ((16+8*Real.pi)/(M:ℝ))*(H:ℝ)*(1+Real.log H) := by
  have hj (h:ℤ) (hh:h∈shortNonzeroModes H) : (h.natAbs:ℝ)≤H := by
    have hb := mem_Icc.mp (mem_erase.mp hh).2
    exact_mod_cast (show h.natAbs≤H by omega)
  calc _ ≤ ∑h∈shortNonzeroModes H,((8+4*Real.pi)/(M:ℝ))*(h.natAbs.divisors.card:ℝ) := by
         apply sum_le_sum;intro h hh
         exact signedTube_mode_bound R Q M hsep h (mem_erase.mp hh).1
           ((mul_le_mul_of_nonneg_right (hj h hh) (by positivity)).trans hcap)
       _ = ((8+4*Real.pi)/(M:ℝ))* (2*∑i∈range H,((i+1).divisors.card:ℝ)) := by
         rw [←mul_sum,sum_shortNonzeroModes]
         simp only [Int.natAbs_neg,Int.natAbs_natCast,←two_mul,mul_sum]
       _ ≤ _ := by
         apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (divisorCard_sum_le_log H)
           (by norm_num : (0:ℝ)≤2)) (by positivity)).trans_eq
         ring
end GoldbachPartial
