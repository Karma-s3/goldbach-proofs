import TruePrimeCenteringYoung
import Mathlib.NumberTheory.Chebyshev

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient

theorem centralPrimeWave_local_energy_chebyshev (n:ℕ) {U : Set ℝ} (hUsub : U ⊆ Set.Icc 0 1) :
    (∫ t in U, ‖centralPrimeWave n t‖^2) ≤ Real.log 4*(n:ℝ)*Real.log n := by
  let F (t:ℝ) := ‖centralPrimeWave n t‖^2
  have hc : Continuous F := by unfold F centralPrimeWave E; fun_prop
  have hU : (∫ t in U, F t) ≤ ∫ t in Set.Icc (0:ℝ) 1,F t :=
    setIntegral_mono_set hc.integrableOn_Icc (Filter.Eventually.of_forall fun _ => sq_nonneg _) hUsub.eventuallySubset
  have hn (k:ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hper : Function.Periodic (centralPrimeWave n) 1 := by
    intro t
    unfold centralPrimeWave
    simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
  have hfper : Function.Periodic F 1 := fun t => congrArg (fun z:ℂ => ‖z‖^2) (hper t)
  have hshift := hfper.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at hshift
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),←hshift] at hU
  have he := finiteAbelWave_unit_energy (range (n+1)) (fun k => (weight k:ℂ))
  change (∫ t in (-(1/2):ℝ)..(1/2),F t)=_ at he
  rw [he] at hU
  have htheta : (∑ k ∈ range (n+1), weight k) = Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
    rfl
  apply hU.trans
  calc _ ≤ ∑ k ∈ range (n+1), weight k*Real.log n := by
         apply sum_le_sum
         intro k hk
         have hkn : k≤n := Nat.le_of_lt_succ (mem_range.mp hk)
         by_cases hp : k.Prime
         · have h0 := Real.log_natCast_nonneg k
           have hlog : Real.log k ≤ Real.log n :=
             Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
           simp only [weight,ite_eq_left hp,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0,pow_two]
           exact mul_le_mul_of_nonneg_left hlog h0
         · simp [weight,hp]
       _ = Chebyshev.theta n * Real.log n := by rw [←sum_mul,htheta]
       _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n))
         (Real.log_natCast_nonneg n)

theorem truePrime_centering_young_chebyshev (n:ℕ) {U:Set ℝ} (hUsub : U ⊆ Set.Icc 0 1)
    (B : ℝ→ℂ) (hB : Continuous B) {s:ℝ} (hs:0<s) :
    ‖(∫ t in U,primeSquareKernel n t)-(∫ t in U,centeredTruePrimeKernel n B t)‖ ≤
      s*(Real.log 4*(n:ℝ)*Real.log n) + (1+s⁻¹)*(∫ t in U, ‖B t‖^2) := by
  let A := centralPrimeWave n
  have hA : Continuous A := by unfold A centralPrimeWave E; fun_prop
  have hF : Continuous (primeSquareKernel n) := by unfold primeSquareKernel E; fun_prop
  have hD : Continuous (centeredTruePrimeKernel n B) := by
    unfold centeredTruePrimeKernel centralPrimeWave E
    fun_prop
  have hint {f:ℝ→ℝ} (h:Continuous f) : IntegrableOn f U := h.integrableOn_Icc.mono_set hUsub
  have hiF : IntegrableOn (primeSquareKernel n) U := hF.integrableOn_Icc.mono_set hUsub
  have hiD : IntegrableOn (centeredTruePrimeKernel n B) U := hD.integrableOn_Icc.mono_set hUsub
  have hp (t:ℝ) : ‖primeSquareKernel n t-centeredTruePrimeKernel n B t‖ ≤ s*‖A t‖^2+(1+s⁻¹)*‖B t‖^2 := by
    have hphase : ‖E (-(n:ℝ)*t)‖=1 := Complex.norm_exp_ofReal_mul_I _
    change ‖(A t)^2*E (-(n:ℝ)*t)-(A t-B t)^2*E (-(n:ℝ)*t)‖ ≤ _
    rw [←sub_mul,norm_mul,hphase,mul_one,show (A t)^2-(A t-B t)^2=2*A t*B t-(B t)^2 by ring]
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul,norm_pow]
    norm_num
    apply (mul_le_mul_iff_right₀ hs).mp
    field_simp
    nlinarith only [sq_nonneg (s*‖A t‖-‖B t‖)]
  have hiA := hint (hA.norm.pow 2)
  have hiB := hint (hB.norm.pow 2)
  change ‖(∫ t in U,primeSquareKernel n t)-(∫ t in U,centeredTruePrimeKernel n B t)‖ ≤ _
  rw [← integral_sub hiF hiD]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t in U, s*‖A t‖^2+(1+s⁻¹)*‖B t‖^2 := integral_mono (hiF.sub hiD).norm
      ((hiA.const_mul _).add (hiB.const_mul _)) hp
    _ ≤ _ := by
      rw [integral_add (f:=fun t => s*‖A t‖^2) (g:=fun t => (1+s⁻¹)*‖B t‖^2) (hiA.const_mul _) (hiB.const_mul _),integral_const_mul,integral_const_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (centralPrimeWave_local_energy_chebyshev n hUsub) hs.le) le_rfl


end GoldbachPartial
