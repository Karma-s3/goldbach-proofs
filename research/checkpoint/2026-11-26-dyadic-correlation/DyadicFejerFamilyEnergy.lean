import GcdDilationFamily
import DyadicFejerSpectrum

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

theorem dyadicFejerEnvelope_pair_integral_le (Q d e:ℕ) (hd:0<d) (he:0<e) :
    (∫ t in (0:ℝ)..1, dyadicFejerEnvelope Q ((d:ℝ)*t)*dyadicFejerEnvelope Q ((e:ℝ)*t)) ≤
      ((Nat.log 2 Q+1:ℕ):ℝ)^2*(1+2*(Q:ℝ)*(d.gcd e:ℝ)/e) := by
  let a := dyadicFejerFourierCoefficient Q
  let P := fejerGramPolynomial Q a
  let F (t:ℝ) := dyadicFejerEnvelope Q ((d:ℝ)*t)*dyadicFejerEnvelope Q ((e:ℝ)*t)
  have hc (t:ℝ) : (F t:ℂ) = P ((d:ℝ)*t)*P ((e:ℝ)*t) := by
    dsimp only [F]
    rw [Complex.ofReal_mul,dyadicFejerEnvelope_fourier,dyadicFejerEnvelope_fourier]
  have hcast : ((∫ t in (0:ℝ)..1, F t : ℝ):ℂ) = ∫ t in (0:ℝ)..1, P ((d:ℝ)*t)*P ((e:ℝ)*t) := by
    rw [←intervalIntegral.integral_ofReal]
    simp_rw [hc]
  have h := fejerGramPolynomial_pair_bound Q d e hd he a a
    (fun h _ => dyadicFejerFourierCoefficient_bound Q h) (fun h _ => dyadicFejerFourierCoefficient_bound Q h)
  change ‖∫ t in (0:ℝ)..1,P ((d:ℝ)*t)*P ((e:ℝ)*t)‖ ≤ _ at h
  rw [←hcast,Complex.norm_real,Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans_eq (by rw [sq]))

theorem dyadicFejerEnvelope_pair_integral_max (Q d e:ℕ) (hd:0<d) (he:0<e) :
    (∫ t in (0:ℝ)..1, dyadicFejerEnvelope Q ((d:ℝ)*t)*dyadicFejerEnvelope Q ((e:ℝ)*t)) ≤
      ((Nat.log 2 Q+1:ℕ):ℝ)^2*(1+2*(Q:ℝ)*(d.gcd e:ℝ)/(max d e:ℕ)) := by
  rcases le_total d e with h|h
  · rw [max_eq_right h]
    exact dyadicFejerEnvelope_pair_integral_le Q d e hd he
  · rw [max_eq_left h,Nat.gcd_comm d e]
    simpa only [mul_comm (dyadicFejerEnvelope Q ((d:ℝ)*_))] using
      dyadicFejerEnvelope_pair_integral_le Q e d he hd

theorem dyadicFejerEnvelope_family_energy (Q D : ℕ) :
    (∫ t in (0:ℝ)..1, (∑ j ∈ range D, dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t))^2) ≤
      ((Nat.log 2 Q+1:ℕ):ℝ)^2*((D:ℝ)^2+4*(Q:ℝ)*D*(1+Real.log D)) := by
  let W (j:ℕ) (t:ℝ) := dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t)
  let K : ℝ := ((Nat.log 2 Q+1:ℕ):ℝ)^2
  let T (d e:ℕ):ℝ := ((d+1).gcd (e+1):ℝ)/((max (d+1) (e+1):ℕ):ℝ)
  have hW (j:ℕ) : Continuous (W j) := by
    unfold W dyadicFejerEnvelope fejerWave dirichletGeometricKernel E
    fun_prop
  have hpoint (t:ℝ) : (∑ j ∈ range D, W j t)^2 = ∑ d ∈ range D, ∑ e ∈ range D, W d t*W e t := by
    rw [sq,sum_mul]; simp_rw [mul_sum]
  change (∫ t in (0:ℝ)..1, (∑ j ∈ range D, W j t)^2) ≤ _
  simp_rw [hpoint]
  have hrow (d:ℕ) : (∫ t in (0:ℝ)..1, ∑ e ∈ range D,W d t*W e t) =
      ∑ e ∈ range D,∫ t in (0:ℝ)..1,W d t*W e t :=
    intervalIntegral.integral_finsetSum (fun e _ => ((hW d).mul (hW e)).intervalIntegrable _ _)
  have hint (d:ℕ) : IntervalIntegrable (fun t => ∑ e ∈ range D, W d t*W e t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro e _
    exact (hW d).mul (hW e)
  rw [intervalIntegral.integral_finsetSum (fun d _ => hint d)]
  simp_rw [hrow]
  calc
    _ ≤ ∑ d ∈ range D, ∑ e ∈ range D, K*(1+(2*(Q:ℝ))*T d e) := by
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro e _
      exact (dyadicFejerEnvelope_pair_integral_max Q (d+1) (e+1) (Nat.succ_pos d) (Nat.succ_pos e)).trans_eq
        (by dsimp only [K,T]; ring)
    _ = K*((D:ℝ)^2 + 2*(Q:ℝ)*(∑ d ∈ range D, ∑ e ∈ range D, T d e)) := by
      simp_rw [←mul_sum,sum_add_distrib]
      simp_rw [←mul_sum]
      simp [nsmul_eq_mul,sq]
    _ ≤ _ := by
      have hg := gcd_max_family_bound D
      rw [sum_comm] at hg
      change (∑ d ∈ range D, ∑ e ∈ range D,T d e) ≤ _ at hg
      exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg (by positivity)))
        (by positivity : 0≤K)).trans_eq (by dsimp only [K]; ring)

end GoldbachPartial