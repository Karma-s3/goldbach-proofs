import DyadicFejerFamilyEnergy

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

theorem singleFejerFamily_pair_integral_le (Q d e:ℕ) (hQ:0<Q) (hd:0<d) (he:0<e) :
    (∫ t in (0:ℝ)..1, fejerWave Q ((d:ℝ)*t)*fejerWave Q ((e:ℝ)*t)) ≤
      (1:ℝ)*(1+2*(Q:ℝ)*(d.gcd e:ℝ)/e) := by
  let a := fejerTriangleCoefficient Q
  let P := fejerGramPolynomial Q a
  let F (t:ℝ) := fejerWave Q ((d:ℝ)*t)*fejerWave Q ((e:ℝ)*t)
  have hc (t:ℝ) : (F t:ℂ) = P ((d:ℝ)*t)*P ((e:ℝ)*t) := by
    dsimp only [F]
    rw [Complex.ofReal_mul,fejerWave_fourier Q Q hQ (Nat.le_succ Q),fejerWave_fourier Q Q hQ (Nat.le_succ Q)]
  have hcast : ((∫ t in (0:ℝ)..1, F t : ℝ):ℂ) = ∫ t in (0:ℝ)..1, P ((d:ℝ)*t)*P ((e:ℝ)*t) := by
    rw [←intervalIntegral.integral_ofReal]
    simp_rw [hc]
  have h := fejerGramPolynomial_pair_bound Q d e hd he a a
    (fun h _ => fejerTriangleCoefficient_norm_le Q h) (fun h _ => fejerTriangleCoefficient_norm_le Q h)
  change ‖∫ t in (0:ℝ)..1,P ((d:ℝ)*t)*P ((e:ℝ)*t)‖ ≤ _ at h
  rw [←hcast,Complex.norm_real,Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans_eq (by ring))

theorem singleFejerFamily_pair_integral_max (Q d e:ℕ) (hQ:0<Q) (hd:0<d) (he:0<e) :
    (∫ t in (0:ℝ)..1, fejerWave Q ((d:ℝ)*t)*fejerWave Q ((e:ℝ)*t)) ≤
      (1:ℝ)*(1+2*(Q:ℝ)*(d.gcd e:ℝ)/(max d e:ℕ)) := by
  rcases le_total d e with h|h
  · rw [max_eq_right h]
    exact singleFejerFamily_pair_integral_le Q d e hQ hd he
  · rw [max_eq_left h,Nat.gcd_comm d e]
    simpa only [mul_comm (fejerWave Q ((d:ℝ)*_))] using
      singleFejerFamily_pair_integral_le Q e d hQ he hd

theorem singleFejerFamily_energy (Q D : ℕ) (hQ:0<Q) :
    (∫ t in (0:ℝ)..1, (∑ j ∈ range D, fejerWave Q (((j+1:ℕ):ℝ)*t))^2) ≤
      (1:ℝ)*((D:ℝ)^2+4*(Q:ℝ)*D*(1+Real.log D)) := by
  let W (j:ℕ) (t:ℝ) := fejerWave Q (((j+1:ℕ):ℝ)*t)
  let K : ℝ := (1:ℝ)
  let T (d e:ℕ):ℝ := ((d+1).gcd (e+1):ℝ)/((max (d+1) (e+1):ℕ):ℝ)
  have hW (j:ℕ) : Continuous (W j) := by
    unfold W fejerWave dirichletGeometricKernel E
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
      exact (singleFejerFamily_pair_integral_max Q (d+1) (e+1) hQ (Nat.succ_pos d) (Nat.succ_pos e)).trans_eq
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

private theorem fejer_energy_cross (f g : ℝ → ℝ) (B C:ℝ) (hf:Continuous f) (hg:Continuous g)
    (hB:0<B) (hC:0<C) (hFB:(∫ t in (0:ℝ)..1,(f t)^2) ≤ B^2)
    (hGC:(∫ t in (0:ℝ)..1,(g t)^2) ≤ C^2) :
    (∫ t in (0:ℝ)..1,f t*g t) ≤ B*C := by
  have hp (t:ℝ) : (2*B*C)*(f t*g t) ≤ C^2*(f t)^2+B^2*(g t)^2 := by
    nlinarith [sq_nonneg (C*f t - B*g t)]
  have hint := intervalIntegral.integral_mono_on (μ:=volume) (a:=0) (b:=1) zero_le_one
    (f:=fun t => (2*B*C)*(f t*g t)) (g:=fun t => C^2*(f t)^2+B^2*(g t)^2)
    (by exact (continuous_const.mul (hf.mul hg)).intervalIntegrable _ _)
    (by exact ((continuous_const.mul (hf.pow 2)).add (continuous_const.mul (hg.pow 2))).intervalIntegrable _ _)
    (fun t _ => hp t)
  rw [intervalIntegral.integral_add (f:=fun t:ℝ => C^2*(f t)^2) (g:=fun t:ℝ => B^2*(g t)^2) ((continuous_const.mul (hf.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul (hg.pow 2)).intervalIntegrable _ _)] at hint
  simp_rw [intervalIntegral.integral_const_mul] at hint
  apply le_of_mul_le_mul_left (a:=2*B*C) _ (by positivity)
  calc
    _ ≤ _ := hint
    _ ≤ C^2*B^2+B^2*C^2 := add_le_add (mul_le_mul_of_nonneg_left hFB (sq_nonneg C)) (mul_le_mul_of_nonneg_left hGC (sq_nonneg B))
    _ = _ := by ring

private theorem fejer_family_triangle (s : Finset ℕ) (f:ℕ→ℝ→ℝ) (A:ℕ→ℝ)
    (hf:∀j,Continuous (f j)) (hA:∀j,0<A j)
    (hen:∀j,(∫t in (0:ℝ)..1,(f j t)^2)≤(A j)^2) :
    (∫t in (0:ℝ)..1,(∑j∈s,f j t)^2) ≤ (∑j∈s,A j)^2 := by
  have hpoint (t:ℝ) : (∑ j ∈ s, f j t)^2 = ∑ d ∈ s, ∑ e ∈ s, f d t*f e t := by
    rw [sq,sum_mul]; simp_rw [mul_sum]
  simp_rw [hpoint]
  have hint (d:ℕ) : IntervalIntegrable (fun t => ∑ e ∈ s, f d t*f e t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro e _
    exact (hf d).mul (hf e)
  rw [intervalIntegral.integral_finsetSum (fun d _ => hint d)]
  have hrow (d:ℕ) : (∫ t in (0:ℝ)..1, ∑ e ∈ s,f d t*f e t) =
      ∑ e ∈ s,∫ t in (0:ℝ)..1,f d t*f e t :=
    intervalIntegral.integral_finsetSum (fun e _ => ((hf d).mul (hf e)).intervalIntegrable _ _)
  simp_rw [hrow]
  rw [sq,sum_mul]
  simp_rw [mul_sum]
  exact sum_le_sum fun d _ => sum_le_sum fun e _ => fejer_energy_cross _ _ _ _ (hf d) (hf e) (hA d) (hA e) (hen d) (hen e)

private theorem fejer_sqrt_geo (k:ℕ) :
    (∑j∈range (k+1),(Real.sqrt 2)^j) ≤ 4*(Real.sqrt 2)^k := by
  have hr := Real.sq_sqrt (by norm_num:0≤(2:ℝ))
  have hb : 4≤3*Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,pow_succ (Real.sqrt 2) k]
    have h := mul_le_mul_of_nonneg_right hb (pow_nonneg (Real.sqrt_nonneg 2) k)
    linarith

theorem dyadicFejerEnvelope_family_energy_sharp (Q D:ℕ) (hQ:0<Q) (hD:0<D) :
    (∫ t in (0:ℝ)..1,(∑d∈range D,dyadicFejerEnvelope Q (((d+1:ℕ):ℝ)*t))^2) ≤
      2*((Nat.log 2 Q+1:ℕ):ℝ)^2*(D:ℝ)^2+128*(Q:ℝ)*D*(1+Real.log D) := by
  let J := Nat.log 2 Q
  let W (j:ℕ) (t:ℝ) := ∑d∈range D,fejerWave (2^j) (((d+1:ℕ):ℝ)*t)
  let b:ℝ := Real.sqrt ((D:ℝ)*(1+Real.log D))
  let r:ℝ := Real.sqrt 2
  let A (j:ℕ):ℝ := (D:ℝ)+2*b*r^j
  have hDr : (1:ℝ)≤D := by exact_mod_cast hD
  have hlog : 0≤Real.log D := Real.log_nonneg hDr
  have hb : 0≤b := Real.sqrt_nonneg _
  have hb2 : b^2=(D:ℝ)*(1+Real.log D) := Real.sq_sqrt (by positivity)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=2 := Real.sq_sqrt (by norm_num)
  have hpow (j:ℕ) : (r^j)^2=(2:ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 2,pow_mul,hr2]
  have hW (j:ℕ) : Continuous (W j) := by
    unfold W fejerWave dirichletGeometricKernel E
    fun_prop
  have hA (j:ℕ):0<A j := by dsimp only [A]; positivity
  have he (j:ℕ) : (∫t in (0:ℝ)..1,(W j t)^2)≤(A j)^2 := by
    have hh := singleFejerFamily_energy (2^j) D (by positivity)
    simp only [one_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
    apply hh.trans
    dsimp only [A]
    have hsq : (2*b*r^j)^2=4*(2:ℝ)^j*D*(1+Real.log D) := by rw [mul_pow,mul_pow,hpow,hb2]; ring
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) D) (show 0≤2*b*r^j by positivity)]
  have hpoint (t:ℝ) : (∑d∈range D,dyadicFejerEnvelope Q (((d+1:ℕ):ℝ)*t))=∑ j∈range (J+1),W j t := by
    exact sum_comm
  simp_rw [hpoint]
  apply (fejer_family_triangle _ W A hW hA he).trans
  have hsum : (∑j∈range (J+1),A j) ≤ ((J+1:ℕ):ℝ)*D+8*b*r^J := by
    simp only [A,sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]
    have h := fejer_sqrt_geo J
    change _ ≤ 4*r^J at h
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0≤2*b)
    linarith
  have hnat : 2^J≤Q := Nat.pow_log_le_self _ hQ.ne'
  have hpowQ : (r^J)^2≤Q := (hpow J).le.trans (by exact_mod_cast hnat)
  have hsqsum : (∑j∈range (J+1),A j)^2 ≤ (((J+1:ℕ):ℝ)*D+8*b*r^J)^2 := by
    exact pow_le_pow_left₀ (sum_nonneg fun j _ => (hA j).le) hsum 2
  apply hsqsum.trans
  have h2 : (8*b*r^J)^2≤64*(D:ℝ)*(1+Real.log D)*Q := by
    rw [mul_pow,mul_pow,hb2]
    calc
      _ ≤ 8^2*((D:ℝ)*(1+Real.log D))*Q := by gcongr
      _ = _ := by ring
  change _ ≤ 2*((J+1:ℕ):ℝ)^2*(D:ℝ)^2+128*(Q:ℝ)*D*(1+Real.log D)
  nlinarith [sq_nonneg (((J+1:ℕ):ℝ)*D - 8*b*r^J)]

end GoldbachPartial