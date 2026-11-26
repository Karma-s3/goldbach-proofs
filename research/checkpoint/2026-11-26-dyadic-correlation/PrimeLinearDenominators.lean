import FejerMajorWindow
import TruePrimeCenteringChebyshev
import TruePrimeLinearReplacement

namespace GoldbachPartial
open Finset ArithmeticFunction
open ExtendedArcCoefficient
noncomputable section

/-- Ramanujan coefficient multiplying a single true prime in the linear cross term. -/
def singlePrimeRamWeight (q h : ℕ) : ℂ :=
  (moebius q : ℂ)/(q.totient:ℂ) *
    (∑ a ∈ (range q).filter (fun a => a.Coprime q), E (-((h:ℝ)*(a:ℝ)/q)))

theorem singlePrimeRamWeight_at_prime {q : ℕ} (hq:q.Prime) (h : ℕ) :
    singlePrimeRamWeight q h =
      ((1-(if q∣h then (q:ℂ) else 0))/((q:ℂ)-1)) := by
  have hu := actualRamanujan_neg_eq_divisor h q hq.pos
  rw [singlePrimeRamWeight,hu,moebius_apply_prime hq,Nat.totient_prime hq,
    Nat.cast_sub hq.one_le,Nat.cast_one,dyadicRamanujanDivisor_squarefree hq.squarefree]
  by_cases hd : q∣h
  · rw [Nat.gcd_eq_left hd,Nat.div_self hq.pos,moebius_apply_one,Nat.totient_prime hq]
    simp only [ite_eq_left hd, Int.cast_neg, Int.cast_one, one_mul]
    push_cast [Nat.cast_sub hq.one_le]
    ring
  · have hc : q.Coprime h := hq.coprime_iff_not_dvd.mpr hd
    rw [hc.gcd_eq_one,Nat.div_one,moebius_apply_prime hq]
    simp [hd,div_eq_mul_inv]

/-- An arbitrary bounded weight may include the actual integrated Dirichlet kernel. -/
theorem prime_denominator_linear_bound (n q : ℕ) (hq:q.Prime)
    (K : ℕ→ℂ) (B : ℝ) (hB : ∀p∈range (n+1), ‖K p‖ ≤ B) :
    ‖∑ p ∈ range (n+1), (weight p:ℂ)*singlePrimeRamWeight q (n-p)*K p‖ ≤
    (B/((q:ℝ)-1))*((∑ p ∈ range (n+1),weight p)+
       (q:ℝ)*∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) := by
  have hv : (0:ℝ)<(q:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hq.one_lt)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hw (p:ℕ) : 0 ≤ weight p := by
    unfold weight
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  have hz (p:ℕ) : ‖singlePrimeRamWeight q (n-p)‖ ≤
      (1+(if q∣n-p then (q:ℝ) else 0))/((q:ℝ)-1) := by
    rw [singlePrimeRamWeight_at_prime hq,norm_div]
    have he : (q:ℂ)-1 = ((q:ℝ)-1:ℝ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
    apply div_le_div_of_nonneg_right _ hv.le
    by_cases h : q∣n-p
    · simpa [h] using norm_sub_le (1:ℂ) (q:ℂ)
    · simp [h]
  have hsum : (∑ p ∈ range (n+1),weight p*(1+(if q∣n-p then (q:ℝ) else 0))) =
      (∑ p ∈ range (n+1),weight p)+(q:ℝ)*∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p := by
    simp_rw [mul_add,mul_one,sum_add_distrib]
    rw [sum_filter,mul_sum]
    congr 1
    apply sum_congr rfl; intro p _
    split_ifs <;> ring
  rw [←hsum,mul_sum]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw _)]
  calc _ ≤ weight p*((1+(if q∣n-p then (q:ℝ) else 0))/((q:ℝ)-1))*B :=
         mul_le_mul (mul_le_mul_of_nonneg_left (hz p) (hw p)) (hB p hp) (norm_nonneg _)
           (by apply mul_nonneg (hw _); exact (norm_nonneg _).trans (hz _))
       _ = _ := by ring

/-- The integrated geometric kernel at a true-prime shift. -/
def singlePrimeWindow (n h : ℕ) (ρ : ℝ) : ℂ :=
  ∫ β in -ρ..ρ, dirichletGeometricKernel n β * E (-((h:ℝ)*β))

theorem singlePrimeWindow_log_bound (n h : ℕ) {ρ:ℝ} (hr : 0≤ρ) (hr' : ρ≤1/2) :
    ‖singlePrimeWindow n h ρ‖ ≤ 4*Real.log (1+((n:ℝ)+1)*ρ) := by
  let A := (n:ℝ)+1
  let f := fun t : ℝ => ‖dirichletGeometricKernel n t‖
  have ha : 0<A := by dsimp [A]; positivity
  have hf : Continuous f := by unfold f dirichletGeometricKernel E; fun_prop
  have htriv (t:ℝ) : f t ≤ A := by
    change ‖∑ k ∈ range (n+1), E ((k:ℝ)*t)‖ ≤ A
    apply (norm_sum_le ..).trans
    have hu (k:ℕ) : ‖E ((k:ℝ)*t)‖=1 := Complex.norm_exp_ofReal_mul_I _
    simp [hu,A]
  have he (t:ℝ) : f (-t)=f t := by
    have hc (x:ℝ) : E (-x)=starRingEnd ℂ (E x) := by
      unfold E
      rw [←Complex.exp_conj]
      congr 1; simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]; push_cast; ring
    unfold f dirichletGeometricKernel
    simp_rw [mul_neg,hc]
    rw [←map_sum]
    exact Complex.norm_conj _
  have hp (t:ℝ) (ht:0≤t) (hub:t≤ρ) : f t ≤ 2*A/(1+A*t) := by
    have hpos : 0 < 1+A*t := by positivity
    apply (le_div_iff₀ hpos).mpr
    by_cases hz : t=0
    · subst t; simpa using (show f 0 ≤ 2*A by linarith only [htriv 0,ha])
    have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm hz)
    have h := GoldbachPartial.fejer_kernel_pointwise n ht' (hub.trans hr')
    have hj : f t*(2*t) ≤ 1 := (le_div_iff₀ (by positivity)).mp h
    nlinarith only [htriv t,mul_le_mul_of_nonneg_left hj ha.le,ha]
  have hcont : ContinuousOn (fun t : ℝ => 2*A/(1+A*t)) (Set.Icc 0 ρ) := by
    refine continuousOn_const.div ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn) ?_
    intro t ht
    exact (add_pos_of_pos_of_nonneg (by norm_num : (0:ℝ)<1) (mul_nonneg ha.le ht.1)).ne'
  have hi : (∫ t in (0:ℝ)..ρ, 2*A/(1+A*t)) = 2*Real.log (1+A*ρ) := by
    let G := fun x:ℝ => 2*Real.log (1+A*x)
    have HH : (∫ t in (0:ℝ)..ρ, 2*A/(1+A*t)) = G ρ-G 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        rw [Set.uIcc_of_le hr] at ht
        have hv : 1+A*t ≠ 0 := by have := ht.1; positivity
        have hd := (((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).const_mul A)).log hv).const_mul 2
        convert hd using 1 <;> dsimp [G]
        ring
      · exact hcont.intervalIntegrable_of_Icc hr
    simpa [G] using HH
  have hn : (∫ t in -ρ..(0:ℝ), f t) = ∫ t in (0:ℝ)..ρ, f t := by
    have H := intervalIntegral.integral_comp_neg (a:=0) (b:=ρ) f
    rw [neg_zero] at H
    rw [←H]
    apply intervalIntegral.integral_congr
    intro t _; exact he t
  have hsub : (∫ t in (0:ℝ)..ρ, f t) ≤ 2*Real.log (1+A*ρ) := by
    rw [←hi]
    apply intervalIntegral.integral_mono_on hr (hf.intervalIntegrable _ _)
    · exact hcont.intervalIntegrable_of_Icc hr
    · intro t ht; exact hp t ht.1 ht.2
  have hN : ‖singlePrimeWindow n h ρ‖ ≤ ∫ t in -ρ..ρ,f t := by
    unfold singlePrimeWindow
    apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : -ρ≤ρ)).trans_eq
    apply intervalIntegral.integral_congr
    intro t _
    change ‖dirichletGeometricKernel n t*E (-((h:ℝ)*t))‖ = _
    rw [norm_mul,show ‖E (-((h:ℝ)*t))‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ:=MeasureTheory.volume) (-ρ) 0) (hf.intervalIntegrable 0 ρ)
  rw [hn] at hadd
  change _ ≤ 4*Real.log (1+A*ρ)
  linarith only [hN,hadd,hsub]

private theorem true_weight_mass (n:ℕ) :
    (∑ k ∈ range (n+1),weight k)=Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_range,sum_filter]
  rfl

private theorem prime_log_reciprocal (R Q:ℕ) (hR:1≤R) (hRQ:R≤Q) :
    (∑ q ∈ Ioc R Q, weight q/(q:ℝ)) ≤ Real.log 4*(Real.log Q-Real.log R) +
        (∑ k∈range (Q+1),weight k)/(Q:ℝ) := by
  induction Q, hRQ using Nat.le_induction with
  | base =>
    simp only [Ioc_self,sum_empty,sub_self,mul_zero,zero_add]
    rw [true_weight_mass]
    exact div_nonneg (Chebyshev.theta_nonneg _) (Nat.cast_nonneg _)
  | succ q hq ih =>
    have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have hq1 : (0:ℝ)<(q:ℝ)+1 := by positivity
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hq1 hq0)
    rw [Real.log_div hq1.ne' hq0.ne',inv_div,
        show 1-(q:ℝ)/(q+1)=1/((q:ℝ)+1) by field_simp; ring] at hl
    let T := ∑ k∈range (q+1),weight k
    have ht : T ≤ Real.log 4*q := (true_weight_mass q).trans_le (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _))
    have hs : T/(q:ℝ) - T/((q:ℝ)+1) ≤ Real.log 4/((q:ℝ)+1) := by
      field_simp
      linarith only [ht]
    have hh := mul_le_mul_of_nonneg_left hl (show 0≤Real.log 4 by positivity)
    rw [mul_one_div] at hh
    rw [sum_Ioc_succ_top (by omega),sum_range_succ]
    push_cast
    change (∑ x ∈ Ioc R q,weight x/(x:ℝ))≤Real.log 4*(Real.log q-Real.log R)+T/q at ih
    rw [add_div]
    dsimp only [T] at ih hs
    linarith only [ih,hs,hh]

theorem prime_denominator_reciprocals (R Q:ℕ) (hR:2≤R) (hRQ:R≤Q) :
    (∑ q ∈ (Ioc R Q).filter Nat.Prime, 1/((q:ℝ)-1)) ≤
      (2/Real.log R)*(Real.log 4*(1+Real.log Q-Real.log R)) := by
  have hlog : 0<Real.log R := Real.log_pos (by exact_mod_cast (show 1<R by omega))
  have hq : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hcost := prime_log_reciprocal R Q (by omega) hRQ
  have ht : (∑ k∈range (Q+1),weight k)/(Q:ℝ) ≤ Real.log 4 := by
    rw [true_weight_mass]
    exact (div_le_iff₀ hq).mpr (Chebyshev.theta_le_log4_mul_x hq.le)
  have he : (∑ q∈(Ioc R Q).filter Nat.Prime,1/((q:ℝ)-1)) ≤
      (2/Real.log R)*(∑ q ∈ Ioc R Q,weight q/(q:ℝ)) := by
    rw [sum_filter,mul_sum]
    apply sum_le_sum
    intro q h
    obtain ⟨hrq,_⟩ := mem_Ioc.mp h
    have hq' : (2:ℝ)≤q := by exact_mod_cast (show 2≤q by omega)
    have hpos : (0:ℝ)<q := by linarith
    have hd : 0<(q:ℝ)-1 := by linarith
    by_cases hp:q.Prime
    · rw [ite_eq_left hp,weight,ite_eq_left hp]
      have hl : Real.log (R:ℝ)≤Real.log (q:ℝ) := Real.log_le_log (by exact_mod_cast (show 0<R by omega)) (by exact_mod_cast hrq.le)
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_left hl (show 0≤2*((q:ℝ)-1) by linarith),
        mul_nonneg (show 0≤(q:ℝ)-2 by linarith) hlog.le]
    · simp [hp,weight]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith only [ht,hcost]

/-- By Theorem 2 of Montgomery and Vaughan (1973), the progression premise
holds with a universal constant when q is prime and q ≤ sqrt(n). -/
theorem prime_single_linear_band_of_progression (n R Q : ℕ)
    (hR : 2≤R) (hRQ : R≤Q) (ρ : ℕ → ℝ) {ρ₀ : ℝ} (hρ₀ : 0≤ρ₀)
    (hρ : ∀ q ∈ (Ioc R Q).filter Nat.Prime, 0≤ρ q ∧ ρ q≤1/2 ∧ ρ q≤ρ₀)
    (hAP : ∀ q ∈ (Ioc R Q).filter Nat.Prime,
      (∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) ≤ 4*n/((q:ℝ)-1)) :
    (∑ q ∈ (Ioc R Q).filter Nat.Prime, ‖2*(∑ p ∈ range (n+1),
      (weight p:ℂ)*singlePrimeRamWeight q (n-p)*singlePrimeWindow n (n-p) (ρ q))‖) ≤
      8*Real.log (1+((n:ℝ)+1)*ρ₀) * ((Real.log 4+8)*n) *
      ((2/Real.log R)*(Real.log 4*(1+Real.log Q-Real.log R))) := by
  let P := (Ioc R Q).filter Nat.Prime
  let B := 4*Real.log (1+((n:ℝ)+1)*ρ₀)
  have hB : 0≤B := mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [mul_nonneg (show 0≤(n:ℝ)+1 by positivity) hρ₀]))
  have ht := (true_weight_mass n).trans_le (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n))
  calc _ ≤ ∑ q ∈ P, (2*B*((Real.log 4+8)*n))*(1/((q:ℝ)-1)) := by
         refine sum_le_sum fun q hq => ?_
         have hpr := (mem_filter.mp hq).2
         have h2 : (2:ℝ)≤q := by exact_mod_cast hpr.two_le
         have hz : 0<(q:ℝ)-1 := by linarith
         obtain ⟨hu,hv,hw⟩ := hρ q hq
         have hb := prime_denominator_linear_bound n q hpr
           (fun p => singlePrimeWindow n (n-p) (ρ q)) B (fun p _ => by
             apply (singlePrimeWindow_log_bound n (n-p) hu hv).trans
             apply mul_le_mul_of_nonneg_left _ (by norm_num)
             apply Real.log_le_log (by positivity)
             gcongr)
         have hap := (div_le_iff₀ hz).mpr (show (q:ℝ)≤2*((q:ℝ)-1) by linarith)
         have hx := mul_le_mul_of_nonneg_left (hAP q hq) (Nat.cast_nonneg (α:=ℝ) q)
         have hy := mul_le_mul_of_nonneg_right hap (show 0≤4*(n:ℝ) by positivity)
         have hj : (q:ℝ)*(4*n/((q:ℝ)-1))=((q:ℝ)/((q:ℝ)-1))*(4*n) := by ring
         rw [hj] at hx
         have hsum := add_le_add ht (hx.trans hy)
         have hsum' : (∑ p ∈ range (n+1),weight p) +
             (q:ℝ)*(∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) ≤ (Real.log 4+8)*n := by
           linarith only [hsum]
         have hh := hb.trans (mul_le_mul_of_nonneg_left hsum' (div_nonneg hB hz.le))
         rw [norm_mul,Complex.norm_ofNat]
         convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2) using 1; ring
       _ = (2*B*((Real.log 4+8)*n))*(∑ q ∈ P, 1/((q:ℝ)-1)) := (mul_sum ..).symm
       _ ≤ _ := by
         have hp := mul_le_mul_of_nonneg_left (prime_denominator_reciprocals R Q hR hRQ)
           (show 0≤2*B*((Real.log 4+8)*n) by positivity)
         dsimp only [B] at hp ⊢
         convert hp using 1; ring

/-- One denominator of the actual true-wave/principal-model cross term. -/
def truePrincipalLinearRow (n q : ℕ) (ρ : ℝ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), ∫ β in -ρ..ρ,
    2*centralPrimeWave n (primeLinearRowCenter q a β)*resonantPrincipalModel n q β*
      E (-(n:ℝ)*primeLinearRowCenter q a β)

theorem truePrincipalLinearRow_fourier (n q : ℕ) (ρ : ℝ) :
    truePrincipalLinearRow n q ρ = 2*(∑ p ∈ range (n+1),
      (weight p:ℂ)*singlePrimeRamWeight q (n-p)*singlePrimeWindow n (n-p) ρ) := by
  let U := (range q).filter (fun a => a.Coprime q)
  let c := (moebius q:ℂ)/(q.totient:ℂ)
  let v (p a:ℕ) := E (-(((n-p:ℕ):ℝ)*a/q))
  let F (p a:ℕ) (β:ℝ) := (2*(weight p:ℂ)*c*v p a) *
    (dirichletGeometricKernel n β * E (-(((n-p:ℕ):ℝ)*β)))
  have hsplit (a:ℕ) (β:ℝ) : 2*centralPrimeWave n (primeLinearRowCenter q a β)*
      resonantPrincipalModel n q β*E (-(n:ℝ)*primeLinearRowCenter q a β) =
      ∑ p ∈ range (n+1),F p a β := by
    unfold centralPrimeWave resonantPrincipalModel
    simp only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
    rw [mul_sum,sum_mul,sum_mul]
    refine sum_congr rfl fun p hp => ?_
    have hpn := Nat.le_of_lt_succ (mem_range.mp hp)
    have he : E ((p:ℝ)*primeLinearRowCenter q a β)*E (-(n:ℝ)*primeLinearRowCenter q a β) =
      v p a*E (-(((n-p:ℕ):ℝ)*β)) := by
      unfold v primeLinearRowCenter
      rw [←phase_add,←phase_add,Nat.cast_sub hpn]
      congr 1
      ring
    change _ = (2*(weight p:ℂ)*c*v p a)*(dirichletGeometricKernel n β*E (-(((n-p:ℕ):ℝ)*β)))
    calc _ = (2*(weight p:ℂ)*c*dirichletGeometricKernel n β) *
           (E ((p:ℝ)*primeLinearRowCenter q a β)*E (-(n:ℝ)*primeLinearRowCenter q a β)) := by dsimp only [c]; ring
         _ = _ := by rw [he]; ring
  have hf (p a:ℕ) : Continuous (F p a) := by unfold F dirichletGeometricKernel E; fun_prop
  unfold truePrincipalLinearRow
  simp_rw [hsplit,intervalIntegral.integral_finsetSum (fun p _ => (hf p _).intervalIntegrable _ _)]
  simp only [F,intervalIntegral.integral_const_mul]
  rw [sum_comm,mul_sum]
  refine sum_congr rfl fun p _ => ?_
  change (∑ a ∈ U,(2*(weight p:ℂ)*c*v p a)*singlePrimeWindow n (n-p) ρ) =
    2*((weight p:ℂ)*(c*(∑ a ∈ U,v p a))*singlePrimeWindow n (n-p) ρ)
  rw [←sum_mul,←mul_sum]
  ring

theorem truePrimeLinearMass_eq_rows (n:ℕ) :
    truePrimeLinearMass n = ∑ j ∈ Ico (terminalPrimeArcCutoff n) (naturalTubeScale n),
      truePrincipalLinearRow n (j+1) (naturalTubeRadius (3*naturalTubeScale n) (j+1)) := rfl

theorem prime_truePrincipalLinearRows_of_progression (n R Q : ℕ)
    (hR : 2≤R) (hRQ : R≤Q) (ρ : ℕ → ℝ) {ρ₀ : ℝ} (hρ₀ : 0≤ρ₀)
    (hρ : ∀ q ∈ (Ioc R Q).filter Nat.Prime, 0≤ρ q ∧ ρ q≤1/2 ∧ ρ q≤ρ₀)
    (hAP : ∀ q ∈ (Ioc R Q).filter Nat.Prime,
      (∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) ≤ 4*n/((q:ℝ)-1)) :
    (∑ q ∈ (Ioc R Q).filter Nat.Prime, ‖truePrincipalLinearRow n q (ρ q)‖) ≤
      8*Real.log (1+((n:ℝ)+1)*ρ₀) * ((Real.log 4+8)*n) *
      ((2/Real.log R)*(Real.log 4*(1+Real.log Q-Real.log R))) := by
  simp_rw [truePrincipalLinearRow_fourier]
  exact prime_single_linear_band_of_progression n R Q hR hRQ ρ hρ₀ hρ hAP

theorem prime_divisor_progression_mass {n q:ℕ} (hp:q.Prime) (hd:q∣n) (hqn:q≤n) :
    (∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) = Real.log q := by
  rw [sum_filter,sum_eq_single q]
  · rw [ite_eq_left (Nat.dvd_sub hd (dvd_refl q))]
    simp [weight,hp]
  · intro p hp' hne
    by_cases h : q∣n-p
    · have hqp : q∣p := by
        have hh := Nat.dvd_sub hd h
        simpa [Nat.sub_sub_self (Nat.le_of_lt_succ (mem_range.mp hp'))] using hh
      have hnp : ¬p.Prime := by
        intro hpr
        exact hne ((Nat.prime_dvd_prime_iff_eq hp hpr).mp hqp).symm
      simp [weight,hnp]
    · simp [h]
  · intro hh
    exact (hh (mem_range.mpr (by omega))).elim

/-- When q²≤n, q dividing n contributes only p=q to the exceptional class.
For q not dividing n the AP hypothesis is exactly the Brun--Titchmarsh input. -/
theorem prime_truePrincipalLinearRows_of_coprime_progression (n R Q:ℕ)
    (hR : 2≤R) (hRQ : R≤Q) (hQ : Q^2≤n) (ρ : ℕ→ℝ) {ρ₀:ℝ} (hρ₀:0≤ρ₀)
    (hρ : ∀ q ∈ (Ioc R Q).filter Nat.Prime, 0≤ρ q ∧ ρ q≤1/2 ∧ ρ q≤ρ₀)
    (hAP : ∀ q ∈ (Ioc R Q).filter Nat.Prime, ¬q∣n →
      (∑ p ∈ (range (n+1)).filter (fun p => q∣n-p),weight p) ≤ 4*n/((q:ℝ)-1)) :
    (∑ q ∈ (Ioc R Q).filter Nat.Prime, ‖truePrincipalLinearRow n q (ρ q)‖) ≤
      8*Real.log (1+((n:ℝ)+1)*ρ₀) * ((Real.log 4+8)*n) *
      ((2/Real.log R)*(Real.log 4*(1+Real.log Q-Real.log R))) := by
  apply prime_truePrincipalLinearRows_of_progression n R Q hR hRQ ρ hρ₀ hρ
  intro q hq
  by_cases hd:q∣n
  · have hp := (mem_filter.mp hq).2
    have hle := (mem_Ioc.mp (mem_filter.mp hq).1).2
    have hqn := (Nat.pow_le_pow_left hle 2).trans hQ
    rw [prime_divisor_progression_mass hp hd ((Nat.le_self_pow (by decide : 2≠0) _).trans hqn)]
    have h2 : (2:ℝ)≤q := by exact_mod_cast hp.two_le
    have hn : (q:ℝ)^2≤n := by exact_mod_cast hqn
    have hlog := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<q)
    apply (le_div_iff₀ (by linarith : 0<(q:ℝ)-1)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlog (show 0≤(q:ℝ)-1 by linarith),
      hn,h2,Nat.cast_nonneg (α:=ℝ) n]
  · exact hAP q hq hd

end
end GoldbachPartial
