import DeepArcMoments
import MangoldtPrimePrefix
namespace GoldbachPartial
open Finset
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

def crtLambdaCoefficient (d : ℕ) : ℝ := -(ArithmeticFunction.moebius d : ℝ) * Real.log d

def crtEndpointCount (n d e : ℕ) : ℝ :=
  ∑ k ∈ Ioo 0 n, if d ∣ k ∧ e ∣ n-k then (1:ℝ) else 0

def crtCompleteCount (n d e : ℕ) : ℕ :=
  ((range (d.lcm e)).filter (fun k => d∣k ∧ k ≡ n [MOD e])).card

def crtRowError (n d e : ℕ) : ℝ :=
  crtEndpointCount n d e - ((n-1:ℕ):ℝ)*crtCompleteCount n d e/(d.lcm e : ℝ)

theorem crtCompleteCount_eq {n d e : ℕ} (hd : 0<d) (he : 0<e) :
    crtCompleteCount n d e = if d.gcd e ∣ n then 1 else 0 := by
  classical
  by_cases h : d.gcd e ∣ n
  · rw [ite_eq_left h]
    let z := Nat.chineseRemainder' (Nat.modEq_zero_iff_dvd.mpr h).symm
    have hz : (z:ℕ)<d.lcm e := Nat.chineseRemainder'_lt_lcm _ hd.ne' he.ne'
    have hset : (range (d.lcm e)).filter (fun k => d∣k ∧ k ≡ n [MOD e]) = {(z:ℕ)} := by
      ext k
      simp only [mem_filter,mem_range,mem_singleton]
      constructor
      · rintro ⟨hk,hd',he'⟩
        have hm : k ≡ (z:ℕ) [MOD d.lcm e] := Nat.modEq_and_modEq_iff_modEq_lcm.mp
          ⟨(Nat.modEq_zero_iff_dvd.mpr hd').trans z.2.1.symm,he'.trans z.2.2.symm⟩
        exact hm.eq_of_lt_of_lt hk hz
      · rintro rfl
        exact ⟨hz,Nat.modEq_zero_iff_dvd.mp z.2.1,z.2.2⟩
    simp [crtCompleteCount,hset]
  · rw [ite_eq_right h]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨_,hd',he'⟩ := mem_filter.mp hk
    have hz := (Nat.modEq_zero_iff_dvd.mpr hd').of_dvd (Nat.gcd_dvd_left d e)
    exact h (Nat.modEq_zero_iff_dvd.mp (((he'.of_dvd (Nat.gcd_dvd_right d e)).symm).trans hz))

theorem crtCompleteCount_of_coprime {n d e : ℕ} (hd : 0<d) (he : 0<e) (hc : d.Coprime e) :
    crtCompleteCount n d e = 1 := by simp [crtCompleteCount_eq hd he,hc.gcd_eq_one]

theorem half_block_row_exact {Y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpY : Y<p) (hqY : Y<q) (hne : p≠q) :
    crtLambdaCoefficient p*crtLambdaCoefficient q*crtRowError (2*Y) p q =
      -((2*Y-1:ℕ):ℝ) * ((Real.log p/p)*(Real.log q/q)) := by
  have hn : crtEndpointCount (2*Y) p q = 0 := by
    apply sum_eq_zero
    intro k hk
    have h := mem_Ioo.mp hk
    apply ite_eq_right
    rintro ⟨hd,he⟩
    have h₁ := Nat.le_of_dvd h.1 hd
    have h₂ := Nat.le_of_dvd (by omega : 0<2*Y-k) he
    omega
  have h₁ : crtLambdaCoefficient p=Real.log p := by simp [crtLambdaCoefficient,ArithmeticFunction.moebius_apply_prime hp]
  have h₂ : crtLambdaCoefficient q=Real.log q := by simp [crtLambdaCoefficient,ArithmeticFunction.moebius_apply_prime hq]
  rw [h₁,h₂,crtRowError,hn,crtCompleteCount_of_coprime hp.pos hq.pos ((Nat.coprime_primes hp hq).mpr hne)]
  rw [((Nat.coprime_primes hp hq).mpr hne).lcm_eq_mul]
  push_cast
  ring

def crtUpperPrimeBlock (Y : ℕ) : ℝ :=
  let P := (Ioc Y (2*Y)).filter Nat.Prime
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    crtLambdaCoefficient p*crtLambdaCoefficient q*crtRowError (2*Y) p q

theorem crtUpperPrimeBlock_eq (Y : ℕ) :
    crtUpperPrimeBlock Y = -((2*Y-1:ℕ):ℝ) *
      ∑ p ∈ (Ioc Y (2*Y)).filter Nat.Prime, ∑ q ∈ ((Ioc Y (2*Y)).filter Nat.Prime).erase p,
        (Real.log p/p)*(Real.log q/q) := by
  unfold crtUpperPrimeBlock
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hqp,hq⟩ := mem_erase.mp hq
  obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
  obtain ⟨hqI,hqq⟩ := mem_filter.mp hq
  exact half_block_row_exact hpp hqq (mem_Ioc.mp hpI).1 (mem_Ioc.mp hqI).1 hqp.symm

theorem crtUpperPrimeBlock_le (Y : ℕ) (hY : 192^4 ≤ Y) :
    crtUpperPrimeBlock Y ≤ -(2*(Y:ℝ))/256 := by
  let P := (Ioc Y (2*Y)).filter Nat.Prime
  let a := fun p : ℕ => Real.log p/(p:ℝ)
  have hY₂ : 512≤Y := (by decide : 512≤192^4).trans hY
  have hYr : (512:ℝ)≤Y := by exact_mod_cast hY₂
  have hYpos : (0:ℝ)<Y := by linarith
  have hm : (Y:ℝ)/4 ≤ ∑ p ∈ P, Real.log p := GoldbachDeepFourth.dyadic_prime_mass Y hY
  have hlog : Real.log (2*(Y:ℝ)) ≤ (Y:ℝ)/8 := by
    have hb := Real.log_le_rpow_div (by positivity : (0:ℝ)≤2*Y) (by norm_num : (0:ℝ)<1/2)
    rw [← Real.sqrt_eq_rpow] at hb
    have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤2*Y)
    have hh : Real.sqrt (2*(Y:ℝ)) ≤ (Y:ℝ)/16 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hYr) hYpos.le,
        sq_nonneg (Real.sqrt (2*(Y:ℝ))-(Y:ℝ)/16)]
    linarith
  have hmA (p : ℕ) (hp : p ∈ P) : 0≤a p ∧ Real.log p ≤ (2*(Y:ℝ))*a p ∧ Real.log p ≤ (Y:ℝ)/8 := by
    obtain ⟨hi,hp'⟩ := mem_filter.mp hp
    have hu : (p:ℝ) ≤ 2*Y := by exact_mod_cast (mem_Ioc.mp hi).2
    have hp0 : (0:ℝ)<p := by exact_mod_cast hp'.pos
    have hlogp : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_le)
    have hapos : 0≤a p := div_nonneg hlogp hp0.le
    refine ⟨hapos,?_,(Real.log_le_log hp0 hu).trans hlog⟩
    calc Real.log p = (p:ℝ)*a p := by dsimp [a]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_right hu hapos
  have hsum (S : Finset ℕ) (hS:S⊆P) : (∑ q ∈ S, Real.log q) ≤ (2*(Y:ℝ))*(∑ q ∈ S, a q) := by
    rw [mul_sum]; exact sum_le_sum (fun q hq => (hmA q (hS hq)).2.1)
  have hall : 1/8 ≤ ∑ p ∈ P, a p := by
    have hh := hm.trans (hsum P (fun _ h => h))
    by_contra! hnot
    nlinarith [mul_neg_of_pos_of_neg hYpos (sub_neg.mpr hnot)]
  have hrow (p : ℕ) (hp:p∈P) : 1/16 ≤ ∑ q ∈ P.erase p, a q := by
    have h₁ := sum_erase_add P (fun q : ℕ => Real.log q) hp
    have h₂ := hsum (P.erase p) (erase_subset ..)
    have h₃ := (hmA p hp).2.2
    by_contra! hnot
    nlinarith [mul_neg_of_pos_of_neg hYpos (sub_neg.mpr hnot)]
  have hpair : 1/128 ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, a p*a q := by
    calc (1:ℝ)/128 ≤ (∑ p ∈ P, a p)*(1/16) := by linarith only [hall]
         _ = ∑ p ∈ P, a p*(1/16) := sum_mul ..
         _ ≤ _ := by
           apply sum_le_sum; intro p hp
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left (hrow p hp) (hmA p hp).1
  rw [crtUpperPrimeBlock_eq]; change -((2*Y-1:ℕ):ℝ)*_ ≤ _
  have hy' : (Y:ℝ)≤((2*Y-1:ℕ):ℝ) := by exact_mod_cast (show Y≤2*Y-1 by omega)
  have htotal := mul_le_mul hy' hpair (by norm_num) (Nat.cast_nonneg (2*Y-1))
  linarith only [htotal]

private theorem crtLambda_divisors (k : ℕ) :
    (∑ d ∈ k.divisors, crtLambdaCoefficient d)=ArithmeticFunction.vonMangoldt k := by
  have hh := ArithmeticFunction.sum_moebius_mul_log_eq (n:=k)
  simp only [ArithmeticFunction.log_apply] at hh
  simp only [crtLambdaCoefficient,neg_mul,Finset.sum_neg_distrib,hh,neg_neg]

private theorem crtLambda_restrict {n k : ℕ} (hk : 0<k) (hkn : k≤n) :
    (∑ d ∈ Icc 1 n, if d ∣ k then crtLambdaCoefficient d else 0) =
      ArithmeticFunction.vonMangoldt k := by
  have he : (Icc 1 n).filter (fun d => d∣k)=k.divisors := by
    ext d
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,h⟩
      exact ⟨h,hk.ne'⟩
    · rintro ⟨h,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h hk,(Nat.le_of_dvd hk h).trans hkn⟩,h⟩
  rw [←sum_filter,he,crtLambda_divisors]

def crtLambdaConvolution (n : ℕ) : ℝ :=
  ∑ k ∈ Ioo 0 n, ArithmeticFunction.vonMangoldt k*ArithmeticFunction.vonMangoldt (n-k)

theorem crtLambdaConvolution_exact (n : ℕ) :
    crtLambdaConvolution n =
      ∑ d ∈ Icc 1 n, ∑ e ∈ Icc 1 n, crtLambdaCoefficient d*crtLambdaCoefficient e*
        (((n-1:ℕ):ℝ)*crtCompleteCount n d e/(d.lcm e : ℝ) + crtRowError n d e) := by
  classical
  let A := crtLambdaCoefficient
  let K := Ioo 0 n
  let S := Icc 1 n
  have hloc (k : ℕ) (hk : k∈K) : ArithmeticFunction.vonMangoldt k*ArithmeticFunction.vonMangoldt (n-k) =
      ∑ d ∈ S, ∑ e ∈ S, A d*A e*(if d∣k ∧ e∣n-k then (1:ℝ) else 0) := by
    obtain ⟨hk₁,hk₂⟩ := mem_Ioo.mp hk
    rw [←crtLambda_restrict hk₁ hk₂.le, ←crtLambda_restrict (by omega : 0<n-k) (Nat.sub_le n k)]
    rw [sum_mul]
    apply sum_congr rfl; intro d _
    rw [mul_sum]
    apply sum_congr rfl; intro e _
    by_cases hd : d∣k <;> by_cases he : e∣n-k <;> simp [hd,he,A]
  have row (d e : ℕ) : (∑ k ∈ K, A d*A e*(if d∣k ∧ e∣n-k then (1:ℝ) else 0)) =
      A d*A e*(((n-1:ℕ):ℝ)*crtCompleteCount n d e/(d.lcm e : ℝ) + crtRowError n d e) := by
    rw [←mul_sum]; dsimp only [crtRowError,crtEndpointCount,K]; ring
  calc crtLambdaConvolution n = ∑ k ∈ K, ∑ d ∈ S, ∑ e ∈ S,
        A d*A e*(if d∣k ∧ e∣n-k then (1:ℝ) else 0) := sum_congr rfl hloc
       _ = _ := by
         rw [sum_comm]
         apply sum_congr rfl; intro d _
         rw [sum_comm]
         exact sum_congr rfl (fun e _ => row d e)

theorem crtLambdaConvolution_prime_error {n : ℕ} (hn : 1≤n) :
    0 ≤ crtLambdaConvolution n - corr n ∧
    crtLambdaConvolution n - corr n ≤ 4*Real.sqrt n*(Real.log n)^2 := by
  let Λ' := ArithmeticFunction.vonMangoldt
  have hnn (k : ℕ) : 0≤weight k ∧ weight k ≤ Λ' k := by
    by_cases hp : k.Prime
    · simp only [weight,ite_eq_left hp,Λ',ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact ⟨Real.log_nonneg (by exact_mod_cast hp.one_le), le_rfl⟩
    · simp [weight,hp,Λ']
  have hbound (k : ℕ) (hk:k≤n) : Λ' k ≤ Real.log n := by
    by_cases h : k=0
    · subst k; simpa [Λ'] using Real.log_nonneg (show 1≤(n:ℝ) by exact_mod_cast hn)
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by exact_mod_cast hk))
  have hident : crtLambdaConvolution n = ∑ k ∈ range (n+1), Λ' k*Λ' (n-k) := by
    apply Finset.sum_subset
    · intro k hk; exact mem_range.mpr (by have := (mem_Ioo.mp hk).2; omega)
    · intro k hk hnot
      have := mem_range.mp hk
      have hd : k=0 ∨ k=n := by simp only [mem_Ioo] at hnot; omega
      rcases hd with rfl|rfl <;> simp

  rw [hident,corr,←sum_sub_distrib]
  constructor
  · apply sum_nonneg; intro k _
    apply sub_nonneg.mpr
    exact mul_le_mul (hnn k).2 (hnn (n-k)).2 (hnn _).1 ((hnn k).1.trans (hnn k).2)
  let g := fun k : ℕ => |Λ' k-weight k|
  let L := Real.log (n:ℝ)
  have hL : 0≤L := Real.log_nonneg (by exact_mod_cast hn)
  have hg (k : ℕ) : g k=Λ' k-weight k := abs_of_nonneg (sub_nonneg.mpr (hnn k).2)
  have href : (∑ k ∈ range (n+1), g (n-k)) = ∑ k ∈ range (n+1), g k := by
    simpa using sum_range_reflect g (n+1)
  calc _ ≤ ∑ k ∈ range (n+1), (g k+g (n-k))*L := by
         apply sum_le_sum; intro k hk
         have hkn : k≤n := by have := mem_range.mp hk; omega
         rw [hg,hg]
         have h₁ := mul_le_mul_of_nonneg_left (hbound _ (Nat.sub_le n k)) (sub_nonneg.mpr (hnn k).2)
         have h₂ := mul_le_mul_of_nonneg_left ((hnn k).2.trans (hbound k hkn)) (sub_nonneg.mpr (hnn (n-k)).2)
         dsimp only [L]
         nlinarith only [h₁,h₂]
       _ = (2*(∑ k ∈ range (n+1), g k))*L := by
         rw [←sum_mul,sum_add_distrib,href]; ring
       _ ≤ 4*Real.sqrt n*(Real.log n)^2 := by
         have h := mul_le_mul_of_nonneg_right (primePowerError_le n) hL
         change (∑ k ∈ range (n+1), g k)*L ≤ 2*Real.sqrt n*L*L at h
         change _ ≤ 4*Real.sqrt n*L^2
         nlinarith only [h]

theorem crtLambdaConvolution_gcd_split (n : ℕ) :
    crtLambdaConvolution n =
      ∑ d ∈ Icc 1 n, ∑ e ∈ Icc 1 n, crtLambdaCoefficient d*crtLambdaCoefficient e*
        ((if d.gcd e ∣ n then ((n-1:ℕ):ℝ)/(d.lcm e:ℝ) else 0) + crtRowError n d e) := by
  rw [crtLambdaConvolution_exact]
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro e he
  rw [crtCompleteCount_eq (mem_Icc.mp hd).1 (mem_Icc.mp he).1]
  split <;> simp

theorem crtRowAbsoluteTotal_lower (Y : ℕ) (hY : 192^4≤Y) :
    2*(Y:ℝ)/256 ≤ ∑ d ∈ Icc 1 (2*Y), ∑ e ∈ Icc 1 (2*Y),
      |crtLambdaCoefficient d*crtLambdaCoefficient e*crtRowError (2*Y) d e| := by
  let P := (Ioc Y (2*Y)).filter Nat.Prime
  let S := Icc 1 (2*Y)
  let f := fun p q => crtLambdaCoefficient p*crtLambdaCoefficient q*crtRowError (2*Y) p q
  have hsub : P ⊆ S := by
    intro p hp
    have hi := mem_Ioc.mp (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega,hi.2⟩
  have hb := crtUpperPrimeBlock_le Y hY
  change (∑ p ∈ P, ∑ q ∈ P.erase p, f p q) ≤ _ at hb
  calc _ ≤ -(∑ p ∈ P, ∑ q ∈ P.erase p, f p q) := by linarith only [hb]
       _ = ∑ p ∈ P, ∑ q ∈ P.erase p, -f p q := by simp only [sum_neg_distrib]
       _ ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, |f p q| :=
         sum_le_sum (fun p _ => sum_le_sum (fun q _ => neg_le_abs _))
       _ ≤ ∑ p ∈ P, ∑ q ∈ S, |f p q| :=
         sum_le_sum (fun p _ => sum_le_sum_of_subset_of_nonneg ((erase_subset ..).trans hsub)
           (fun _ _ _ => abs_nonneg _))
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sum_nonneg (fun _ _ => abs_nonneg _))

end
end GoldbachPartial
