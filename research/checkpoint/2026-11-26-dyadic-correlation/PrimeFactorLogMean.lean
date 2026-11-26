import Mathlib.NumberTheory.Chebyshev

namespace GoldbachPartial
open Finset Filter
open scoped ArithmeticFunction.vonMangoldt

/-- Exact summation of the von Mangoldt divisor identity with the endpoint multiplicities. -/
theorem mangoldt_floor_sum_logSum (Y : ℕ) :
    (∑ k ∈ Ioc 0 Y, Λ k * ((Y/k:ℕ):ℝ)) = ∑ j ∈ Ioc 0 Y, Real.log j := by
  classical
  calc
    _ = ∑ k ∈ Ioc 0 Y, ∑ j ∈ Ioc 0 Y, if k∣j then Λ k else 0 := by
      refine sum_congr rfl fun k _ => ?_
      rw [←sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
    _ = ∑ j ∈ Ioc 0 Y, ∑ k ∈ Ioc 0 Y, if k∣j then Λ k else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun j hj => ?_
      obtain ⟨hj0,hjY⟩ := mem_Ioc.mp hj
      have he : (Ioc 0 Y).filter (fun k => k∣j)=j.divisors := by
        ext k
        rw [mem_filter,mem_Ioc,Nat.mem_divisors]
        exact ⟨fun h => ⟨h.2,hj0.ne'⟩, fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hj0,
          (Nat.le_of_dvd hj0 h.1).trans hjY⟩,h.1⟩⟩
      rw [←sum_filter,he,ArithmeticFunction.vonMangoldt_sum]

theorem mangoldt_floor_sum_log_factorial (Y : ℕ) :
    (∑ k ∈ Ioc 0 Y, Λ k * ((Y/k:ℕ):ℝ)) = Real.log Y.factorial := by
  rw [mangoldt_floor_sum_logSum]
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [sum_Ioc_succ_top (by omega : 0≤Y),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero Y),add_comm]

/-- Restricting the floor error to primes sharpens the constant to log 4. -/
theorem prime_log_reciprocal_upto (Y : ℕ) (hY : 0<Y) :
    (∑ p ∈ (Ioc 0 Y).filter Nat.Prime, Real.log p/(p:ℝ)) ≤ Real.log Y + Real.log 4 := by
  classical
  let S := (Ioc 0 Y).filter Nat.Prime
  have hY0 : (0:ℝ) < Y := by exact_mod_cast hY
  have hfloor : (∑ p ∈ S, Real.log p * ((Y/p:ℕ):ℝ)) ≤ (Y:ℝ)*Real.log Y := by
    calc
      _ = ∑ p ∈ S, Λ p*((Y/p:ℕ):ℝ) := by
        refine sum_congr rfl fun p hp => ?_
        rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
      _ ≤ ∑ k ∈ Ioc 0 Y, Λ k*((Y/k:ℕ):ℝ) := sum_le_sum_of_subset_of_nonneg
        (filter_subset _ _) (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
      _ = _ := mangoldt_floor_sum_logSum Y
      _ ≤ ∑ _j ∈ Ioc 0 Y, Real.log Y := by
        exact sum_le_sum fun j hj => Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hj).1)
          (by exact_mod_cast (mem_Ioc.mp hj).2)
      _ = _ := by simp
  have htheta : (∑ p ∈ S,Real.log p) ≤ Real.log 4 * Y := by
    simpa only [S,Chebyshev.theta,Nat.floor_natCast] using Chebyshev.theta_le_log4_mul_x hY0.le
  apply (mul_le_mul_iff_left₀ hY0).mp
  rw [sum_mul]
  calc
    _ ≤ ∑ p ∈ S, (Real.log p*((Y/p:ℕ):ℝ) + Real.log p) := by
      refine sum_le_sum fun p hp => ?_
      have hpp := (mem_filter.mp hp).2
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
      have hdiv : (Y:ℝ)/p ≤ ((Y/p:ℕ):ℝ)+1 := by
        apply (div_le_iff₀ hp0).mpr
        have hn := (Nat.lt_mul_div_succ Y hpp.pos).le
        rw [Nat.mul_comm] at hn
        exact_mod_cast hn
      have he := mul_le_mul_of_nonneg_left hdiv (Real.log_natCast_nonneg p)
      linear_combination he
    _ ≤ _ := by rw [sum_add_distrib]; linarith only [hfloor,htheta]

private theorem primeFactor_log_sum_le (n : ℕ) (hn : 0<n) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hp : 0 < ∏ p ∈ n.primeFactors,p := prod_pos fun p h => (Nat.prime_of_mem_primeFactors h).pos
  have he := Real.log_le_log (by exact_mod_cast hp : (0:ℝ)<((∏ p ∈ n.primeFactors,p:ℕ):ℝ))
    (by exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n) :
      ((∏ p ∈ n.primeFactors,p:ℕ):ℝ)≤n)
  rw [Nat.cast_prod,Real.log_prod] at he
  · exact he
  · intro p h
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).ne_zero

theorem primeFactor_log_mean_bound_sharp {n : ℕ} (hn : 1≤Real.log n) :
    (∑ p ∈ n.primeFactors, Real.log p/(p:ℝ)) ≤ Real.log (Real.log n)+Real.log 4+1 := by
  let L := Real.log n
  let Y := ⌊L⌋₊
  have hL0 : 0<L := zero_lt_one.trans_le hn
  have hY : 1≤Y := (Nat.one_le_floor_iff _).mpr hn
  have hyn : (Y:ℝ)≤L := Nat.floor_le hL0.le
  have hny : L < (Y:ℝ)+1 := Nat.lt_floor_add_one _
  have hn0 : 0<n := by by_contra! h; have := Nat.eq_zero_of_le_zero h; norm_num [this] at hn
  let S := n.primeFactors.filter (fun p => p≤Y)
  let T := n.primeFactors.filter (fun p => ¬p≤Y)
  have hsplit : (∑ p ∈ n.primeFactors,Real.log p/(p:ℝ)) =
      (∑ p ∈ S,Real.log p/(p:ℝ)) + ∑ p ∈ T,Real.log p/(p:ℝ) :=
    (sum_filter_add_sum_filter_not n.primeFactors (fun p => p≤Y) _).symm
  have hsmall : (∑ p ∈ S,Real.log p/(p:ℝ)) ≤ Real.log L+Real.log 4 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (t:=(Ioc 0 Y).filter Nat.Prime) ?_
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)))
    · exact (prime_log_reciprocal_upto Y hY).trans (add_le_add (Real.log_le_log (by exact_mod_cast hY) hyn) le_rfl)
    · intro p hp
      obtain ⟨hpn,hpY⟩ := mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hpn
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpr.pos,hpY⟩,hpr⟩
  have htail : (∑ p ∈ T, Real.log p/(p:ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ T,Real.log p/L := by
        refine sum_le_sum fun p hp => ?_
        have hpy : Y+1≤p := by have := (mem_filter.mp hp).2; omega
        have hpL : L ≤ (p:ℝ) := hny.le.trans (by exact_mod_cast hpy)
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg _) hL0 hpL
      _ ≤ (∑ p ∈ n.primeFactors, Real.log p)/L := by
        rw [←sum_div]
        exact div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p _ _ => Real.log_natCast_nonneg _)) hL0.le
      _ ≤ L/L := div_le_div_of_nonneg_right (primeFactor_log_sum_le n hn0) hL0.le
      _ = 1 := div_self hL0.ne'
  rw [hsplit]
  linarith only [hsmall,htail]

theorem primeFactor_log_mean_bound :
    ∀ᶠ n : ℕ in atTop, (∑ p ∈ n.primeFactors, Real.log p/(p:ℝ)) ≤ Real.log (Real.log n)+10 := by
  have he := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [he] with n hn
  have h := primeFactor_log_mean_bound_sharp hn
  linarith only [h,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]

end GoldbachPartial