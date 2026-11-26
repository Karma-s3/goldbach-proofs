import NaturalPrimeGapArcs

namespace GoldbachPartial
open Finset

theorem positive_gcd_row_bound (e N : ℕ) (he : 0<e) :
    ∑ i ∈ range N, ((i+1).gcd e:ℝ) ≤ (N:ℝ)*e.divisors.card := by
  have hp (i : ℕ) : ((i+1).gcd e:ℝ) ≤
      ∑ d ∈ e.divisors, if d∣i+1 then (d:ℝ) else 0 := by
    let g := (i+1).gcd e
    have hmem : g∈e.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,he.ne'⟩
    have h := Finset.single_le_sum (f:=fun d => if d∣i+1 then (d:ℝ) else 0)
      (fun d _ => by split_ifs <;> positivity) hmem
    have hdiv : g∣i+1 := Nat.gcd_dvd_left ..
    simpa only [ite_eq_left hdiv] using h
  calc
    _ ≤ ∑ i ∈ range N, ∑ d ∈ e.divisors,if d∣i+1 then (d:ℝ) else 0 := sum_le_sum fun i _ => hp i
    _ = ∑ d ∈ e.divisors,∑ i ∈ range N,if d∣i+1 then (d:ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ e.divisors,(N:ℝ) := by
      apply sum_le_sum
      intro d _
      rw [←sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self N d
    _ = _ := by simp [nsmul_eq_mul,mul_comm]

private theorem familyHarmonic (N : ℕ) : (∑ j ∈ range N,((j+1:ℕ):ℝ)⁻¹)≤1+Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl|hn
    · norm_num
    have h0 : (0:ℝ)<N := by exact_mod_cast hn
    have hp : 0<(N:ℝ)+1 := by linarith
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hp h0)
    rw [Real.log_div hp.ne' h0.ne',inv_div] at h
    have hratio : 1-(N:ℝ)/(N+1)=((N:ℝ)+1)⁻¹ := by field_simp;ring
    rw [hratio] at h
    push_cast at ih ⊢
    linarith only [ih,h]

theorem divisorCard_sum_le_log (D : ℕ) :
    ∑ i ∈ range D,((i+1).divisors.card:ℝ) ≤ (D:ℝ)*(1+Real.log D) := by
  have hc (i) (hi : i∈range D) : ((i+1).divisors.card:ℝ)=
      ∑ j ∈ range D,if j+1∣i+1 then (1:ℝ) else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast (Finset.card_bij (s:=(i+1).divisors) (t:=(range D).filter (fun j => j+1∣i+1)) (fun d _ => d-1) (by
      intro d hd
      have h := Nat.dvd_of_mem_divisors hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hle := Nat.le_of_dvd (Nat.succ_pos i) h
      refine mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hi; omega),?_⟩
      rwa [Nat.sub_add_cancel hd0]) (by
      intro d hd e he h
      have := Nat.pos_of_mem_divisors hd
      have := Nat.pos_of_mem_divisors he
      omega) (by
      intro j hj
      have h := (mem_filter.mp hj).2
      exact ⟨j+1,Nat.mem_divisors.mpr ⟨h,by omega⟩,by omega⟩))
  rw [sum_congr rfl hc,sum_comm]
  have hu (j : ℕ) : (∑ i ∈ range D,if j+1∣i+1 then (1:ℝ) else 0)≤(D:ℝ)*((j+1:ℕ):ℝ)⁻¹ := by
    rw [←sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul,mul_one,←div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast Nat.div_mul_le_self D (j+1)
  calc
    _ ≤ ∑ j ∈ range D,(D:ℝ)*((j+1:ℕ):ℝ)⁻¹ := sum_le_sum fun j _ => hu j
    _ ≤ _ := by
      rw [←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact familyHarmonic D

theorem gcd_max_family_bound (D : ℕ) :
    (∑ j ∈ range D,∑ i ∈ range D,((i+1).gcd (j+1):ℝ)/((max (i+1) (j+1):ℕ):ℝ)) ≤
       2*(D:ℝ)*(1+Real.log D) := by
  let F := fun i j : ℕ => if i≤j then ((i+1).gcd (j+1):ℝ)/((j+1:ℕ):ℝ) else 0
  have h (i j : ℕ) : ((i+1).gcd (j+1):ℝ)/((max (i+1) (j+1):ℕ):ℝ) ≤ F i j+F j i := by
    rcases le_total i j with hij|hji
    · rw [max_eq_right (by omega)]
      dsimp only [F]
      rw [ite_eq_left hij]
      apply le_add_of_nonneg_right
      split_ifs <;> positivity
    · rw [max_eq_left (by omega)]
      dsimp only [F]
      rw [ite_eq_left hji,Nat.gcd_comm (i+1) (j+1)]
      apply le_add_of_nonneg_left
      split_ifs <;> positivity
  have hf (j : ℕ) (hj : j∈range D) :
      (∑ i ∈ range D,F i j)≤((j+1).divisors.card:ℝ) := by
    change (∑ i ∈ range D,if i≤j then _ else 0)≤_
    rw [←sum_filter,show (range D).filter (·≤j)=range (j+1) by
      ext i; simp only [mem_filter,mem_range]; have := mem_range.mp hj; omega,←sum_div]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using positive_gcd_row_bound (j+1) (j+1) (by omega)
  have htotal := (sum_le_sum hf).trans (divisorCard_sum_le_log D)
  calc
    _ ≤ ∑ j ∈ range D,∑ i ∈ range D,(F i j+F j i) := sum_le_sum fun j _ => sum_le_sum fun i _ => h i j
    _ = (∑ j ∈ range D,∑ i ∈ range D,F i j)+(∑ j ∈ range D,∑ i ∈ range D,F i j) := by
      simp only [sum_add_distrib]
      congr 1
      rw [sum_comm]
    _ ≤ _ := by linarith only [htotal]

end GoldbachPartial