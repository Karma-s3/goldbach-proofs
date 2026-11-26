import VerifiedDivisorWeightConcentration
import VerifiedSquarefreeBrunSurvivors

namespace GoldbachPartial
open Finset

private theorem totient_fourth_factor {p : ℕ} (hp : p.Prime) :
    (1+1/((p:ℝ)-1))^4 ≤ 1+30/(p:ℝ) := by
  let t := 1/((p:ℝ)-1)
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have h0 : (0:ℝ)<p-1 := by linarith
  have ht : 0≤t := by dsimp [t];positivity
  have h1 : t≤1 := by dsimp [t];rw [div_le_iff₀ h0];linarith
  have h2' : t^2≤t := by simpa only [sq] using (mul_le_of_le_one_right ht h1)
  have h3 : t^3≤t := by simpa only [pow_succ] using (mul_le_mul_of_nonneg_right h2' ht).trans (by simpa only [sq] using h2')
  have h4 : t^4≤t := by simpa only [pow_succ] using (mul_le_mul_of_nonneg_right h3 ht).trans (by simpa only [sq] using h2')
  have hP : (0:ℝ)<p := by linarith
  have hfrac : 15*t ≤ 30/(p:ℝ) := by
    dsimp [t]
    field_simp
    linarith
  change (1+t)^4 ≤ _
  linarith only [h2',h3,h4,hfrac]

open private sf_inverse_tail from VerifiedSquarefreeBrunSurvivors

/-- A uniform fourth-moment bound for the singular factors in a pointwise upper sieve. -/
theorem totient_ratio_fourth_moment (X : ℕ) :
    (∑ n∈Icc 1 X, ((n:ℝ)/n.totient)^4) ≤ Real.exp 30*X := by
  classical
  let B := (Ioc 1 X).filter Nat.Prime
  let v (p : ℕ) : ℝ := 30/(p:ℝ)
  let w (S : Finset ℕ) := ∏ p∈S, v p
  let d (S : Finset ℕ) := ∏ p∈S,p
  have hw (S : Finset ℕ) : 0≤w S := prod_nonneg fun p _ => by dsimp [v]; positivity
  have hrow (n : ℕ) (hn : n∈Icc 1 X) : ((n:ℝ)/n.totient)^4 ≤
      ∑ S ∈ B.powerset, if d S∣n then w S else 0 := by
    have hn' := (mem_Icc.mp hn).1
    rw [←goodDivisorWeight_sum hn',←prod_one_add,←Finset.prod_pow]
    calc
      _ ≤ ∏ p∈n.primeFactors,(1+v p) := by
        refine prod_le_prod₀ (fun p _ => ?_) (fun p h => totient_fourth_factor (Nat.prime_of_mem_primeFactors h))
        positivity
      _ = ∑S∈n.primeFactors.powerset,w S := prod_one_add _
      _ ≤ _ := by
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg _ (fun S _ _ => hw S)
        intro S hS
        have h := mem_powerset.mp hS
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr (h.trans ?_), (prod_dvd_prod_of_subset _ _ id h).trans (Nat.prod_primeFactors_dvd n)⟩
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp'.one_lt,(Nat.le_of_dvd hn' (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2⟩,hp'⟩
  have hm (S : Finset ℕ) : (∑ n∈Icc 1 X,if d S∣n then w S else 0) ≤
      (X:ℝ)*∏ p∈S, (30/(p:ℝ)^2) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have hcard : ((Icc 1 X).filter (fun n=>d S∣n)).card ≤ X/d S := by
      rw [←Nat.card_multiples' X (d S)]
      apply card_le_card
      intro n hn
      obtain ⟨hi,hd⟩ := mem_filter.mp hn
      have hi' := mem_Icc.mp hi
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,hd⟩
    have h := mul_le_mul_of_nonneg_right ((show (((Icc 1 X).filter (fun n=>d S∣n)).card:ℝ)≤(X/d S:ℕ) by exact_mod_cast hcard).trans Nat.cast_div_le) (hw S)
    apply h.trans_eq
    dsimp only [d,w,v]
    rw [Nat.cast_prod,div_eq_mul_inv,mul_assoc]
    simp only [←prod_inv_distrib, ←prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro p _
    ring
  have hsum := sum_le_sum hrow
  rw [sum_comm] at hsum
  refine hsum.trans ((sum_le_sum fun S _ => hm S).trans ?_)
  rw [←mul_sum,←prod_one_add,mul_comm (Real.exp 30)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ p∈B,Real.exp (30/(p:ℝ)^2) := by
      apply prod_le_prod₀ (fun p _ => by positivity)
      intro p _
      linarith only [Real.add_one_le_exp (30/(p:ℝ)^2)]
    _ = Real.exp (∑ p∈B,30/(p:ℝ)^2) := (Real.exp_sum ..).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := (sum_le_sum_of_subset_of_nonneg (show B ⊆ Ioc 1 X from filter_subset ..)
        (fun p _ _ => show 0≤1/(p:ℝ)^2 by positivity)).trans (sf_inverse_tail 1 X)
      norm_num at h
      calc _ = 30*∑ p∈B,1/(p:ℝ)^2 := by rw [mul_sum];apply sum_congr rfl;intro p _;ring
           _ ≤ _ := by simp only [one_div]; linarith

end GoldbachPartial