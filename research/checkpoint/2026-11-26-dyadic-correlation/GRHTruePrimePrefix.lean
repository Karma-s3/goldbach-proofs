import GRHWindowCertificate
import MangoldtPrimePrefix

namespace GoldbachPartial
open Finset Classical
open scoped ArithmeticFunction.vonMangoldt

theorem grhPsi0_nat_eq_mangoldtCharacterPrefix (q j : ℕ) (χ : DirichletCharacter ℂ q) :
    grhPsi0 χ (j:ℝ) = mangoldtCharacterPrefix q j χ -
      (if χ=1 then (j:ℂ) else 0) := by
  classical
  unfold grhPsi0 mangoldtCharacterPrefix
  rw [Nat.floor_natCast,Complex.ofReal_natCast]
  congr 1
  have hset : Finset.Icc 1 j = (Finset.range (j+1)).erase 0 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hset]
  simp

theorem true_prime_prefix_uniform_of_grhAllUniform (hψ : grhAllUniform) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 2≤n → ∀ (q : ℕ) [NeZero q], q≤n →
      ∀ χ : DirichletCharacter ℂ q, ∀ j≤n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤
        C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 := by
  classical
  obtain ⟨K,hK,hU⟩ := hψ
  refine ⟨(K+1)+3,by positivity,?_⟩
  intro n hn q _ hq
  apply centeredPrimeArcTransform_grh_scale_of_psi q hn (K+1)
  intro χ j hj
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hq' : (1:ℝ)≤q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let L := Real.log (2*(n:ℝ)^2)
  have hL : 1≤L := by
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    have h := Real.log_le_log (by norm_num : 0<(2:ℝ)^2)
      (show (2:ℝ)^2 ≤ 2*(n:ℝ)^2 by nlinarith [sq_nonneg ((n:ℝ)-2)])
    rw [Real.log_pow] at h
    dsimp [L]
    norm_num at h
    linarith
  have hs := Real.one_le_sqrt.mpr (show (1:ℝ)≤n by linarith)
  have hone : 1 ≤ Real.sqrt n*L^2 :=
    one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ hL)
  have hsmall : 1 ≤ (K+1)*Real.sqrt n*L^2 := by
    nlinarith only [hone,mul_nonneg hK.le (mul_nonneg (Real.sqrt_nonneg (n:ℝ)) (sq_nonneg L))]
  by_cases hj2 : 2≤j
  · have hj2' : (2:ℝ)≤j := by exact_mod_cast hj2
    have hjn : (j:ℝ)≤n := by exact_mod_cast hj
    have hqn : (q:ℝ)≤n := by exact_mod_cast hq
    have harg : 2*(q:ℝ)*j ≤ 2*(n:ℝ)^2 := by
      rw [sq,← mul_assoc]
      gcongr
    have hpos : (1:ℝ) ≤ 2*(q:ℝ)*j := by
      nlinarith [mul_le_mul_of_nonneg_right hq' (Nat.cast_nonneg (α := ℝ) j)]
    have hlog := Real.log_le_log (show 0<2*(q:ℝ)*j by linarith) harg
    have hu := hU q χ (j:ℝ) hj2'
    rw [grhPsi0_nat_eq_mangoldtCharacterPrefix] at hu
    refine hu.trans ?_
    gcongr
    · linarith
    · exact Real.log_nonneg hpos
  · have hj01 : j=0 ∨ j=1 := by omega
    have hm : mangoldtCharacterPrefix q j χ = 0 := by
      rcases hj01 with rfl|rfl <;> simp [mangoldtCharacterPrefix,Finset.sum_range_succ]
    have hnorm : ‖mangoldtCharacterPrefix q j χ - (if χ=1 then (j:ℂ) else 0)‖ ≤ 1 := by
      rw [hm]
      rcases hj01 with rfl|rfl <;> by_cases hc : χ=1 <;> simp [hc]
    exact hnorm.trans hsmall

end GoldbachPartial
