import DyadicCorrelationReduction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace GoldbachPartial

open Finset ExtendedArcCoefficient
open scoped ArithmeticFunction.vonMangoldt
open Classical

theorem primePowerError_eq_psi_sub_theta (n : ℕ) :
    ∑ k ∈ range (n+1), |Λ k - weight k| =
      Chebyshev.psi n - Chebyshev.theta n := by
  have h (k : ℕ) : weight k ≤ Λ k := by
    by_cases hp : k.Prime
    · simp [weight, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [weight, hp]
  simp_rw [abs_of_nonneg (sub_nonneg.mpr (h _))]
  rw [Finset.sum_sub_distrib, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
    Nat.range_succ_eq_Icc_zero, Nat.floor_natCast, Finset.sum_filter]
  rfl

theorem primePowerError_le (n : ℕ) :
    ∑ k ∈ range (n+1), |Λ k - weight k| ≤ 2 * Real.sqrt n * Real.log n := by
  rw [primePowerError_eq_psi_sub_theta]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

theorem primePowerError_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∑ k ∈ range (n+1), |Λ k - weight k| ≤ C * Real.sqrt n := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  rw [primePowerError_eq_psi_sub_theta]
  exact (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

noncomputable def mangoldtCharacterPrefix (q j : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ range (j+1), (Λ k : ℂ) * χ (k : ZMod q)

set_option maxHeartbeats 1200000 in
theorem centeredPrimeArcTransform_le_psi_error (q : ℕ) [NeZero q] (j : ℕ)
    (χ : DirichletCharacter ℂ q) :
    ‖centeredPrimeArcTransform q j 0 ((j : ℂ)+1) χ‖ ≤
      ‖mangoldtCharacterPrefix q j χ⁻¹ - (if χ⁻¹=1 then (j:ℂ) else 0)‖ +
        (Chebyshev.psi j - Chebyshev.theta j) + 1 := by
  let P := ∑ k ∈ range (j+1), (weight k : ℂ) * χ⁻¹ (k : ZMod q)
  let A := mangoldtCharacterPrefix q j χ⁻¹
  let M : ℂ := if χ=1 then j else 0
  let M' : ℂ := if χ=1 then (j:ℂ)+1 else 0
  have hPA : ‖P-A‖ ≤ Chebyshev.psi j - Chebyshev.theta j := by
    rw [← primePowerError_eq_psi_sub_theta]
    dsimp only [P, A, mangoldtCharacterPrefix]
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm (weight k)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (DirichletCharacter.norm_le_one χ⁻¹ (k : ZMod q)) (abs_nonneg (Λ k-weight k))
  have hMM : ‖M-M'‖ ≤ 1 := by
    by_cases he : χ=1 <;> simp [M, M', he]
  have hcenter : centeredPrimeArcTransform q j 0 ((j : ℂ)+1) χ = P - M' := by
    simp [centeredPrimeArcTransform, weightedArcCharacterSum, E, P, M', MulChar.star_apply']
  have htri : ‖P-M'‖ ≤ ‖A-M‖ + (Chebyshev.psi j - Chebyshev.theta j) + 1 := calc
    ‖P-M'‖ = ‖((A-M)+(P-A))+(M-M')‖ := by congr 1; ring
    _ ≤ ‖(A-M)+(P-A)‖ + ‖M-M'‖ := norm_add_le _ _
    _ ≤ (‖A-M‖ + ‖P-A‖) + ‖M-M'‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl hPA) hMM
  simpa only [hcenter, A, M, inv_eq_one] using htri

theorem centeredPrimeArcTransform_prefix_of_psi (q : ℕ) [NeZero q] (n : ℕ) (D : ℝ)
    (hψ : ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ n,
      ‖mangoldtCharacterPrefix q j χ - (if χ=1 then (j:ℂ) else 0)‖ ≤ D) :
    ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤
        D + 2*Real.sqrt n*Real.log n + 1 := by
  intro χ j hj
  apply (centeredPrimeArcTransform_le_psi_error q j χ).trans
  refine add_le_add (add_le_add (hψ χ⁻¹ j hj) ?_) le_rfl
  rw [← primePowerError_eq_psi_sub_theta]
  apply le_trans _ (primePowerError_le n)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun k _ _ => abs_nonneg (Λ k - weight k))


theorem centeredPrimeArcTransform_grh_scale_of_psi (q : ℕ) [NeZero q] {n : ℕ}
    (hn : 2 ≤ n) (C : ℝ)
    (hψ : ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ n,
      ‖mangoldtCharacterPrefix q j χ - (if χ=1 then (j:ℂ) else 0)‖ ≤
        C * Real.sqrt n * Real.log (2*(n:ℝ)^2)^2) :
    ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤
        (C+3)*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 := by
  intro χ j hj
  let L := Real.log (2*(n:ℝ)^2)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
  have hL : 1 ≤ L := by
    have htwo := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at htwo
    have hh : Real.log (2*2) ≤ L :=
      Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg ((n:ℝ)-2)])
    rw [Real.log_mul (by norm_num) (by norm_num)] at hh
    linarith
  have hlog : Real.log n ≤ L :=
    Real.log_le_log (by linarith) (by nlinarith [sq_nonneg ((n:ℝ)-2)])
  have hsq : L ≤ L^2 := by nlinarith [sq_nonneg (L-1)]
  have hterm : Real.sqrt n * Real.log n ≤ Real.sqrt n * L^2 :=
    mul_le_mul_of_nonneg_left (hlog.trans hsq) (Real.sqrt_nonneg _)
  have hone : 1 ≤ Real.sqrt n * L^2 := one_le_mul_of_one_le_of_one_le hs (hL.trans hsq)
  have he := centeredPrimeArcTransform_prefix_of_psi q n _ hψ χ j hj
  change _ ≤ (C+3)*Real.sqrt n*L^2
  change _ ≤ C*Real.sqrt n*L^2 + 2*Real.sqrt n*Real.log n + 1 at he
  nlinarith


theorem centeredPrimeArcTransform_prefix_of_standard_psi (q : ℕ) [NeZero q]
    {n : ℕ} (hn : 2 ≤ n) (hq : q ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ χ : DirichletCharacter ℂ q, ∀ j : ℕ, 1 ≤ j → j ≤ n →
      ‖mangoldtCharacterPrefix q j χ - (if χ=1 then (j:ℂ) else 0)‖ ≤
        C * Real.sqrt j * Real.log (2*(j:ℝ)*q)^2) :
    ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤
        (C+3)*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 := by
  apply centeredPrimeArcTransform_grh_scale_of_psi q hn C
  intro χ j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp [mangoldtCharacterPrefix]
    positivity
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hjpos
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hjn : (j:ℝ) ≤ n := by exact_mod_cast hj
  have hqn : (q:ℝ) ≤ n := by exact_mod_cast hq
  have hlow : 1 ≤ 2*(j:ℝ)*q := one_le_mul_of_one_le_of_one_le (by linarith) hq1
  have harg : 2*(j:ℝ)*q ≤ 2*(n:ℝ)^2 := by
    rw [sq, ← mul_assoc]
    gcongr
  have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hlow) harg
  apply (hψ χ j hjpos hj).trans
  gcongr
  exact Real.log_nonneg hlow

end GoldbachPartial