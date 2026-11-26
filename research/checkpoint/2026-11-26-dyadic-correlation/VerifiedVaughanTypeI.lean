import VerifiedPrimitiveSieveTransfer
import PinnedUpstream316

namespace GoldbachPartial
open Finset
open scoped Classical

private theorem typeI_shift (T : ℕ) (g : ℕ → ℂ) :
    (∑ n ∈ Icc 1 T, g n) = ∑ k ∈ range T, g (k+1) := by
  rw [show Icc 1 T = Ico 1 (T+1) by ext n; simp, sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Partial summation with the complete periods removed before taking norms. -/
theorem nonprincipal_monotone_prefix {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (w : ℕ → ℝ) (hw : Monotone w) (hpos : ∀ n, 0 ≤ w n) (T : ℕ) :
    ‖∑ n ∈ Icc 1 T, (w n : ℂ)*χ (n:ZMod q)‖ ≤ 2*((q:ℝ)+1)*w (T+1) := by
  let W (k : ℕ) := w (k+1)
  let F (k : ℕ) := χ ((k+1:ℕ):ZMod q)
  have hP (K : ℕ) : ‖∑ k ∈ range K, F k‖ ≤ (q:ℝ)+1 := by
    rw [← typeI_shift K (fun n => χ (n:ZMod q))]
    exact OAI.LargePrimeGaps.char_sum_Icc_norm_le hχ K
  have hwW : Monotone W := fun _ _ h => hw (Nat.add_le_add_right h 1)
  rw [typeI_shift]
  have hp := sum_range_by_parts W F T
  change ‖∑ k ∈ range T, (W k:ℂ) * F k‖ ≤ _
  simp only [Complex.real_smul] at hp
  rw [hp]
  refine (norm_sub_le _ _).trans ?_
  have htop : ‖(W (T-1):ℂ) * ∑ k ∈ range T, F k‖ ≤ W (T-1)*((q:ℝ)+1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    exact mul_le_mul_of_nonneg_left (hP T) (hpos _)
  have hd (i : ℕ) : 0 ≤ W (i+1) - W i := sub_nonneg.mpr (hwW (by omega))
  have ht : ‖∑ i ∈ range (T-1), ((W (i+1)-W i:ℝ):ℂ)*(∑ j ∈ range (i+1), F j)‖ ≤
      (W (T-1)-W 0)*((q:ℝ)+1) := by
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_range_sub W, sum_mul]
    apply sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd i)]
    exact mul_le_mul_of_nonneg_left (hP (i+1)) (hd i)
  have hle := mul_le_mul_of_nonneg_right (hwW (Nat.sub_le T 1)) (show (0:ℝ)≤q+1 by positivity)
  have h0 := mul_nonneg (hpos 1) (show (0:ℝ)≤q+1 by positivity)
  change _ ≤ 2*((q:ℝ)+1)*W T
  change 0 ≤ W 0*((q:ℝ)+1) at h0
  linarith only [htop,ht,hle,h0]

noncomputable def typeICharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ)
    (D : Finset ℕ) (c : ℕ → ℂ) (w : ℕ → ℝ) : ℂ :=
  ∑ d ∈ D, c d * χ (d:ZMod q) * ∑ n ∈ Icc 1 (X/d), (w n:ℂ)*χ (n:ZMod q)

theorem typeI_monotone_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (X : ℕ) (D : Finset ℕ) (c : ℕ → ℂ) (w : ℕ → ℝ)
    (hw : Monotone w) (hpos : ∀ n, 0 ≤ w n) :
    ‖typeICharacterSum χ X D c w‖ ≤ (2*((q:ℝ)+1)*w (X+1)) * ∑ d ∈ D, ‖c d‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro d _
  rw [norm_mul,norm_mul]
  have h1 : ‖c d‖ * ‖χ (d:ZMod q)‖ ≤ ‖c d‖ := by
    simpa using mul_le_mul_of_nonneg_left (χ.norm_le_one (d:ZMod q)) (norm_nonneg (c d))
  have h2 := (nonprincipal_monotone_prefix hχ w hw hpos (X/d)).trans
    (mul_le_mul_of_nonneg_left (hw (Nat.add_le_add_right (Nat.div_le_self X d) 1)) (by positivity))
  simpa only [mul_comm (‖c d‖)] using mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

private theorem natLog_mono : Monotone (fun n : ℕ => Real.log (n:ℝ)) := by
  intro m n h
  by_cases hm : m=0
  · simp [hm]
    exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast h)

theorem typeI_log_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (X : ℕ) (D : Finset ℕ) (c : ℕ → ℂ) :
    ‖typeICharacterSum χ X D c (fun n => Real.log n)‖ ≤
      (2*((q:ℝ)+1)*Real.log (X+1:ℕ)) * ∑ d ∈ D, ‖c d‖ :=
  typeI_monotone_bound hχ X D c _ natLog_mono Real.log_natCast_nonneg

end GoldbachPartial