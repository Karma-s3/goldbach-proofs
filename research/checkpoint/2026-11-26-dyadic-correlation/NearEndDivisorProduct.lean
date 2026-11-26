import TrueMixedFrequencies
import DivisorSquareMean

namespace GoldbachPartial
open Finset

def nearEndDivisorIndices (n J : ℕ) : Finset ℕ := Icc 1 J ∪ Ico (n-J) n

theorem nearEndDivisorIndices_inside {n J : ℕ} (hJ : J<n) {k : ℕ}
    (hk : k∈nearEndDivisorIndices n J) : 0<k ∧ k<n := by
  rcases mem_union.mp hk with h|h
  · obtain ⟨h1,h2⟩ := mem_Icc.mp h
    omega
  · obtain ⟨h1,h2⟩ := mem_Ico.mp h
    omega

private theorem nearEnd_reflect {n J : ℕ} (hJ : J<n) (f : ℕ→ℝ) :
    (∑ k∈Icc 1 J,f (n-k)) = ∑ k∈Ico (n-J) n,f k := by
  apply sum_bij (fun k _ => n-k)
  · intro k hk
    obtain ⟨h0,h1⟩ := mem_Icc.mp hk
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  · intro i hi j hj h
    have hi' := (mem_Icc.mp hi).2
    have hj' := (mem_Icc.mp hj).2
    omega
  · intro k hk
    obtain ⟨h0,h1⟩ := mem_Ico.mp hk
    exact ⟨n-k,mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro k _
    rfl

theorem nearEndDivisorProduct
    {n J : ℕ} (hJ : J<n) :
    (∑ k∈nearEndDivisorIndices n J,(k.divisors.card:ℝ)*((n-k).divisors.card:ℝ)) ≤
      2*Real.sqrt n*Real.sqrt J*(1+Real.log n)^3 := by
  let τ := fun k : ℕ => (k.divisors.card:ℝ)
  let F := fun k : ℕ => τ k * τ (n-k)
  let S := Icc 1 J
  let U := Ico (n-J) n
  let L := (1+Real.log n)^3
  have hL : 0≤L := pow_nonneg (by linarith [Real.log_natCast_nonneg n]) 3
  have hrev : (∑ k∈U,F k) = ∑ k∈S,F k := by
    rw [←nearEnd_reflect hJ F]
    apply sum_congr rfl
    intro k hk
    have hkn := ((mem_Icc.mp hk).2).trans hJ.le
    dsimp only [F]
    rw [Nat.sub_sub_self hkn,mul_comm]
  have htot : (∑ k∈nearEndDivisorIndices n J,F k) ≤ 2*∑ k∈S,F k := by
    have hsplit := sum_union_inter (s₁:=S) (s₂:=U) (f:=F)
    have hnon : 0≤∑ k∈S∩U,F k := sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    change (∑ k∈S∪U,F k) ≤ _
    rw [hrev] at hsplit
    linarith only [hsplit,hnon]
  have hlow : ∑k∈S,τ k^2 ≤ (J:ℝ)*L := by
    apply (divisor_square_mean_bound J).trans
    rcases Nat.eq_zero_or_pos J with rfl|hj
    · simp
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg J])
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast hj) (by exact_mod_cast hJ.le)) _
  have hu : U⊆ Icc 1 n := by
    intro k hk
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hk
    exact mem_Icc.mpr ⟨by omega,h₂.le⟩
  have hhi : ∑k∈S,τ (n-k)^2 ≤ (n:ℝ)*L := by
    rw [show (∑k∈S,τ (n-k)^2) = ∑k∈U,τ k^2 from nearEnd_reflect hJ (fun k => τ k^2)]
    exact (sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ => sq_nonneg _)).trans (divisor_square_mean_bound n)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S τ (fun k => τ (n-k))
  change _ ≤ _ at hcs
  apply htot.trans
  calc
    _ ≤ 2*(Real.sqrt ((J:ℝ)*L)*Real.sqrt ((n:ℝ)*L)) :=
      mul_le_mul_of_nonneg_left (hcs.trans
        (mul_le_mul (Real.sqrt_le_sqrt hlow) (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg J),Real.sqrt_mul (Nat.cast_nonneg n)]
      have he := Real.sq_sqrt hL
      change _ = 2*Real.sqrt n*Real.sqrt J*L
      linear_combination (2*Real.sqrt n*Real.sqrt J)*he

theorem trueMixedFrequencyBand_nearEnd_bound {n J : ℕ} (D R Q : ℕ) (hJ : J<n)
    {B : ℝ} (hB : 0≤B)
    (hT : ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤B) :
    ‖trueMixedFrequencyBand n D R Q (nearEndDivisorIndices n J)‖ ≤
      (4/(3*(Q:ℝ))*Real.log n*B*(1+Real.log Q))*
        (2*Real.sqrt n*Real.sqrt J*(1+Real.log n)^3) := by
  apply (trueMixedFrequencyBand_nonzero_bound D R Q _ (fun _ hk => nearEndDivisorIndices_inside hJ hk) hB hT).trans
  apply mul_le_mul_of_nonneg_left (nearEndDivisorProduct hJ)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.log_natCast_nonneg _)) hB)
    (le_add_of_nonneg_of_le (by norm_num) (Real.log_natCast_nonneg _))

end GoldbachPartial