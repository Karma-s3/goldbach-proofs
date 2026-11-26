import PrimeArcModelBounds

namespace GoldbachPartial

open Finset MeasureTheory

private theorem harmonicSuccessors_le (R : ℕ) :
    (∑ j ∈ range R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    by_cases h : R=0
    · subst R; norm_num
    · have hR : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(R:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hR)
      rw [Real.log_div hp.ne' hR.ne',inv_div] at hl
      have he : 1-(R:ℝ)/(R+1) = ((R:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]

theorem primeArc_signed_Ico_of_prefix (n Y R : ℕ) {ρ D s : ℝ}
    (hρ : 0≤ρ) (hhalf : ρ≤1/2) (hD : 0≤D) (hs : 0<s)
    (hp : ∀ j ∈ Ico Y R, ∀ χ, ∀ k ≤ n,
      ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ D) :
    ‖∑ j ∈ Ico Y R, primeArcSignedChange (j+1) n ρ‖ ≤
      (1+s)*(4*ρ*(R:ℝ)^2*(D^2*(1+2*Real.pi*n*ρ)^2+(Real.log R)^2)) +
      s⁻¹*((n:ℝ)+1)*(1+(Nat.log 2 R:ℝ))*(1+Real.log R) := by
  let J := Ico Y R
  let U := (D*(1+2*Real.pi*n*ρ))^2+(Real.log R)^2
  let K := 1+(Nat.log 2 R:ℝ)
  have hU : 0≤U := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hq {j : ℕ} (hj : j∈J) : j+1 ≤ R := (mem_Ico.mp hj).2
  have he : (∑ j ∈ J, 4*ρ*((j+1).totient:ℝ)*
      ((D*(1+2*Real.pi*n*ρ))^2+(Real.log (j+1:ℕ))^2)) ≤ 4*ρ*(R:ℝ)^2*U := calc
    _ ≤ ∑ _j ∈ J, 4*ρ*(R:ℝ)*U := by
      refine sum_le_sum fun j hj => ?_
      have ht : ((j+1).totient:ℝ) ≤ R :=
        by exact_mod_cast (Nat.totient_le _).trans (hq hj)
      have hpos : (0:ℝ)<(j+1:ℕ) := by positivity
      have hlog := Real.log_le_log hpos (show ((j+1:ℕ):ℝ)≤R by exact_mod_cast hq hj)
      have hlog0 : 0≤Real.log (j+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 j)
      dsimp only [U]
      gcongr
    _ = ((R-Y:ℕ):ℝ)*(4*ρ*(R:ℝ)*U) := by simp [J,nsmul_eq_mul]
    _ ≤ (R:ℝ)*(4*ρ*(R:ℝ)*U) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le R Y) (by positivity)
    _ = _ := by ring
  have hi : (∑ j ∈ J, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
    apply le_trans _ (harmonicSuccessors_le R)
    exact sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.mpr (mem_Ico.mp hj).2) (fun _ _ _ => by positivity)
  have hm : (∑ j ∈ J, ((j+1).totient:ℝ)*
      ∫ t in -ρ..ρ, ‖geometricPrimeArcModel (j+1) n t‖^2) ≤
      (((n:ℝ)+1)*K)*(1+Real.log R) := calc
    _ ≤ ∑ j ∈ J, (((n:ℝ)+1)*K)*((j+1:ℕ):ℝ)⁻¹ := by
      refine sum_le_sum fun j hj => ?_
      have hφ : (0:ℝ)<(j+1).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos j)
      have hq0 : (0:ℝ)<(j+1:ℕ) := by positivity
      have hratio : ((j+1:ℕ):ℝ) ≤ K*((j+1).totient:ℝ) := by
        dsimp only [K]
        rw [add_comm (1:ℝ) (Nat.log 2 R:ℝ)]
        exact_mod_cast (nat_le_totient_mul_log2_succ (Nat.succ_pos j)).trans
          (Nat.mul_le_mul_right (j+1).totient
            (Nat.add_le_add_right (Nat.log_mono_right (b:=2) (hq hj)) 1))
      have hrec : 1/((j+1).totient:ℝ) ≤ K/((j+1:ℕ):ℝ) :=
        (div_le_div_iff₀ hφ hq0).mpr (by simpa only [one_mul] using hratio)
      apply (geometricPrimeArcModel_window_energy (j+1) n hρ hhalf
        (principal_unitGauss_norm_le_one _)).trans
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        mul_le_mul_of_nonneg_left hrec (show 0≤(n:ℝ)+1 by positivity)
    _ = (((n:ℝ)+1)*K)*∑ j ∈ J, ((j+1:ℕ):ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
  apply (primeArc_signed_band_of_prefix J n (fun _ => ρ) (fun _ => D)
    (fun _ _ => hρ) (fun _ _ => hD) hs hp).trans
  have h := add_le_add (mul_le_mul_of_nonneg_left he (show 0≤1+s by positivity))
    (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs.le))
  simpa only [U,K,mul_pow,mul_assoc] using h

end GoldbachPartial