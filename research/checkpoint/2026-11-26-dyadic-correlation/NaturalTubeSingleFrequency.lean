import NaturalTubeShortModes

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

private theorem singleMode_harmonic (R : ℕ) :
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


private theorem singleMode_multiple_reciprocals (R Q d : ℕ) (hd : 0<d) :
    ∑ j ∈ Ico R Q, (if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0) ≤ 1+Real.log Q := by
  rw [←sum_filter]
  apply le_trans _ (singleMode_harmonic Q)
  let s := (Ico R Q).filter (fun j => d∣j+1)
  let u (j:ℕ) := (j+1)/d-1
  have hdiv (j:ℕ) (hj:j∈s) :
      0<(j+1)/d ∧ d*((j+1)/d)=j+1 ∧ j<Q := by
    obtain ⟨hj,hjd⟩ := mem_filter.mp hj
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hjd) hd,Nat.mul_div_cancel' hjd,(mem_Ico.mp hj).2⟩
  apply sum_le_sum_of_injOn u
  · intro i hi j hj he
    obtain ⟨hi',him,_⟩ := hdiv _ hi
    obtain ⟨hj',hjm,_⟩ := hdiv _ hj
    dsimp only [u] at he
    have hh : (i+1)/d=(j+1)/d := by omega
    rw [hh] at him
    omega
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    obtain ⟨hpos,_,hQ⟩ := hdiv _ hj
    have hle := Nat.div_le_self (j+1) d
    exact mem_range.mpr (by dsimp only [u]; omega)
  · intro j hj
    obtain ⟨hj0,he,_⟩ := hdiv _ hj
    dsimp only [u]
    rw [Nat.sub_add_cancel (by omega : 1≤(j+1)/d)]
    have hd' : (0:ℝ)<d := by exact_mod_cast hd
    have hk' : (0:ℝ)<((j+1)/d:ℕ) := by exact_mod_cast hj0
    have hprod : (d:ℝ)*(((j+1)/d:ℕ):ℝ) = ((j+1:ℕ):ℝ) := by exact_mod_cast he
    rw [←hprod]
    field_simp
    exact le_rfl
  · intro k _ _
    positivity

theorem naturalTubeFourierMode_divisor_bound (R Q M : ℕ) (hsep : 2*Q<M) (h : ℤ) (hh : h≠0) :
    ‖naturalTubeFourierMode R Q M h‖ ≤
      (2/(M:ℝ))*(1+Real.log Q)*(h.natAbs.divisors.card:ℝ) := by
  have hn : 0<h.natAbs := Int.natAbs_pos.mpr hh
  have hrow (q:ℕ) (hq:0<q) : |(dyadicRamanujanDivisor h.natAbs q:ℝ)|/(q:ℝ) ≤
      ∑ d ∈ h.natAbs.divisors, if d∣q then (d:ℝ)/(q:ℝ) else 0 := by
    have he : (q.gcd h.natAbs).divisors = h.natAbs.divisors.filter (fun d => d∣q) := by
      ext d
      simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
      simp [hn.ne',(Nat.gcd_pos_of_pos_left _ hq).ne',and_comm]
    unfold dyadicRamanujanDivisor
    push_cast
    rw [←sum_filter,←sum_div,he]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [abs_mul,show |(d:ℝ)|=(d:ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q/d)))
  apply (naturalTubeFourierMode_ramanujan_bound R Q M hsep h).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ j ∈ Ico R Q, ∑ d ∈ h.natAbs.divisors, if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0 :=
      sum_le_sum fun j _ => hrow (j+1) (Nat.succ_pos j)
    _ = ∑ d ∈ h.natAbs.divisors, ∑ j ∈ Ico R Q, if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ h.natAbs.divisors, (1+Real.log Q) :=
      sum_le_sum fun d hd => singleMode_multiple_reciprocals R Q d (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp [nsmul_eq_mul,mul_comm,mul_add]

end GoldbachPartial