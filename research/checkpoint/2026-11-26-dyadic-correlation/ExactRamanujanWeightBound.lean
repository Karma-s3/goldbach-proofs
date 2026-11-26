import ExactRamanujanWeights
import ResonantModelEnergy
open Finset
namespace GoldbachPartial

private theorem weightTotientIcc (R : ℕ) :
    (∑ m ∈ Icc 1 R, 1/(m.totient : ℝ)) ≤ 4 * (1 + Real.log R) := by
  have he : (∑ m ∈ Icc 1 R, 1/(m.totient : ℝ)) =
      ∑ j ∈ Ico 0 R, 1/((j+1).totient : ℝ) := by
    apply sum_bij (fun m _ => m-1)
    · intro m hm
      obtain ⟨h1,h2⟩ := mem_Icc.mp hm
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro m hm m' hm' hh
      have h := (mem_Icc.mp hm).1
      have h' := (mem_Icc.mp hm').1
      omega
    · intro j hj
      have hr := (mem_Ico.mp hj).2
      exact ⟨j+1, mem_Icc.mpr ⟨by omega,by omega⟩, by omega⟩
    · intro m hm
      rw [Nat.sub_add_cancel (mem_Icc.mp hm).1]
  exact he.trans_le (modelTotientReciprocal_sum 0 R)

private theorem weight_divisor_mass (d : ℕ) (hd : 0<d) :
    (d:ℝ)/d.totient ≤ 2 * ∑ v ∈ d.divisors, 1/(v.totient:ℝ) := by
  apply (model_totient_ratio_le_divisor_reciprocals _ hd).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine sum_le_sum fun v hv => ?_
  have hv' : 0<v := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hv).1 hd
  rw [← one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast Nat.totient_pos.mpr hv')
    (by exact_mod_cast Nat.totient_le v)

private theorem weight_coprime_divisor_product (R d : ℕ) (hd : 0<d) :
    (∑ j ∈ (Icc 1 (R/d)).filter (fun j => j.Coprime d), 1/(j.totient:ℝ)) *
    (∑ v ∈ d.divisors, 1/(v.totient:ℝ)) ≤ ∑ m ∈ Icc 1 R, 1/(m.totient:ℝ) := by
  let J := (Icc 1 (R/d)).filter (fun j => j.Coprime d)
  let V := d.divisors
  let f (z : ℕ × ℕ) := z.1 * z.2
  change (∑ j ∈ J, _) * (∑ v ∈ V, _) ≤ _
  rw [sum_mul_sum]
  change (∑ j ∈ J, ∑ v ∈ V, _) ≤ _
  rw [← sum_product (f := fun p : ℕ × ℕ => 1/(p.1.totient:ℝ) * (1/(p.2.totient:ℝ)))]
  apply sum_le_sum_of_injOn f
  · intro x hx y hy hxy
    obtain ⟨hxj,hxv⟩ := mem_product.mp hx
    obtain ⟨hyj,hyv⟩ := mem_product.mp hy
    have h₁ := Nat.gcd_mul_of_coprime_of_dvd (mem_filter.mp hxj).2 (Nat.mem_divisors.mp hxv).1
    have h₂ := Nat.gcd_mul_of_coprime_of_dvd (mem_filter.mp hyj).2 (Nat.mem_divisors.mp hyv).1
    have hv : x.2=y.2 := h₁.symm.trans ((congrArg (fun m => m.gcd d) hxy).trans h₂)
    apply Prod.ext _ hv
    change x.1*x.2 = y.1*y.2 at hxy
    rw [← hv] at hxy
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hxv).1 hd) hxy
  · intro b hb
    obtain ⟨⟨j,v⟩,hx,rfl⟩ := mem_image.mp hb
    obtain ⟨hj,hv⟩ := mem_product.mp hx
    obtain ⟨hjp,hjR⟩ := mem_Icc.mp (mem_filter.mp hj).1
    have hvd := (Nat.mem_divisors.mp hv).1
    have hvpos := Nat.pos_of_dvd_of_pos hvd hd
    exact mem_Icc.mpr ⟨Nat.mul_pos hjp hvpos,
      (Nat.mul_le_mul_left j (Nat.le_of_dvd hd hvd)).trans ((Nat.le_div_iff_mul_le hd).mp hjR)⟩
  · rintro ⟨j,v⟩ hx
    obtain ⟨hj,hv⟩ := mem_product.mp hx
    have hc := (mem_filter.mp hj).2
    have hcv := Nat.Coprime.coprime_dvd_right (Nat.mem_divisors.mp hv).1 hc
    simp [f, Nat.totient_mul hcv, one_div, mul_comm]
  · intro m _ _
    positivity

/-- Uniform logarithmic bound for the finite inverse Ramanujan weights. -/
theorem exact_inverse_weight_sum_le (R d : ℕ) (hd : 0 < d) :
  |(d:ℝ)*∑ j ∈ Icc 1 (R/d), (ArithmeticFunction.moebius j:ℝ) *
    ((ArithmeticFunction.moebius (j*d):ℝ)/((j*d).totient:ℝ))| ≤ 8*(1+Real.log R) := by
  let J := (Icc 1 (R/d)).filter (fun j => j.Coprime d)
  let V := d.divisors
  let U := ∑ j ∈ J, 1/(j.totient:ℝ)
  let W := ∑ v ∈ V, 1/(v.totient:ℝ)
  have hU : 0 ≤ U := sum_nonneg fun _ _ => by positivity
  have hφ : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hm (k : ℕ) : |(ArithmeticFunction.moebius k:ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  have hψ :
      |∑ j ∈ Icc 1 (R/d), (ArithmeticFunction.moebius j:ℝ) *
        ((ArithmeticFunction.moebius (j*d):ℝ)/((j*d).totient:ℝ))| ≤ U/d.totient := by
    apply (abs_sum_le_sum_abs ..).trans
    dsimp only [U, J]
    rw [sum_div, sum_filter]
    refine sum_le_sum fun j hj => ?_
    by_cases hc : j.Coprime d
    · rw [ite_eq_left hc, abs_mul, abs_div, abs_of_nonneg (show (0:ℝ)≤(j*d).totient by positivity), Nat.totient_mul hc,
        Nat.cast_mul]
      have hjp := (mem_Icc.mp hj).1
      have htj : 0 < (j.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hjp
      calc
        _ ≤ 1 * (1 / ((j.totient:ℝ)*d.totient)) :=
          mul_le_mul (hm j) (div_le_div_of_nonneg_right (hm (j*d)) (by positivity))
            (by positivity) (by norm_num)
        _ = _ := by ring
    · have hs : ¬Squarefree (j*d) := fun h => hc (Nat.coprime_of_squarefree_mul h)
      rw [ite_eq_right hc, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simp
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (d:ℝ)*(U/d.totient) := mul_le_mul_of_nonneg_left hψ (Nat.cast_nonneg _)
    _ = U * ((d:ℝ)/d.totient) := by ring
    _ ≤ U * (2*W) := mul_le_mul_of_nonneg_left (weight_divisor_mass _ hd) hU
    _ = 2*(U*W) := by ring
    _ ≤ 2*(∑ m ∈ Icc 1 R, 1/(m.totient:ℝ)) :=
      mul_le_mul_of_nonneg_left (weight_coprime_divisor_product _ _ hd) (by norm_num)
    _ ≤ 2*(4*(1+Real.log R)) := mul_le_mul_of_nonneg_left (weightTotientIcc _) (by norm_num)
    _ = _ := by ring

theorem exactRamanujanWeight_abs_le_log (R d : ℕ) :
    |exactRamanujanWeight R d| ≤ 8 * (1 + Real.log R) := by
  by_cases hd : d = 0
  · subst d
    simp only [exactRamanujanWeight, Nat.cast_zero, zero_mul, abs_zero]
    by_cases hR : R = 0
    · simp [hR]
    · have hl : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hR)
      linarith
  · rw [exactRamanujanWeight_eq_sum _ _ (Nat.pos_of_ne_zero hd)]
    exact exact_inverse_weight_sum_le _ _ (Nat.pos_of_ne_zero hd)

end GoldbachPartial