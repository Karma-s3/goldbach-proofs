import NaturalPrimeGapTubeUnion

namespace GoldbachPartial
open Finset Filter MeasureTheory

private theorem reciprocalSquares_two (Q : ℕ) :
    ∑ j ∈ range Q, 1/(((j+2:ℕ):ℝ)^2) ≤ 3/4 := by
  have h (k:ℕ) : ∑ j ∈ range (k+1), 1/(((j+2:ℕ):ℝ)^2) ≤ 3/4-1/((k+2:ℕ):ℝ) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ]
      apply (add_le_add ih le_rfl).trans
      push_cast
      have ha : (0:ℝ)<k+2 := by positivity
      have hb : (0:ℝ)<k+1+2 := by positivity
      field_simp
      nlinarith only [Nat.cast_nonneg (α:=ℝ) k]
  cases Q with
  | zero => norm_num
  | succ k => exact (h k).trans (sub_le_self _ (by positivity))

private theorem totient_reciprocal_budget {q Q:ℕ} (hq : 0<q) (hqQ:q≤Q) :
    1 ≤ (q.totient:ℝ)/q + ∑ j ∈ range Q, if j+2 ∣ q then 1/((j+2:ℕ):ℝ) else 0 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  let f (d:ℕ) := ((q/d).totient:ℝ)/(q:ℝ)
  have ht : ∑ d ∈ q.divisors, f d = 1 := by
    dsimp only [f]
    rw [←sum_div]
    have hx : (∑ d ∈ q.divisors, (q/d).totient) = q := (Nat.sum_div_divisors q Nat.totient).trans (Nat.sum_totient q)
    exact (congrArg (fun a:ℝ => a/(q:ℝ)) (by exact_mod_cast hx : (∑ d ∈ q.divisors, ((q/d).totient:ℝ))=(q:ℝ))).trans (div_self hq'.ne')
  have h₁ := add_sum_erase q.divisors f (Nat.one_mem_divisors.mpr hq.ne')
  conv_lhs => rw [←ht,←h₁]
  simp only [f,Nat.div_one]
  apply add_le_add le_rfl
  apply sum_le_sum_of_injOn (fun d:ℕ => d-2)
  · intro d hd e he heq
    dsimp only at heq
    have hd' := mem_erase.mp hd
    have he' := mem_erase.mp he
    have hd0 := Nat.pos_of_mem_divisors hd'.2
    have he0 := Nat.pos_of_mem_divisors he'.2
    omega
  · intro j hj
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    have hd' := mem_erase.mp hd
    have hpos := Nat.pos_of_mem_divisors hd'.2
    have hle := Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd'.2)
    exact mem_range.mpr (by omega)
  · intro d hd
    have hd' := mem_erase.mp hd
    have hpos := Nat.pos_of_mem_divisors hd'.2
    have hdiv := Nat.dvd_of_mem_divisors hd'.2
    rw [Nat.sub_add_cancel (by omega : 2≤d),ite_eq_left hdiv]
    have hd0 : (0:ℝ)<d := by exact_mod_cast hpos
    apply (div_le_div_iff₀ hq' hd0).mpr
    rw [one_mul]
    exact_mod_cast (Nat.mul_le_mul_right d (Nat.totient_le (q/d))).trans_eq (Nat.div_mul_cancel hdiv)
  · intro j _ _
    split_ifs <;> positivity

theorem totient_ratio_sum_lower (Q:ℕ) :
    (Q:ℝ)/4 ≤ ∑ j ∈ range Q, ((j+1).totient:ℝ)/((j+1:ℕ):ℝ) := by
  let loss (d j:ℕ) : ℝ := if d+2 ∣ j+1 then 1/((d+2:ℕ):ℝ) else 0
  have hcol (d:ℕ) : ∑ j ∈ range Q, loss d j ≤ Q*(1/(((d+2:ℕ):ℝ)^2)) := by
    dsimp only [loss]
    rw [←sum_filter,Finset.sum_const,Nat.card_multiples,nsmul_eq_mul]
    have hd : (0:ℝ)<(d+2:ℕ) := by positivity
    calc
      _ ≤ ((Q:ℝ)/((d+2:ℕ):ℝ))*(1/((d+2:ℕ):ℝ)) := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
      _ = _ := by ring
  have he : ∑ j ∈ range Q, ∑ d ∈ range Q, loss d j ≤ (Q:ℝ)*(3/4) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ d ∈ range Q, (Q:ℝ)*(1/(((d+2:ℕ):ℝ)^2)) := sum_le_sum fun d _ => hcol d
      _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (reciprocalSquares_two Q) (by positivity)
  have hrow : ∑ _j ∈ range Q, (1:ℝ) ≤
      ∑ j ∈ range Q, (((j+1).totient:ℝ)/((j+1:ℕ):ℝ)+∑ d ∈ range Q, loss d j) :=
    sum_le_sum fun j hj => totient_reciprocal_budget (Nat.succ_pos j) (mem_range.mp hj)
  rw [sum_add_distrib] at hrow
  simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at hrow
  linarith only [hrow,he]

theorem naturalTubeUnion_realVolume_eq (R Q M:ℕ) (hsep : 2*Q<M) :
    volume.real (naturalTubeUnion R Q M) =
      (2/(M:ℝ))*∑ j ∈ Ico R Q, ((j+1).totient:ℝ)/((j+1:ℕ):ℝ) := by
  have he := naturalTubeUnion_integral_rows R Q M hsep (fun _:ℝ => (1:ℂ)) continuous_const
  rw [setIntegral_const] at he
  simp only [intervalIntegral.integral_const,sub_neg_eq_add,ZMod.card_units_eq_totient,
    sum_const,card_univ,nsmul_eq_mul,Complex.real_smul, mul_one] at he
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  apply Complex.ofReal_injective
  rw [he]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [mul_inv,div_eq_mul_inv]
  ring

theorem naturalTubeUnion_realVolume_ge_twelfth {R Q : ℕ} (hQ:0<Q) (hR : 8*R≤Q) :
    (1:ℝ)/12 ≤ volume.real (naturalTubeUnion R Q (3*Q)) := by
  rw [naturalTubeUnion_realVolume_eq R Q (3*Q) (by omega)]
  have hq0 : (0:ℝ)<Q := by exact_mod_cast hQ
  have hr : 8*(R:ℝ)≤Q := by exact_mod_cast hR
  have hrem : ∑ j ∈ range R, ((j+1).totient:ℝ)/((j+1:ℕ):ℝ) ≤ (R:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ range R, (1:ℝ) := by
        apply sum_le_sum
        intro j _
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.totient_le _
      _ = _ := by simp
  rw [sum_Ico_eq_sub _ (by omega : R≤Q)]
  have hlo := totient_ratio_sum_lower Q
  push_cast at hrem hlo ⊢
  calc
    (1:ℝ)/12 = 2/(3*(Q:ℝ))*((Q:ℝ)/8) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hlo,hrem,hr]) (by positivity)


/-- The disjoint natural arcs remaining above the logarithmically reduced square-root cutoff
occupy at least a twelfth of the unit interval for every sufficiently large n. -/
theorem terminalNaturalTube_realVolume_ge_twelfth :
    ∀ᶠ n : ℕ in atTop, (1:ℝ)/12 ≤ volume.real
      (naturalTubeUnion (terminalPrimeArcCutoff n) (naturalTubeScale n) (3*naturalTubeScale n)) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hlog,eventually_ge_atTop (1:ℕ)] with n h hn
  change 1≤Real.log (n:ℝ) at h
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hQ : 0<naturalTubeScale n := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  apply naturalTubeUnion_realVolume_ge_twelfth hQ
  apply Nat.le_floor
  let L := terminalPrimeArcLog n
  have hL : 2≤L := by dsimp only [L,terminalPrimeArcLog]; linarith
  have hL0 : 0<L := by linarith
  have h8 : 8≤L^5 := by
    have hu := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hL 5
    norm_num at hu
    linarith
  have hcut : (terminalPrimeArcCutoff n:ℝ) ≤ Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  push_cast
  calc
    8*(terminalPrimeArcCutoff n:ℝ) ≤ 8*(Real.sqrt n/L^5) := by gcongr
    _ ≤ _ := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hL0 5)).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg (n:ℝ))

end GoldbachPartial