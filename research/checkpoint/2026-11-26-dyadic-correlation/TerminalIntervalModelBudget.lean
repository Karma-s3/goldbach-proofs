import DeepPrimeShell
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GoldbachPartial
open Filter

private theorem project_divisor_count_fourth_root {n : ℕ} (hn : 0<n) :
    (n.divisors.card:ℝ) ≤ 4096*(n:ℝ)^(1/4:ℝ) := by
  have hx : (0:ℝ) < n := by exact_mod_cast hn
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4≠0)).mp
  calc
    _ ≤ (2:ℝ)^48*n := by exact_mod_cast divisor_count_fourth_le n
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hx.le]; norm_num

private theorem shell_log_two_bound {R n : ℕ} (hn : 0<n) (hR : R≤n) (hL : 1≤Real.log (n:ℝ)) :
    ((Nat.log 2 R:ℕ):ℝ)+1 ≤ 3*Real.log n := by
  have hi : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have h := Real.log_le_log (show 0 < (2:ℝ)^(Nat.log 2 n) by positivity)
    (show (2:ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast hi)
  rw [Real.log_pow] at h
  have hhalf : (1:ℝ)/2 ≤ Real.log 2 := by
    have h' := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h' ⊢
    exact h'
  have h' := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 n))
  have hlog : ((Nat.log 2 R:ℕ):ℝ) ≤ (Nat.log 2 n:ℕ) := by exact_mod_cast Nat.log_mono_right (b:=2) hR
  linarith

/-- Uniformly for every upper denominator at most n, the model envelope is o(n/log² n). -/
theorem eventually_interval_model_budget_log_sq {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ R : ℕ, R≤n →
      ((n:ℝ)+1)*((((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*(n.divisors.card:ℝ)/(medDeskD n:ℝ))) ≤
        ε*(n:ℝ)/(1+Real.log n)^2 := by
  have hp := (isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0:ℝ)<1/12)).bound
    (show 0 < ε/1179648 by positivity)
  have he := tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually hp
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hroot := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [he,hlog,hroot,eventually_ge_atTop (1:ℕ)] with n hsmall hL hroot hn
  intro R hR
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0:ℝ)<n := by linarith
  change 1 ≤ Real.log (n:ℝ) at hL
  change 1 ≤ (n:ℝ)^(1/3:ℝ) at hroot
  have hL0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hB1 : 1 ≤ medDeskD n := Nat.le_floor (by simpa using hroot)
  have hB1' : (1:ℝ) ≤ medDeskD n := by exact_mod_cast hB1
  have hB0 : (0:ℝ) < medDeskD n := by linarith
  have hB : (n:ℝ)^(1/3:ℝ) ≤ 2*(medDeskD n:ℝ) := by
    have hh : (n:ℝ)^(1/3:ℝ) < (medDeskD n:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have hpow : (Real.log (n:ℝ))^4 ≤ ε/1179648*(n:ℝ)^(1/12:ℝ) := by
    change ‖Real.log (n:ℝ) ^ (4:ℝ)‖ ≤ _ at hsmall
    simpa only [show (4:ℝ)=((4:ℕ):ℝ) from rfl, Real.rpow_natCast,Real.norm_of_nonneg
      (pow_nonneg hL0 4),Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] using hsmall
  have hK := shell_log_two_bound hn hR hL
  have hτ := project_divisor_count_fourth_root hn
  have hsum : (n:ℝ)^(1/12:ℝ)*(n:ℝ)^(1/4:ℝ) = (n:ℝ)^(1/3:ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  apply (le_div_iff₀ (by positivity : 0<(1+Real.log (n:ℝ))^2)).mpr
  rw [show ((n:ℝ)+1)*((((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*(n.divisors.card:ℝ)/(medDeskD n:ℝ))) *
      (1+Real.log n)^2 = (((n:ℝ)+1)*(((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*n.divisors.card)*
      (1+Real.log n)^2)/(medDeskD n:ℝ) by ring]
  apply (div_le_iff₀ hB0).mpr
  have h1 : (n:ℝ)+1 ≤ 2*n := by linarith
  have h2 : (1+Real.log (n:ℝ)) ≤ 2*Real.log n := by linarith
  calc
    _ ≤ (2*(n:ℝ))*(3*Real.log n)^2*(2*(4096*(n:ℝ)^(1/4:ℝ)))*(2*Real.log n)^2 := by gcongr
    _ = 589824*(n:ℝ)*(Real.log n)^4*(n:ℝ)^(1/4:ℝ) := by ring
    _ ≤ 589824*(n:ℝ)*(ε/1179648*(n:ℝ)^(1/12:ℝ))*(n:ℝ)^(1/4:ℝ) := by gcongr
    _ = (ε*(n:ℝ)/2)*((n:ℝ)^(1/12:ℝ)*(n:ℝ)^(1/4:ℝ)) := by ring
    _ ≤ (ε*(n:ℝ)/2)*(2*(medDeskD n:ℝ)) := by rw [hsum]; gcongr
    _ = _ := by ring


end GoldbachPartial
