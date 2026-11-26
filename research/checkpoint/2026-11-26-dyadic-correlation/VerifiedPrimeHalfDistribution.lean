import VerifiedPrimeQuarterDistribution

namespace GoldbachPartial
open Finset Filter
open scoped Topology

private def meanLevelExponent (A b : ℕ) := A+b+1+2*vaughanParameterExponent A b

private theorem half_level_budget (A b : ℕ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q:ℝ)*(1+Real.log X)^(meanLevelExponent A b) ≤ Real.sqrt X →
      let H := (vaughanParameterCutoff A b X:ℝ)
      let L := 1+Real.log X
      C*L^b*((Q:ℝ)^2*H^2+(X:ℝ)/Real.sqrt H+(X:ℝ)/H+(Q:ℝ)*Real.sqrt X) ≤ (X:ℝ)/L^A := by
  let K := vaughanParameterExponent A b
  let d := A+b+1
  let D := meanLevelExponent A b
  have hD : D = d+2*K := rfl
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (4*C),vaughan_parameter_floor_bounds A b] with X hC4 hf
  intro Q hQ H L
  let W := L^d
  have hL : 1≤L := by dsimp only [L];linarith [Real.log_natCast_nonneg X]
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hW : 0<W := pow_pos hLp _
  obtain ⟨hH1,_,hH,hroot,hWH⟩ := hf
  change W ≤ Real.sqrt H at hroot
  change W ≤ H at hWH
  change H ≤ (Real.log X)^K at hH
  change (Q:ℝ)*L^D ≤ Real.sqrt X at hQ
  have hH' := hH.trans (pow_le_pow_left₀ (Real.log_natCast_nonneg X) (show Real.log X≤L by dsimp [L];linarith) K)
  have hcoef : H^2*W ≤ (L^D)^2 := by
    calc H^2*W ≤ (L^K)^2*W := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by dsimp [H];positivity) hH' 2) hW.le
         _ = L^D := by dsimp only [W];rw [hD,pow_add L d (2*K),mul_comm 2 K,pow_mul];ring
         _ ≤ _ := le_self_pow₀ (one_le_pow₀ hL) (by decide)
  have hfirst : (Q:ℝ)^2*H^2 ≤ (X:ℝ)/W := by
    apply (le_div_iff₀ hW).mpr
    calc _ = (Q:ℝ)^2*(H^2*W) := by ring
         _ ≤ (Q:ℝ)^2*(L^D)^2 := mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
         _ = ((Q:ℝ)*L^D)^2 := (mul_pow ..).symm
         _ ≤ (Real.sqrt X)^2 := pow_le_pow_left₀ (by positivity) hQ _
         _ = _ := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsecond : (X:ℝ)/Real.sqrt H ≤ (X:ℝ)/W := div_le_div_of_nonneg_left (by positivity) hW hroot
  have hthird : (X:ℝ)/H ≤ (X:ℝ)/W := div_le_div_of_nonneg_left (by positivity) hW hWH
  have hqw : (Q:ℝ)*W ≤ Real.sqrt X := (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by rw [hD];omega : d≤D)) (Nat.cast_nonneg (α:=ℝ) Q)).trans hQ
  have hfourth : (Q:ℝ)*Real.sqrt X ≤ (X:ℝ)/W := by
    apply (le_div_iff₀ hW).mpr
    calc _ = ((Q:ℝ)*W)*Real.sqrt X := by ring
         _ ≤ Real.sqrt X*Real.sqrt X := mul_le_mul_of_nonneg_right hqw (by positivity)
         _ = _ := Real.mul_self_sqrt (by positivity)
  have hc : 4*C≤L := by dsimp only [L]; change 4*C≤Real.log X at hC4;linarith
  calc
    _ ≤ (C*L^b)*(4*((X:ℝ)/W)) := mul_le_mul_of_nonneg_left (by linarith only [hfirst,hsecond,hthird,hfourth]) (by positivity)
    _ = (4*C/L)*((X:ℝ)/L^A) := by dsimp only [W,d];rw [pow_succ,pow_add];field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) ((div_le_one hLp).mpr hc)

open private quarter_mean_envelope from VerifiedPrimeQuarterDistribution

/-- A fixed-endpoint Bombieri–Vinogradov estimate for the project prime weights.
The maximum ranges over the reduced classes at each modulus. -/
theorem prime_progressions_half_level (A : ℕ) :
    ∃ D : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q:ℝ)*(1+Real.log X)^D ≤ Real.sqrt X →
      (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError X q) ≤ C*X/(Real.log X)^A := by
  obtain ⟨c,hc,b,hm⟩ := quarter_mean_envelope vaughan_actual_conductor_bound
  let K := vaughanParameterExponent A b
  have hk : 0<K := by dsimp [K,vaughanParameterExponent];omega
  obtain ⟨C,hC,hsmall⟩ := primitive_small_conductor_mean (A+1) K hk
  refine ⟨meanLevelExponent A b,8*C+1,by positivity,?_⟩
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (2:ℕ),ht,hsmall,half_level_budget A b c hc.le,
    vaughan_parameter_floor_bounds A b] with X hX ht hs hp hf
  let T := Real.log X
  let L := 1+T
  let H := vaughanParameterCutoff A b X
  change 1≤T at ht
  have hT : 0<T := zero_lt_one.trans_le ht
  obtain ⟨hH,_,hcut,_,_⟩ := hf
  have hS := hs H hcut
  change primitiveConductorMass X (Icc 1 H) ≤ C*X/T^(A+1) at hS
  intro Q hQ
  rcases Nat.eq_zero_or_pos Q with rfl | hQp
  · simp only [Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),sum_empty]
    positivity
  have hXr : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have hQXr : (Q:ℝ)≤X := calc
    _ ≤ (Q:ℝ)*(1+Real.log X)^(meanLevelExponent A b) := le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ (by linarith [Real.log_natCast_nonneg X]))
    _ ≤ _ := hQ
    _ ≤ _ := ((Real.sqrt_le_iff).mpr ⟨hXr.trans' zero_le_one,le_self_pow₀ hXr (by decide)⟩)
  have hb := hm X Q H hX hQp (by exact_mod_cast hQXr) hH
  have hS0 : 0≤primitiveConductorMass X (Icc 1 H) :=
    sum_nonneg fun q _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _)
  have hsmall' : 4*L*primitiveConductorMass X (Icc 1 H) ≤ (8*C)*X/T^A := by
    calc
      _ ≤ (8*T)*(C*X/T^(A+1)) := mul_le_mul (by dsimp [L];linarith) hS hS0 (by positivity)
      _ = _ := by rw [pow_succ];field_simp
  have hpow : (X:ℝ)/L^A ≤ (X:ℝ)/T^A :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hT _)
      (pow_le_pow_left₀ hT.le (by dsimp [L];linarith) _)
  change _ ≤ (8*C+1)*X/T^A
  exact hb.trans ((add_le_add hsmall' ((hp Q hQ).trans hpow)).trans_eq (by ring))

end GoldbachPartial