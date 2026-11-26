import PinnedUpstream316

namespace GoldbachPartial
open Filter
open scoped Topology

def vaughanParameterExponent (A B : ℕ) : ℕ := 2*(A+B+2)
noncomputable def vaughanParameterCutoff (A B X : ℕ) : ℕ :=
  ⌊(Real.log X)^(vaughanParameterExponent A B)⌋₊

private theorem vaughan_eventually_logPower_fourthRoot (m : ℕ) :
    ∀ᶠ X : ℕ in atTop, (1+Real.log X)^m ≤ Real.sqrt (Real.sqrt X) := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((m+1:ℕ):ℝ) (by norm_num : (0:ℝ)<1/4))
  filter_upwards [ht.eventually_ge_atTop (max 1 ((2:ℝ)^m)),hp] with X hlog hpow
  let T := Real.log X
  have h1 : 1≤T := (le_max_left ..).trans hlog
  have hc : (2:ℝ)^m≤T := (le_max_right ..).trans hlog
  have hR : T^(m+1)≤Real.sqrt (Real.sqrt X) := by
    simpa only [T,Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow,
      ←Real.rpow_mul (Nat.cast_nonneg (α:=ℝ) X),show (1/2:ℝ)*(1/2)=1/4 by norm_num] using hpow
  calc
    _ ≤ (2*T)^m := pow_le_pow_left₀ (by positivity) (by change 1+T≤2*T;linarith) _
    _ = (2:ℝ)^m*T^m := mul_pow ..
    _ ≤ T^(m+1) := by rw [pow_succ,mul_comm (T^m)];exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := hR

/-- The integer Vaughan cutoffs use the unshifted natural logarithm. The other bounds
are stated with 1+log, so either convention for the losses is available. -/
theorem vaughan_parameter_floor_bounds (A B : ℕ) :
    ∀ᶠ X : ℕ in atTop, let T := Real.log X
      let U := vaughanParameterCutoff A B X
      let K := vaughanParameterExponent A B
      1≤U ∧ T^K/2 ≤ (U:ℝ) ∧ (U:ℝ)≤T^K ∧
      (1+T)^(A+B+1)≤Real.sqrt U ∧ (1+T)^(A+B+1)≤(U:ℝ) := by
  let d := A+B+1
  let K := vaughanParameterExponent A B
  have hKe : K=2*d+2 := by dsimp [K,d,vaughanParameterExponent];omega
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (max 2 (2*(2:ℝ)^(2*d)))] with X hlog
  let T := Real.log X
  let U := vaughanParameterCutoff A B X
  have hT : 2≤T := (le_max_left ..).trans hlog
  have hT1 : 1≤T := by linarith
  have hc : 2*(2:ℝ)^(2*d)≤T := (le_max_right ..).trans hlog
  have hTp : 0<T := by linarith
  have hpow : 2≤T^K := hT.trans (by simpa only [pow_one] using (pow_le_pow_right₀ hT1 (by omega : 1≤K)))
  have hU : (U:ℝ)≤T^K := Nat.floor_le (pow_nonneg hTp.le _)
  have hnear : T^K < (U:ℝ)+1 := Nat.lt_floor_add_one _
  have hU1 : 1≤U := Nat.le_floor (by simpa using (le_trans (by norm_num : (1:ℝ)≤2) hpow))
  have hfloor : T^K/2≤(U:ℝ) := by linarith
  have hsq : ((1+T)^d)^2≤(U:ℝ) := by
    apply le_trans _ hfloor
    rw [←pow_mul,show d*2=2*d by omega,hKe,pow_add]
    calc
      (1+T)^(2*d) ≤ (2*T)^(2*d) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = (2:ℝ)^(2*d)*T^(2*d) := mul_pow ..
      _ ≤ T^(2*d)*T^2/2 := by
        have hcoef : (2:ℝ)^(2*d)≤T^2/2 := by nlinarith only [hc,hT,hTp.le,mul_nonneg hTp.le (show 0≤T-1 by linarith)]
        exact (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hTp.le _)).trans_eq (by ring)
  have hroot := (Real.le_sqrt (by positivity : 0≤(1+T)^d) (Nat.cast_nonneg (α:=ℝ) U)).mpr hsq
  have hR : Real.sqrt U≤(U:ℝ) := by
    have h1 : (1:ℝ)≤Real.sqrt U := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using (show (1:ℝ)≤U by exact_mod_cast hU1))
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) U),
      mul_nonneg (sub_nonneg.mpr h1) (Real.sqrt_nonneg (U:ℝ))]
  exact ⟨hU1,hfloor,hU,hroot,hroot.trans hR⟩

/-- One common integer cutoff works for the two Vaughan variables and the conductor
split. The four errors may carry the same arbitrary constant and logarithmic loss. -/
theorem vaughan_quarter_level_parameter_budget (A B : ℕ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ, Q^4≤X →
      let U := (vaughanParameterCutoff A B X:ℝ)
      let L := 1+Real.log X
      C*L^B*((Q:ℝ)^2*U^2 + (X:ℝ)/Real.sqrt U + (X:ℝ)/U + (Q:ℝ)*Real.sqrt X) ≤ (X:ℝ)/L^A := by
  let d := A+B+1
  let K := vaughanParameterExponent A B
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [vaughan_parameter_floor_bounds A B,vaughan_eventually_logPower_fourthRoot (d+2*K),
    ht.eventually_ge_atTop (max 2 (4*C)),eventually_ge_atTop (1:ℕ)] with X hf hbig hlog hX
  intro Q hQ
  let T := Real.log X
  let L := 1+T
  let U := (vaughanParameterCutoff A B X:ℝ)
  let W := L^d
  change max 2 (4*C)≤T at hlog
  have h1 : 1≤L := by dsimp only [L];linarith only [(le_max_left 2 (4*C)).trans hlog]
  have hLp : 0<L := zero_lt_one.trans_le h1
  have hC4 : 4*C≤L := by dsimp only [L];linarith only [(le_max_right 2 (4*C)).trans hlog]
  have hW : 0<W := pow_pos hLp _
  have hXr : (1:ℝ)≤X := by exact_mod_cast hX
  have hT : 0≤T := Real.log_natCast_nonneg _
  obtain ⟨hUpos,_,hU,hroot,hWU⟩ := hf
  change U≤T^K at hU
  change W≤Real.sqrt U at hroot
  change W≤U at hWU
  have hUp := hW.trans_le hWU
  have hrootUp := hW.trans_le hroot
  have hQreal : (Q:ℝ)^4≤X := by exact_mod_cast hQ
  have hQsq : (Q:ℝ)^2≤Real.sqrt X :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by simpa only [←pow_mul] using hQreal)
  have hQr : (Q:ℝ)≤Real.sqrt (Real.sqrt X) := (Real.le_sqrt (by positivity) (by positivity)).mpr hQsq
  have hR : Real.sqrt (Real.sqrt X)≤Real.sqrt X := by
    have h11 : 1≤Real.sqrt (X:ℝ) := by simpa using Real.sqrt_le_sqrt hXr
    have h2 : 1≤Real.sqrt (Real.sqrt X) := by simpa using Real.sqrt_le_sqrt h11
    nlinarith only [Real.sq_sqrt (Real.sqrt_nonneg (X:ℝ)),mul_nonneg (sub_nonneg.mpr h2) (Real.sqrt_nonneg (Real.sqrt X))]
  have hWU2 : W*U^2≤Real.sqrt X := by
    apply le_trans _ (hbig.trans hR)
    change L^d*U^2≤L^(d+2*K)
    rw [pow_add L d (2*K),mul_comm 2 K,pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hUp.le (hU.trans (pow_le_pow_left₀ hT (by dsimp only [L];linarith) _)) _) hW.le
  have hw4 : W≤Real.sqrt (Real.sqrt X) := (pow_le_pow_right₀ h1 (by omega : d≤d+2*K)).trans hbig
  have hfirst : (Q:ℝ)^2*U^2 ≤ (X:ℝ)/W := by
    apply (le_div_iff₀ hW).mpr
    calc
      _ = (Q:ℝ)^2*(W*U^2) := by ring
      _ ≤ Real.sqrt X*Real.sqrt X := mul_le_mul hQsq hWU2 (by positivity) (by positivity)
      _ = _ := Real.mul_self_sqrt (by positivity)
  have hsecond : (X:ℝ)/Real.sqrt U ≤ (X:ℝ)/W := div_le_div_of_nonneg_left (by positivity) hW hroot
  have hthird : (X:ℝ)/U ≤ (X:ℝ)/W := div_le_div_of_nonneg_left (by positivity) hW hWU
  have hfourth : (Q:ℝ)*Real.sqrt X ≤ (X:ℝ)/W := by
    apply (le_div_iff₀ hW).mpr
    have hqw : (Q:ℝ)*W≤Real.sqrt X :=
      (mul_le_mul hQr hw4 hW.le (by positivity)).trans_eq (Real.mul_self_sqrt (Real.sqrt_nonneg (X:ℝ)))
    calc
      _ = ((Q:ℝ)*W)*Real.sqrt X := by ring
      _ ≤ Real.sqrt X*Real.sqrt X := mul_le_mul_of_nonneg_right hqw (by positivity)
      _ = _ := Real.mul_self_sqrt (by positivity)
  change C*L^B*_ ≤ (X:ℝ)/L^A
  calc
    _ ≤ (C*L^B)*(4*((X:ℝ)/W)) := mul_le_mul_of_nonneg_left (by linarith only [hfirst,hsecond,hthird,hfourth]) (by positivity)
    _ = (4*C/L)*((X:ℝ)/L^A) := by dsimp only [W,d];rw [pow_succ,pow_add];field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) ((div_le_one hLp).mpr hC4)

end GoldbachPartial