import VerifiedMedDeskProgression

namespace GoldbachPartial
open Finset Filter
open scoped Topology

theorem polylog_window_uniform_prime_class (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ u : ℕ in atTop,
      ∀ q a : ℕ, 0<q → (q:ℝ)≤(Real.log u)^d → a<q → a.Coprime q →
        |GoldbachMajorArc.classMass (u+1) q a - (u:ℝ)/q.totient| ≤ C*u/(Real.log u)^(2*d+1) := by
  let A : ℕ := 2*d+1
  have hA : 0 < (A:ℝ) := by dsimp [A]; positivity
  obtain ⟨M,hM,x₀,_,hap⟩ := GoldbachMajorArc.prime_progression_error (A:ℝ) (d:ℝ) hA (by exact_mod_cast hd)
  refine ⟨M+4,by positivity,?_⟩
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((A+2:ℕ):ℝ) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [htlog,hpow,eventually_ge_atTop (max 1 ⌈x₀⌉₊)] with u hlog hpow hu
  intro q a hq hqL ha hc
  let L := Real.log u
  have hx : x₀≤(u:ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right 1 ⌈x₀⌉₊).trans hu)
  have huR : (1:ℝ)≤u := by exact_mod_cast (le_max_left 1 ⌈x₀⌉₊).trans hu
  change 1≤L at hlog
  have hL : 0<L := by linarith
  have hbig : L^(A+2) ≤ Real.sqrt u := by simpa only [L,Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow] using hpow
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) u)
  have hnext := (pow_le_pow_right₀ hlog (by omega : A+1≤A+2)).trans hbig
  have hroot : Real.sqrt u≤(u:ℝ) := by
    have h1 : 1≤Real.sqrt (u:ℝ) := by simpa using Real.sqrt_le_sqrt huR
    nlinarith only [hr,mul_nonneg (zero_le_one.trans h1) (sub_nonneg.mpr h1)]
  have hqlog : Real.log q≤L := by
    apply Real.log_le_log (by exact_mod_cast hq)
    exact hqL.trans ((pow_le_pow_right₀ hlog (by dsimp [A]; omega : d≤A+2)).trans (hbig.trans hroot))
  have hnat : (Nat.log 2 u:ℝ)≤2*L := by
    have h := Real.natLog_le_logb u 2
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    simp only [Nat.cast_ofNat,Real.logb] at h
    apply h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr _)
    nlinarith only [mul_nonneg hL.le (show 0≤2*Real.log 2-1 by linarith)]
  have hAP := hap u q a hx hq (by simpa only [Real.rpow_natCast] using hqL) ha hc
  change _ ≤ M*(u:ℝ)*L^(-(A:ℝ))+(Nat.log 2 u:ℝ)*Real.log q+2*Real.sqrt u*L at hAP
  rw [Real.rpow_neg hL.le,Real.rpow_natCast,←div_eq_mul_inv] at hAP
  apply hAP.trans
  have hx1 : (Nat.log 2 u:ℝ)*Real.log q ≤ 2*(u:ℝ)/L^A := by
    apply (mul_le_mul hnat hqlog (Real.log_natCast_nonneg _) (by positivity)).trans
    apply (le_div_iff₀ (pow_pos hL A)).mpr
    calc
      _ = 2*L^(A+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbig.trans hroot) (by norm_num)
  have hx2 : 2*Real.sqrt u*L ≤ 2*(u:ℝ)/L^A := by
    apply (le_div_iff₀ (pow_pos hL A)).mpr
    calc
      _ = 2*Real.sqrt u*L^(A+1) := by rw [pow_succ]; ring
      _ ≤ 2*Real.sqrt u*Real.sqrt u := mul_le_mul_of_nonneg_left hnext (by positivity)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  change _≤(M+4)*(u:ℝ)/L^A
  linear_combination hx1+hx2

end GoldbachPartial