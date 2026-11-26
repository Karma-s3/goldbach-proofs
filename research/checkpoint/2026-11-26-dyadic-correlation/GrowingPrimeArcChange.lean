import SignedPrimeBandThrough
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace GoldbachPartial

open Finset Filter
open scoped Topology

noncomputable abbrev growingPrimeArcCutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(3/8:ℝ)⌋₊

noncomputable def growingPrimeArcChange (n : ℕ) : ℂ :=
  ∑ j ∈ Ico (medDeskD n) (growingPrimeArcCutoff n),
    primeArcSignedChange (j+1) n (1/(20*(n:ℝ)))

def growingPrimeArcPrefix (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j ∈ Ico (medDeskD n) (growingPrimeArcCutoff n),
    ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤
      C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2

theorem growingPrimeArcChange_power_bound (C : ℝ) (hC : 0≤C) (hp : growingPrimeArcPrefix C) :
    ∀ᶠ n : ℕ in atTop, ‖growingPrimeArcChange n‖ ≤
      (2/5*((9*C)^2*(1+Real.pi/10)^2+1)+12)*(n:ℝ)^(15/16:ℝ) := by
  let t (n : ℕ) := (n:ℝ)^(1/48:ℝ)
  have hl : Tendsto (fun n : ℕ => Real.log n / t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/48)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hp,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hn hprefix hlog
  let T := t n
  let R := growingPrimeArcCutoff n
  let ρ := 1/(20*(n:ℝ))
  let D := C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2
  let F := 1+Real.pi/10
  let V := (9*C)^2*F^2+1
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have ht : 1≤T := Real.one_le_rpow hn1 (by norm_num)
  have ht0 : 0<T := lt_of_lt_of_le zero_lt_one ht
  have hρ : 0≤ρ := by dsimp only [ρ]; positivity
  have hhalf : ρ ≤ 1/2 := by
    dsimp only [ρ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hD : 0≤D := by dsimp only [D]; positivity
  have hV : 0≤V := by dsimp only [V]; positivity
  have hpow (k : ℕ) : T^k = (n:ℝ)^((1/48:ℝ)*k) := by
    dsimp only [T,t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  have h48 : T^48=(n:ℝ) := by rw [hpow]; norm_num
  have h18 : T^18=(n:ℝ)^(3/8:ℝ) := by rw [hpow]; norm_num
  have h45 : T^45=(n:ℝ)^(15/16:ℝ) := by rw [hpow]; norm_num
  have h24 : Real.sqrt n=T^24 := by rw [hpow,Real.sqrt_eq_rpow]; norm_num
  have hR : (R:ℝ) ≤ T^18 := by rw [h18]; exact Nat.floor_le (by positivity)
  have hR1 : 1≤R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 (by norm_num))
  have hlogn : Real.log n ≤ T := by
    change Real.log n/T < 1 at hlog
    linarith [(div_lt_iff₀ ht0).mp hlog]
  have hlogR : Real.log R ≤ T :=
    (Real.log_le_log (by exact_mod_cast hR1)
      (hR.trans ((pow_le_pow_right₀ ht (by decide : 18≤48)).trans_eq h48))).trans hlogn
  have hlogR0 : 0≤Real.log R := Real.log_nonneg (by exact_mod_cast hR1)
  have hbase : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x:=2) (by norm_num)
    norm_num at h ⊢; linarith
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (x:=2) (by norm_num)]
  have hK : 1+(Nat.log 2 R:ℝ) ≤ 3*T := by
    have hb := Real.natLog_le_logb R 2
    simp only [Real.logb, Nat.cast_ofNat] at hb
    have hb' : Real.log R/Real.log 2 ≤ 2*T := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hbase)]
    linarith
  have hlogbig : Real.log (2*(n:ℝ)^2) ≤ 3*T := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),Real.log_pow]; push_cast; linarith
  have hlogbig0 : 0 ≤ Real.log (2*(n:ℝ)^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((n:ℝ)-1)])
  have hDb : D ≤ (9*C)*T^26 := calc
    D ≤ C*T^24*(3*T)^2 := by dsimp only [D]; rw [h24]; gcongr
    _ = _ := by ring
  have hF : 1+2*Real.pi*n*ρ = F := by dsimp only [ρ,F]; field_simp; ring
  have hRb : (R:ℝ)^2 ≤ T^36 := by simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hR 2
  have hbracket : D^2*F^2+(Real.log R)^2 ≤ V*T^52 := calc
    _ ≤ ((9*C)*T^26)^2*F^2+T^2 := by gcongr
    _ ≤ ((9*C)*T^26)^2*F^2+T^52 := by gcongr; decide
    _ = _ := by dsimp only [V]; ring
  have hs : 0<T^5 := pow_pos ht0 _
  have h1 : 1+T^5 ≤ 2*T^5 := by linarith [one_le_pow₀ ht (n:=5)]
  have hfirst :
      (1+T^5)*(4*ρ*(R:ℝ)^2*(D^2*F^2+(Real.log R)^2)) ≤ (2/5)*V*T^45 := calc
    _ ≤ (2*T^5)*(4*ρ*T^36*(V*T^52)) := by gcongr
    _ = _ := by dsimp only [ρ]; rw [← h48]; field_simp; ring
  have hsecond :
      (T^5)⁻¹*((n:ℝ)+1)*(1+(Nat.log 2 R:ℝ))*(1+Real.log R) ≤ 12*T^45 := calc
    _ ≤ (T^5)⁻¹*(2*T^48)*(3*T)*(2*T) := by
      gcongr
      · linarith [h48]
      · linarith
    _ = _ := by field_simp; ring
  have h := primeArc_signed_Ico_of_prefix n (medDeskD n) R hρ hhalf hD hs hprefix
  rw [hF] at h
  change ‖growingPrimeArcChange n‖ ≤ _ at h
  rw [← h45]
  change _ ≤ (2/5*V+12)*T^45
  linarith only [h,hfirst,hsecond]

theorem growingPrimeArcChange_div_tendsto_zero (C : ℝ) (hC : 0≤C) (hp : growingPrimeArcPrefix C) :
    Tendsto (fun n : ℕ => ‖growingPrimeArcChange n‖/(n:ℝ)) atTop (𝓝 0) := by
  let A := 2/5*((9*C)^2*(1+Real.pi/10)^2+1)+12
  have hdec : Tendsto (fun n : ℕ => A*(n:ℝ)^(-(1/16:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_const_nhds (x:=A)).mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hdec
  filter_upwards [growingPrimeArcChange_power_bound C hC hp,eventually_ge_atTop (1:ℕ)] with n h hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  apply (div_le_iff₀ hn0).mpr
  rw [mul_assoc, ← Real.rpow_add_one hn0.ne']
  norm_num1
  exact h

end GoldbachPartial