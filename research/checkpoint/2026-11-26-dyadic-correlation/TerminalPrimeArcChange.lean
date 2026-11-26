import SignedPrimeBandThrough
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace GoldbachPartial

open Finset Filter
open scoped Topology

noncomputable abbrev terminalPrimeArcLog (n : ℕ) : ℝ := 1+Real.log n
noncomputable abbrev terminalPrimeArcCutoff (n : ℕ) : ℕ :=
  ⌊Real.sqrt n/(terminalPrimeArcLog n)^5⌋₊

noncomputable def terminalPrimeArcChange (n : ℕ) : ℂ :=
  ∑ j ∈ Ico (medDeskD n) (terminalPrimeArcCutoff n),
    primeArcSignedChange (j+1) n (1/(20*(n:ℝ)))

def terminalPrimeArcPrefixAt (C : ℝ) (n : ℕ) : Prop :=
  ∀ j ∈ Ico (medDeskD n) (terminalPrimeArcCutoff n), ∀ χ, ∀ k ≤ n,
    ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤
      C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2

def terminalPrimeArcPrefix (C : ℝ) : Prop := ∀ᶠ n : ℕ in atTop, terminalPrimeArcPrefixAt C n

noncomputable abbrev terminalPrimeArcConstant (C : ℝ) : ℝ :=
  2/5*((4*C)^2*(1+Real.pi/10)^2+1)+4

theorem terminalPrimeArcChange_bound_at {n : ℕ} (hn : 1≤n) {C : ℝ} (hC : 0≤C)
    (hp : terminalPrimeArcPrefixAt C n) :
    ‖terminalPrimeArcChange n‖ ≤ terminalPrimeArcConstant C*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  let L := terminalPrimeArcLog n
  let R := terminalPrimeArcCutoff n
  let ρ := 1/(20*(n:ℝ))
  let D := C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2
  let F := 1+Real.pi/10
  let V := (4*C)^2*F^2+1
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hL : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hρ : 0≤ρ := by dsimp only [ρ]; positivity
  have hhalf : ρ≤1/2 := by dsimp only [ρ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hD : 0≤D := by dsimp only [D]; positivity
  have hV : 0≤V := by dsimp only [V]; positivity
  have hR : (R:ℝ) ≤ Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hRn : (R:ℝ) ≤ n :=
    (hR.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL))).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hn1))
  have hR2 : (R:ℝ)^2 ≤ (n:ℝ)/L^10 := calc
    _ ≤ (Real.sqrt n/L^5)^2 := pow_le_pow_left₀ (by positivity) hR _
    _ = _ := by rw [div_pow, Real.sq_sqrt hn0.le, ← pow_mul]
  have hlogR : Real.log R ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos R with hz | hr
    · rw [hz,Nat.cast_zero,Real.log_zero]; exact Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hr) hRn
  have hlogadd : 1+Real.log R ≤ L := add_le_add le_rfl hlogR
  have hlogRL : Real.log R ≤ L := by linarith
  have hbase : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x:=2) (by norm_num)
    norm_num at h ⊢; linarith
  have hK : 1+(Nat.log 2 R:ℝ) ≤ 2*L := by
    have hb := Real.natLog_le_logb R 2
    simp only [Real.logb, Nat.cast_ofNat] at hb
    have hb' : Real.log R/Real.log 2 ≤ 2*Real.log n := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      nlinarith [mul_nonneg (Real.log_natCast_nonneg n) (sub_nonneg.mpr hbase)]
    dsimp only [L,terminalPrimeArcLog]
    linarith
  have hlogbig : Real.log (2*(n:ℝ)^2) ≤ 2*L := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),Real.log_pow]
    dsimp only [L,terminalPrimeArcLog]; push_cast
    linarith [Real.log_le_sub_one_of_pos (x:=2) (by norm_num)]
  have hlogbig0 : 0 ≤ Real.log (2*(n:ℝ)^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((n:ℝ)-1)])
  have hDb : D ≤ (4*C)*Real.sqrt n*L^2 := calc
    D ≤ C*Real.sqrt n*(2*L)^2 := by dsimp only [D]; gcongr
    _ = _ := by ring
  have hF : 1+2*Real.pi*n*ρ = F := by dsimp only [ρ,F]; field_simp; ring
  have hbracket : D^2*F^2+(Real.log R)^2 ≤ V*(n:ℝ)*L^4 := calc
    _ ≤ ((4*C)*Real.sqrt n*L^2)^2*F^2 + L^2 := by gcongr
    _ ≤ ((4*C)*Real.sqrt n*L^2)^2*F^2 + (n:ℝ)*L^4 := by
      apply add_le_add le_rfl
      exact (pow_le_pow_right₀ hL (by decide : 2≤4)).trans
        (le_mul_of_one_le_left (by positivity) hn1)
    _ = _ := by dsimp only [V]; rw [mul_pow, mul_pow, Real.sq_sqrt hn0.le]; ring
  have hs : 0<L^4 := pow_pos hL0 _
  have h1 : 1+L^4 ≤ 2*L^4 := by linarith [one_le_pow₀ hL (n:=4)]
  have hfirst :
      (1+L^4)*(4*ρ*(R:ℝ)^2*(D^2*F^2+(Real.log R)^2)) ≤ (2/5)*V*(n:ℝ)/L^2 := calc
    _ ≤ (2*L^4)*(4*ρ*((n:ℝ)/L^10)*(V*n*L^4)) := by gcongr
    _ = _ := by dsimp only [ρ]; field_simp; ring
  have hsecond :
      (L^4)⁻¹*((n:ℝ)+1)*(1+(Nat.log 2 R:ℝ))*(1+Real.log R) ≤ 4*(n:ℝ)/L^2 := calc
    _ ≤ (L^4)⁻¹*(2*(n:ℝ))*(2*L)*L := by gcongr; linarith
    _ = _ := by field_simp; ring
  have hh := primeArc_signed_Ico_of_prefix n (medDeskD n) R hρ hhalf hD hs hp
  rw [hF] at hh
  change ‖terminalPrimeArcChange n‖ ≤ _ at hh
  change _ ≤ (2/5*V+4)*(n:ℝ)/L^2
  calc
    _ ≤ _ := hh.trans (add_le_add hfirst hsecond)
    _ = _ := by ring

theorem terminalPrimeArcChange_log_bound (C : ℝ) (hC : 0≤C) (hp : terminalPrimeArcPrefix C) :
    ∀ᶠ n : ℕ in atTop, ‖terminalPrimeArcChange n‖ ≤
      terminalPrimeArcConstant C*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  filter_upwards [eventually_ge_atTop (1:ℕ),hp] with n hn hprefix
  exact terminalPrimeArcChange_bound_at hn hC hprefix

theorem terminalPrimeArcChange_div_tendsto_zero (C : ℝ) (hC : 0≤C) (hp : terminalPrimeArcPrefix C) :
    Tendsto (fun n : ℕ => ‖terminalPrimeArcChange n‖/(n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto terminalPrimeArcLog atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [terminalPrimeArcLog]; linarith) hlog
  have hpow : Tendsto (fun n : ℕ => (terminalPrimeArcLog n)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp hL
  have hdec : Tendsto (fun n : ℕ => terminalPrimeArcConstant C/(terminalPrimeArcLog n)^2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x:=terminalPrimeArcConstant C)).div_atTop hpow
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hdec
  filter_upwards [terminalPrimeArcChange_log_bound C hC hp,eventually_ge_atTop (1:ℕ)] with n h hn
  apply (div_le_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr
  calc
    _ ≤ _ := h
    _ = _ := by ring

end GoldbachPartial