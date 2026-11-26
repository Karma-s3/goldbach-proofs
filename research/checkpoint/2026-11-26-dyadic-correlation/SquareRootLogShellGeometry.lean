import DyadicCorrelationReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GoldbachPartial
open Filter
open scoped Topology

noncomputable def squareRootLogShellCutoff (n : ℕ) : ℕ :=
  ⌊Real.sqrt (n : ℝ) / (1 + Real.log n)^5⌋₊

private theorem logShell_baseTwo_log_le {n : ℕ} (hn : 2 ≤ n) :
    ((Nat.log 2 (n+2) : ℕ) : ℝ) ≤ 4 * Real.log n := by
  let m := Nat.log 2 (n+2)
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  norm_num at h₂
  have hp : (2:ℝ)^m ≤ (n:ℝ)+2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hl
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have harg : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hl' := Real.log_le_log (by positivity) harg
  rw [Real.log_pow] at hl'
  norm_num at hl'
  change (m:ℝ) ≤ _
  nlinarith only [hl,hl',mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) m)]

theorem squareRootLogShell_budget_with_multiple (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := squareRootLogShellCutoff n
      0 < B ∧ B ≤ R ∧ R^2 ≤ n ∧ R ≤ n ∧ R*(256*B*medDeskQ n+B)<n ∧ k*B ≤ R := by
  let t := fun n : ℕ => (n:ℝ)^(1/48 : ℝ)
  have htt : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp tendsto_natCast_atTop_atTop
  have hll := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/48)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),htt.eventually_ge_atTop (max 4098 (32*(k:ℝ))),
    hll.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn ht hl
  let T := t n
  let B := medDeskD n
  let R := squareRootLogShellCutoff n
  let L := Real.log (n:ℝ)
  let D := (1+L)^5
  have hT : 4098 ≤ T := (le_max_left ..).trans ht
  have hK : 32*(k:ℝ) ≤ T := (le_max_right ..).trans ht
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hL0 : 0 ≤ L := Real.log_nonneg hn1
  have hL : L ≤ T := by
    change L/T < 1 at hl
    linarith [(div_lt_iff₀ hT0).mp hl]
  have hD1 : 1 ≤ D := one_le_pow₀ (show 1 ≤ 1+L by linarith)
  have hD0 : 0 < D := by linarith
  have hD : D ≤ 32*T^5 := by
    calc D ≤ (2*T)^5 := pow_le_pow_left₀ (show 0 ≤ 1+L by linarith) (by linarith) 5
         _ = _ := by ring
  have hroot : T^24 = Real.sqrt n := by
    dsimp [T,t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have hb' : (n:ℝ)^(1/3:ℝ) = T^16 := by
    dsimp [T,t]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have hB : (B:ℝ) ≤ T^16 := by
    rw [← hb']
    exact Nat.floor_le (by positivity)
  have hBpos : 0 < B := by
    change 1 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    exact Nat.le_floor (by simpa using Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 1/3))
  have hm := logShell_baseTwo_log_le hn
  have hQ : (medDeskQ n : ℝ) ≤ 16*T^2 := by
    change ((Nat.log 2 (n+2)^2:ℕ):ℝ) ≤ _
    push_cast
    have h : ((Nat.log 2 (n+2):ℕ):ℝ) ≤ 4*T := hm.trans (by dsimp [L] at hL; linarith)
    calc _ ≤ (4*T)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
         _ = _ := by ring
  have hsmall (j : ℕ) (hj : 32*(j:ℝ) ≤ T) : j*B ≤ R := by
    apply Nat.le_floor
    change _ ≤ Real.sqrt (n:ℝ) / D
    apply (le_div_iff₀ hD0).mpr
    push_cast
    calc (j:ℝ)*B*D ≤ (j:ℝ)*T^16*(32*T^5) := by gcongr
         _ = (32*(j:ℝ))*T^21 := by ring
         _ ≤ T*T^21 := mul_le_mul_of_nonneg_right hj (by positivity)
         _ = T^22 := by ring
         _ ≤ T^24 := pow_le_pow_right₀ hT1 (by decide)
         _ = _ := hroot
  have hRf : (R:ℝ) ≤ Real.sqrt n := by
    calc (R:ℝ) ≤ Real.sqrt (n:ℝ)/D := Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) hD0.le)
         _ ≤ _ := div_le_self (Real.sqrt_nonneg _) hD1
  have hRsq : R^2 ≤ n := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) R) hRf 2
    rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hh
    exact_mod_cast hh
  have hRn : R ≤ n := (Nat.le_self_pow (by decide : 2≠0) R).trans hRsq
  have hband : (256:ℝ)*B*medDeskQ n+B < Real.sqrt n := by
    calc (256:ℝ)*B*medDeskQ n+B ≤ 256*T^16*(16*T^2)+T^16 := by gcongr
         _ ≤ 4096*T^18+T^18 := by
           rw [show 256*T^16*(16*T^2) = 4096*T^18 by ring]
           exact add_le_add le_rfl (pow_le_pow_right₀ hT1 (by decide : 16 ≤ 18))
         _ = 4097*T^18 := by ring
         _ < T*T^18 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
         _ = T^19 := by ring
         _ ≤ T^24 := pow_le_pow_right₀ hT1 (by decide)
         _ = _ := hroot
  have hs : R*(256*B*medDeskQ n+B)<n := by
    have hnpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hh := calc
      (R:ℝ)*(256*B*medDeskQ n+B) ≤ Real.sqrt n*(256*B*medDeskQ n+B) := by gcongr
      _ < Real.sqrt n*Real.sqrt n := mul_lt_mul_of_pos_left hband hnpos
      _ = (n:ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
    exact_mod_cast hh
  exact ⟨hBpos,by simpa using hsmall 1 (by push_cast; linarith),hRsq,hRn,hs,hsmall k hK⟩

theorem squareRootLogShell_geometry :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := squareRootLogShellCutoff n
      0 < B ∧ B ≤ R ∧ R^2 ≤ n ∧ R ≤ n ∧ R*(256*B*medDeskQ n+B)<n := by
  filter_upwards [squareRootLogShell_budget_with_multiple 1] with n hn
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1⟩

theorem squareRootLogShell_eventually_dominates (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c*(medDeskD n : ℝ) ≤ (squareRootLogShellCutoff n : ℝ) := by
  filter_upwards [squareRootLogShell_budget_with_multiple ⌈c⌉₊] with n hn
  exact (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (Nat.cast_nonneg (medDeskD n))).trans
    (by exact_mod_cast hn.2.2.2.2.2)
end GoldbachPartial
