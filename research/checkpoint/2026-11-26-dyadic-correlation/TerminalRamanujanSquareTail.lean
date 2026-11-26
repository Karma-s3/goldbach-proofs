import RamanujanSquareDenominatorTail

namespace GoldbachPartial
open Finset Filter
open scoped Topology

private theorem square_tail_divisor_bound {n : ℕ} (hn : 0<n) :
    (n.divisors.card:ℝ) ≤ 4096*(n:ℝ)^(1/4:ℝ) := by
  have hx : (0:ℝ) < n := by exact_mod_cast hn
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4≠0)).mp
  calc
    _ ≤ (2:ℝ)^48*n := by exact_mod_cast divisor_count_fourth_le n
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hx.le]; norm_num

private theorem square_tail_log_bound {R n : ℕ} (hn : 0<n) (hR : R≤n) (hL : 1≤Real.log (n:ℝ)) :
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

private theorem square_tail_scale_bound {n R : ℕ} (hn : 0<n) (hR : R≤n) (hL : 1≤Real.log (n:ℝ)) :
    ramanujanSquareScale R ≤ 7*(Real.log n)^3 := by
  have hl : Real.log R≤Real.log n := by
    by_cases hz : R=0
    · simpa [hz] using (Real.log_natCast_nonneg n)
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hR)
  have hK := square_tail_log_bound hn hR hL
  have h1 : 1+Real.log R≤2*Real.log n := by linarith
  have h3 : Real.log n ≤ (Real.log n)^3 := by simpa using pow_le_pow_right₀ hL (by decide : 1≤3)
  unfold ramanujanSquareScale
  calc
    _ ≤ Real.log n*(2*Real.log n)^2+3*Real.log n := by
      rw [add_assoc]
      apply add_le_add _ hK
      gcongr
    _ ≤ _ := by linarith only [h3]

/-- A uniform power saving beyond the cube-root cutoff for every upper limit up to n. -/
theorem ramanujan_square_cube_root_tail_power :
    ∀ᶠ n : ℕ in atTop, ∀ R : ℕ, R≤n →
      (∑ r∈Ioc (medDeskD n) R, |(dyadicRamanujanDivisor n r:ℝ)*
        (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2|) ≤
        802816/(n:ℝ)^(1/48:ℝ) := by
  have hp := (isLittleO_log_rpow_rpow_atTop 6 (by norm_num : (0:ℝ)<1/16)).bound zero_lt_one
  have he := tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually hp
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hroot := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [he,hlog,hroot,eventually_ge_atTop (1:ℕ)] with n hsmall hL hroot hn
  intro R hR
  have hx : (0:ℝ)<n := by exact_mod_cast hn
  change 1≤Real.log (n:ℝ) at hL
  change 1≤(n:ℝ)^(1/3:ℝ) at hroot
  have hL0 := Real.log_natCast_nonneg n
  have hY1 : 1≤medDeskD n := Nat.le_floor (by simpa using hroot)
  have hY1' : (1:ℝ)≤medDeskD n := by exact_mod_cast hY1
  have hY0 : (0:ℝ)<medDeskD n := by linarith
  have hY : (n:ℝ)^(1/3:ℝ) ≤ 2*(medDeskD n:ℝ) := by
    have hh : (n:ℝ)^(1/3:ℝ) < (medDeskD n:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have hpow : (Real.log n)^6 ≤ (n:ℝ)^(1/16:ℝ) := by
    change ‖Real.log (n:ℝ)^(6:ℝ)‖≤_ at hsmall
    simpa only [show (6:ℝ)=((6:ℕ):ℝ) from rfl,Real.rpow_natCast,Real.norm_of_nonneg
      (pow_nonneg hL0 6),Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),one_mul] using hsmall
  have hK := square_tail_scale_bound hn hR hL
  have hτ := square_tail_divisor_bound hn
  have hK0 : 0≤ramanujanSquareScale R := by dsimp [ramanujanSquareScale];positivity
  apply (ramanujan_square_large_denominators n (medDeskD n) R hn hY1).trans
  rw [←mul_div_assoc]
  apply (div_le_iff₀ hY0).mpr
  have hs : (n:ℝ)^(1/16:ℝ)*(n:ℝ)^(1/4:ℝ)*(n:ℝ)^(1/48:ℝ)=(n:ℝ)^(1/3:ℝ) := by
    rw [←Real.rpow_add hx,←Real.rpow_add hx];norm_num
  calc
    _ ≤ (7*(Real.log n)^3)^2*(2*(4096*(n:ℝ)^(1/4:ℝ))) := by gcongr
    _ = 401408*(Real.log n)^6*(n:ℝ)^(1/4:ℝ) := by ring
    _ ≤ 401408*(n:ℝ)^(1/16:ℝ)*(n:ℝ)^(1/4:ℝ) := by gcongr
    _ ≤ _ := by
      apply (le_of_mul_le_mul_right (a:=(n:ℝ)^(1/48:ℝ)) _ (Real.rpow_pos_of_pos hx _))
      rw [show (802816/(n:ℝ)^(1/48:ℝ)*(medDeskD n:ℝ))*((n:ℝ)^(1/48:ℝ))=
        802816*(medDeskD n:ℝ) by field_simp]
      linarith only [hs,hY]

theorem ramanujan_square_terminal_tail_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let R:=terminalPrimeArcCutoff n
      (∑ r∈Ioc (medDeskD n) R, |(dyadicRamanujanDivisor n r:ℝ)*
        (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2|) ≤ ε := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (802816/ε)
  filter_upwards [ramanujan_square_cube_root_tail_power,squareRootLogShell_geometry,hg,eventually_ge_atTop (1:ℕ)]
    with n h hg hn hn0
  apply (h (terminalPrimeArcCutoff n) hg.2.2.2.1).trans
  have hx : (0:ℝ)<n := by exact_mod_cast hn0
  change 802816/ε≤(n:ℝ)^(1/48:ℝ) at hn
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mpr
  linarith only [(div_le_iff₀ hε).mp hn]

end GoldbachPartial
