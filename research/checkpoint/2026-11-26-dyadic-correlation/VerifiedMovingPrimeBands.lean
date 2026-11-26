import PrimeLinearDenominators
import VerifiedFourNinthsBrun
import VerifiedFixedTargetBrunEulerSharp
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

noncomputable def movingPrimeCutoff (n : ℕ) (a : ℝ) : ℕ := ⌊(n:ℝ)^a⌋₊
noncomputable def movingPrimeBand (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (Ioc (movingPrimeCutoff n a) (movingPrimeCutoff n b)).filter Nat.Prime

theorem movingPrimeBand_weight_upper (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ n:ℕ in atTop, (∑r∈movingPrimeBand n a b,brunEulerWeight r) ≤
      8*Real.log 4*((b-a)/a) := by
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpa := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hpa.eventually_ge_atTop (4:ℝ),
    hln.eventually_ge_atTop (2*Real.log 2/a),
    hln.eventually_ge_atTop ((1+Real.log 2)/(b-a))] with n hn hpow h1 h2
  let R := movingPrimeCutoff n a
  let Q := movingPrimeCutoff n b
  let L := Real.log (n:ℝ)
  have hN : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn' : (0:ℝ)<n := by linarith
  change 4≤(n:ℝ)^a at hpow
  have hR : 2≤R := (Nat.le_floor_iff (by positivity)).mpr (by push_cast;linarith)
  have hRQ : R≤Q := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN hab.le)
  have hRq : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hQq : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hRf : (n:ℝ)^a<(R:ℝ)+1 := Nat.lt_floor_add_one _
  have hRlog : a*L-Real.log 2≤Real.log R := by
    have hle : (n:ℝ)^a/2≤(R:ℝ) := by linarith
    have hh := Real.log_le_log (by positivity) hle
    rw [Real.log_div (by positivity) (by norm_num),Real.log_rpow hn'] at hh
    simpa [L,mul_comm] using hh
  have hQlog : Real.log Q≤b*L := by
    have hh := Real.log_le_log hQq (Nat.floor_le (by positivity : 0≤(n:ℝ)^b))
    rwa [Real.log_rpow hn'] at hh
  have hL : 0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  change 2*Real.log 2/a≤L at h1
  change (1+Real.log 2)/(b-a)≤L at h2
  have hsmall := (div_le_iff₀ ha).mp h1
  have hgap := (div_le_iff₀ (sub_pos.mpr hab)).mp h2
  have hrl : 0<Real.log R := Real.log_pos (by exact_mod_cast (show 1<R by omega))
  have hbase := prime_denominator_reciprocals R Q hR hRQ
  apply hbase.trans
  rw [div_mul_eq_mul_div,div_le_iff₀ hrl]
  have hg : 1+Real.log Q-Real.log R≤2*((b-a)*L) := by linarith
  have hlo : a*L≤2*Real.log R := by linarith
  have hlog4 : 0≤Real.log 4 := by positivity
  have hpos : 0≤(b-a)/a := div_nonneg (sub_nonneg.mpr hab.le) ha.le
  have hbott := mul_le_mul_of_nonneg_right hlo (sub_nonneg.mpr hab.le)
  field_simp [ha.ne']
  nlinarith only [mul_le_mul_of_nonneg_right hg ha.le,hbott]

theorem movingPrimeBand_arbitrarily_small {a B ε : ℝ} (ha : 0<a) (hB : a<B) (hε : 0<ε) :
    ∃ b:ℝ, a<b ∧ b<B ∧ ∀ᶠ n:ℕ in atTop, (∑r∈movingPrimeBand n a b,brunEulerWeight r)≤ε := by
  have hc : 0<8*Real.log 4 := by positivity
  let b := a + min ((B-a)/2) (ε*a/(8*Real.log 4))
  have hb : a<b := by dsimp [b]; exact lt_add_of_pos_right _ (lt_min (by linarith) (by positivity))
  have hbB : b<B := by dsimp [b];linarith only [min_le_left ((B-a)/2) (ε*a/(8*Real.log 4)),hB]
  refine ⟨b,hb,hbB,(movingPrimeBand_weight_upper a b ha hb).mono (fun n hn=>hn.trans ?_)⟩
  have h0 := min_le_right ((B-a)/2) (ε*a/(8*Real.log 4))
  rw [le_div_iff₀ hc] at h0
  dsimp only [b]
  rw [add_sub_cancel_left,mul_div_assoc',div_le_iff₀ ha]
  linarith
end GoldbachPartial