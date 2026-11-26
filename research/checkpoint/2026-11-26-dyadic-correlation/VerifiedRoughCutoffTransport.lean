import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace RoughCutoffTransport
open Finset
open scoped Classical

theorem floor_to_real_rough_card (n : ℕ) (x : ℝ) (S : Finset ℕ) (hx : 1≤x)
    (hS : S⊆range n)
    (hrough : ∀k∈S,∀r:ℕ,r.Prime → (r ∣ n - k) → ⌊x⌋₊≤r) :
    S.card ≤ (S.filter (fun k=>∀r:ℕ,r.Prime → (r ∣ n - k) → x≤(r:ℝ))).card + n/⌊x⌋₊ := by
  let z := ⌊x⌋₊
  let P := fun k:ℕ=>∀r:ℕ,r.Prime → (r ∣ n - k) → x≤(r:ℝ)
  let A := S.filter (fun k=>¬P k)
  have hpos : 0<z := Nat.le_floor (by simpa using hx)
  have hbad {k : ℕ} (hk : k∈A) : z∣n-k := by
    obtain ⟨hs,hno⟩ := mem_filter.mp hk
    change ¬(∀r:ℕ,r.Prime → (r ∣ n - k) → x≤(r:ℝ)) at hno
    push Not at hno
    obtain ⟨r,hr,hd,hl⟩ := hno
    have hzr : z≤r := hrough k hs r hr hd
    have hrz : r≤z := Nat.le_floor hl.le
    exact le_antisymm hzr hrz ▸ hd
  have hcard : A.card≤(Icc 1 (n/z)).card := by
    apply card_le_card_of_injOn (fun k=> (n-k)/z)
    · intro k hk
      have hk' : k<n := mem_range.mp (hS (mem_filter.mp hk).1)
      have hlead : z≤n-k := Nat.le_of_dvd (by omega) (hbad hk)
      exact mem_Icc.mpr ⟨Nat.div_pos hlead hpos,Nat.div_le_div_right (Nat.sub_le n k)⟩
    · intro k hk l hl he
      have hk' : k<n := mem_range.mp (hS (mem_filter.mp hk).1)
      have hl' : l<n := mem_range.mp (hS (mem_filter.mp hl).1)
      have heq := congrArg (fun m:ℕ=>m*z) he
      change (n-k)/z*z=(n-l)/z*z at heq
      rw [Nat.div_mul_cancel (hbad hk),Nat.div_mul_cancel (hbad hl)] at heq
      omega
  have heq := card_filter_add_card_filter_not (s:=S) (p:=P)
  have hc : A.card≤n/z := by simpa using hcard
  change S.card≤(S.filter P).card+n/z
  change (S.filter P).card+A.card=S.card at heq
  omega


open Filter in
theorem floor_power_residue_error (δ β : ℝ) (hδ : 0<δ) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ((n/⌊(n:ℝ)^β⌋₊ : ℕ):ℝ) ≤ δ*(n:ℝ)/(Real.log n)^2 := by
  have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop (2:ℝ) hβ).bound (by positivity : 0<δ/2))
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hh,ht.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with n he hl hn
  let x := (n:ℝ)^β
  let z := ⌊x⌋₊
  have hx : 1≤x := Real.one_le_rpow (by exact_mod_cast hn) hβ.le
  have hz : 0<z := Nat.le_floor (by simpa using hx)
  have hz1 : (1:ℝ)≤z := by exact_mod_cast hz
  have hxz : x<(z:ℝ)+1 := Nat.lt_floor_add_one x
  have hxr : x≤2*(z:ℝ) := by linarith only [hz1,hxz]
  have hL : 0<Real.log (n:ℝ) := zero_lt_one.trans_le hl
  have hnorm : (Real.log (n:ℝ))^2 ≤ δ/2*x := by
    change ‖Real.log (n:ℝ)^(2:ℝ)‖≤δ/2*‖x‖ at he
    simpa only [Real.rpow_two,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (zero_le_one.trans hx)] using he
  have hpow : (Real.log n)^2 ≤ δ*(z:ℝ) := by
    have hv := mul_le_mul_of_nonneg_left hxr (show 0≤δ/2 by positivity)
    linarith only [hnorm,hv]
  have hdiv : ((n/z:ℕ):ℝ)*(z:ℝ)≤n := by exact_mod_cast Nat.div_mul_le_self n z
  change ((n/z:ℕ):ℝ)≤_
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  have hpay := (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α:=ℝ) (n/z))).trans_eq (by ring : ((n/z:ℕ):ℝ)*(δ*(z:ℝ))=δ*(((n/z:ℕ):ℝ)*(z:ℝ)))
  exact hpay.trans (mul_le_mul_of_nonneg_left hdiv hδ.le)

end RoughCutoffTransport