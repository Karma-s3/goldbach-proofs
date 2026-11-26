import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace GoldbachPartial
open Finset
noncomputable section

private abbrev DivisorPair := Σ _k:ℕ, ℕ × ℕ
private abbrev DivisorQuad := Σ _f:ℕ × (ℕ × ℕ), ℕ

private def divisorPairToQuad (x : DivisorPair) : DivisorQuad :=
  let d := x.2.1
  let e := x.2.2
  let g := d.gcd e
  ⟨(g,d/g,e/g),x.1/(d.lcm e)⟩

private def quadToDivisorPair (f : DivisorQuad) : DivisorPair :=
  let g := f.1.1
  let a := f.1.2.1
  let b := f.1.2.2
  ⟨g*a*b*f.2,g*a,g*b⟩

private theorem divisorPair_product {k d e:ℕ} (hd : d∈k.divisors) (_he : e∈k.divisors) :
    (d.gcd e)*(d/(d.gcd e))*(e/(d.gcd e)) = d.lcm e := by
  let g := d.gcd e
  have hg := Nat.gcd_pos_of_pos_left e (Nat.pos_of_mem_divisors hd)
  have hgd : g*(d/g)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hge : g*(e/g)=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  apply Nat.eq_of_mul_eq_mul_left hg
  change g*(g*(d/g)*(e/g))=g*(d.lcm e)
  calc _ = (g*(d/g))*(g*(e/g)) := by ring
       _ = _ := by rw [hgd,hge]; exact (Nat.gcd_mul_lcm d e).symm

private theorem divisorPair_inverse {k d e:ℕ} (hd:d∈k.divisors) (he:e∈k.divisors) :
    quadToDivisorPair (divisorPairToQuad ⟨k,d,e⟩)=⟨k,d,e⟩ := by
  dsimp [quadToDivisorPair,divisorPairToQuad]
  rw [divisorPair_product hd he,Nat.mul_div_cancel' (Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]

theorem divisor_square_sum_le_quotients (n:ℕ) :
    (∑ k ∈ Icc 1 n, k.divisors.card^2) ≤
      ∑ g ∈ Icc 1 n, ∑ a ∈ Icc 1 n, ∑ b ∈ Icc 1 n, n/(g*a*b) := by
  classical
  let I := Icc 1 n
  let S : Finset DivisorPair := I.sigma (fun k => k.divisors ×ˢ k.divisors)
  let T : Finset DivisorQuad :=
    (I ×ˢ (I ×ˢ I)).sigma (fun f => Icc 1 (n/(f.1*f.2.1*f.2.2)))
  have hb : S.card ≤ T.card := by
    apply card_le_card_of_injOn divisorPairToQuad
    · rintro ⟨k,d,e⟩ hx
      obtain ⟨hkn,hr⟩ := mem_sigma.mp hx
      obtain ⟨hd,he⟩ := mem_product.mp hr
      have hk0 : 0<k := (mem_Icc.mp hkn).1
      have hdn := Nat.le_of_dvd hk0 (Nat.dvd_of_mem_divisors hd)
      have hen := Nat.le_of_dvd hk0 (Nat.dvd_of_mem_divisors he)
      have hk := (mem_Icc.mp hkn).2
      have hg := Nat.gcd_pos_of_pos_left e (Nat.pos_of_mem_divisors hd)
      have hgd := Nat.gcd_dvd_left d e
      have hge := Nat.gcd_dvd_right d e
      have hde := Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
      have hl := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
      apply mem_sigma.mpr
      constructor
      · apply mem_product.mpr
        refine ⟨mem_Icc.mpr ⟨hg,(Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hgd).trans (hdn.trans hk)⟩,?_⟩
        apply mem_product.mpr
        refine ⟨mem_Icc.mpr ⟨?_,(Nat.div_le_self ..).trans (hdn.trans hk)⟩,mem_Icc.mpr ⟨?_,(Nat.div_le_self ..).trans (hen.trans hk)⟩⟩
        · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hgd) hg
        · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_mem_divisors he) hge) hg
      · apply mem_Icc.mpr
        change 1 ≤ k/(d.lcm e) ∧ k/(d.lcm e) ≤ n/(d.gcd e*(d/d.gcd e)*(e/d.gcd e))
        rw [divisorPair_product hd he]
        exact ⟨Nat.div_pos (Nat.le_of_dvd ((mem_Icc.mp hkn).1) hde) hl,Nat.div_le_div_right hk⟩
    · rintro ⟨k,d,e⟩ hx ⟨l,j,s⟩ hy hab
      obtain ⟨hd,he⟩ := mem_product.mp (mem_sigma.mp hx).2
      obtain ⟨hj,hs⟩ := mem_product.mp (mem_sigma.mp hy).2
      exact (divisorPair_inverse hd he).symm.trans ((congrArg quadToDivisorPair hab).trans (divisorPair_inverse hj hs))
  simpa [S,T,I,card_sigma,card_product,Finset.sum_product, pow_two] using hb

private theorem divisor_harmonic_le (n : ℕ) :
    (∑ j ∈ Icc 1 n,(j:ℝ)⁻¹) ≤ 1+Real.log n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1)]
    by_cases h : n=0
    · subst n; norm_num
    · have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(n:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hn)
      rw [Real.log_div hp.ne' hn.ne',inv_div] at hl
      have he : 1-(n:ℝ)/(n+1)=((n:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]

/-- The second moment of the divisor function has an elementary cubic logarithmic bound. -/
theorem divisor_square_mean_bound (n:ℕ) :
    (∑ k ∈ Icc 1 n, (k.divisors.card:ℝ)^2) ≤ (n:ℝ)*(1+Real.log n)^3 := by
  let I := Icc 1 n
  let H : ℝ := ∑ k ∈ I,(k:ℝ)⁻¹
  have hH : 0 ≤ H := sum_nonneg (fun k _ => by positivity)
  have hc : (∑ k ∈ I, (k.divisors.card:ℝ)^2) ≤
      ∑ g ∈ I, ∑ a ∈ I, ∑ b ∈ I, ((n/(g*a*b):ℕ):ℝ) := by
    exact_mod_cast divisor_square_sum_le_quotients n
  apply hc.trans
  calc _ ≤ ∑ g ∈ I, ∑ a ∈ I, ∑ b ∈ I, (n:ℝ)*(g:ℝ)⁻¹*(a:ℝ)⁻¹*(b:ℝ)⁻¹ := by
         apply sum_le_sum
         intro g hg
         apply sum_le_sum
         intro a ha
         apply sum_le_sum
         intro b hb
         have hh := Nat.cast_div_le (α:=ℝ) (m:=n) (n:=g*a*b)
         simpa [Nat.cast_mul,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
       _ = (n:ℝ)*H^3 := by
         simp only [←Finset.mul_sum]
         change (∑ g ∈ I, (∑ a ∈ I, (n:ℝ)*(g:ℝ)⁻¹*(a:ℝ)⁻¹*H)) = _
         simp_rw [←Finset.sum_mul,←Finset.mul_sum]
         rw [←Finset.sum_mul,←Finset.mul_sum]
         change ((n:ℝ)*H*H)*H = _
         ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH (divisor_harmonic_le n) 3)
           (Nat.cast_nonneg n)

end
end GoldbachPartial
