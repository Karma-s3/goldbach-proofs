import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

open Finset

namespace RoughCutoffTransport
theorem odd_correction_totient (n : ℕ) (hn : 0<n) (hev : Even n) :
    (n:ℝ)/n.totient ≤ 2*∏p∈n.primeFactors.filter (fun p=>2<p),((p:ℝ)-1)/((p:ℝ)-2) := by
  classical
  have hh := congrArg (fun z:ℚ=>(z:ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at hh
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hprod : (∏p∈n.primeFactors,(1-(p:ℝ)⁻¹))=(n.totient:ℝ)/n := by
    apply (eq_div_iff hn').mpr
    rw [mul_comm,←hh]
  have h2 : 2∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp hev,hn.ne'⟩
  have hset : n.primeFactors.erase 2=n.primeFactors.filter (fun p=>2<p) := by
    ext p
    simp only [mem_erase,mem_filter]
    constructor
    · rintro ⟨h,hp⟩
      exact ⟨hp,lt_of_le_of_ne (Nat.prime_of_mem_primeFactors hp).two_le (Ne.symm h)⟩
    · rintro ⟨hp,h⟩
      exact ⟨h.ne',hp⟩
  rw [←inv_div,←hprod,←prod_inv_distrib,←mul_prod_erase _ _ h2,hset]
  norm_num
  rw [←prod_inv_distrib,←prod_div_distrib]
  apply prod_le_prod₀
  · intro p hp
    have hp' : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
    exact inv_nonneg.mpr (sub_nonneg.mpr (by rw [inv_le_one₀ (by linarith : (0:ℝ)<p)]; linarith))
  · intro p hp
    have hp' : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
    have h1 : 0<1-(p:ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr (by linarith))
    rw [inv_eq_one_div,div_le_div_iff₀ h1 (by linarith)]
    field_simp
    nlinarith
end RoughCutoffTransport
