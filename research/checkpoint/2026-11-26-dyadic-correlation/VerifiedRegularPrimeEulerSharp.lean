import VerifiedThinSemiprimeLogUpper
import Batteries.Tactic.OpenPrivate

namespace GoldbachPartial
open Finset
open private thinTotientRatio from VerifiedThinSemiprimeLogUpper

theorem regularPrime_euler_density_one (n z : ℕ) (hn : 0<n) :
    Real.log ((z:ℝ)+1)*((n.totient:ℝ)/n)*
       (∏p∈thinRegularPrimes n z,(1-1/((p:ℝ)-1))) ≤ 1 := by
  let P := (Icc 2 z).filter Nat.Prime
  let G := thinRegularPrimes n z
  let F := P.filter (fun p=>p∣n)
  let g (p : ℕ) := 1-(p:ℝ)⁻¹
  have hg {p : ℕ} (hp : p.Prime) : 0≤g p :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le))
  have hGP (p : ℕ) (hp : p∈G) : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
  have hfun : (∏p∈G,g p)*(∏p∈F,g p)=∏p∈P,g p := by
    rw [mul_comm]
    exact prod_filter_mul_prod_filter_not P (fun p => p∣n) g
  have hFsub : F⊆n.primeFactors := by
    intro p hp
    obtain ⟨hp',hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp').2,hd,hn.ne'⟩
  have hF : (n.totient:ℝ)/n≤∏p∈F,g p := by
    rw [thinTotientRatio n hn]
    apply prod_le_prod_of_subset_of_le_one₀ hFsub
    · exact fun p hp => hg (Nat.prime_of_mem_primeFactors hp)
    · intro p _ _
      linarith only [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) p)]
  have hD : (∏p∈G,(1-1/((p:ℝ)-1)))≤∏p∈G,g p := by
    apply prod_le_prod₀
    · intro p hp
      have hh : (2:ℝ)≤p := by exact_mod_cast (hGP p hp).two_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
    · intro p hp
      have hh : (2:ℝ)≤p := by exact_mod_cast (hGP p hp).two_le
      have hh' := one_div_le_one_div_of_le (show (0:ℝ)<p-1 by linarith) (show (p:ℝ)-1≤p by linarith)
      simpa only [g,one_div] using sub_le_sub_left hh' 1
  have hL : 0≤Real.log ((z:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) z; linarith)
  have hG : 0≤∏p∈G,g p := prod_nonneg fun p hp => hg (hGP p hp)
  calc
    _ ≤ (Real.log ((z:ℝ)+1))*(((n.totient:ℝ)/n)*(∏p∈G,g p)) := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_left hD (mul_nonneg hL (by positivity))
    _ ≤ (Real.log ((z:ℝ)+1))*((∏p∈F,g p)*(∏p∈G,g p)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF hG) hL
    _ ≤ 1 := by rw [mul_comm (∏p∈F,g p),hfun]; exact thinEuler_prime_product_log z

theorem regularPrime_euler_singular_upper (n z : ℕ) (hn : 0<n) (hz : 0<z) :
    (∏p∈thinRegularPrimes n z,(1-1/((p:ℝ)-1))) ≤
      ((n:ℝ)/n.totient)/Real.log ((z:ℝ)+1) := by
  have hl : 0<Real.log ((z:ℝ)+1) := Real.log_pos (by exact_mod_cast (show 1<z+1 by omega))
  have hφ : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hh := regularPrime_euler_density_one n z hn
  rw [le_div_iff₀ hl,le_div_iff₀ hφ]
  field_simp at hh
  linarith
end GoldbachPartial