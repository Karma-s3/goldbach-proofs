import VerifiedFixedTargetBrunEulerSharp
import VerifiedMiddleFactorCount
namespace GoldbachPartial
open Finset Filter
open scoped Classical
open private thinTotientRatio from VerifiedThinSemiprimeLogUpper
open private large_prime_factor_count from VerifiedMiddleFactorCount
open private product_one_sub_leakage from VerifiedBlockModelHalfSoon

/-- For a power-sized cutoff all prime divisors above the cutoff change the
singular factor by a bounded amount. This recovers one power of n/φ(n) in
the lower sieve, uniformly at a fixed even target. -/
theorem fixedTarget_brunEuler_singular_lower (n y K : ℕ) (hn : 0<n) (he : Even n)
    (hy : 2≤y) (hyK : 2*K≤y) (hnK : n≤y^K) :
    ((n:ℝ)/n.totient)/(512*(1+Real.log y)) ≤ ∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p) := by
  let F := ((Icc 3 y).filter Nat.Prime).filter (fun p=>p∣n)
  let B := fixedTargetBrunPrimes n y
  let P := (Icc 3 y).filter Nat.Prime
  let D := n.primeFactors.filter (fun p=>y<p)
  let g := fun p:ℕ => 1-(p:ℝ)⁻¹
  let w := fun p:ℕ => 1-brunEulerWeight p
  have hB : B=P.filter (fun p=>¬p∣n) := by
    ext p
    simp only [B,P,fixedTargetBrunPrimes,mem_filter,mem_range_succ_iff,mem_Icc]
    constructor
    · rintro ⟨hpy,hpr,hd⟩
      have h2 := hpr.two_le
      exact ⟨⟨⟨by by_contra! h;exact hd ((show p=2 by omega) ▸ even_iff_two_dvd.mp he),hpy⟩,hpr⟩,hd⟩
    · rintro ⟨⟨⟨_,h⟩,hp⟩,hd⟩
      exact ⟨h,hp,hd⟩
  have hfull : (∏p∈F,w p)*(∏p∈B,w p)=∏p∈P,w p := by
    rw [hB];exact prod_filter_mul_prod_filter_not P (fun p=>p∣n) w
  have hlow := brunEuler_product_log_lower y P (filter_subset ..) (fun p hp=>(mem_filter.mp hp).2)
  have hw {p:ℕ} (hp:3≤p) : 0≤w p := sub_nonneg.mpr (brunEulerWeight_bounds hp).2
  have hBW : 0≤∏p∈B,w p := by
    rw [hB];exact prod_nonneg (fun p hp=>hw (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1)
  have hF₂ : 2∉F := fun h=>by have hh := (mem_Icc.mp (mem_filter.mp (mem_filter.mp h).1).1).1;omega
  have hsmall : n.primeFactors.filter (fun p=>¬y<p)=insert 2 F := by
    ext p
    simp only [mem_filter,Nat.mem_primeFactors,mem_insert,F,mem_filter,mem_Icc,not_lt]
    constructor
    · rintro ⟨⟨hp,hd,_⟩,hy'⟩
      by_cases h:p=2
      · exact Or.inl h
      · exact Or.inr ⟨⟨⟨by have := hp.two_le;omega,hy'⟩,hp⟩,hd⟩
    · rintro (rfl|⟨⟨⟨_,hy'⟩,hp⟩,hd⟩)
      · exact ⟨⟨Nat.prime_two,even_iff_two_dvd.mp he,hn.ne'⟩,hy⟩
      · exact ⟨⟨hp,hd,hn.ne'⟩,hy'⟩
  have hprod := prod_filter_mul_prod_filter_not n.primeFactors (fun p=>y<p) g
  rw [hsmall,prod_insert hF₂,←thinTotientRatio n hn] at hprod
  change (∏p∈D,g p)*(g 2*(∏p∈F,g p))=(n.totient:ℝ)/n at hprod
  have h2g : g 2=1/2 := by norm_num [g]
  rw [h2g] at hprod
  have hcard : D.card≤K := large_prime_factor_count hn (by omega) (hnK.trans_lt (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)))
  have hinv (p : ℕ) (hp : p∈D) : (p:ℝ)⁻¹≤1/y := by
    have hp' := (mem_filter.mp hp).2
    simpa only [one_div] using one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0<y) : (0:ℝ)<y) (by exact_mod_cast hp'.le : (y:ℝ)≤p)
  have hsum : (∑p∈D,(p:ℝ)⁻¹)≤1/2 := by
    calc _ ≤ ∑_p∈D,(1/(y:ℝ)) := sum_le_sum hinv
         _ = (D.card:ℝ)/y := by simp [div_eq_mul_inv]
         _ ≤ (K:ℝ)/y := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
         _ ≤ _ := (div_le_iff₀ (by exact_mod_cast (by omega : 0<y))).mpr (by
           have hh : (2:ℝ)*K≤y := by exact_mod_cast hyK
           linarith only [hh])
  have hD : 1/2≤∏p∈D,g p := by
    have hh := product_one_sub_leakage D (fun p=>(p:ℝ)⁻¹) (fun p hp=> ⟨inv_nonneg.mpr (Nat.cast_nonneg _),
      inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).one_le)⟩)
    dsimp only [g];linarith only [hsum,hh]
  have hcomp : (∏p∈F,w p)≤∏p∈F,g p := by
    apply prod_le_prod₀
    · exact fun p hp=>hw (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
    · intro p hp
      have h3 : (3:ℝ)≤p := by exact_mod_cast (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
      dsimp only [w,g,brunEulerWeight]
      rw [←one_div]
      exact sub_le_sub_left (one_div_le_one_div_of_le (by linarith) (by linarith)) _
  have hF0 : 0≤∏p∈F,g p := hcomp.trans' (prod_nonneg (fun p hp=>hw (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1))
  have hcomp' : (∏p∈F,w p)≤4*((n.totient:ℝ)/n) := by
    have hh := mul_le_mul_of_nonneg_right hD (mul_nonneg (by norm_num : (0:ℝ)≤1/2) hF0)
    linarith only [hh,hprod,hcomp]
  have hf := mul_le_mul_of_nonneg_right hcomp' hBW
  rw [hfull] at hf
  have h := hlow.trans hf
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hp' : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hL : 0<1+Real.log y := by linarith only [Real.log_natCast_nonneg y]
  change (n:ℝ)/n.totient/(512*(1+Real.log y))≤∏p∈B,w p
  field_simp at h ⊢
  linarith only [h]

theorem sieve_survivor_singular_model_floor (n y K : ℕ) (hn : 20≤n) (he : Even n)
    (hy : 2≤y) (hyK : 2*K≤y) (hnK : n≤y^K) (hyn : y≤n) (hL : 1≤Real.log n) :
    ((n:ℝ)/n.totient)*n/(8192*Real.log n) ≤
      ((n/2-n/4:ℕ):ℝ)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) := by
  have hl := fixedTarget_brunEuler_singular_lower n y K (by omega) he hy hyK hnK
  have hl0 := Real.log_le_log (by exact_mod_cast (show 0<y by omega) : (0:ℝ)<y) (by exact_mod_cast hyn : (y:ℝ)≤n)
  have hLn : 0<Real.log n := by linarith
  have hLy : 0<1+Real.log y := by linarith only [Real.log_natCast_nonneg y]
  have hu : ((n:ℝ)/n.totient)/(1024*Real.log n) ≤ _ := (div_le_div_of_nonneg_left (by positivity)
    (mul_pos (by norm_num) hLy) (by linarith only [hl0,hL] : 512*(1+Real.log y) ≤ 1024*Real.log n)).trans hl
  have hlen : (n:ℝ)/8 ≤ ((n/2-n/4:ℕ):ℝ) := by
    have ht : (n:ℝ)≤8*((n/2-n/4:ℕ):ℝ) := by exact_mod_cast (show n≤8*(n/2-n/4) by omega)
    linarith only [ht]
  exact le_trans (le_of_eq (by ring)) (mul_le_mul hlen hu (by positivity) (Nat.cast_nonneg _))

end GoldbachPartial