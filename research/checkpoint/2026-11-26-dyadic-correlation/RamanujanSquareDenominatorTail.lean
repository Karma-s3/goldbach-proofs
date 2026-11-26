import TruncatedRamanujanSquare
import DeepPrimeShell
import NonresonantZeroFrequency

namespace GoldbachPartial
open Finset Filter
open scoped Topology

/-- An explicit upper bound on r times the absolute difference of the two
coefficients in the completed square. -/
noncomputable def ramanujanSquareScale (R : ℕ) : ℝ :=
  Real.log R*(1+Real.log R)^2 + ((Nat.log 2 R:ℕ):ℝ)+1

theorem scaled_crtRamanujanTruncation_bound (R r : ℕ) (hr : 0<r) :
    (r:ℝ)*|crtRamanujanTruncation R r| ≤ Real.log R*(1+Real.log R)^2 := by
  let I := (Icc 1 R).filter (fun d => r∣d)
  let u := fun d : ℕ => d/r-1
  have hd {d : ℕ} (h : d∈I) : 0<d/r ∧ d/r*r=d ∧ d≤R := by
    obtain ⟨hi,hdiv⟩ := mem_filter.mp h
    have hpos := (mem_Icc.mp hi).1
    exact ⟨Nat.div_pos (Nat.le_of_dvd hpos hdiv) hr,Nat.div_mul_cancel hdiv,(mem_Icc.mp hi).2⟩
  have hf : ∑ d∈I,(r:ℝ)/(d:ℝ) ≤ (1+Real.log R)^2 := by
    apply le_trans _ (signedFiber_divisor_harmonic R)
    apply sum_le_sum_of_injOn u
    · intro a ha b hb h
      have h1 := hd ha;have h2 := hd hb
      dsimp only [u] at h
      have he : a/r=b/r := by omega
      rw [he] at h1
      omega
    · intro k hk
      obtain ⟨d,he,rfl⟩ := mem_image.mp hk
      have hh := hd he
      have ht := Nat.div_le_self d r
      exact mem_range.mpr (by dsimp [u];omega)
    · intro d he
      obtain ⟨hg,hm,_⟩ := hd he
      have hu : u d+1=d/r := by dsimp [u];omega
      rw [hu]
      have hn : 1≤(d/r).divisors.card := card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hg.ne'⟩⟩
      have hh : (1:ℝ)≤(d/r).divisors.card := by exact_mod_cast hn
      have heq : (r:ℝ)/(d:ℝ)=1/((d/r:ℕ):ℝ) := by
        have hm' : ((d/r:ℕ):ℝ)*r=d := by exact_mod_cast hm
        have hi : (0:ℝ)<r := by exact_mod_cast hr
        rw [←hm'];field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
    · intro k _ _
      positivity
  have hR : 0≤Real.log R := Real.log_natCast_nonneg R
  change (r:ℝ)*|∑ d∈I,crtLambdaCoefficient d/(d:ℝ)|≤_
  apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (Nat.cast_nonneg r)).trans
  rw [mul_sum]
  calc
    _ ≤ ∑ d∈I,Real.log R*((r:ℝ)/d) := by
      apply sum_le_sum
      intro d hdmem
      obtain ⟨hp,hR'⟩ := mem_Icc.mp (mem_filter.mp hdmem).1
      have hmu : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
      have hf' : |crtLambdaCoefficient d|≤Real.log R := by
        rw [crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg _)]
        exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hmu).trans
          (Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hR'))
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)]
      calc _ ≤ (r:ℝ)*(Real.log R/d) := by gcongr
           _ = _ := by ring
    _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left hf hR

theorem ramanujan_square_large_denominators (n Y R : ℕ) (hn : 0<n) (hY : 0<Y) :
    (∑ r∈Ioc Y R, |(dyadicRamanujanDivisor n r:ℝ)*
      (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2|) ≤
      (ramanujanSquareScale R)^2*(2*(n.divisors.card:ℝ)/Y) := by
  let K := ramanujanSquareScale R
  have hK : 0≤K := by dsimp [K,ramanujanSquareScale];positivity
  have hrow (r : ℕ) (hr : r∈Ioc Y R) :
      |(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2|
        ≤ K^2*((r.gcd n:ℝ)/(r:ℝ)^2) := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hr
    have hr' : 0<r := by omega
    have hr0 : (0:ℝ)<r := by exact_mod_cast hr'
    by_cases hs : Squarefree r
    · have hc : |(dyadicRamanujanDivisor n r:ℝ)|≤(r.gcd n:ℝ) := by
        exact_mod_cast (abs_dyadicRamanujanDivisor_squarefree hs).le.trans
          (show ((r.gcd n).totient:ℤ)≤(r.gcd n:ℤ) by exact_mod_cast Nat.totient_le _)
      have hp : (0:ℝ)<r.totient := by exact_mod_cast Nat.totient_pos.mpr hr'
      have hm : |(ArithmeticFunction.moebius r:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=r)
      have hrat : (r:ℝ) ≤ (((Nat.log 2 R:ℕ):ℝ)+1)*r.totient := by
        exact_mod_cast (nat_le_totient_mul_log2_succ hr').trans
          (Nat.mul_le_mul_right r.totient (Nat.add_le_add_right (Nat.log_mono_right (b:=2) hu) 1))
      have hm' : (r:ℝ)*|(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ)|≤((Nat.log 2 R:ℕ):ℝ)+1 := by
        rw [abs_div,abs_of_nonneg hp.le,←mul_div_assoc]
        exact (div_le_iff₀ hp).mpr ((mul_le_of_le_one_right hr0.le hm).trans hrat)
      have hh := mul_le_mul_of_nonneg_left (abs_sub (crtRamanujanTruncation R r)
        ((ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))) hr0.le
      have hb : |crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ)|≤K/r := by
        apply (le_div_iff₀ hr0).mpr
        dsimp [K,ramanujanSquareScale]
        linarith only [hh,hm',scaled_crtRamanujanTruncation_bound R r hr']
      rw [abs_mul,abs_pow]
      exact (mul_le_mul hc (pow_le_pow_left₀ (abs_nonneg _) hb 2) (sq_nonneg _) (Nat.cast_nonneg _)).trans_eq (by ring)
    · have hm := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      have htr : crtRamanujanTruncation R r=0 := by
        unfold crtRamanujanTruncation
        apply sum_eq_zero
        intro d hd
        have hd' : ¬Squarefree d := fun h => hs (h.squarefree_of_dvd (mem_filter.mp hd).2)
        simp [crtLambdaCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd']
      rw [htr,hm]
      simp only [Int.cast_zero,zero_div,sub_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
        zero_pow,mul_zero,abs_zero]
      positivity
  change _≤K^2*_
  calc
    _ ≤ ∑ r∈Ioc Y R,K^2*((r.gcd n:ℝ)/(r:ℝ)^2) := sum_le_sum hrow
    _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left (interval_gcd_over_sq n Y R hn hY) (sq_nonneg _)

end GoldbachPartial