import PrimeArcModelBounds
import LargeDivisorZeroDecomposition

namespace GoldbachPartial
open Finset

/-- The sum of the Ramanujan coefficients over a complete divisor lattice. -/
theorem sum_dyadicRamanujanDivisor_divisors (n : ℕ) {m : ℕ} (hm : 0<m) :
    ∑ r∈m.divisors, dyadicRamanujanDivisor n r = if m∣n then (m:ℤ) else 0 := by
  let g (d : ℕ) : ℤ := if d∣n then d else 0
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f:=dyadicRamanujanDivisor n) (g:=g)).mpr _ m hm
  intro k hk
  simp only [Int.cast_id]
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => (ArithmeticFunction.moebius i:ℤ)*g j)]
  unfold dyadicRamanujanDivisor
  have hfilter : k.divisors.filter (fun d => d∣n)=(k.gcd n).divisors := by
    ext d
    constructor
    · rintro hx
      obtain ⟨hd,hn⟩ := mem_filter.mp hx
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hd) hn,(Nat.gcd_pos_of_pos_left n hk).ne'⟩
    · intro hx
      obtain ⟨hdk,hdn⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hx)
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdk,hk.ne'⟩,hdn⟩
  rw [←hfilter,Finset.sum_filter]
  apply sum_congr rfl; intro d _
  by_cases h : d∣n <;> simp [g,h]

/-- The truncated transform of the divisor weights in the finite Ramanujan expansion. -/
noncomputable def crtRamanujanTruncation (R r : ℕ) : ℝ :=
  ∑ d∈(Icc 1 R).filter (fun d => r∣d),crtLambdaCoefficient d/(d:ℝ)

private theorem finite_square_exchange (I : Finset ℕ) (C : ℕ→ℝ) (b : ℕ→ℕ→ℝ) :
    ∑ r∈I,C r*(∑ d∈I,b r d)^2 = ∑ d∈I,∑ e∈I,∑ r∈I,C r*b r d*b r e := by
  calc
    _ = ∑ r∈I,∑ d∈I,∑ e∈I,C r*b r d*b r e := by
      apply sum_congr rfl; intro r _
      rw [pow_two]
      simp only [mul_sum, sum_mul, mul_assoc]
      apply sum_congr rfl; intro d _
      apply sum_congr rfl; intro e _;ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      exact sum_comm

private theorem restricted_ramanujan_sum {d e R : ℕ} (n : ℕ)
    (hd : d∈Icc 1 R) (_he : e∈Icc 1 R) :
    ∑ r∈(Icc 1 R).filter (fun r => r∣d ∧ r∣e),(dyadicRamanujanDivisor n r:ℝ) =
      if d.gcd e∣n then (d.gcd e:ℝ) else 0 := by
  have hd0 : 0<d := (mem_Icc.mp hd).1
  have hpos := Nat.gcd_pos_of_pos_left e hd0
  have hset : (Icc 1 R).filter (fun r => r∣d ∧ r∣e)=(d.gcd e).divisors := by
    ext r
    constructor
    · intro h
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (mem_filter.mp h).2.1 (mem_filter.mp h).2.2,hpos.ne'⟩
    · intro h
      obtain ⟨hrd,hre⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors h)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hrd hd0,(Nat.le_of_dvd hd0 hrd).trans (mem_Icc.mp hd).2⟩,hrd,hre⟩
  rw [hset]
  exact_mod_cast sum_dyadicRamanujanDivisor_divisors n hpos

/-- Diagonalization of the complete-period CRT density for the actual small-divisor weights. -/
theorem crt_small_main_ramanujan (n R : ℕ) (X : ℝ) :
    (∑ d∈Icc 1 R,∑ e∈Icc 1 R,crtLambdaCoefficient d*crtLambdaCoefficient e*
      (if d.gcd e∣n then X/(d.lcm e:ℝ) else 0)) =
    X*∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r)^2 := by
  let I := Icc 1 R
  let C := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)
  let w := fun d : ℕ => crtLambdaCoefficient d/(d:ℝ)
  let b := fun r d : ℕ => if r∣d then w d else 0
  have hw (r : ℕ) : crtRamanujanTruncation R r=∑ d∈I,b r d := by
    unfold crtRamanujanTruncation;exact Finset.sum_filter ..
  change _=X*∑ r∈I,C r*(crtRamanujanTruncation R r)^2
  simp_rw [hw]
  rw [finite_square_exchange]
  simp only [mul_sum]
  apply sum_congr rfl;intro d hd
  apply sum_congr rfl;intro e he
  have hd0 : 0<d := (mem_Icc.mp hd).1
  have he0 : 0<e := (mem_Icc.mp he).1
  have hsum : (∑ r∈I,X*(C r*b r d*b r e)) =
      X*(w d*w e)*(∑ r∈I.filter (fun r => r∣d ∧ r∣e),C r) := by
    rw [Finset.sum_filter,mul_sum]
    apply sum_congr rfl;intro r _
    by_cases hrd : r∣d <;> by_cases hre : r∣e <;> simp [b,hrd,hre]
    ring
  rw [hsum]
  have h := restricted_ramanujan_sum n hd he
  change (∑ r∈I.filter (fun r => r∣d ∧ r∣e),C r)=_ at h
  rw [h]
  by_cases hg : d.gcd e∣n
  · simp only [hg,ite_true]
    have hl : (0:ℝ)<d.lcm e := by exact_mod_cast Nat.lcm_pos hd0 he0
    have hd' : (0:ℝ)<d := by exact_mod_cast hd0
    have he' : (0:ℝ)<e := by exact_mod_cast he0
    have hprod : (d.gcd e:ℝ)*(d.lcm e:ℝ)=(d:ℝ)*e := by exact_mod_cast Nat.gcd_mul_lcm d e
    dsimp only [w]
    field_simp
    linear_combination -(crtLambdaCoefficient d*crtLambdaCoefficient e*X)*hprod
  · simp [hg]

/-- The true finite endpoint count splits into the diagonalized complete-period term and its CRT remainders. -/
theorem crt_small_endpoints_ramanujan (n R : ℕ) :
    (∑ d∈Icc 1 R,∑ e∈Icc 1 R,crtLambdaCoefficient d*crtLambdaCoefficient e*crtEndpointCount n d e) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r)^2) +
      ∑ d∈Icc 1 R,∑ e∈Icc 1 R,crtLambdaCoefficient d*crtLambdaCoefficient e*crtRowError n d e := by
  rw [←crt_small_main_ramanujan,←sum_add_distrib]
  apply sum_congr rfl; intro d hd
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro e he
  rw [crtRowError,crtCompleteCount_eq (mem_Icc.mp hd).1 (mem_Icc.mp he).1]
  by_cases h : d.gcd e∣n <;> simp [h]
  ring

private theorem truncatedLambdaDivisors_window (R k : ℕ) (hk : 0<k) :
    truncatedLambdaDivisors R k=∑ d∈Icc 1 R,if d∣k then crtLambdaCoefficient d else 0 := by
  unfold truncatedLambdaDivisors;rw [←sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext d
  simp only [mem_filter,Nat.mem_divisors,mem_Icc]
  constructor
  · rintro ⟨⟨hd,_⟩,hR⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk,hR⟩,hd⟩
  · rintro ⟨⟨_,hR⟩,hd⟩
    exact ⟨⟨hd,hk.ne'⟩,hR⟩

/-- The exact small-divisor self-convolution appearing in the zero-frequency correction. -/
theorem truncatedLambda_self_ramanujan (n R : ℕ) :
    (∑ k∈Ioo 0 n,truncatedLambdaDivisors R k*truncatedLambdaDivisors R (n-k)) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(crtRamanujanTruncation R r)^2) +
      ∑ d∈Icc 1 R,∑ e∈Icc 1 R,crtLambdaCoefficient d*crtLambdaCoefficient e*crtRowError n d e := by
  rw [←crt_small_endpoints_ramanujan]
  let K := Ioo 0 n
  let I := Icc 1 R
  let f := crtLambdaCoefficient
  let z := fun k d e : ℕ => f d*f e*(if d∣k ∧ e∣n-k then (1:ℝ) else 0)
  calc
    _ = ∑ k∈K,∑ d∈I,∑ e∈I,z k d e := by
      apply sum_congr rfl; intro k hk
      obtain ⟨h₁,h₂⟩ := mem_Ioo.mp hk
      rw [truncatedLambdaDivisors_window _ _ h₁,truncatedLambdaDivisors_window _ _ (by omega : 0<n-k),sum_mul]
      apply sum_congr rfl;intro d _
      rw [mul_sum]
      apply sum_congr rfl;intro e _
      by_cases h : d∣k <;> by_cases he : e∣n-k <;> simp [h,he,z,f]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      rw [sum_comm]
      apply sum_congr rfl;intro e _
      dsimp only [z,crtEndpointCount,f,K]
      rw [mul_sum]

end GoldbachPartial
