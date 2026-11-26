import ExactRamanujanWeights
import SmallDivisorCompletedSquare

namespace GoldbachPartial
open Finset

/-- The divisor weight on one integer, with all divisors taken from the positive cutoff. -/
noncomputable def finiteDivisorWeightSum (R : ℕ) (f : ℕ→ℝ) (k : ℕ) : ℝ :=
  ∑ d∈(Icc 1 R).filter (fun d => d∣k),f d

/-- The zero-frequency correction for exact finite Ramanujan divisor weights. -/
noncomputable def exactRamanujanZeroCorrection (n R : ℕ) : ℝ :=
  (∑ k∈Ioo 0 n,finiteDivisorWeightSum R (exactRamanujanWeight R) k*
    finiteDivisorWeightSum R (exactRamanujanWeight R) (n-k)) -
  2*∑ k∈Ioo 0 n,ArithmeticFunction.vonMangoldt k*finiteDivisorWeightSum R (exactRamanujanWeight R) (n-k)

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

/-- Diagonalization of the complete-period CRT density for arbitrary finite divisor weights. -/
theorem finiteWeight_square_main (n R : ℕ) (F : ℕ→ℝ) (X : ℝ) :
    (∑ d∈Icc 1 R,∑ e∈Icc 1 R,F d*F e*
      (if d.gcd e∣n then X/(d.lcm e:ℝ) else 0)) =
    X*∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(finiteRamanujanTransform R F r)^2 := by
  let I := Icc 1 R
  let C := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)
  let w := fun d : ℕ => F d/(d:ℝ)
  let b := fun r d : ℕ => if r∣d then w d else 0
  have hw (r : ℕ) : finiteRamanujanTransform R F r=∑ d∈I,b r d := by
    unfold finiteRamanujanTransform;exact Finset.sum_filter ..
  change _=X*∑ r∈I,C r*(finiteRamanujanTransform R F r)^2
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
    linear_combination -(F d*F e*X)*hprod
  · simp [hg]

/-- The true finite endpoint count splits into the diagonalized complete-period term and its CRT remainders. -/
theorem finiteWeight_square_endpoints (n R : ℕ) (F : ℕ→ℝ) :
    (∑ d∈Icc 1 R,∑ e∈Icc 1 R,F d*F e*crtEndpointCount n d e) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(finiteRamanujanTransform R F r)^2) +
      ∑ d∈Icc 1 R,∑ e∈Icc 1 R,F d*F e*crtRowError n d e := by
  rw [←finiteWeight_square_main,←sum_add_distrib]
  apply sum_congr rfl; intro d hd
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro e he
  rw [crtRowError,crtCompleteCount_eq (mem_Icc.mp hd).1 (mem_Icc.mp he).1]
  by_cases h : d.gcd e∣n <;> simp [h]
  ring

/-- The exact small-divisor self-convolution appearing in the zero-frequency correction. -/
theorem finiteWeight_self_ramanujan (n R : ℕ) (F : ℕ→ℝ) :
    (∑ k∈Ioo 0 n,finiteDivisorWeightSum R F k*finiteDivisorWeightSum R F (n-k)) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*(finiteRamanujanTransform R F r)^2) +
      ∑ d∈Icc 1 R,∑ e∈Icc 1 R,F d*F e*crtRowError n d e := by
  rw [←finiteWeight_square_endpoints]
  let K := Ioo 0 n
  let I := Icc 1 R
  let z := fun k d e : ℕ => F d*F e*(if d∣k ∧ e∣n-k then (1:ℝ) else 0)
  calc
    _ = ∑ k∈K,∑ d∈I,∑ e∈I,z k d e := by
      apply sum_congr rfl; intro k _
      simp only [finiteDivisorWeightSum,sum_filter]
      rw [sum_mul]
      apply sum_congr rfl;intro d _
      rw [mul_sum]
      apply sum_congr rfl;intro e _
      by_cases h : d∣k <;> by_cases he : e∣n-k <;> simp [h,he,z]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      rw [sum_comm]
      apply sum_congr rfl;intro e _
      dsimp only [z,crtEndpointCount,K]
      rw [mul_sum]

/-- Diagonal form of the prime progression main term, with the actual truncated divisor weights. -/
theorem finiteWeight_mixed_main (n R : ℕ) (F : ℕ→ℝ) (hF : ∀ d, ¬Squarefree d → F d=0) (X : ℝ) :
    (∑ d∈Icc 1 R,F d*(if d.Coprime n then X/(d.totient:ℝ) else 0)) =
    X*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)*
      finiteRamanujanTransform R F r) := by
  let I := Icc 1 R
  let C := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)
  let f := F
  let a := fun r d : ℕ => if r∣d then C r else 0
  have row (r : ℕ) :
      X*(C r*finiteRamanujanTransform R F r)=∑ d∈I, X*(f d/(d:ℝ))*a r d := by
    unfold finiteRamanujanTransform
    rw [sum_filter,mul_sum,mul_sum]
    apply sum_congr rfl;intro d _
    by_cases h : r∣d <;> simp [a,f,h]
    ring
  have col (d : ℕ) (hd : d∈I) :
      (∑ r∈I,X*(f d/(d:ℝ))*a r d)= f d*(if d.Coprime n then X/(d.totient:ℝ) else 0) := by
    rw [←mul_sum]
    by_cases hs : Squarefree d
    · have hset : I.filter (fun r => r∣d)=d.divisors := by
        ext r
        constructor
        · intro h
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2,hs.ne_zero⟩
        · intro h
          have hrd := Nat.dvd_of_mem_divisors h
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors h,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hrd).trans (mem_Icc.mp hd).2⟩,hrd⟩
      dsimp only [a]
      rw [←sum_filter,hset]
      have hsum := mixed_ramanujan_divisor_local n hs
      change (∑ r∈d.divisors,C r)=_ at hsum
      rw [hsum]
      have hd' : (d:ℝ)≠0 := by exact_mod_cast hs.ne_zero
      split_ifs <;> field_simp
      ring
    · simp [f,hF d hs]
  symm
  change X*(∑ r∈I,C r*finiteRamanujanTransform R F r)=_
  rw [mul_sum]
  calc
    _ = ∑ r∈I,∑ d∈I,X*(f d/(d:ℝ))*a r d := sum_congr rfl (fun r _ => row r)
    _ = _ := by rw [sum_comm];exact sum_congr rfl col

/-- The mixed convolution in the true zero frequency, before taking any distributional estimates. -/
theorem finiteWeight_mixed_ramanujan (n R : ℕ) (F : ℕ→ℝ) (hF : ∀ d, ¬Squarefree d → F d=0) :
    (∑ k∈Ioo 0 n,ArithmeticFunction.vonMangoldt k*finiteDivisorWeightSum R F (n-k)) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)*
      finiteRamanujanTransform R F r) +
    ∑ d∈Icc 1 R,F d*primeSmallProgressionError n d := by
  let f := F
  let Λ' := ArithmeticFunction.vonMangoldt
  let S := Icc 1 R
  let K := Ioo 0 n
  rw [←finiteWeight_mixed_main n R F hF,←sum_add_distrib]
  have hloc (k : ℕ) (_hk : k∈K) : Λ' k*finiteDivisorWeightSum R F (n-k)=
      ∑ d∈S,f d*(if d∣n-k then Λ' k else 0) := by
    rw [finiteDivisorWeightSum,sum_filter,mul_sum]
    apply sum_congr rfl;intro d _
    by_cases h : d∣n-k <;> simp [h,f,mul_comm]
  calc
    _ = ∑ k∈K,∑ d∈S,f d*(if d∣n-k then Λ' k else 0) := sum_congr rfl hloc
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      rw [←mul_sum]
      dsimp only [primeSmallProgressionError,f,Λ',K]
      ring

theorem exactRamanujanWeight_zero_of_not_squarefree (R d : ℕ) (hd : ¬ Squarefree d) :
    exactRamanujanWeight R d=0 := by
  unfold exactRamanujanWeight finiteMultipleMobiusInverse
  have h : (∑ m∈(Icc 1 R).filter (fun m => d∣m),
      (ArithmeticFunction.moebius (m/d):ℝ)*((ArithmeticFunction.moebius m:ℝ)/(m.totient:ℝ)))=0 := by
    apply sum_eq_zero;intro m hm
    have hn : ¬Squarefree m := fun h => hd (h.squarefree_of_dvd (mem_filter.mp hm).2)
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  rw [h,mul_zero]

/-- Exact zero-frequency correction. The only remaining errors are the finite CRT endpoints
and the centered prime progression discrepancies. -/
theorem exactRamanujanZeroCorrection_eq (n R : ℕ) :
    exactRamanujanZeroCorrection n R =
      -((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n R +
        (∑ d∈Icc 1 R,∑ e∈Icc 1 R,exactRamanujanWeight R d*exactRamanujanWeight R e*crtRowError n d e) -
        2*(∑ d∈Icc 1 R,exactRamanujanWeight R d*primeSmallProgressionError n d) := by
  let F := exactRamanujanWeight R
  let h := fun r : ℕ => (ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ)
  let C := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)
  have hF : ∀ d,¬Squarefree d → F d=0 := exactRamanujanWeight_zero_of_not_squarefree R
  have e1 : (∑ r∈Icc 1 R,C r*(finiteRamanujanTransform R F r)^2)=finiteRamanujanSingularSum n R := by
    apply sum_congr rfl;intro r hr
    rw [show finiteRamanujanTransform R F r=h r from exactRamanujanWeight_transform R hr]
  have e2 : (∑ r∈Icc 1 R,C r*h r*finiteRamanujanTransform R F r)=finiteRamanujanSingularSum n R := by
    apply sum_congr rfl;intro r hr
    rw [show finiteRamanujanTransform R F r=h r from exactRamanujanWeight_transform R hr]
    change C r*h r*h r=C r*(h r)^2
    ring
  unfold exactRamanujanZeroCorrection
  rw [finiteWeight_self_ramanujan,finiteWeight_mixed_ramanujan n R F hF,e1,e2]
  ring

end GoldbachPartial
