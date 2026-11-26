import VerifiedMajorCoefficientPowerset
namespace GoldbachPartial
open Finset

noncomputable def smallGoodDivisorMass (n P : ℕ) : ℝ :=
  ∑ t ∈ n.primeFactors.powerset.filter (fun t => 16*(∏ p ∈ t,p)≤P),
    ∏ p ∈ t,1/((p:ℝ)-1)

theorem goodDivisorWeight_sum {n:ℕ} (hn:0<n) :
    (∑ t∈n.primeFactors.powerset,∏ p∈t,1/((p:ℝ)-1)) = (n:ℝ)/n.totient := by
  have hphi : (n.totient:ℝ)=n*(∏p∈n.primeFactors,(1-(p:ℝ)⁻¹)) := by
    have hh := congrArg (fun z:ℚ=>(z:ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hh
    exact hh
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hh : (∏p∈n.primeFactors,(1-(p:ℝ)⁻¹))=(n.totient:ℝ)/n := by
    apply (eq_div_iff hn').mpr
    rw [mul_comm,←hphi]
  rw [←prod_one_add,←inv_div,←hh,←prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  field_simp
  ring

private theorem local_goodMoment (S:Finset ℕ) (hs:∀p∈S,Nat.Prime p) :
    (∑ t∈S.powerset,(∏p∈t,1/((p:ℝ)-1))*Real.log ((∏p∈t,p):ℕ)) =
      (∑ t∈S.powerset,∏p∈t,1/((p:ℝ)-1))*(∑p∈S,Real.log p/(p:ℝ)) := by
  classical
  let w (p:ℕ) := 1/((p:ℝ)-1)
  let A (t:Finset ℕ) := ∏p∈t,w p
  let d (t:Finset ℕ) := ∏p∈t,p
  change (∑t∈S.powerset,A t*Real.log (d t))=(∑t∈S.powerset,A t)*(∑p∈S,Real.log p/(p:ℝ))
  induction S using Finset.induction_on with
  | empty => simp [A,d]
  | @insert p S hp ih =>
    have hS : ∀r∈S,Nat.Prime r := fun r hr=>hs r (mem_insert_of_mem hr)
    have hpp := hs p (mem_insert_self p S)
    have hp1:(1:ℝ)<p := by exact_mod_cast hpp.one_lt
    have hi := ih hS
    have hno (t:Finset ℕ) (ht:t∈S.powerset) : p∉t := fun h=>hp (mem_powerset.mp ht h)
    have hA (t:Finset ℕ) (ht:t∈S.powerset) : A (insert p t)=w p*A t := by
      simp [A,prod_insert (hno t ht)]
    have hlog (t:Finset ℕ) (ht:t∈S.powerset) : Real.log (d (insert p t))=Real.log p+Real.log (d t) := by
      have hd:0<d t := prod_pos (fun r hr=>(hS r (mem_powerset.mp ht hr)).pos)
      dsimp only [d]
      rw [prod_insert (hno t ht),Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hd.ne')]
    have hnew : (∑t∈S.powerset,A (insert p t)*Real.log (d (insert p t))) =
        (w p*Real.log p)*(∑t∈S.powerset,A t)+w p*(∑t∈S.powerset,A t*Real.log (d t)) := by
      rw [mul_sum,mul_sum,←sum_add_distrib];apply sum_congr rfl;intro t ht;rw [hA t ht,hlog t ht];ring
    have hmass : (∑t∈S.powerset,A (insert p t))=w p*(∑t∈S.powerset,A t) := by
      rw [mul_sum];exact sum_congr rfl hA
    have hid : (1+w p)*(Real.log p/(p:ℝ))=w p*Real.log p := by
      dsimp [w];field_simp;ring
    rw [sum_powerset_insert hp,sum_powerset_insert hp,sum_insert hp,hnew,hmass,hi]
    linear_combination -(∑t∈S.powerset,A t)*hid

theorem goodDivisorWeight_logMoment {n:ℕ} (hn:0<n) :
    (∑ t∈n.primeFactors.powerset,(∏p∈t,1/((p:ℝ)-1))*Real.log ((∏p∈t,p):ℕ)) =
      ((n:ℝ)/n.totient)*(∑p∈n.primeFactors,Real.log p/(p:ℝ)) := by
  rw [local_goodMoment _ (fun _ hp => Nat.prime_of_mem_primeFactors hp),goodDivisorWeight_sum hn]

/-- The part outside the cutoff is bounded by its logarithmic first moment. -/
theorem smallGoodDivisorMass_markov {n P:ℕ} (hn:0<n) (hP:16<P) :
    (((n:ℝ)/n.totient)-smallGoodDivisorMass n P)*Real.log ((P:ℝ)/16) ≤
      ((n:ℝ)/n.totient)*(∑p∈n.primeFactors,Real.log p/(p:ℝ)) := by
  classical
  let S := n.primeFactors.powerset
  let A (t:Finset ℕ) : ℝ := ∏p∈t,1/((p:ℝ)-1)
  let d (t:Finset ℕ) : ℕ := ∏p∈t,p
  let good (t:Finset ℕ) := 16*(d t)≤P
  let L := Real.log ((P:ℝ)/16)
  have he : ((n:ℝ)/n.totient)-smallGoodDivisorMass n P = ∑t∈S.filter (fun t=>¬good t),A t := by
    have hh := sum_filter_add_sum_filter_not S good A
    change (∑t∈S.filter good,A t)+(∑t∈S.filter (fun t=>¬good t),A t)=∑t∈S,A t at hh
    rw [←goodDivisorWeight_sum hn]
    have hhg : smallGoodDivisorMass n P = ∑t∈S.filter good,A t := by
      simp only [smallGoodDivisorMass,Finset.sum_filter,S,A,good,d]
    rw [hhg]
    change (∑t∈S,A t)-(∑t∈S.filter good,A t)=_
    linarith only [hh]
  rw [he,←goodDivisorWeight_logMoment hn,sum_mul]
  change (∑t∈S.filter (fun t=>¬good t),A t*L) ≤ ∑t∈S,A t*Real.log (d t)
  have hprime (t:Finset ℕ) (ht:t∈S) (p:ℕ) (hp:p∈t) : p.Prime :=
    Nat.prime_of_mem_primeFactors (mem_powerset.mp ht hp)
  have hnA (t:Finset ℕ) (ht:t∈S) : 0≤A t := by
    apply prod_nonneg;intro p hp
    have hp1 : (1:ℝ)≤p := by exact_mod_cast (hprime t ht p hp).one_le
    positivity
  apply le_trans (sum_le_sum (g:=fun t=>A t*Real.log (d t)) ?_)
  · apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
    intro t ht _
    exact mul_nonneg (hnA t ht) (Real.log_natCast_nonneg _)
  · intro t ht
    obtain ⟨ht,hg⟩ := mem_filter.mp ht
    apply mul_le_mul_of_nonneg_left _ (hnA t ht)
    apply Real.log_le_log (by positivity : (0:ℝ)<(P:ℝ)/16)
    have hgt : P<16*d t := lt_of_not_ge hg
    have hreal : (P:ℝ)<16*(d t:ℝ) := by exact_mod_cast hgt
    linarith

theorem smallGoodDivisorMass_of_log_mean {n P:ℕ} (hn:0<n) (hP:16<P) (α:ℝ)
    (hm : (∑p∈n.primeFactors,Real.log p/(p:ℝ)) ≤ α*Real.log ((P:ℝ)/16)) :
    (1-α)*((n:ℝ)/n.totient) ≤ smallGoodDivisorMass n P := by
  have hP' : (16:ℝ)<P := by exact_mod_cast hP
  have hL : 0<Real.log ((P:ℝ)/16) := Real.log_pos (by linarith)
  have hh := (smallGoodDivisorMass_markov hn hP).trans
    (mul_le_mul_of_nonneg_left hm (by positivity : 0≤(n:ℝ)/n.totient))
  apply (le_of_mul_le_mul_right (a:=Real.log ((P:ℝ)/16)) _ hL)
  linarith only [hh]

theorem smallGoodDivisorMass_quarter {n P:ℕ} (hn:0<n) (hP:16<P)
    (hm : (∑p∈n.primeFactors,Real.log p/(p:ℝ)) ≤ (3/4:ℝ)*Real.log ((P:ℝ)/16)) :
    (1/4:ℝ)*((n:ℝ)/n.totient) ≤ smallGoodDivisorMass n P := by
  simpa only [show 1-(3/4:ℝ)=1/4 by norm_num] using
    smallGoodDivisorMass_of_log_mean hn hP (3/4) hm

theorem smallGoodDivisorMass_fortynine {n P:ℕ} (hn:0<n) (hP:16<P)
    (hm : (∑p∈n.primeFactors,Real.log p/(p:ℝ)) ≤ (51/100:ℝ)*Real.log ((P:ℝ)/16)) :
    (49/100:ℝ)*((n:ℝ)/n.totient) ≤ smallGoodDivisorMass n P := by
  simpa only [show 1-(51/100:ℝ)=49/100 by norm_num] using
    smallGoodDivisorMass_of_log_mean hn hP (51/100) hm

end GoldbachPartial
