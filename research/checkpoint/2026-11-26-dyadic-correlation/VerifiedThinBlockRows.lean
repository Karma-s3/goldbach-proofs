import VerifiedBrunOrdinaryUpper
import VerifiedThinSemiprimeLogUpper

namespace GoldbachPartial
open Finset
open scoped Classical

theorem thinSurvivors_block_model_upper (n L X J : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hp : ∀p∈B,p.Prime ∧ ¬p∣n ∧ ¬p∣L) :
    (thinSurvivors n L X B:ℝ) ≤ (X:ℝ)*
      (∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunBlockOrder J i) (fun p=>(2:ℝ)/p)) +
        (brunBlockBoundary J:ℝ)^202 := by
  let c := brunOrdinaryBlockWeight J B
  let d := fun t : Finset ℕ => ∏p∈t,p
  let W := B.powerset.filter fun t=>c t≠0
  let D := (brunBlockBoundary J)^101
  let w := fun p : ℕ => (2:ℝ)/p
  let I := Ioc 0 X
  have hsub {t : Finset ℕ} (ht : t∈W) : t⊆B := mem_powerset.mp (mem_filter.mp ht).1
  have hlevel {t : Finset ℕ} (ht : t∈W) : d t≤D :=
    brunOrdinaryBlockWeight_level J B t hB (hsub ht) (mem_filter.mp ht).2
  have hcard : W.card≤D := by
    have hc : W.card ≤ (Ioc 0 D).card := by
      apply card_le_card_of_injOn d
      · intro t ht
        exact mem_Ioc.mpr ⟨prod_pos (fun p hh=>(hp p (hsub ht hh)).1.pos),hlevel ht⟩
      · intro s hs t ht he
        have h1 := Nat.primeFactors_prod (fun p hh=>(hp p (hsub hs hh)).1)
        have h2 := Nat.primeFactors_prod (fun p hh=>(hp p (hsub ht hh)).1)
        exact h1.symm.trans ((congrArg Nat.primeFactors he).trans h2)
    simpa using hc
  have hfilter (f : Finset ℕ→ℝ) : (∑t∈B.powerset,c t*f t)=∑t∈W,c t*f t := by
    rw [sum_filter]
    apply sum_congr rfl;intro t _
    by_cases hc : c t=0 <;> simp [hc]
  have hreal : (thinSurvivors n L X B:ℝ) ≤ ∑t∈W,c t*thinPolyRow n L (d t) X := by
    calc
      _ = ∑b∈I,if ∀p∈B,¬thinBad n L b p then (1:ℝ) else 0 := by
        rw [←sum_filter];simp [I,thinSurvivors]
      _ ≤ ∑b∈I,∑t∈B.powerset,if ∀p∈t,thinBad n L b p then c t else 0 := by
        apply sum_le_sum
        intro b _
        exact brunOrdinaryBlock_majorizes J B hB (thinBad n L b)
      _ = ∑t∈B.powerset,c t*thinPolyRow n L (d t) X := by
        rw [sum_comm]
        apply sum_congr rfl
        intro t ht
        rw [thinPolyRow_eq_bad_intersection n L X t (fun p hh=>(hp p (mem_powerset.mp ht hh)).1),
          ←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
      _ = _ := hfilter _
  have hrow (t : Finset ℕ) (ht : t∈W) :
      c t*(thinPolyRow n L (d t) X:ℝ) ≤ (X:ℝ)*(c t*(∏p∈t,w p))+(D:ℝ) := by
    have h := thinPolyRow_prime_product n L X t (fun p hh=>hp p (hsub ht hh))
    have hpow : 2^t.card≤d t := by
      rw [←prod_const (b:=2) (s:=t)]
      exact prod_le_prod (fun p hh=>(hp p (hsub ht hh)).1.two_le)
    have hM : (X:ℝ)*(∏p∈t,w p) = (2:ℝ)^t.card*((X:ℝ)/(d t:ℝ)) := by
      dsimp only [d,w]
      rw [prod_div_distrib,prod_const,Nat.cast_prod]
      ring
    have h0 : |(thinPolyRow n L (d t) X:ℝ)-(X:ℝ)*(∏p∈t,w p)|≤(D:ℝ) := by
      rw [hM]
      apply h.trans
      exact_mod_cast hpow.trans (hlevel ht)
    have h1 := (le_abs_self (c t*((thinPolyRow n L (d t) X:ℝ)-(X:ℝ)*(∏p∈t,w p))))
    rw [abs_mul] at h1
    have h2 := (mul_le_of_le_one_left (abs_nonneg ((thinPolyRow n L (d t) X:ℝ)-(X:ℝ)*(∏p∈t,w p))) (brunOrdinaryBlockWeight_abs_le J B t)).trans h0
    change |c t| * _≤(D:ℝ) at h2
    linarith only [h1,h2]
  calc
    _ ≤ _ := hreal
    _ ≤ ∑t∈W,((X:ℝ)*(c t*(∏p∈t,w p))+(D:ℝ)) := sum_le_sum hrow
    _ = (X:ℝ)*(∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunBlockOrder J i) w)+W.card*(D:ℝ) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum,←hfilter,←brunOrdinaryBlock_factorization J B hB w]
    _ ≤ _ := by
      apply add_le_add_right
      calc
        (W.card:ℝ)*(D:ℝ) ≤ (D:ℝ)*(D:ℝ) := by gcongr
        _ = (brunBlockBoundary J:ℝ)^202 := by
          simp only [D,Nat.cast_pow,←pow_add]

theorem thinSurvivors_even_regular_block_upper (n J : ℕ) (he : Even n) :
    let z := brunBlockBoundary J
    let B := thinRegularPrimes n z
    (thinSurvivors n 1 n B:ℝ) ≤ (n:ℝ)*
      (∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunBlockOrder J i) (fun p=>(2:ℝ)/p)) +
        (z:ℝ)^202 := by
  intro z B
  have hB : B⊆Icc 3 z := by
    intro p hp
    have hi := mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1
    have hne : p≠2 := by rintro rfl;exact (mem_filter.mp hp).2 (even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by omega,hi.2⟩
  apply thinSurvivors_block_model_upper n 1 n J B hB
  intro p hp
  have hpr : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
  exact ⟨hpr,(mem_filter.mp hp).2,hpr.not_dvd_one⟩

end GoldbachPartial