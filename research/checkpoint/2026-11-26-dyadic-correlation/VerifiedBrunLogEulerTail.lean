import BrunEulerTail
import PrimeFactorLogMean
import VerifiedDivisorWeightConcentration
import ResonantModelEnergy

namespace GoldbachPartial
open Finset

private theorem brunSubset_totient (t : Finset ℕ) (hp : ∀ p∈t,p.Prime) :
    (∏ p∈t,p).totient = ∏ p∈t,(p-1) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hpt ih =>
    have hprime := hp p (mem_insert_self ..)
    have ht (l : ℕ) (hl : l∈t) := hp l (mem_insert_of_mem hl)
    have hc : p.Coprime (∏ l∈t,l) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro l hl
      exact (Nat.coprime_primes hprime (ht l hl)).mpr (by rintro rfl; exact hpt hl)
    rw [prod_insert hpt,prod_insert hpt,Nat.totient_mul hc,Nat.totient_prime hprime,ih ht]

theorem smallGoodDivisorMass_totient_bound (n U : ℕ) :
    smallGoodDivisorMass n (16*U) ≤ 4*(1+Real.log U) := by
  let f (t : Finset ℕ) := ∏ p∈t,p
  let T := n.primeFactors.powerset.filter (fun t => 16*f t ≤ 16*U)
  have hpr {t : Finset ℕ} (ht : t ∈ T) (p : ℕ) (hp : p ∈ t) : p.Prime :=
    Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_filter.mp ht).1 hp)
  have hid {t : Finset ℕ} (ht : t ∈ T) : (f t).primeFactors=t :=
    Nat.primeFactors_prod (hpr ht)
  have he : smallGoodDivisorMass n (16*U) ≤ ∑ k∈Icc 1 U,1/(k.totient:ℝ) := by
    change (∑t ∈ T, ∏ p ∈ t, 1/((p:ℝ)-1)) ≤ _
    apply sum_le_sum_of_injOn f
    · intro t ht s hs heq
      rw [←hid ht,←hid hs,heq]
    · intro k hk
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hk
      exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hpr ht p hp).pos),
        by have hh := (mem_filter.mp ht).2; change 16*f t≤16*U at hh; omega⟩
    · intro t ht
      dsimp only [f]
      apply le_of_eq
      rw [brunSubset_totient t (hpr ht),Nat.cast_prod,one_div,←prod_inv_distrib]
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (hpr ht p hp).one_le,Nat.cast_one,one_div]
    · intro _ _ _; positivity
  have hh := modelTotientReciprocal_sum 0 U
  rw [Finset.sum_Ico_add' (fun k : ℕ => 1/(k.totient:ℝ)) 0 U (c:=1)] at hh
  simp only [zero_add,Finset.Ico_add_one_right_eq_Icc] at hh
  exact he.trans hh

/-- Mertens-type bound for the multiplicative weights on any finite subset
of the primes up to z. -/
theorem brunEuler_positive_product_log_bound (z : ℕ) (B : Finset ℕ)
    (hB : B ⊆ Icc 3 z) (hpr : ∀p∈B,p.Prime) :
    (∏p∈B,(1+brunEulerWeight p)) ≤ 64*(1+Real.log z) := by
  by_cases hz : z=0
  · subst z
    have he : B=∅ := eq_empty_iff_forall_notMem.mpr (fun p hp => by have hi := mem_Icc.mp (hB hp); omega)
    simp [he]
  have hz' := Nat.pos_of_ne_zero hz
  let n := ∏p∈B,p
  let U := (4*z)^2
  have hn : 0<n := prod_pos fun p hp => (hpr p hp).pos
  have hfac : n.primeFactors=B := Nat.primeFactors_prod hpr
  have hzR : 0<(z:ℝ) := by exact_mod_cast hz'
  have hU : 1<U := by dsimp only [U]; nlinarith [Nat.succ_le_of_lt hz',Nat.zero_le z]
  have hP : 16<16*U := by omega
  have hℓ : Real.log (((16*U:ℕ):ℝ)/16)=2*(Real.log z+Real.log 4) := by
    dsimp only [U]
    push_cast
    rw [show 16*((4:ℝ)*z)^2/16=(4*z)^2 by ring,Real.log_pow,Real.log_mul (by norm_num) hzR.ne']
    push_cast;ring
  have hmean : (∑p∈n.primeFactors,Real.log p/(p:ℝ)) ≤ (1/2:ℝ)*Real.log (((16*U:ℕ):ℝ)/16) := by
    rw [hfac,hℓ]
    have hs : B⊆(Ioc 0 z).filter Nat.Prime := fun p hp =>
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hpr p hp).pos,(mem_Icc.mp (hB hp)).2⟩,hpr p hp⟩
    apply (sum_le_sum_of_subset_of_nonneg hs
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))).trans
    linarith only [prime_log_reciprocal_upto z hz']
  have hh := (smallGoodDivisorMass_of_log_mean hn hP (1/2) hmean).trans (smallGoodDivisorMass_totient_bound n U)
  have hprod : ∏p∈B,(1+brunEulerWeight p)=(n:ℝ)/n.totient := by
    rw [←goodDivisorWeight_sum hn,hfac,←prod_one_add]
    rfl
  have hlog : Real.log U=2*(Real.log z+Real.log 4) := by
    dsimp only [U];push_cast
    rw [Real.log_pow,Real.log_mul (by norm_num) hzR.ne']
    push_cast;ring
  rw [hprod]
  rw [hlog] at hh
  linarith only [hh,Real.log_natCast_nonneg z,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]

theorem brunEuler_product_log_lower (z : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 z)
    (hpr : ∀p∈B,p.Prime) :
    1/(128*(1+Real.log z)) ≤ ∏p∈B,(1-brunEulerWeight p) := by
  let P := ∏p∈B,(1-brunEulerWeight p)
  let Q := ∏p∈B,(1+brunEulerWeight p)
  have hR : 0<1+Real.log z := by linarith [Real.log_natCast_nonneg z]
  have hP : 0≤P := prod_nonneg fun p hp =>
    sub_nonneg.mpr (brunEulerWeight_bounds (mem_Icc.mp (hB hp)).1).2
  have hQ : Q≤64*(1+Real.log z) := brunEuler_positive_product_log_bound z B hB hpr
  have hid : P*Q=∏p∈B,(1-1/((p:ℝ)-1)^2) := by
    dsimp only [P,Q]
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    simp only [brunEulerWeight,one_div,←inv_pow]
    ring
  have hsmall := odd_prime_product_lower (P:=B) fun p hp => ⟨hpr p hp,(mem_Icc.mp (hB hp)).1⟩
  rw [←hid] at hsmall
  change 1/(128*(1+Real.log z))≤P
  apply (div_le_iff₀ (by positivity)).mpr
  have he := mul_le_mul_of_nonneg_left hQ hP
  linarith only [he,hsmall]

theorem brunEuler_prime_powerset_tail (z K : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 z) (hpr : ∀p∈B,p.Prime) :
    (∑ t ∈ B.powerset.filter (fun t => K≤t.card), ∏ p ∈ t, brunEulerWeight p) ≤
      (64*(1+Real.log z))^2/(2:ℝ)^K := by
  have hw (t : Finset ℕ) (ht : t∈B.powerset) : 0≤∏ p∈t,brunEulerWeight p :=
    prod_nonneg fun p hp => (brunEulerWeight_bounds (mem_Icc.mp (hB (mem_powerset.mp ht hp))).1).1
  apply (le_div_iff₀ (by positivity)).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ t ∈ B.powerset.filter (fun t => K≤t.card),
        (∏ p ∈ t,brunEulerWeight p)*(2:ℝ)^t.card := by
      refine sum_le_sum fun t ht => ?_
      have hh := mem_filter.mp ht
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh.2) (hw t hh.1)
    _ ≤ ∑ t ∈ B.powerset, (∏ p ∈ t,brunEulerWeight p)*(2:ℝ)^t.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t ht _ => mul_nonneg (hw t ht) (by positivity))
    _ = ∏ p ∈ B,(1+2*brunEulerWeight p) := by
      rw [prod_one_add]
      refine sum_congr rfl fun t _ => ?_
      rw [prod_mul_distrib,prod_const,mul_comm]
    _ ≤ ∏ p ∈ B,(1+brunEulerWeight p)^2 := by
      apply prod_le_prod₀
      · intro p hp
        linarith only [(brunEulerWeight_bounds (mem_Icc.mp (hB hp)).1).1]
      · intro p _
        nlinarith only [sq_nonneg (brunEulerWeight p)]
    _ ≤ _ := by
      rw [prod_pow]
      apply pow_le_pow_left₀ _ (brunEuler_positive_product_log_bound z B hB hpr)
      refine prod_nonneg fun p hp => ?_
      linarith only [(brunEulerWeight_bounds (mem_Icc.mp (hB hp)).1).1]

theorem brunEuler_prime_signed_truncation_error (z K : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 z) (hpr : ∀p∈B,p.Prime) :
    |(∑ t ∈ B.powerset.filter (fun t => t.card<K), ∏ p ∈ t, -brunEulerWeight p) -
      ∏ p ∈ B, (1-brunEulerWeight p)| ≤ (64*(1+Real.log z))^2/(2:ℝ)^K := by
  classical
  let f (t : Finset ℕ) := ∏ p ∈ t, -brunEulerWeight p
  have hfull : (∏ p ∈ B,(1-brunEulerWeight p)) = ∑ t ∈ B.powerset, f t := by
    simp only [sub_eq_add_neg,prod_one_add,f]
  have hsplit := sum_filter_add_sum_filter_not B.powerset (fun t => t.card<K) f
  simp only [not_lt] at hsplit
  have he : (∑ t ∈ B.powerset.filter (fun t => t.card<K), f t) - ∏ p ∈ B,(1-brunEulerWeight p) =
      -(∑ t ∈ B.powerset.filter (fun t => K≤t.card), f t) := by rw [hfull,←hsplit];ring
  rw [he,abs_neg]
  apply (abs_sum_le_sum_abs ..).trans
  apply le_trans ?_ (brunEuler_prime_powerset_tail z K B hB hpr)
  refine sum_le_sum fun t ht => le_of_eq ?_
  have hsub := mem_powerset.mp (mem_filter.mp ht).1
  dsimp only [f]
  rw [Finset.abs_prod]
  apply prod_congr rfl
  intro p hp
  rw [abs_neg,abs_of_nonneg (brunEulerWeight_bounds (mem_Icc.mp (hB (hsub hp))).1).1]

theorem brunEuler_prime_truncation_half_log_density (z K : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 z) (hpr : ∀p∈B,p.Prime)
    (hK : 1048576*(1+Real.log z)^3 ≤ (2:ℝ)^K) :
    1/(256*(1+Real.log z)) ≤
      ∑ t ∈ B.powerset.filter (fun t => t.card<K), ∏ p ∈ t, -brunEulerWeight p := by
  have h := brunEuler_prime_signed_truncation_error z K B hB hpr
  have hL : 0<1+Real.log z := by linarith [Real.log_natCast_nonneg z]
  have hs : (64*(1+Real.log z))^2/(2:ℝ)^K ≤ 1/(256*(1+Real.log z)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hK]
  have hf := brunEuler_product_log_lower z B hB hpr
  have he : 2*(1/(256*(1+Real.log z)))=1/(128*(1+Real.log z)) := by field_simp;ring
  linarith only [(abs_le.mp h).1,hs,hf,he]

end GoldbachPartial