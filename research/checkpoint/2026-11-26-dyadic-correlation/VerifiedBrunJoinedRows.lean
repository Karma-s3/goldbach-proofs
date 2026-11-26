import VerifiedBrunJoinedCoefficient

namespace GoldbachPartial
open Finset
open scoped Classical

private theorem brun_product_indicator (s : Finset ℕ) (P : ℕ→Prop) :
    (∏ p∈s, (if P p then (1:ℝ) else 0)) = if ∀p∈s,P p then 1 else 0 := by
  by_cases h : ∀p∈s,P p
  · rw [ite_eq_left h]
    exact prod_eq_one (fun p hp=>ite_eq_left (h p hp))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨p,hp,hno⟩ := h
    exact prod_eq_zero hp (ite_eq_right hno)

private theorem brun_upper_indicator (B : Finset ℕ) (r : ℕ) (P : ℕ→Prop) :
    brunLocalUpperSum B r (fun p=>if P p then 1 else 0) = brunBlockUpper (B.filter P) r := by
  rw [brunLocalUpperSum_eq_filter,brunBlockUpper_at]
  apply sum_congr rfl
  intro t _
  rw [brun_product_indicator]
  by_cases h : ∀p∈t,P p <;> simp [h]

private theorem brun_defect_indicator (B : Finset ℕ) (r : ℕ) (P : ℕ→Prop) :
    brunLocalDefectSum B r (fun p=>if P p then 1 else 0) = brunBlockDefect (B.filter P) r := by
  rw [brunLocalDefectSum_eq_powersetCard,brunBlockDefect_at]
  exact sum_congr rfl (fun t _ => brun_product_indicator t P)

theorem brunJoinedCoefficient_on_bad (J : Finset ℕ) (B : ℕ→Finset ℕ)
    (hd : ∀ i∈J,∀ j∈J,i≠j → Disjoint (B i) (B j)) (r : ℕ→ℕ) (P : ℕ→Prop) :
    (∑ S∈(J.biUnion B).powerset.filter (fun S => ∀p∈S,P p), brunJoinedCoefficient J B r S) =
      (∏i∈J, brunBlockUpper ((B i).filter P) (r i)) -
      ∑e∈J,brunBlockDefect ((B e).filter P) (r e) * ∏ i∈J.erase e,brunBlockUpper ((B i).filter P) (r i) := by
  have h := brunJoinedCoefficient_factorization J B hd r (fun p=>if P p then (1:ℝ) else 0)
  simp_rw [brun_upper_indicator,brun_defect_indicator,brun_product_indicator] at h
  rw [←h,sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases h : ∀p∈S,P p <;> simp [h]

/-- Aggregate the actual CRT rows with the joined coefficients before applying their analytic error bound. -/
theorem fixedTarget_Brun_joined_rows (n z : ℕ) (hz : z≤n/4) (J : Finset ℕ) (B : ℕ→Finset ℕ)
    (hd : ∀ i∈J,∀ j∈J,i≠j → Disjoint (B i) (B j))
    (hB : J.biUnion B = fixedTargetBrunPrimes n z) (r : ℕ→ℕ) (hr : ∀i∈J,Even (r i)) :
    (∑ S∈(fixedTargetBrunPrimes n z).powerset,
      brunJoinedCoefficient J B r S * fixedTargetDivisorRow n (∏ p∈S,p)) ≤
        fixedTargetBrunSurvivorMass n z := by
  let I := Ioc (n/4) (n/2)
  let B₀ := J.biUnion B
  let A := B₀.powerset
  let c := brunJoinedCoefficient J B r
  let P := fun k p : ℕ => p∣n-k
  let G := fun k : ℕ => (∏i∈J,brunBlockUpper ((B i).filter (P k)) (r i)) -
    ∑e∈J,brunBlockDefect ((B e).filter (P k)) (r e) * ∏i∈J.erase e,brunBlockUpper ((B i).filter (P k)) (r i)
  have hu (k : ℕ) (_ : k∈I) : 0≤weight k := by
    unfold weight
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  have hjoined (k : ℕ) : (∑ S∈A, if ∀p∈S,P k p then c S else 0) = G k := by
    rw [←sum_filter]
    convert brunJoinedCoefficient_on_bad J B hd r (P k) using 1
    · apply sum_congr (by ext S; simp only [A,B₀,mem_filter]) (fun _ _=>rfl)
    · dsimp only [G]
      congr! 8
  have hrow (S : Finset ℕ) (hS : S∈A) :
      c S * fixedTargetDivisorRow n (∏ p∈S,p) =
        ∑ k∈I,weight k*(if ∀p∈S,P k p then c S else 0) := by
    have hsub : S⊆fixedTargetBrunPrimes n z := hB ▸ mem_powerset.mp hS
    have hpr (p : ℕ) (hp : p∈S) := (mem_filter.mp (hsub hp)).2.1
    unfold fixedTargetDivisorRow
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    have he := fixedTarget_prime_subset_product_dvd S hpr (n-k)
    change _ = weight k * (if ∀p∈S,p∣n-k then c S else 0)
    rw [if_congr he rfl rfl]
    by_cases h : ∀p∈S,p∣n-k <;> simp [h,mul_comm]
  have hminor (k : ℕ) : G k ≤ if ∀i∈J,(B i).filter (P k)=∅ then 1 else 0 :=
    by
      convert brunBlocks_pointwise_lower J (fun i=>(B i).filter (P k)) r hr using 1
      · dsimp only [G]
        congr! 8
      · congr! 8
  rw [←hB]
  change (∑S∈A,c S*fixedTargetDivisorRow n (∏p∈S,p))≤_
  calc
    _ = ∑S∈A,∑k∈I,weight k*(if ∀p∈S,P k p then c S else 0) := sum_congr rfl hrow
    _ = ∑k∈I,weight k*G k := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [←mul_sum,hjoined]
    _ ≤ ∑k∈I,weight k*(if ∀i∈J,(B i).filter (P k)=∅ then 1 else 0) :=
      sum_le_sum (fun k hk=>mul_le_mul_of_nonneg_left (hminor k) (hu k hk))
    _ = _ := by
      unfold fixedTargetBrunSurvivorMass
      rw [sum_filter]
      apply sum_congr rfl
      intro k hk
      by_cases prime : k.Prime
      · have hiff : (∀i∈J,(B i).filter (P k)=∅) ↔ (∀p : ℕ,p.Prime→p≤z→¬p∣n-k) := by
          constructor
          · intro ha p hp hpz
            by_cases hpn : p∣n
            · exact fixedTarget_common_prime_excluded hz hp hpz hpn prime hk
            · have hmem : p∈fixedTargetBrunPrimes n z := mem_filter.mpr ⟨mem_range_succ_iff.mpr hpz,hp,hpn⟩
              rw [←hB] at hmem
              obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hmem
              exact (filter_eq_empty_iff.mp (ha i hi)) hpi
          · intro ha i hi
            apply filter_eq_empty_iff.mpr
            intro p hp
            have hm : p∈fixedTargetBrunPrimes n z := hB ▸ mem_biUnion.mpr ⟨i,hi,hp⟩
            exact ha p (mem_filter.mp hm).2.1 (mem_range_succ_iff.mp (mem_filter.mp hm).1)
        rw [if_congr hiff rfl rfl]
        by_cases hh : ∀p : ℕ,p.Prime→p≤z→¬p∣n-k <;> simp [hh]
      · simp [weight,prime]

end GoldbachPartial