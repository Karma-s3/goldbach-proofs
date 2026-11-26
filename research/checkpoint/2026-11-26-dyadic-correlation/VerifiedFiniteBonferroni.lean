import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DyadicCorrelationReduction

namespace GoldbachPartial
open Finset
open scoped Classical

theorem truncatedPowerset_alternating {ν:Type*} (S:Finset ν) (K:ℕ) :
    (∑t∈S.powerset.filter (fun t=>t.card≤K),(-1:ℤ)^t.card)=
      ∑j∈range (K+1),(-1:ℤ)^j*(S.card.choose j) := by
  let T:=S.powerset.filter (fun t=>t.card≤K)
  trans ∑j∈range (K+1),∑t∈T.filter (fun t=>t.card=j),(-1:ℤ)^t.card
  · apply (sum_fiberwise_of_maps_to ?_ _).symm
    intro t ht
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp ht).2)
  · apply sum_congr rfl
    intro j hj
    have hJ : j≤K := Nat.le_of_lt_succ (mem_range.mp hj)
    have hset : T.filter (fun t=>t.card=j)=S.powersetCard j := by
      ext t
      simp only [T,mem_filter,mem_powerset,mem_powersetCard]
      grind
    rw [hset]
    have hh : (∑t∈S.powersetCard j,(-1:ℤ)^t.card)=∑_t∈S.powersetCard j,(-1:ℤ)^j :=
      sum_congr rfl fun t ht=>by rw [(mem_powersetCard.mp ht).2]
    rw [hh,sum_const,card_powersetCard,nsmul_eq_mul,mul_comm]

theorem oddTruncatedPowerset_le {ν:Type*} (S:Finset ν) {K:ℕ} (hK:Odd K) :
    (∑t∈S.powerset.filter (fun t=>t.card≤K),(-1:ℝ)^t.card) ≤ (if S=∅ then 1 else 0) := by
  by_cases h0:S=∅
  · subst S
    rw [sum_filter];simp
  rw [ite_eq_right h0]
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h0))
  have hh:=truncatedPowerset_alternating S K
  rw [hm,Int.alternating_sum_range_choose_eq_choose,hK.neg_one_pow,neg_one_mul] at hh
  have hle : (∑t∈S.powerset.filter (fun t=>t.card≤K),(-1:ℤ)^t.card)≤0 :=
    hh.trans_le (by simp)
  exact_mod_cast hle

/-- Lower Bonferroni inequality for any nonnegative weights and finite family of bad events. -/
theorem weightedBonferroni_odd {ι ν:Type*} (I:Finset ι) (B:Finset ν)
    (u:ι→ℝ) (hu:∀k∈I,0≤u k) (bad:ι→ν→Prop) {K:ℕ} (hK:Odd K) :
    (∑t∈B.powerset.filter (fun t=>t.card≤K),(-1:ℝ)^t.card*
      ∑k∈I.filter (fun k=>∀p∈t,bad k p),u k) ≤
      ∑k∈I.filter (fun k=>∀p∈B,¬bad k p),u k := by
  let T:=B.powerset.filter (fun t=>t.card≤K)
  let f (k:ι) (t:Finset ν) : ℝ := if ∀p∈t,bad k p then (-1:ℝ)^t.card else 0
  have hr (k:ι) : (∑t∈T,f k t)=∑t∈(B.filter (bad k)).powerset.filter (fun t=>t.card≤K),(-1:ℝ)^t.card := by
    calc _ = ∑t∈T.filter (fun t=>∀p∈t,bad k p),(-1:ℝ)^t.card := by simp only [f,sum_filter]
         _ = _ := by
           apply sum_congr _ fun _ _=>rfl
           ext t
           simp only [T,mem_filter,mem_powerset]
           constructor
           · rintro ⟨⟨h,hc⟩,hb⟩
             exact ⟨fun p hp=>mem_filter.mpr ⟨h hp,hb p hp⟩,hc⟩
           · rintro ⟨h,hc⟩
             exact ⟨⟨fun p hp=>(mem_filter.mp (h hp)).1,hc⟩,fun p hp=>(mem_filter.mp (h hp)).2⟩
  have he (k:ι) : B.filter (bad k)=∅ ↔ ∀p∈B,¬bad k p := by simp [Finset.filter_eq_empty_iff]
  simp_rw [sum_filter (s:=I),mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro k hk
  have hrew : (∑t∈T,(-1:ℝ)^t.card*(if ∀p∈t,bad k p then u k else 0))=(∑t∈T,f k t)*u k := by
    rw [sum_mul];apply sum_congr rfl;intro t _;by_cases hh:∀p∈t,bad k p <;> simp [f,hh]
  rw [hrew,hr]
  apply (mul_le_mul_of_nonneg_right (oddTruncatedPowerset_le _ hK) (hu k hk)).trans_eq
  by_cases hh:∀p∈B,¬bad k p
  · rw [ite_eq_left hh,ite_eq_left ((he k).mpr hh),one_mul]
  · rw [ite_eq_right hh,ite_eq_right (fun hh'=>hh ((he k).mp hh')),zero_mul]

theorem truncatedPrimeSubsets_card (B:Finset ℕ) {z K:ℕ} (hz:1≤z)
    (hp:∀p∈B,Nat.Prime p) (hB:∀p∈B,p≤z) :
    (B.powerset.filter (fun t=>t.card≤K)).card≤z^K := by
  let T:=B.powerset.filter (fun t=>t.card≤K)
  have h : T.card≤(Icc 1 (z^K)).card := by
    apply Finset.card_le_card_of_injOn (fun t:Finset ℕ=>∏p∈t,p)
    · intro t ht
      have hs:=mem_powerset.mp (mem_filter.mp ht).1
      have hpos : 0<∏p∈t,p := prod_pos fun p h=> (hp p (hs h)).pos
      have hle : ∏p∈t,p≤z^t.card := by
        calc _ ≤ ∏_p∈t,z := Finset.prod_le_prod (fun p h=>hB p (hs h))
             _ = _ := by simp
      exact mem_Icc.mpr ⟨hpos,hle.trans (Nat.pow_le_pow_right hz (mem_filter.mp ht).2)⟩
    · intro s hs t ht he
      have h₁:=mem_powerset.mp (mem_filter.mp hs).1
      have h₂:=mem_powerset.mp (mem_filter.mp ht).1
      exact (Nat.primeFactors_prod (fun p h=>hp p (h₁ h))).symm.trans
        ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (fun p h=>hp p (h₂ h))))
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using h

end GoldbachPartial
