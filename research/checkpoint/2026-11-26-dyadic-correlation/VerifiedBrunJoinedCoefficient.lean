import VerifiedBrunBlockSupport
import VerifiedBlockPowersetFactorization
import FixedTargetBrunBonferroni

namespace GoldbachPartial
open Finset
open scoped Classical

noncomputable def brunOrdinaryCoefficient (r m : ℕ) : ℝ := if m≤r then (-1:ℝ)^m else 0
noncomputable def brunDefectCoefficient (r m : ℕ) : ℝ := if m=r+1 then 1 else 0

noncomputable def brunJoinedCoefficient (J : Finset ℕ) (B : ℕ→Finset ℕ) (r : ℕ→ℕ) (S : Finset ℕ) : ℝ :=
  let U := fun i => brunOrdinaryCoefficient (r i) (S∩B i).card
  let D := fun i => brunDefectCoefficient (r i) (S∩B i).card
  (∏ i∈J,U i) - ∑ i∈J, D i * ∏ j∈J.erase i,U j

private theorem brun_join_all (J : Finset ℕ) (B : ℕ→Finset ℕ) (r : ℕ→ℕ) (S : Finset ℕ)
    (h : ∀ i∈J,(S∩B i).card≤r i) :
    brunJoinedCoefficient J B r S = ∏i∈J,(-1:ℝ)^(S∩B i).card := by
  dsimp only [brunJoinedCoefficient]
  have hzero (i : ℕ) (hi : i∈J) : brunDefectCoefficient (r i) (S∩B i).card=0 :=
    ite_eq_right (by have := h i hi; omega)
  rw [sum_eq_zero (fun i hi => by rw [hzero i hi,zero_mul]),sub_zero]
  exact prod_congr rfl (fun i hi => ite_eq_left (h i hi))

private theorem brun_join_over (J : Finset ℕ) (B : ℕ→Finset ℕ) (r : ℕ→ℕ) (S : Finset ℕ)
    {e : ℕ} (he : e∈J) (ho : r e < (S∩B e).card) :
    brunJoinedCoefficient J B r S = -(brunDefectCoefficient (r e) (S∩B e).card *
      ∏ i∈J.erase e,brunOrdinaryCoefficient (r i) (S∩B i).card) := by
  let U := fun i => brunOrdinaryCoefficient (r i) (S∩B i).card
  have hzero : U e=0 := ite_eq_right ho.not_ge
  unfold brunJoinedCoefficient
  change (∏ i∈J,U i) - (∑ i∈J,_ * ∏ j∈J.erase i,U j) = _
  rw [prod_eq_zero he hzero,sum_eq_single_of_mem e he,zero_sub]
  intro i _ hie
  rw [prod_eq_zero (mem_erase.mpr ⟨hie.symm,he⟩) hzero,mul_zero]

theorem brunJoinedCoefficient_abs_le (J : Finset ℕ) (B : ℕ→Finset ℕ) (r : ℕ→ℕ) (S : Finset ℕ) :
    |brunJoinedCoefficient J B r S| ≤ 1 := by
  by_cases h : ∀ i∈J,(S∩B i).card≤r i
  · rw [brun_join_all J B r S h]
    simp [Finset.abs_prod,abs_pow]
  · push Not at h
    obtain ⟨e,he,ho⟩ := h
    rw [brun_join_over J B r S he ho,abs_neg,abs_mul,Finset.abs_prod]
    have hD : |brunDefectCoefficient (r e) (S∩B e).card|≤1 := by
      unfold brunDefectCoefficient
      split_ifs <;> norm_num
    apply (mul_le_mul_of_nonneg_right hD (prod_nonneg (fun _ _ => abs_nonneg _))).trans
    rw [one_mul]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro i _
    unfold brunOrdinaryCoefficient
    split_ifs <;> simp [abs_pow]

theorem brunJoinedCoefficient_support (J : Finset ℕ) (B : ℕ→Finset ℕ) (r : ℕ→ℕ) (S : Finset ℕ)
    (hc : brunJoinedCoefficient J B r S ≠ 0) :
    ∃ e : ℕ, ∀ i∈J,(S∩B i).card≤r i+(if i=e then 1 else 0) := by
  by_cases h : ∀ i∈J,(S∩B i).card≤r i
  · exact ⟨0,fun i hi => (h i hi).trans (Nat.le_add_right ..)⟩
  push Not at h
  obtain ⟨e,he,ho⟩ := h
  rw [brun_join_over J B r S he ho] at hc
  have htop : (S∩B e).card=r e+1 := by
    by_contra hne
    rw [brunDefectCoefficient,ite_eq_right hne,zero_mul,neg_zero] at hc
    exact hc rfl
  refine ⟨e,?_⟩
  intro i hi
  by_cases hie : i=e
  · subst i;simp [htop]
  · rw [ite_eq_right hie,Nat.add_zero]
    by_contra hne
    have hz : brunOrdinaryCoefficient (r i) (S∩B i).card=0 := ite_eq_right hne
    rw [prod_eq_zero (mem_erase.mpr ⟨hie,hi⟩) hz,mul_zero,neg_zero] at hc
    exact hc rfl

private theorem brun_switch_prod (J : Finset ℕ) (U D : ℕ→ℝ) {e : ℕ} (he : e∈J) :
    (∏ i∈J,if i=e then D i else U i)=D e*(∏ i∈J.erase e,U i) := by
  rw [←mul_prod_erase J _ he,ite_eq_left rfl]
  congr 1
  exact prod_congr rfl (fun i hi => ite_eq_right (mem_erase.mp hi).1)

noncomputable def brunLocalUpperSum (B : Finset ℕ) (r : ℕ) (w : ℕ→ℝ) : ℝ :=
  ∑ t∈B.powerset, brunOrdinaryCoefficient r t.card * ∏ p∈t,w p
noncomputable def brunLocalDefectSum (B : Finset ℕ) (r : ℕ) (w : ℕ→ℝ) : ℝ :=
  ∑ t∈B.powerset, brunDefectCoefficient r t.card * ∏ p∈t,w p

theorem brunJoinedCoefficient_factorization (J : Finset ℕ) (B : ℕ→Finset ℕ)
    (hd : ∀ i∈J,∀ j∈J,i≠j → Disjoint (B i) (B j)) (r : ℕ→ℕ) (w : ℕ→ℝ) :
    (∑ S∈(J.biUnion B).powerset, brunJoinedCoefficient J B r S * ∏ p∈S,w p) =
        (∏i∈J, brunLocalUpperSum (B i) (r i) w) -
        ∑ e∈J, brunLocalDefectSum (B e) (r e) w * ∏ i∈J.erase e,brunLocalUpperSum (B i) (r i) w := by
  let A := (J.biUnion B).powerset
  let U := fun i (s : Finset ℕ) => brunOrdinaryCoefficient (r i) s.card
  let D := fun i (s : Finset ℕ) => brunDefectCoefficient (r i) s.card
  let V := fun e i (s : Finset ℕ) => if i=e then D i s else U i s
  have hrow (f : ℕ→Finset ℕ→ℝ) :
      (∑ S∈A,(∏i∈J,f i (S∩B i))*(∏p∈S,w p)) =
        ∏i∈J, ∑s∈(B i).powerset, f i s*(∏p∈s,w p) := by
    rw [←block_powerset_factorization J B hd]
    apply sum_congr rfl
    intro S hS
    rw [prod_mul_distrib]
    congr 1
    have hdis : Set.PairwiseDisjoint (↑J : Set ℕ) (fun i => S ∩ B i) := by
      intro i hi j hj hne
      exact (hd i hi j hj hne).mono (inter_subset_right ..) (inter_subset_right ..)
    rw [←prod_biUnion hdis,←inter_biUnion,inter_eq_left.mpr (mem_powerset.mp hS)]
  have hv (e : ℕ) (he : e∈J) :
      (∏i∈J,∑s∈(B i).powerset,V e i s * ∏p∈s,w p) =
      brunLocalDefectSum (B e) (r e) w * ∏i∈J.erase e,brunLocalUpperSum (B i) (r i) w := by
    rw [←brun_switch_prod J (fun i=>brunLocalUpperSum (B i) (r i) w)
      (fun i=>brunLocalDefectSum (B i) (r i) w) he]
    apply prod_congr rfl
    intro i _
    by_cases hi : i=e <;> simp only [V,hi,ite_true,ite_false] <;> rfl
  have hsplit (S : Finset ℕ) :
      brunJoinedCoefficient J B r S * (∏p∈S,w p) =
        (∏i∈J,U i (S∩B i))*(∏p∈S,w p) -
        ∑e∈J,(∏i∈J,V e i (S∩B i))*(∏p∈S,w p) := by
    unfold brunJoinedCoefficient
    dsimp only
    rw [sub_mul,sum_mul]
    congr 1
    apply sum_congr rfl
    intro e he
    congr 1
    exact (brun_switch_prod J (fun i=>U i (S∩B i)) (fun i=>D i (S∩B i)) he).symm
  simp_rw [hsplit]
  rw [sum_sub_distrib,sum_comm (s:=A) (t:=J),hrow U]
  congr 1
  apply sum_congr rfl
  intro e he
  exact (hrow (V e)).trans (hv e he)

theorem brunLocalUpperSum_eq_filter (B : Finset ℕ) (r : ℕ) (w : ℕ→ℝ) :
    brunLocalUpperSum B r w =
      ∑ t∈B.powerset.filter (fun t=>t.card≤r), (-1:ℝ)^t.card*(∏p∈t,w p) := by
  unfold brunLocalUpperSum
  rw [sum_filter]
  apply sum_congr rfl
  intro t _
  by_cases ht : t.card≤r <;> simp [brunOrdinaryCoefficient,ht]

theorem brunLocalDefectSum_eq_powersetCard (B : Finset ℕ) (r : ℕ) (w : ℕ→ℝ) :
    brunLocalDefectSum B r w = ∑ t∈B.powersetCard (r+1),∏p∈t,w p := by
  have hset : B.powersetCard (r+1)=B.powerset.filter (fun t=>t.card=r+1) := by
    ext t; simp only [mem_powersetCard,mem_filter,mem_powerset]
  rw [hset,sum_filter]
  unfold brunLocalDefectSum
  apply sum_congr rfl
  intro t _
  by_cases ht : t.card=r+1 <;> simp [brunDefectCoefficient,ht]

end GoldbachPartial