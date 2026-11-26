import VerifiedFiniteBonferroni

namespace GoldbachPartial
open Finset

def brunBlockBoundary (i : ℕ) : ℕ := 2^(2^i)
def brunSieveBlock (B : Finset ℕ) (i : ℕ) : Finset ℕ :=
  B ∩ Ioc (brunBlockBoundary i) (brunBlockBoundary (i+1))
def brunBlockOrder (J i : ℕ) : ℕ := 48 + 2*(J-1-i)

theorem brunBlockBoundary_mono : Monotone brunBlockBoundary := by
  intro i j hij
  exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hij)

theorem brunSieveBlock_disjoint (B : Finset ℕ) {i j : ℕ} (hij : i≠j) :
    Disjoint (brunSieveBlock B i) (brunSieveBlock B j) := by
  apply disjoint_left.mpr
  intro p hi hj
  obtain ⟨hli,hui⟩ := mem_Ioc.mp (mem_inter.mp hi).2
  obtain ⟨hlj,huj⟩ := mem_Ioc.mp (mem_inter.mp hj).2
  rcases lt_or_gt_of_ne hij with h|h
  · exact hlj.not_ge (hui.trans (brunBlockBoundary_mono h))
  · exact hli.not_ge (huj.trans (brunBlockBoundary_mono h))

theorem brunSieveBlock_biUnion (B : Finset ℕ) (J : ℕ) :
    (range J).biUnion (brunSieveBlock B) = B ∩ Ioc 2 (brunBlockBoundary J) := by
  induction J with
  | zero => simp [brunBlockBoundary]
  | succ J ih =>
    rw [range_add_one,biUnion_insert,ih]
    have h1 : 2≤brunBlockBoundary J := brunBlockBoundary_mono (Nat.zero_le J)
    have h2 := brunBlockBoundary_mono (Nat.le_succ J)
    rw [brunSieveBlock, ←inter_union_distrib_left,
      union_comm (Ioc (brunBlockBoundary J) (brunBlockBoundary (J+1))),
      Ioc_union_Ioc_eq_Ioc h1 h2]

theorem brunSieveBlock_partition (B : Finset ℕ) (J : ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J)) :
    (range J).biUnion (brunSieveBlock B) = B := by
  rw [brunSieveBlock_biUnion]
  apply inter_eq_left.mpr
  intro p hp
  exact mem_Ioc.mpr (mem_Icc.mp (hB hp))

private theorem brunBlock_geometric (J : ℕ) :
    (∑ i∈range J,2^(i+1))+2=2*2^J := by
  induction J with
  | zero => norm_num
  | succ J ih => rw [sum_range_succ,pow_succ]; omega

/-- The exact exponent budget for all ordinary (unexceptional) rows. -/
theorem brunBlock_order_budget (J : ℕ) :
    (∑ i∈range J,2^(i+1)*brunBlockOrder J i) + 4*J+100=100*2^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hshift : (∑ i∈range J,2^(i+1)*brunBlockOrder (J+1) i) =
        (∑ i∈range J,2^(i+1)*brunBlockOrder J i) + 2*(∑ i∈range J,2^(i+1)) := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      have hle := mem_range.mp hi
      have horder : brunBlockOrder (J+1) i=brunBlockOrder J i+2 := by dsimp [brunBlockOrder];omega
      rw [horder]
      ring
    rw [sum_range_succ,hshift,show brunBlockOrder (J+1) J=48 by dsimp [brunBlockOrder];omega,pow_succ]
    have hs := brunBlock_geometric J
    omega

private theorem brunBlock_extra_budget (J e : ℕ) :
    (∑ i∈range J,2^(i+1)*(if i=e then 1 else 0))≤2^J := by
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq']
  split_ifs with h
  · exact Nat.pow_le_pow_right (by decide) (mem_range.mp h)
  · exact Nat.zero_le _

/-- The exceptional row can occur in any one block. Choosing e=J gives no exceptional row. -/
theorem brunBlock_subset_product_le (J e : ℕ) (B S : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hS : S⊆B)
    (hc : ∀ i<J,(S∩brunSieveBlock B i).card ≤ brunBlockOrder J i + (if i=e then 1 else 0)) :
    (∏ p∈S,p) ≤ (brunBlockBoundary J)^101 := by
  let T := fun i => S ∩ brunSieveBlock B i
  have hunion : (range J).biUnion T = S := by
    dsimp only [T]
    rw [←inter_biUnion,brunSieveBlock_partition B J hB,inter_eq_left.mpr hS]
  have hdis : Set.PairwiseDisjoint (↑(range J) : Set ℕ) T := by
    intro i _ j _ hne
    exact (brunSieveBlock_disjoint B hne).mono (inter_subset_right ..) (inter_subset_right ..)
  calc
    _ = ∏ i∈range J,∏ p∈T i,p := by rw [←prod_biUnion hdis,hunion]
    _ ≤ ∏ i∈range J,2^(2^(i+1)*(brunBlockOrder J i + (if i=e then 1 else 0))) := by
      apply prod_le_prod
      intro i hi
      calc
        _ ≤ ∏ _p∈T i,brunBlockBoundary (i+1) := by
          apply prod_le_prod
          intro p hp
          exact (mem_Ioc.mp (mem_inter.mp (mem_inter.mp hp).2).2).2
        _ = (brunBlockBoundary (i+1))^(T i).card := by simp
        _ ≤ (brunBlockBoundary (i+1))^(brunBlockOrder J i + (if i=e then 1 else 0)) :=
          Nat.pow_le_pow_right (by dsimp [brunBlockBoundary];positivity) (hc i (mem_range.mp hi))
        _ = _ := (pow_mul ..).symm
    _ = 2^(∑ i∈range J, 2^(i+1)*(brunBlockOrder J i+(if i=e then 1 else 0))) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 2^(2^J*101) := by
      apply Nat.pow_le_pow_right (by decide)
      simp only [Nat.mul_add,sum_add_distrib]
      have hn := brunBlock_order_budget J
      have he := brunBlock_extra_budget J e
      omega
    _ = _ := pow_mul ..

/-- The same support allows the exceptional index to depend on the prime subset.
Distinct prime subsets give distinct integers, with no loss from the number of blocks. -/
theorem brunBlock_supported_family_card (J : ℕ) (B : Finset ℕ) (W : Finset (Finset ℕ))
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hpr : ∀ p∈B, p.Prime)
    (hW : ∀ S∈W, S⊆B ∧ ∃ e : ℕ, ∀ i<J,
      (S∩brunSieveBlock B i).card ≤ brunBlockOrder J i+(if i=e then 1 else 0)) :
    W.card ≤ (brunBlockBoundary J)^101 := by
  have h : W.card ≤ (Icc 1 ((brunBlockBoundary J)^101)).card := by
    apply card_le_card_of_injOn (fun S : Finset ℕ => ∏ p∈S,p)
    · intro S hS
      obtain ⟨hs,e,he⟩ := hW S hS
      exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hpr p (hs hp)).pos),
        brunBlock_subset_product_le J e B S hB hs he⟩
    · intro S hS T hT hST
      exact (Nat.primeFactors_prod (fun p hp => hpr p ((hW S hS).1 hp))).symm.trans
        ((congrArg Nat.primeFactors hST).trans (Nat.primeFactors_prod (fun p hp => hpr p ((hW T hT).1 hp))))
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using h

theorem brunBlock_ordinary_subset_product_le (J : ℕ) (B S : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hS : S⊆B)
    (hc : ∀ i<J,(S∩brunSieveBlock B i).card ≤ brunBlockOrder J i) :
    (∏ p∈S,p) ≤ (brunBlockBoundary J)^101 := by
  apply brunBlock_subset_product_le J J B S hB hS
  intro i hi
  simpa only [ite_eq_right hi.ne,Nat.add_zero] using hc i hi

end GoldbachPartial