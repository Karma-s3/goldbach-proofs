import VerifiedBrunDistributionBudget

namespace GoldbachPartial
open Finset
open scoped Classical

noncomputable def brunOrdinaryBlockWeight (J : ℕ) (B S : Finset ℕ) : ℝ :=
  ∏ i∈range J,brunOrdinaryCoefficient (brunBlockOrder J i) (S∩brunSieveBlock B i).card

theorem brunOrdinaryBlockWeight_abs_le (J : ℕ) (B S : Finset ℕ) :
    |brunOrdinaryBlockWeight J B S|≤1 := by
  rw [brunOrdinaryBlockWeight,Finset.abs_prod]
  apply prod_le_one₀ (fun _ _=>abs_nonneg _)
  intro i _
  unfold brunOrdinaryCoefficient
  split_ifs <;> simp [abs_pow]

theorem brunOrdinaryBlockWeight_level (J : ℕ) (B S : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hS : S⊆B) (hc : brunOrdinaryBlockWeight J B S≠0) : (∏p∈S,p)≤(brunBlockBoundary J)^101 := by
  apply brunBlock_ordinary_subset_product_le J B S hB hS
  intro i hi
  by_contra ho
  have hz : brunOrdinaryCoefficient (brunBlockOrder J i) (S∩brunSieveBlock B i).card=0 := ite_eq_right ho
  exact hc (prod_eq_zero (mem_range.mpr hi) hz)

theorem brunOrdinaryBlock_factorization (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (w : ℕ→ℝ) :
    (∑S∈B.powerset,brunOrdinaryBlockWeight J B S * ∏p∈S,w p) =
      ∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunBlockOrder J i) w := by
  let A := brunSieveBlock B
  have hdis (i : ℕ) (_hi : i∈range J) (j : ℕ) (_hj : j∈range J) (hne : i≠j) :
      Disjoint (A i) (A j) := brunSieveBlock_disjoint B hne
  have hfac := block_powerset_factorization (range J) A hdis (fun i t=>
      brunOrdinaryCoefficient (brunBlockOrder J i) t.card*(∏p∈t,w p))
  have hpart : (range J).biUnion A=B := brunSieveBlock_partition B J hB
  rw [hpart] at hfac
  apply Eq.trans _ hfac
  apply sum_congr rfl
  intro S hs
  rw [prod_mul_distrib]
  congr 1
  have hd : Set.PairwiseDisjoint (↑(range J) : Set ℕ) (fun i => S∩A i) := by
    intro i hi j hj hne
    exact (hdis i hi j hj hne).mono (inter_subset_right ..) (inter_subset_right ..)
  rw [←prod_biUnion hd,←inter_biUnion,hpart,inter_eq_left.mpr (mem_powerset.mp hs)]

private theorem brunUpper_inflation (I : Finset ℕ) (δ : ℕ→ℝ) (hp : ∀ i∈I,0≤δ i)
    (hs : (∑i∈I,δ i)≤1/8) : (∏i∈I,(1+δ i)) ≤ 1+(8/7:ℝ)*(∑i∈I,δ i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hI ih =>
    have hpI (j : ℕ) (hj : j∈I) := hp j (mem_insert_of_mem hj)
    have hi := hp i (mem_insert_self ..)
    rw [sum_insert hI] at hs ⊢
    have hpart : (∑j∈I,δ j)≤1/8 := by linarith only [hs,hi]
    have hcap : 1+(8/7:ℝ)*(∑j∈I,δ j)≤8/7 := by linarith
    rw [prod_insert hI]
    apply (mul_le_mul_of_nonneg_left (ih hpI hpart) (by linarith : 0≤1+δ i)).trans
    nlinarith only [mul_le_mul_of_nonneg_left hcap hi]

theorem brunOrdinaryBlock_model_upper (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (∑ S∈B.powerset,brunOrdinaryBlockWeight J B S*∏p∈S,brunEulerWeight p) ≤
      (8/7:ℝ)*(∏p∈B,(1-brunEulerWeight p)) := by
  let A := brunSieveBlock B
  let U := fun i => brunLocalUpperSum (A i) (brunBlockOrder J i) brunEulerWeight
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let δ := brunBlockRelativeError J
  have hδ (i : ℕ) : 0≤δ i := by dsimp [δ,brunBlockRelativeError];positivity
  have htot := brunBlockRelativeError_sum J
  have hV (i : ℕ) : 0≤V i := (brunBlockIndividual_relative J i B hpr).1.le
  have hlocal (i : ℕ) : |U i - V i| ≤ δ i*V i := by
    dsimp only [U]
    rw [brunLocalUpperSum_eq_filter]
    exact (brunBlockIndividual_relative J i B hpr).2.1
  have hab (i : ℕ) : |U i|≤(1+δ i)*V i := by
    have h := abs_add_le (U i-V i) (V i)
    rw [sub_add_cancel,abs_of_nonneg (hV i)] at h
    linarith only [h,hlocal i]
  rw [brunOrdinaryBlock_factorization J B hB,←brunBlock_density_product J B hB]
  change (∏i∈range J,U i) ≤ (8/7:ℝ)*(∏i∈range J,V i)
  apply (le_abs_self _).trans
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏i∈range J,(1+δ i)*V i := prod_le_prod₀ (fun _ _=>abs_nonneg _) (fun i _=>hab i)
    _ = _ := prod_mul_distrib
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _=>hV i))
      apply (brunUpper_inflation (range J) δ (fun i _=>hδ i) htot).trans
      change (∑i∈range J,δ i)≤1/8 at htot
      linarith only [htot]

private theorem marked_product_indicator (S : Finset ℕ) (P : ℕ→Prop) :
    (∏p∈S,if P p then (1:ℝ) else 0) = if ∀p∈S,P p then 1 else 0 := by
  by_cases h : ∀p∈S,P p
  · rw [ite_eq_left h]
    exact prod_eq_one (fun p hp=>ite_eq_left (h p hp))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨p,hp,h⟩ := h
    exact prod_eq_zero hp (ite_eq_right h)

theorem brunOrdinaryBlock_on_bad (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (P : ℕ→Prop) :
    (∑S∈B.powerset, if ∀p∈S,P p then brunOrdinaryBlockWeight J B S else 0) =
      ∏i∈range J,brunBlockUpper ((brunSieveBlock B i).filter P) (brunBlockOrder J i) := by
  have he := brunOrdinaryBlock_factorization J B hB (fun p=> if P p then 1 else 0)
  simp_rw [marked_product_indicator] at he
  apply Eq.trans _ (he.trans _)
  · apply sum_congr rfl;intro S _
    by_cases h : ∀p∈S,P p <;> simp [h]
  · apply prod_congr rfl
    intro i _
    rw [brunLocalUpperSum_eq_filter,brunBlockUpper_at]
    apply sum_congr rfl
    intro t _
    rw [marked_product_indicator]
    by_cases h : ∀p∈t,P p <;> simp [h]

/-- Pointwise upper majorant on an actual complement. -/
theorem brunOrdinaryBlock_majorizes (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (P : ℕ→Prop) :
    (if ∀p∈B,¬P p then (1:ℝ) else 0) ≤
      ∑S∈B.powerset,if ∀p∈S,P p then brunOrdinaryBlockWeight J B S else 0 := by
  rw [brunOrdinaryBlock_on_bad J B hB P]
  by_cases h : ∀p∈B,¬P p
  · rw [ite_eq_left h]
    apply le_of_eq
    symm
    apply prod_eq_one
    intro i _
    have he : (brunSieveBlock B i).filter P=∅ :=
      filter_eq_empty_iff.mpr (fun p hp=>h p (mem_inter.mp hp).1)
    rw [he,brunBlockUpper_empty]
  · rw [ite_eq_right h]
    exact prod_nonneg (fun i _=>brunBlockUpper_nonneg _ ⟨24+(J-1-i),by dsimp only [brunBlockOrder];omega⟩)

end GoldbachPartial