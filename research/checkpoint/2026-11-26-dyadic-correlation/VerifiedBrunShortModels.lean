import VerifiedBrunShortBlockSupport
namespace GoldbachPartial
open Finset

theorem brunShortBlock_joined_model_half (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (1/2:ℝ)*(∏p∈B,(1-brunEulerWeight p))≤
      ∑S∈B.powerset,brunJoinedCoefficient (range J) (brunSieveBlock B) (brunShortBlockOrder J) S*
        ∏p∈S,brunEulerWeight p := by
  let A := brunSieveBlock B
  let r := brunShortBlockOrder J
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let U := fun i => brunLocalUpperSum (A i) (r i) brunEulerWeight
  let D := fun i => brunLocalDefectSum (A i) (r i) brunEulerWeight
  have hr (i : ℕ) := shortBrun_local J i B hpr
  have hf := block_model_half_of_relative_tail (range J) U V D (brunBlockRelativeError J)
    (fun i _ => (hr i).1.le) (fun i _ => by dsimp [brunBlockRelativeError]; positivity)
    (fun i _ => (hr i).2.1)
    (fun i _ => (hr i).2.2)
    (brunBlockRelativeError_sum J)
  have hdis (i : ℕ) (_hi : i∈range J) (j : ℕ) (_hj : j∈range J) (h : i≠j) :
      Disjoint (A i) (A j) := brunSieveBlock_disjoint B h
  have hfac := brunJoinedCoefficient_factorization (range J) A hdis r brunEulerWeight
  rw [show (range J).biUnion A = B from brunSieveBlock_partition B J hB] at hfac
  rw [hfac,←brunBlock_density_product J B hB]
  have hErase (i : ℕ) : @Finset.erase ℕ (fun a b => Classical.propDecidable (a=b)) (range J) i =
      (range J).erase i := by
    exact congrArg (fun x : DecidableEq ℕ => @Finset.erase ℕ x (range J) i) (Subsingleton.elim _ _)
  simpa only [hErase,V,U,D,A,r] using hf


open scoped Classical
open private brunUpper_inflation marked_product_indicator from VerifiedBrunOrdinaryUpper

noncomputable def brunShortOrdinaryBlockWeight (J : ℕ) (B S : Finset ℕ) : ℝ :=
  ∏ i∈range J,brunOrdinaryCoefficient (brunShortBlockOrder J i) (S∩brunSieveBlock B i).card

theorem brunShortOrdinaryBlockWeight_abs_le (J : ℕ) (B S : Finset ℕ) :
    |brunShortOrdinaryBlockWeight J B S|≤1 := by
  rw [brunShortOrdinaryBlockWeight,Finset.abs_prod]
  apply prod_le_one₀ (fun _ _=>abs_nonneg _)
  intro i _
  unfold brunOrdinaryCoefficient
  split_ifs <;> simp [abs_pow]

theorem brunShortOrdinaryBlockWeight_level (J : ℕ) (B S : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hS : S⊆B) (hc : brunShortOrdinaryBlockWeight J B S≠0) : (∏p∈S,p)≤(brunBlockBoundary J)^29 := by
  apply brunShortBlock_ordinary_subset_product_le J B S hB hS
  intro i hi
  by_contra ho
  have hz : brunOrdinaryCoefficient (brunShortBlockOrder J i) (S∩brunSieveBlock B i).card=0 := ite_eq_right ho
  exact hc (prod_eq_zero (mem_range.mpr hi) hz)

theorem brunShortOrdinaryBlock_factorization (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (w : ℕ→ℝ) :
    (∑S∈B.powerset,brunShortOrdinaryBlockWeight J B S * ∏p∈S,w p) =
      ∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunShortBlockOrder J i) w := by
  let A := brunSieveBlock B
  have hdis (i : ℕ) (_hi : i∈range J) (j : ℕ) (_hj : j∈range J) (hne : i≠j) :
      Disjoint (A i) (A j) := brunSieveBlock_disjoint B hne
  have hfac := block_powerset_factorization (range J) A hdis (fun i t=>
      brunOrdinaryCoefficient (brunShortBlockOrder J i) t.card*(∏p∈t,w p))
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

theorem brunShortOrdinaryBlock_model_upper (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (∑ S∈B.powerset,brunShortOrdinaryBlockWeight J B S*∏p∈S,brunEulerWeight p) ≤
      (8/7:ℝ)*(∏p∈B,(1-brunEulerWeight p)) := by
  let A := brunSieveBlock B
  let U := fun i => brunLocalUpperSum (A i) (brunShortBlockOrder J i) brunEulerWeight
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let δ := brunBlockRelativeError J
  have hδ (i : ℕ) : 0≤δ i := by dsimp [δ,brunBlockRelativeError];positivity
  have htot := brunBlockRelativeError_sum J
  have hV (i : ℕ) : 0≤V i := (shortBrun_local J i B hpr).1.le
  have hlocal (i : ℕ) : |U i - V i| ≤ δ i*V i := by
    exact (shortBrun_local J i B hpr).2.1
  have hab (i : ℕ) : |U i|≤(1+δ i)*V i := by
    have h := abs_add_le (U i-V i) (V i)
    rw [sub_add_cancel,abs_of_nonneg (hV i)] at h
    linarith only [h,hlocal i]
  rw [brunShortOrdinaryBlock_factorization J B hB,←brunBlock_density_product J B hB]
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

theorem brunShortOrdinaryBlock_on_bad (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (P : ℕ→Prop) :
    (∑S∈B.powerset, if ∀p∈S,P p then brunShortOrdinaryBlockWeight J B S else 0) =
      ∏i∈range J,brunBlockUpper ((brunSieveBlock B i).filter P) (brunShortBlockOrder J i) := by
  have he := brunShortOrdinaryBlock_factorization J B hB (fun p=> if P p then 1 else 0)
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
theorem brunShortOrdinaryBlock_majorizes (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (P : ℕ→Prop) :
    (if ∀p∈B,¬P p then (1:ℝ) else 0) ≤
      ∑S∈B.powerset,if ∀p∈S,P p then brunShortOrdinaryBlockWeight J B S else 0 := by
  rw [brunShortOrdinaryBlock_on_bad J B hB P]
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
    exact prod_nonneg (fun i _=>brunBlockUpper_nonneg _ ⟨6+(J-1-i),by dsimp only [brunShortBlockOrder];omega⟩)

end GoldbachPartial
