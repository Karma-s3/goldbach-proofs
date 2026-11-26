import VerifiedFiniteBonferroni

namespace GoldbachPartial
open Finset
open scoped Classical

/-- The upper polynomial on the finite family of events that hold at one point. -/
noncomputable def brunBlockUpper {ν:Type*} (S:Finset ν) (r:ℕ) : ℝ :=
  ∑t∈S.powerset.filter (fun t=>t.card≤r),(-1:ℝ)^t.card

/-- The single omitted rank following an even upper truncation. -/
def brunBlockDefect {ν:Type*} (S:Finset ν) (r:ℕ) : ℝ := (S.card.choose (r+1):ℝ)

theorem brunBlockUpper_range {ν:Type*} (S:Finset ν) (r:ℕ) :
    brunBlockUpper S r=∑j∈range (r+1),(-1:ℝ)^j*(S.card.choose j) := by
  unfold brunBlockUpper
  exact_mod_cast truncatedPowerset_alternating S r

theorem brunBlockUpper_empty {ν:Type*} (r:ℕ) : brunBlockUpper (∅:Finset ν) r=1 := by
  simp [brunBlockUpper,sum_filter]

theorem brunBlockUpper_nonneg {ν:Type*} (S:Finset ν) {r:ℕ} (hr:Even r) : 0≤brunBlockUpper S r := by
  by_cases hs:S=∅
  · rw [hs,brunBlockUpper_empty];norm_num
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hs))
  have hh:=truncatedPowerset_alternating S r
  rw [hm,Int.alternating_sum_range_choose_eq_choose,hr.neg_one_pow,one_mul] at hh
  have h : 0≤∑t∈S.powerset.filter (fun t=>t.card≤r),(-1:ℤ)^t.card := hh.ge.trans' (by positivity)
  unfold brunBlockUpper
  exact_mod_cast h

theorem brunBlock_interval {ν:Type*} (S:Finset ν) {r:ℕ} (hr:Even r) :
    brunBlockUpper S r-brunBlockDefect S r ≤ (if S=∅ then 1 else 0) ∧
    (if S=∅ then 1 else 0) ≤ brunBlockUpper S r := by
  have hodd : Odd (r+1) := by obtain ⟨k,hk⟩:=hr;exact ⟨k,by omega⟩
  have hh : brunBlockUpper S (r+1)=brunBlockUpper S r-brunBlockDefect S r := by
    rw [brunBlockUpper_range,brunBlockUpper_range,sum_range_succ,hodd.neg_one_pow,neg_one_mul,sub_eq_add_neg]
    rfl
  constructor
  · rw [←hh];exact oddTruncatedPowerset_le _ hodd
  · by_cases hs:S=∅
    · rw [hs,brunBlockUpper_empty];simp
    · rw [ite_eq_right hs];exact brunBlockUpper_nonneg S hr

/-- The product minorant pays for the first omitted rank in at most one block.
This formulation permits different even ranks on different blocks. -/
theorem brunBlocks_pointwise_lower {κ ν:Type*} (J:Finset κ) (S:κ→Finset ν)
    (r:κ→ℕ) (hr:∀j∈J,Even (r j)) :
    (∏j∈J,brunBlockUpper (S j) (r j)) -
      (∑j∈J,brunBlockDefect (S j) (r j)*
        ∏l∈J.erase j,brunBlockUpper (S l) (r l)) ≤
      (if ∀j∈J,S j=∅ then 1 else 0) := by
  classical
  let U (j:κ):=brunBlockUpper (S j) (r j)
  let D (j:κ):=brunBlockDefect (S j) (r j)
  let T (j:κ):=D j*∏l∈J.erase j,U l
  have hU (j:κ)(hj:j∈J) : 0≤U j := brunBlockUpper_nonneg _ (hr j hj)
  have hT (j:κ)(hj:j∈J) : 0≤T j :=
    mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun l hl=>hU l (mem_of_mem_erase hl))
  change (∏j∈J,U j)-(∑j∈J,T j)≤_
  by_cases h:∀j∈J,S j=∅
  · have hprod : (∏j∈J,U j)=1 := prod_eq_one fun j hj=>by simp only [U,h j hj,brunBlockUpper_empty]
    rw [hprod,ite_eq_left h]
    linarith only [sum_nonneg hT]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j,hj,hnon⟩:=h
    have hj' : S j≠∅ := hnon.ne_empty
    have hd := (brunBlock_interval (S j) (hr j hj)).1
    rw [ite_eq_right hj'] at hd
    have hud : U j≤D j := by dsimp only [U,D];linarith only [hd]
    have hrow : (∏l∈J,U l)≤T j := by
      rw [←mul_prod_erase J U hj];exact mul_le_mul_of_nonneg_right hud (prod_nonneg fun l hl=>hU l (mem_of_mem_erase hl))
    exact sub_nonpos.mpr (hrow.trans (single_le_sum hT hj))

theorem weightedBrunBlocks_lower {ι κ ν:Type*} (I:Finset ι) (J:Finset κ) (B:κ→Finset ν)
    (bad:ι→ν→Prop) (u:ι→ℝ) (hu:∀k∈I,0≤u k) (r:κ→ℕ) (hr:∀j∈J,Even (r j)) :
    (∑k∈I,u k*((∏j∈J,brunBlockUpper ((B j).filter (bad k)) (r j))-
      (∑j∈J,brunBlockDefect ((B j).filter (bad k)) (r j)*
        ∏l∈J.erase j,brunBlockUpper ((B l).filter (bad k)) (r l)))) ≤
      ∑k∈I.filter (fun k=>∀j∈J,∀p∈B j,¬bad k p),u k := by
  classical
  rw [sum_filter]
  apply sum_le_sum;intro k hk
  apply (mul_le_mul_of_nonneg_left (brunBlocks_pointwise_lower J (fun j=>(B j).filter (bad k)) r hr) (hu k hk)).trans_eq
  by_cases h:∀j∈J,∀p∈B j,¬bad k p
  · have he : ∀j∈J,(B j).filter (bad k)=∅ := fun j hj=>Finset.filter_eq_empty_iff.mpr (h j hj)
    rw [ite_eq_left he,ite_eq_left h,mul_one]
  · have he : ¬∀j∈J,(B j).filter (bad k)=∅ := fun he=>h (fun j hj=>Finset.filter_eq_empty_iff.mp (he j hj))
    rw [ite_eq_right he,ite_eq_right h,mul_zero]

theorem brunBlockUpper_at {ν:Type*} (B:Finset ν) (bad:ν→Prop) (r:ℕ) :
    brunBlockUpper (B.filter bad) r =
      ∑t∈B.powerset.filter (fun t=>t.card≤r),if ∀p∈t,bad p then (-1:ℝ)^t.card else 0 := by
  unfold brunBlockUpper
  rw [←sum_filter]
  apply sum_congr _ fun _ _=>rfl
  ext t
  simp only [mem_filter,mem_powerset]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun p hp=>(mem_filter.mp (h hp)).1,hc⟩,fun p hp=>(mem_filter.mp (h hp)).2⟩
  · rintro ⟨⟨h,hc⟩,hb⟩
    exact ⟨fun p hp=>mem_filter.mpr ⟨h hp,hb p hp⟩,hc⟩

theorem brunBlockDefect_at {ν:Type*} (B:Finset ν) (bad:ν→Prop) (r:ℕ) :
    brunBlockDefect (B.filter bad) r =
      ∑t∈B.powersetCard (r+1),if ∀p∈t,bad p then (1:ℝ) else 0 := by
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  unfold brunBlockDefect
  rw [←card_powersetCard]
  congr 2
  ext t
  simp only [mem_filter,mem_powersetCard]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun p hp=>(mem_filter.mp (h hp)).1,hc⟩,fun p hp=>(mem_filter.mp (h hp)).2⟩
  · rintro ⟨⟨h,hc⟩,hb⟩
    exact ⟨fun p hp=>mem_filter.mpr ⟨h hp,hb p hp⟩,hc⟩

/-- A sum of relative local defects controls the independently evaluated block polynomial. -/
theorem brunBlocks_model_lower {κ:Type*} (J:Finset κ) (U V D δ:κ→ℝ)
    (hv:∀j∈J,0≤V j) (hu:∀j∈J,V j≤U j) (hd:∀j∈J,D j≤δ j*U j)
    (hδ:(∑j∈J,δ j)≤1) :
    (1-∑j∈J,δ j)*(∏j∈J,V j) ≤
      (∏j∈J,U j)-∑j∈J,D j*∏l∈J.erase j,U l := by
  have hU (j:κ)(hj:j∈J):0≤U j := (hv j hj).trans (hu j hj)
  have hsum : (∑j∈J,D j*∏l∈J.erase j,U l)≤(∑j∈J,δ j)*(∏l∈J,U l) := by
    rw [sum_mul]
    apply sum_le_sum;intro j hj
    rw [←mul_prod_erase J U hj]
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hd j hj) (prod_nonneg fun l hl=>hU l (mem_of_mem_erase hl))
  have hprod := mul_le_mul_of_nonneg_left (prod_le_prod₀ hv hu) (sub_nonneg.mpr hδ)
  linarith only [hsum,hprod]

end GoldbachPartial
