import VerifiedMarkedBrunUpper

namespace GoldbachPartial
open Finset
open scoped Classical
open private product_one_sub_leakage from VerifiedBlockModelHalfSoon
open private brunModel_square_interval_subset from VerifiedBrunJoinedModelHalf
open private brunUpper_inflation from VerifiedBrunOrdinaryUpper

private noncomputable def preciseBlockDelta (J i : ℕ) := 1/(2:ℝ)^(11+(J-1-i))

private theorem preciseBlockDelta_sum (J : ℕ) : (∑ i∈range J,preciseBlockDelta J i)≤1/1024 := by
  have hp (i : ℕ) : preciseBlockDelta J i = brunBlockRelativeError J i/128 := by
    unfold preciseBlockDelta brunBlockRelativeError
    rw [show 11+(J-1-i)=4+(J-1-i)+7 by omega,pow_add]
    norm_num
    ring
  simp_rw [hp,←sum_div]
  linarith only [brunBlockRelativeError_sum J]

private theorem block_model_precise {κ : Type*} (J : Finset κ)
    (U V D δ : κ→ℝ) (hv : ∀ i∈J,0≤V i) (hδ : ∀ i∈J,0≤δ i)
    (hclose : ∀ i∈J,|U i-V i|≤δ i*V i) (hd : ∀ i∈J,D i≤δ i*V i)
    (hsmall : (∑ i∈J,δ i)≤1/1024) :
    (99/100:ℝ)*(∏i∈J,V i) ≤ (∏i∈J,U i)-∑i∈J,D i*∏j∈J.erase i,U j := by
  let W := fun i => (1-δ i)*V i
  have hbound (i : κ) (hi : i∈J) : δ i≤1/1024 := (single_le_sum hδ hi).trans hsmall
  have hl (i : κ) (hi : i∈J) : W i≤U i := by
    have h := (abs_le.mp (hclose i hi)).1
    dsimp [W];linarith only [h]
  have hW (i : κ) (hi : i∈J) : 0≤W i :=
    mul_nonneg (by linarith only [hbound i hi]) (hv i hi)
  have h2 (i : κ) (hi : i∈J) : D i≤(2*δ i)*U i := by
    apply (hd i hi).trans
    have hhalf := mul_le_mul_of_nonneg_right (show δ i≤1/2 by linarith only [hbound i hi]) (hv i hi)
    have hU : V i≤2*U i := by have := hl i hi;dsimp only [W] at this;linarith only [hhalf,this]
    nlinarith only [mul_le_mul_of_nonneg_left hU (hδ i hi)]
  have hsum : (∑i∈J,2*δ i)=2*(∑i∈J,δ i) := (mul_sum ..).symm
  have hWM := brunBlocks_model_lower J U W D (fun i=>2*δ i) hW hl h2 (by rw [hsum];linarith only [hsmall])
  rw [hsum] at hWM
  apply le_trans _ hWM
  have hp := product_one_sub_leakage J δ (fun i hi => ⟨hδ i hi,by linarith only [hbound i hi]⟩)
  dsimp only [W]
  rw [prod_mul_distrib]
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg hv)
  have h7 : 1023/1024 ≤ ∏i∈J,(1-δ i) := by linarith only [hp,hsmall]
  have h3 : 511/512 ≤ 1-2*∑i∈J,δ i := by linarith only [hsmall]
  have ht := mul_le_mul h3 h7 (by norm_num) (by linarith only [h3])
  linarith only [ht]

theorem brunBlockPrecise_relative (J i : ℕ) (B : Finset ℕ) (hpr : ∀p∈B,p.Prime) :
    let S := brunSieveBlock B i
    let r := brunBlockOrder J i
    let V := ∏p∈S,(1-brunEulerWeight p)
    0<V ∧
    |(∑t∈S.powerset.filter (fun t => t.card≤r), (-1:ℝ)^t.card*∏p∈t,brunEulerWeight p)-V|
      ≤ preciseBlockDelta J i*V ∧
    (∑t∈S.powersetCard (r+1),∏p∈t,brunEulerWeight p)≤preciseBlockDelta J i*V := by
  let S := brunSieveBlock B i
  let j := J-1-i
  let r := brunBlockOrder J i
  let V := ∏p∈S,(1-brunEulerWeight p)
  have h2 : 2≤brunBlockBoundary i := brunBlockBoundary_mono (Nat.zero_le i)
  have hpr' (p : ℕ) (hp : p∈S) : p.Prime := hpr p (mem_inter.mp hp).1
  have hr : r+1=49+2*j := by dsimp [r,j,brunBlockOrder];omega
  have hV : 0<V := (Real.exp_pos _).trans_le (brunBlock_product_bounds _ S h2
    (brunModel_square_interval_subset B i) hpr').2
  have hδ : 1/(2:ℝ)^(17+2*j)≤preciseBlockDelta J i :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by dsimp [preciseBlockDelta,j];omega))
  have hlim : V/(2:ℝ)^(17+2*j)≤preciseBlockDelta J i*V := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using mul_le_mul_of_nonneg_left hδ hV.le
  refine ⟨hV,?_,?_⟩
  · have he := brunBlock_signed_truncation_relative _ j (r+1) S h2
      (brunModel_square_interval_subset B i) hpr' (by omega)
    simpa only [Nat.lt_succ_iff,Finset.prod_neg] using he.trans hlim
  · have he := brunBlock_elementary_defect _ j S h2 (brunModel_square_interval_subset B i) hpr'
    change (∑t∈S.powersetCard (r+1),∏p∈t,brunEulerWeight p)≤_
    rw [hr]; exact he.trans hlim


theorem brunJoined_precise_lower (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (99/100:ℝ)*(∏p∈B,(1-brunEulerWeight p))≤
      ∑S∈B.powerset,brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J) S*
        ∏p∈S,brunEulerWeight p := by
  let A := brunSieveBlock B
  let r := brunBlockOrder J
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let U := fun i => brunLocalUpperSum (A i) (r i) brunEulerWeight
  let D := fun i => brunLocalDefectSum (A i) (r i) brunEulerWeight
  have hr (i : ℕ) := brunBlockPrecise_relative J i B hpr
  have hf := block_model_precise (range J) U V D (preciseBlockDelta J)
    (fun i _ => (hr i).1.le) (fun i _ => by dsimp [preciseBlockDelta]; positivity)
    (fun i _ => by dsimp only [U];rw [brunLocalUpperSum_eq_filter];exact (hr i).2.1)
    (fun i _ => by dsimp only [D];rw [brunLocalDefectSum_eq_powersetCard];exact (hr i).2.2)
    (preciseBlockDelta_sum J)
  have hdis (i : ℕ) (_hi : i∈range J) (j : ℕ) (_hj : j∈range J) (h : i≠j) :
      Disjoint (A i) (A j) := brunSieveBlock_disjoint B h
  have hfac := brunJoinedCoefficient_factorization (range J) A hdis r brunEulerWeight
  rw [show (range J).biUnion A = B from brunSieveBlock_partition B J hB] at hfac
  rw [hfac,←brunBlock_density_product J B hB]
  have hErase (i : ℕ) : @Finset.erase ℕ (fun a b => Classical.propDecidable (a=b)) (range J) i =
      (range J).erase i := by
    exact congrArg (fun x : DecidableEq ℕ => @Finset.erase ℕ x (range J) i) (Subsingleton.elim _ _)
  simpa only [hErase,V,U,D,A,r] using hf

theorem brunOrdinary_precise_upper (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (∑ S∈B.powerset,brunOrdinaryBlockWeight J B S*∏p∈S,brunEulerWeight p) ≤
      (101/100:ℝ)*(∏p∈B,(1-brunEulerWeight p)) := by
  let A := brunSieveBlock B
  let U := fun i => brunLocalUpperSum (A i) (brunBlockOrder J i) brunEulerWeight
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let δ := preciseBlockDelta J
  have hδ (i : ℕ) : 0≤δ i := by dsimp [δ,preciseBlockDelta];positivity
  have htot := preciseBlockDelta_sum J
  have hV (i : ℕ) : 0≤V i := (brunBlockPrecise_relative J i B hpr).1.le
  have hlocal (i : ℕ) : |U i - V i| ≤ δ i*V i := by
    dsimp only [U]
    rw [brunLocalUpperSum_eq_filter]
    exact (brunBlockPrecise_relative J i B hpr).2.1
  have hab (i : ℕ) : |U i|≤(1+δ i)*V i := by
    have h := abs_add_le (U i-V i) (V i)
    rw [sub_add_cancel,abs_of_nonneg (hV i)] at h
    linarith only [h,hlocal i]
  rw [brunOrdinaryBlock_factorization J B hB,←brunBlock_density_product J B hB]
  change (∏i∈range J,U i) ≤ (101/100:ℝ)*(∏i∈range J,V i)
  apply (le_abs_self _).trans
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏i∈range J,(1+δ i)*V i := prod_le_prod₀ (fun _ _=>abs_nonneg _) (fun i _=>hab i)
    _ = _ := prod_mul_distrib
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _=>hV i))
      apply (brunUpper_inflation (range J) δ (fun i _=>hδ i) (htot.trans (by norm_num))).trans
      change (∑i∈range J,δ i)≤1/1024 at htot
      linarith only [htot]


theorem fixedTarget_precise_brunsieve_lower (n y J : ℕ) (he : Even n)
    (hy : y≤n/4) (hscale : y≤brunBlockBoundary J) :
    ((99/100:ℝ)*((n/2-n/4:ℕ):ℝ))*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) -
      fixedTargetBrunDistributionError n ((brunBlockBoundary J)^101) ≤
        fixedTargetBrunSurvivorMass n y := by
  let B := fixedTargetBrunPrimes n y
  let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
  let h : ℝ := (n/2-n/4:ℕ)
  have hpr (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hp
    obtain ⟨hmem,hp',hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hp'.two_le; omega,(mem_range_succ_iff.mp hmem).trans hscale⟩
  have hmodel := mul_le_mul_of_nonneg_left (brunJoined_precise_lower J B hB (fun p hp=>(hpr p hp).1))
    (show 0≤h by dsimp [h];positivity)
  have herr := (abs_le.mp (brun_joined_error_sum n J B hB hpr)).1
  have hrow := fixedTarget_Brun_joined_rows n y hy (range J) (brunSieveBlock B)
    (fun i _ j _ hij=>brunSieveBlock_disjoint B hij) (brunSieveBlock_partition B J hB)
    (brunBlockOrder J) (fun i _ => ⟨24+(J-1-i),by simp only [brunBlockOrder];omega⟩)
  apply le_trans _ hrow
  change (99/100:ℝ)*h*(∏p∈B,(1-brunEulerWeight p)) - _ ≤ _
  change h*((99/100:ℝ)*(∏p∈B,(1-brunEulerWeight p))) ≤ h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at hmodel
  change -_ ≤ (∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p))-h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at herr
  change _ ≤ ∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p)
  linear_combination hmodel+herr


theorem fixedTarget_precise_marked_upper (n y w J : ℕ) (R : Finset ℕ)
    (he : Even n) (hscale : y≤brunBlockBoundary J)
    (hR : ∀r∈R,r.Prime ∧ y<r ∧ r≤w ∧ ¬r∣n) :
    fixedTargetMarkedPrimeMass n y R ≤ (101/100:ℝ)*((n/2-n/4:ℕ):ℝ)*
      (∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))*(∑r∈R,brunEulerWeight r) +
        fixedTargetBrunDistributionError n (w*(brunBlockBoundary J)^101) := by
  let B := fixedTargetBrunPrimes n y
  let h : ℝ := (n/2-n/4:ℕ)
  have hp (p : ℕ) (hb : p∈B) : p.Prime ∧ p≤y ∧ ¬p∣n := by
    obtain ⟨hm,hpr,hn⟩ := mem_filter.mp hb
    exact ⟨hpr,mem_range_succ_iff.mp hm,hn⟩
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hb
    obtain ⟨hpr,hy,hn⟩ := hp p hb
    have hne : p≠2 := fun e=>hn (e ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hpr.two_le;omega,hy.trans hscale⟩
  have hpos : 0≤h*(∑r∈R,brunEulerWeight r) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro r hr
    unfold brunEulerWeight
    apply one_div_nonneg.mpr
    exact sub_nonneg.mpr (by exact_mod_cast (hR r hr).1.one_le)
  apply (sum_le_sum (fun r hr=>fixedTargetMarkedPrime_row_upper n y J r B hB
    (fun p hb=>⟨(hp p hb).1,(hp p hb).2.1⟩) (hR r hr).1 (hR r hr).2.1)).trans
  apply (markedBrun_progression_error n y w J B R hB hp hR).trans
  apply add_le_add_left
  change h*(∑r∈R,brunEulerWeight r)*_ ≤ 101/100*h*(∏p∈B,(1-brunEulerWeight p))*(∑r∈R,brunEulerWeight r)
  apply (mul_le_mul_of_nonneg_left (brunOrdinary_precise_upper J B hB (fun p hb=>(hp p hb).1)) hpos).trans
  apply le_of_eq
  ring

end GoldbachPartial