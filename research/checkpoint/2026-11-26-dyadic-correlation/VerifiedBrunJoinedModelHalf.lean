import BrunBlockEuler
import VerifiedBrunBlockSupport
import VerifiedBlockModelHalfSoon
import VerifiedBrunJoinedCoefficient

namespace GoldbachPartial
open Finset

noncomputable def brunBlockRelativeError (J i : ℕ) : ℝ := 1/(2:ℝ)^(4+(J-1-i))

theorem brunBlockRelativeError_sum (J : ℕ) :
    (∑i∈range J,brunBlockRelativeError J i)≤1/8 := by
  let f (j : ℕ) : ℝ := 1/(2:ℝ)^(4+j)
  change (∑i∈range J,f (J-1-i))≤1/8
  rw [sum_range_reflect]
  induction J with
  | zero => norm_num
  | succ J ih =>
    have hshift (j : ℕ) : f (j+1)=f j/2 := by
      dsimp [f]
      rw [←Nat.add_assoc,pow_succ]
      ring
    rw [sum_range_succ',show (∑i∈range J,f (i+1))=(∑i∈range J,f i)/2 by
      simp only [hshift,sum_div]]
    have h0 : f 0 = 1/16 := by norm_num [f]
    linarith only [ih,h0]

private theorem brunModel_square_interval_subset (B : Finset ℕ) (i : ℕ) :
    brunSieveBlock B i⊆Ioc (brunBlockBoundary i) ((brunBlockBoundary i)^2) := by
  have hc : brunBlockBoundary (i+1) = (brunBlockBoundary i)^2 := by
    rw [brunBlockBoundary,brunBlockBoundary,pow_succ,pow_mul]
  intro p hp
  exact hc ▸ (mem_inter.mp hp).2

theorem brunBlockIndividual_relative (J i : ℕ) (B : Finset ℕ) (hpr : ∀p∈B,p.Prime) :
    let S := brunSieveBlock B i
    let r := brunBlockOrder J i
    let V := ∏p∈S,(1-brunEulerWeight p)
    0<V ∧
    |(∑t∈S.powerset.filter (fun t => t.card≤r), (-1:ℝ)^t.card*∏p∈t,brunEulerWeight p)-V|
      ≤ brunBlockRelativeError J i*V ∧
    (∑t∈S.powersetCard (r+1),∏p∈t,brunEulerWeight p)≤brunBlockRelativeError J i*V := by
  let S := brunSieveBlock B i
  let j := J-1-i
  let r := brunBlockOrder J i
  let V := ∏p∈S,(1-brunEulerWeight p)
  have h2 : 2≤brunBlockBoundary i := brunBlockBoundary_mono (Nat.zero_le i)
  have hpr' (p : ℕ) (hp : p∈S) : p.Prime := hpr p (mem_inter.mp hp).1
  have hr : r+1=49+2*j := by dsimp [r,j,brunBlockOrder];omega
  have hV : 0<V := (Real.exp_pos _).trans_le (brunBlock_product_bounds _ S h2
    (brunModel_square_interval_subset B i) hpr').2
  have hδ : 1/(2:ℝ)^(17+2*j)≤brunBlockRelativeError J i :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by dsimp [j];omega))
  have hlim : V/(2:ℝ)^(17+2*j)≤brunBlockRelativeError J i*V := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using mul_le_mul_of_nonneg_left hδ hV.le
  refine ⟨hV,?_,?_⟩
  · have he := brunBlock_signed_truncation_relative _ j (r+1) S h2
      (brunModel_square_interval_subset B i) hpr' (by omega)
    simpa only [Nat.lt_succ_iff,Finset.prod_neg] using he.trans hlim
  · have he := brunBlock_elementary_defect _ j S h2 (brunModel_square_interval_subset B i) hpr'
    change (∑t∈S.powersetCard (r+1),∏p∈t,brunEulerWeight p)≤_
    rw [hr]; exact he.trans hlim

theorem brunBlock_density_product (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J)) :
    (∏i∈range J,∏p∈brunSieveBlock B i,(1-brunEulerWeight p))=
      (∏p∈B,(1-brunEulerWeight p)) := by
  have hd : Set.PairwiseDisjoint (↑(range J) : Set ℕ) (brunSieveBlock B) :=
    fun _ _ _ _ h => brunSieveBlock_disjoint B h
  rw [←prod_biUnion hd, brunSieveBlock_partition B J hB]

theorem brunBlock_joined_model_half (J : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hpr : ∀p∈B,p.Prime) :
    (1/2:ℝ)*(∏p∈B,(1-brunEulerWeight p))≤
      ∑S∈B.powerset,brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J) S*
        ∏p∈S,brunEulerWeight p := by
  let A := brunSieveBlock B
  let r := brunBlockOrder J
  let V := fun i => ∏p∈A i,(1-brunEulerWeight p)
  let U := fun i => brunLocalUpperSum (A i) (r i) brunEulerWeight
  let D := fun i => brunLocalDefectSum (A i) (r i) brunEulerWeight
  have hr (i : ℕ) := brunBlockIndividual_relative J i B hpr
  have hf := block_model_half_of_relative_tail (range J) U V D (brunBlockRelativeError J)
    (fun i _ => (hr i).1.le) (fun i _ => by dsimp [brunBlockRelativeError]; positivity)
    (fun i _ => by dsimp only [U];rw [brunLocalUpperSum_eq_filter];exact (hr i).2.1)
    (fun i _ => by dsimp only [D];rw [brunLocalDefectSum_eq_powersetCard];exact (hr i).2.2)
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

end GoldbachPartial