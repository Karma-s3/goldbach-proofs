import VerifiedBrunJoinedModelHalf
import VerifiedThinSemiprimeLogUpper
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GoldbachPartial
open Finset
noncomputable section

private theorem thinBlock_product_bounds (y : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) :
    (∏p∈B,(1+(4:ℝ)/p))≤Real.exp 16 ∧ Real.exp (-16)≤∏p∈B,(1-(2:ℝ)/p) := by
  let w (p : ℕ) := (2:ℝ)/p
  have h3 (p : ℕ) (hp : p∈B) : (3:ℝ)≤p := by
    have h := (mem_Ioc.mp (hB hp)).1
    exact_mod_cast (by omega : 3≤p)
  have hw (p : ℕ) : 0≤w p := by dsimp [w]; positivity
  have hw' (p : ℕ) (hp : p∈B) : w p≤2/3 := by
    apply (div_le_div_iff₀ (by linarith only [h3 p hp]) (by norm_num)).mpr
    linarith only [h3 p hp]
  have hs : (∑p∈B,w p)≤8 := by
    calc _ ≤ ∑p∈B,2*brunEulerWeight p := by
           apply sum_le_sum
           intro p hp
           have h := h3 p hp
           have h' : 1/(p:ℝ) ≤ brunEulerWeight p := one_div_le_one_div_of_le (by linarith : 0<(p:ℝ)-1) (by linarith)
           dsimp only [w]; rw [show (2:ℝ)/(p:ℝ)=2*(1/(p:ℝ)) by ring]; exact mul_le_mul_of_nonneg_left h' (by norm_num)
         _ ≤ _ := by rw [←mul_sum];linarith only [brunBlockWeight_sum_le_four y B hy hB hpr]
  constructor
  · calc
      _ ≤ ∏p∈B,Real.exp (2*w p) := by
        apply prod_le_prod₀ (fun p _ => by positivity)
        intro p _
        have h := Real.add_one_le_exp (2*w p)
        rw [show (4:ℝ)/(p:ℝ)=2*w p by dsimp [w];ring];linarith only [h]
      _ ≤ _ := by rw [←Real.exp_sum,←mul_sum];exact Real.exp_le_exp.mpr (by linarith only [hs])
  · calc
      _ ≤ Real.exp (∑p∈B,-(2*w p)) := by
        rw [sum_neg_distrib,←mul_sum]; exact Real.exp_le_exp.mpr (by linarith only [hs])
      _ = ∏p∈B,Real.exp (-(2*w p)) := Real.exp_sum _ _
      _ ≤ _ := by
        apply prod_le_prod₀ (fun p _=>(Real.exp_pos _).le)
        intro p hp
        let b := w p
        have h0 : 0≤b := hw p
        have h1 : b≤2/3 := hw' p hp
        have hexp := Real.sum_le_exp_of_nonneg (show 0≤2*b by positivity) 3
        norm_num [sum_range_succ] at hexp
        change Real.exp (-(2*b))≤1-b
        rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos _)]
        have hsq := pow_le_pow_left₀ h0 h1 2
        have hc := mul_nonneg h0 (show 0≤1-2*b^2 by nlinarith only [hsq])
        have hm := mul_le_mul_of_nonneg_left hexp (show 0≤1-b by linarith only [h1])
        nlinarith only [hm,hc]

private theorem thinAbsTruncation (B : Finset ℕ) (K : ℕ) :
    |brunLocalUpperSum B K (fun p=>(2:ℝ)/p)-(∏p∈B,(1-(2:ℝ)/p))| ≤
      (∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1) := by
  let w (t : Finset ℕ) := ∏p∈t,((2:ℝ)/p)
  let f (t : Finset ℕ) := (-1:ℝ)^t.card*w t
  let T := B.powerset.filter (fun t=>K<t.card)
  have hw (t : Finset ℕ) : 0≤w t := prod_nonneg (fun _ _=>by positivity)
  have hsum : (∏p∈B,(1-(2:ℝ)/p))=∑t∈B.powerset,f t := by
    simp only [sub_eq_add_neg,prod_one_add,prod_neg,f,w]
  have hsplit := sum_filter_add_sum_filter_not B.powerset (fun t=>t.card≤K) f
  simp only [not_le] at hsplit
  have htail : (∑t∈T,w t)≤(∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [sum_mul]
    calc
      _ ≤ ∑t∈T,w t*(2:ℝ)^t.card := sum_le_sum (fun t ht =>
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (mem_filter.mp ht).2) (hw t))
      _ ≤ ∑t∈B.powerset,w t*(2:ℝ)^t.card := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun t _ _ => mul_nonneg (hw t) (by positivity))
      _ = _ := by
        rw [prod_one_add]
        apply sum_congr rfl
        intro t _
        change (∏p∈t,((2:ℝ)/p))*2^t.card=_
        rw [←prod_const (s:=t) (b:=(2:ℝ)),←prod_mul_distrib]
        exact prod_congr rfl (fun p _ => by ring)
  rw [brunLocalUpperSum_eq_filter,hsum,←hsplit]
  change |(∑t∈B.powerset.filter (fun t=>t.card≤K),f t)-((∑t∈B.powerset.filter (fun t=>t.card≤K),f t)+∑t∈T,f t)|≤_
  rw [sub_add_cancel_left,abs_neg]
  apply le_trans _ htail
  apply (abs_sum_le_sum_abs ..).trans
  exact sum_le_sum fun t _ => le_of_eq (by simp [f,abs_mul,abs_of_nonneg (hw t)])

theorem thinBrunBlock_model_upper (J : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hpr : ∀p∈B,p.Prime) :
    (∏i∈range J,brunLocalUpperSum (brunSieveBlock B i) (brunBlockOrder J i) (fun p=>(2:ℝ)/p))
      ≤ Real.exp 1*(∏p∈B,(1-(2:ℝ)/p)) := by
  let A := brunSieveBlock B
  let D := fun i => ∏p∈A i,(1-(2:ℝ)/p)
  let U := fun i => brunLocalUpperSum (A i) (brunBlockOrder J i) (fun p=>(2:ℝ)/p)
  let δ := fun i => 8*brunBlockRelativeError J i
  have hd (i : ℕ) : 0≤δ i := by dsimp [δ,brunBlockRelativeError]; positivity
  have hpp (i : ℕ) (p : ℕ) (hp : p∈A i) : p.Prime := hpr p (mem_inter.mp hp).1
  have hi (i : ℕ) : A i⊆Ioc (brunBlockBoundary i) ((brunBlockBoundary i)^2) := by
    have he : brunBlockBoundary (i+1)=(brunBlockBoundary i)^2 := by rw [brunBlockBoundary,brunBlockBoundary,pow_succ,pow_mul]
    exact fun p hp => he ▸ (mem_inter.mp hp).2
  have hbounds (i : ℕ) := thinBlock_product_bounds (brunBlockBoundary i) (A i)
    (brunBlockBoundary_mono (Nat.zero_le i)) (hi i) (hpp i)
  have hD (i : ℕ) : 0≤D i := (Real.exp_pos _).le.trans (hbounds i).2
  have hexp : Real.exp 32≤(2:ℝ)^48 := by
    calc _ ≤ Real.exp (((48:ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr (by norm_num;linarith only [Real.log_two_gt_d9])
         _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hU (i : ℕ) : |U i|≤(1+δ i)*D i := by
    let j := J-1-i
    let G := ∏p∈A i,(1+(4:ℝ)/p)
    have h1 : 1≤D i * Real.exp 16 := by
      have h := mul_le_mul_of_nonneg_right (hbounds i).2 (Real.exp_pos 16).le
      rwa [←Real.exp_add,show (-16:ℝ)+16=0 by norm_num,Real.exp_zero] at h
    have hG : G≤D i*2^48 := by
      calc _ ≤ Real.exp 16 := (hbounds i).1
           _ = Real.exp 16*1 := (mul_one _).symm
           _ ≤ Real.exp 16*(D i*Real.exp 16) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
           _ = D i*Real.exp 32 := by rw [show (32:ℝ)=16+16 by norm_num,Real.exp_add];ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hexp (hD i)
    have hr : brunBlockOrder J i+1=49+2*j := by dsimp [brunBlockOrder,j];omega
    have hrem : G/(2:ℝ)^(brunBlockOrder J i+1)≤D i/(2:ℝ)^(1+j) := by
      rw [hr,div_le_div_iff₀ (by positivity) (by positivity)]
      calc _ ≤ (D i*2^48)*(2:ℝ)^(1+j) := mul_le_mul_of_nonneg_right hG (by positivity)
           _ = D i*2^(48+(1+j)) := by rw [pow_add (2:ℝ) 48 (1+j),mul_assoc]
           _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (hD i)
    have hf := (thinAbsTruncation (A i) (brunBlockOrder J i)).trans hrem
    have he : D i/(2:ℝ)^(1+j)=δ i*D i := by
      change D i/(2:ℝ)^(1+j)=(8*(1/(2:ℝ)^(4+j)))*D i
      rw [show 4+j=3+(1+j) by omega,pow_add (2:ℝ) 3 (1+j)]
      ring
    change |U i-D i|≤D i/(2:ℝ)^(1+j) at hf
    rw [he] at hf
    have hh := abs_add_le (U i-D i) (D i)
    rw [sub_add_cancel,abs_of_nonneg (hD i)] at hh
    linarith only [hh,hf]
  have hinf : (∏i∈range J,(1+δ i))≤Real.exp 1 := by
    calc _ ≤ ∏i∈range J,Real.exp (δ i) := by
           apply prod_le_prod₀ (fun i _ => by linarith only [hd i])
           intro i _;linarith only [Real.add_one_le_exp (δ i)]
         _ ≤ _ := by
           rw [←Real.exp_sum]
           apply Real.exp_le_exp.mpr
           dsimp only [δ];rw [←mul_sum]
           linarith only [brunBlockRelativeError_sum J]
  have hdis : Set.PairwiseDisjoint (↑(range J):Set ℕ) A := fun _ _ _ _ h=>brunSieveBlock_disjoint B h
  have hprod : (∏i∈range J,D i)=∏p∈B,(1-(2:ℝ)/p) := by
    dsimp only [D];rw [←prod_biUnion hdis,show (range J).biUnion A=B from brunSieveBlock_partition B J hB]
  calc
    _ ≤ |∏i∈range J,U i| := le_abs_self _
    _ = ∏i∈range J,|U i| := abs_prod ..
    _ ≤ ∏i∈range J,((1+δ i)*D i) := prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hU i)
    _ = (∏i∈range J,(1+δ i))*(∏i∈range J,D i) := prod_mul_distrib
    _ ≤ _ := by rw [←hprod];exact mul_le_mul_of_nonneg_right hinf (prod_nonneg fun i _=>hD i)
end
end GoldbachPartial