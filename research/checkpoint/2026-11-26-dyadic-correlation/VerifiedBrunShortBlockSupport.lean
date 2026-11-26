import VerifiedBrunOrdinaryUpper
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GoldbachPartial
open Finset
noncomputable section

private theorem shortBrun_sum (y : ℕ) (B : Finset ℕ) (hy : 16≤y)
    (hB : B⊆Ioc y (y^2)) (hp : ∀p∈B,p.Prime) : (∑p∈B,brunEulerWeight p)≤8/3 := by
  have hyR : (16:ℝ)≤y := by exact_mod_cast hy
  have hy0 : (0:ℝ)<y := by linarith
  have hL : 0<Real.log y := Real.log_pos (by linarith)
  have hprime : B⊆(Ioc 0 (y^2)).filter Nat.Prime := by
    intro p h
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hp p h).pos,(mem_Ioc.mp (hB h)).2⟩,hp p h⟩
  have hmass : (∑ p ∈ B,Real.log p/(p:ℝ))≤2*Real.log y+Real.log 4 := by
    apply (sum_le_sum_of_subset_of_nonneg hprime
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))).trans
    calc _ ≤ Real.log ((y^2:ℕ):ℝ)+Real.log 4 := prime_log_reciprocal_upto (y^2) (by positivity)
         _ = _ := by push_cast;rw [Real.log_pow];norm_num
  have hlg : 2*Real.log 4≤Real.log y := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<16) hyR
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow] at h
    norm_num at h;exact h
  apply (mul_le_mul_iff_left₀ hL).mp
  rw [sum_mul]
  calc
    _ ≤ ∑p∈B,(17/16:ℝ)*(Real.log p/(p:ℝ)) := by
      apply sum_le_sum
      intro p h
      have hpy := (mem_Ioc.mp (hB h)).1
      have h17 : (17:ℝ)≤p := by exact_mod_cast (by omega : 17≤p)
      have hc : brunEulerWeight p ≤ (17/16:ℝ)/p := by
        unfold brunEulerWeight
        apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
        linarith
      have hh := Real.log_le_log hy0 (by exact_mod_cast hpy.le : (y:ℝ)≤p)
      exact (mul_le_mul hc hh hL.le (by positivity)).trans_eq (by ring)
    _ ≤ _ := by rw [←mul_sum];linarith only [hmass,hlg,hL]

private theorem shortBrun_prod (y : ℕ) (B : Finset ℕ) (hy : 16≤y)
    (hB : B⊆Ioc y (y^2)) (hp : ∀p∈B,p.Prime) :
    (∏p∈B,(1+4*brunEulerWeight p))≤Real.exp (32/3) ∧ Real.exp (-4)≤∏p∈B,(1-brunEulerWeight p) := by
  have hs := shortBrun_sum y B hy hB hp
  have h3 (p : ℕ) (h : p∈B) : 17≤p := by have hh := (mem_Ioc.mp (hB h)).1;omega
  have hw (p : ℕ) (h : p∈B) : 0≤brunEulerWeight p := (brunEulerWeight_bounds (by have := h3 p h;omega)).1
  constructor
  · calc
      _ ≤ ∏p∈B,Real.exp (4*brunEulerWeight p) := by
        apply prod_le_prod₀ (fun p h=>by linarith only [hw p h])
        intro p _;linarith only [Real.add_one_le_exp (4*brunEulerWeight p)]
      _ ≤ _ := by rw [←Real.exp_sum,←mul_sum];exact Real.exp_le_exp.mpr (by linarith only [hs])
  · calc
      _ ≤ Real.exp (∑p∈B,-((3/2:ℝ)*brunEulerWeight p)) := by
        rw [sum_neg_distrib,←mul_sum];exact Real.exp_le_exp.mpr (by linarith only [hs])
      _ = ∏p∈B,Real.exp (-((3/2:ℝ)*brunEulerWeight p)) := Real.exp_sum _ _
      _ ≤ _ := by
        apply prod_le_prod₀ (fun _ _=>(Real.exp_pos _).le)
        intro p h
        let b := brunEulerWeight p
        have hb : 0≤b := hw p h
        have hb' : b≤1/3 := by
          have hh : (17:ℝ)≤p := by exact_mod_cast h3 p h
          exact (div_le_div_iff₀ (by linarith) (by norm_num)).mpr (by linarith)
        change Real.exp (-((3/2:ℝ)*b))≤1-b
        rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos _)]
        have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((3/2:ℝ)*b)) (show 0≤1-b by linarith only [hb'])
        nlinarith only [hh,mul_nonneg hb (sub_nonneg.mpr hb')]

def brunShortBlockOrder (J i : ℕ) : ℕ := 12+2*(J-1-i)

private theorem shortBrun_genTail (B : Finset ℕ) (K : ℕ) (hB : ∀p∈B,3≤p) :
    (∑t∈B.powerset.filter (fun t=>K≤t.card),∏p∈t,brunEulerWeight p)*(4:ℝ)^K≤
      (∏p∈B,(1+4*brunEulerWeight p)) := by
  have hw (t : Finset ℕ) (ht : t∈B.powerset) : 0≤∏ p∈t,brunEulerWeight p :=
    prod_nonneg fun p hp => (brunEulerWeight_bounds (hB p (mem_powerset.mp ht hp))).1
  rw [sum_mul]
  calc
    _ ≤ ∑ t ∈ B.powerset.filter (fun t => K≤t.card),
        (∏ p ∈ t,brunEulerWeight p)*(4:ℝ)^t.card := by
      refine sum_le_sum fun t ht => ?_
      have hh := mem_filter.mp ht
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh.2) (hw t hh.1)
    _ ≤ ∑ t ∈ B.powerset, (∏ p ∈ t,brunEulerWeight p)*(4:ℝ)^t.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t ht _ => mul_nonneg (hw t ht) (by positivity))
    _ = ∏ p ∈ B, (1+4*brunEulerWeight p) := by
      rw [prod_one_add]
      refine sum_congr rfl fun t _ => ?_
      rw [prod_mul_distrib,prod_const,mul_comm]





theorem shortBrun_local (J i : ℕ) (B : Finset ℕ) (hpr : ∀p∈B,p.Prime) :
    let S := brunSieveBlock B i
    let r := brunShortBlockOrder J i
    let V := ∏p∈S,(1-brunEulerWeight p)
    0<V ∧ |brunLocalUpperSum S r brunEulerWeight-V|≤brunBlockRelativeError J i*V ∧
      brunLocalDefectSum S r brunEulerWeight ≤ brunBlockRelativeError J i*V := by
  let S:=brunSieveBlock B i
  let r:=brunShortBlockOrder J i
  let y:=brunBlockBoundary i
  let j:=J-1-i
  let V:=∏p∈S,(1-brunEulerWeight p)
  have hr : r+1=13+2*j := by dsimp [r,brunShortBlockOrder,j];omega
  have hbd : brunBlockBoundary (i+1)=y^2 := by
    dsimp only [y];rw [brunBlockBoundary,brunBlockBoundary,pow_succ,pow_mul]
  have hI : S⊆Ioc y (y^2) := fun p hp => hbd ▸ (mem_inter.mp hp).2
  have hP (p : ℕ) (hp : p∈S) : p.Prime := hpr p (mem_inter.mp hp).1
  have h2 : 2≤y := brunBlockBoundary_mono (Nat.zero_le i)
  have h3 (p : ℕ) (hp : p∈S) : 3≤p := by have h:=(mem_Ioc.mp (hI hp)).1;omega
  have hV : 0<V := (Real.exp_pos _).trans_le (brunBlock_product_bounds y S h2 hI hP).2
  have hδ : 0≤brunBlockRelativeError J i := by dsimp [brunBlockRelativeError]; positivity
  refine ⟨hV,?_⟩
  rw [brunLocalUpperSum_eq_filter,brunLocalDefectSum_eq_powersetCard]
  change |(∑t∈S.powerset.filter (fun t=>t.card≤r),(-1:ℝ)^t.card*∏p∈t,brunEulerWeight p)-V|≤_ ∧
    (∑t∈S.powersetCard (r+1),∏p∈t,brunEulerWeight p)≤_
  by_cases hsmall : i<2
  · have hsub : S⊆(Ioc 2 16).filter Nat.Prime := by
      intro p hp
      obtain ⟨hl,hu⟩:=mem_Ioc.mp (mem_inter.mp hp).2
      have htop : brunBlockBoundary (i+1)≤16 := brunBlockBoundary_mono (by omega : i+1≤2)
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hu.trans htop⟩,hP p hp⟩
    have hcr : S.card≤r := by
      have hc := card_le_card hsub
      have hsz : ((Ioc 2 16).filter Nat.Prime).card≤12 := by decide
      dsimp only [r,brunShortBlockOrder];omega
    have hset : S.powerset.filter (fun t=>t.card≤r)=S.powerset :=
      filter_eq_self.mpr (fun t ht=>(card_le_card (mem_powerset.mp ht)).trans hcr)
    have hset' : S.powersetCard (r+1)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨hs,he⟩:=mem_powersetCard.mp ht
      have := card_le_card hs;omega
    have hF : (∑t∈S.powerset,(-1:ℝ)^t.card*∏p∈t,brunEulerWeight p)=V := by
      dsimp only [V];simp only [sub_eq_add_neg,prod_one_add,prod_neg]
    rw [hset,hset',hF,sub_self,abs_zero,sum_empty]
    exact ⟨mul_nonneg hδ hV.le,mul_nonneg hδ hV.le⟩
  have hy : 16≤y := brunBlockBoundary_mono (show (2:ℕ) ≤ i by omega)
  let G := ∏p∈S,(1+4*brunEulerWeight p)
  obtain ⟨hG,hV'⟩:=shortBrun_prod y S hy hI hP
  have h1 : 1≤V*Real.exp 4 := by
    have hh:=mul_le_mul_of_nonneg_right hV' (Real.exp_pos 4).le
    rwa [←Real.exp_add,show (-4:ℝ)+4=0 by norm_num,Real.exp_zero] at hh
  have h22 : Real.exp (32/3+4)≤(2:ℝ)^22 := by
    calc _ ≤ Real.exp (((22:ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr (by norm_num;linarith only [Real.log_two_gt_d9])
         _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hGV : G≤V*2^22 := by
    calc _ ≤ Real.exp (32/3) := hG
         _ = Real.exp (32/3)*1 := (mul_one _).symm
         _ ≤ Real.exp (32/3)*(V*Real.exp 4) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
         _ = V*Real.exp (32/3+4) := by rw [Real.exp_add];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left h22 hV.le
  let T:=S.powerset.filter (fun t=>r+1≤t.card)
  let w (t:Finset ℕ):=∏p∈t,brunEulerWeight p
  have hw (t:Finset ℕ) (ht:t⊆S) : 0≤w t := prod_nonneg (fun p hp=>(brunEulerWeight_bounds (h3 p (ht hp))).1)
  have hTail : (∑t∈T,w t)≤brunBlockRelativeError J i*V := by
    have hbg := (shortBrun_genTail S (r+1) h3).trans hGV
    have hpow : (2:ℝ)^(4+j)*2^22≤(4:ℝ)^(r+1) := by
      rw [←pow_add,show (4:ℝ)=2^2 by norm_num,←pow_mul]
      apply pow_le_pow_right₀ (by norm_num)
      omega
    change (∑t∈T,w t)≤(1/(2:ℝ)^(4+j))*V
    rw [one_div,←div_eq_inv_mul]
    apply (le_div_iff₀ (by positivity)).mpr
    apply (mul_le_mul_iff_left₀ (show (0:ℝ)<2^22 by positivity)).mp
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hpow (sum_nonneg (fun t ht=>hw t (mem_powerset.mp (mem_filter.mp ht).1)))).trans hbg
  constructor
  · let f (t:Finset ℕ):=(-1:ℝ)^t.card*w t
    have hF : V=∑t∈S.powerset,f t := by dsimp only [V,f,w];simp only [sub_eq_add_neg,prod_one_add,prod_neg]
    have hs:=sum_filter_add_sum_filter_not S.powerset (fun t=>t.card≤r) f
    simp only [not_le] at hs
    change |(∑t∈S.powerset.filter (fun t=>t.card≤r),f t)-V|≤_
    rw [hF,←hs,sub_add_cancel_left,abs_neg]
    apply (abs_sum_le_sum_abs ..).trans
    apply le_trans _ hTail
    exact sum_le_sum (fun t ht=>le_of_eq (by simp [f,abs_mul,abs_of_nonneg (hw t (mem_powerset.mp (mem_filter.mp ht).1))]))
  · apply le_trans _ hTail
    apply sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨h,hc⟩:=mem_powersetCard.mp ht
      exact mem_filter.mpr ⟨mem_powerset.mpr h,hc.ge⟩
    · exact fun t ht _=>hw t (mem_powerset.mp (mem_filter.mp ht).1)

open private brunBlock_geometric brunBlock_extra_budget from VerifiedBrunBlockSupport

theorem brunShortBlock_order_budget (J : ℕ) :
    (∑ i∈range J,2^(i+1)*brunShortBlockOrder J i) + 4*J+28=28*2^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hshift : (∑ i∈range J,2^(i+1)*brunShortBlockOrder (J+1) i) =
        (∑ i∈range J,2^(i+1)*brunShortBlockOrder J i) + 2*(∑ i∈range J,2^(i+1)) := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      have hle := mem_range.mp hi
      have horder : brunShortBlockOrder (J+1) i=brunShortBlockOrder J i+2 := by dsimp [brunShortBlockOrder];omega
      rw [horder]
      ring
    rw [sum_range_succ,hshift,show brunShortBlockOrder (J+1) J=12 by dsimp [brunShortBlockOrder];omega,pow_succ]
    have hs := brunBlock_geometric J
    omega

theorem brunShortBlock_subset_product_le (J e : ℕ) (B S : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hS : S⊆B)
    (hc : ∀ i<J,(S∩brunSieveBlock B i).card ≤ brunShortBlockOrder J i + (if i=e then 1 else 0)) :
    (∏ p∈S,p) ≤ (brunBlockBoundary J)^29 := by
  let T := fun i => S ∩ brunSieveBlock B i
  have hunion : (range J).biUnion T = S := by
    dsimp only [T]
    rw [←inter_biUnion,brunSieveBlock_partition B J hB,inter_eq_left.mpr hS]
  have hdis : Set.PairwiseDisjoint (↑(range J) : Set ℕ) T := by
    intro i _ j _ hne
    exact (brunSieveBlock_disjoint B hne).mono (inter_subset_right ..) (inter_subset_right ..)
  calc
    _ = ∏ i∈range J,∏ p∈T i,p := by rw [←prod_biUnion hdis,hunion]
    _ ≤ ∏ i∈range J,2^(2^(i+1)*(brunShortBlockOrder J i + (if i=e then 1 else 0))) := by
      apply prod_le_prod
      intro i hi
      calc
        _ ≤ ∏ _p∈T i,brunBlockBoundary (i+1) := by
          apply prod_le_prod
          intro p hp
          exact (mem_Ioc.mp (mem_inter.mp (mem_inter.mp hp).2).2).2
        _ = (brunBlockBoundary (i+1))^(T i).card := by simp
        _ ≤ (brunBlockBoundary (i+1))^(brunShortBlockOrder J i + (if i=e then 1 else 0)) :=
          Nat.pow_le_pow_right (by dsimp [brunBlockBoundary];positivity) (hc i (mem_range.mp hi))
        _ = _ := (pow_mul ..).symm
    _ = 2^(∑ i∈range J, 2^(i+1)*(brunShortBlockOrder J i+(if i=e then 1 else 0))) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 2^(2^J*29) := by
      apply Nat.pow_le_pow_right (by decide)
      simp only [Nat.mul_add,sum_add_distrib]
      have hn := brunShortBlock_order_budget J
      have he := brunBlock_extra_budget J e
      omega
    _ = _ := pow_mul ..

theorem brunShortBlock_ordinary_subset_product_le (J : ℕ) (B S : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hS : S⊆B)
    (hc : ∀ i<J,(S∩brunSieveBlock B i).card ≤ brunShortBlockOrder J i) :
    (∏ p∈S,p) ≤ (brunBlockBoundary J)^29 := by
  apply brunShortBlock_subset_product_le J J B S hB hS
  intro i hi
  simpa only [ite_eq_right hi.ne,Nat.add_zero] using hc i hi

end
end GoldbachPartial