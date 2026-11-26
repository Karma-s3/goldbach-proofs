import BrunEulerTail
import PrimeFactorLogMean

namespace GoldbachPartial
open Finset

theorem brunEulerWeight_le_half {p : ℕ} (hp : 3≤p) : brunEulerWeight p≤1/2 := by
  have h : (3:ℝ)≤p := by exact_mod_cast hp
  unfold brunEulerWeight
  exact (div_le_div_iff₀ (by linarith) (by norm_num)).mpr (by linarith)

theorem brunBlockWeight_sum_le_four (y : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) :
    (∑ p∈B,brunEulerWeight p)≤4 := by
  have h3 (p : ℕ) (hp : p∈B) : 3≤p := by have hi := (mem_Ioc.mp (hB hp)).1;omega
  by_cases h4 : y<4
  · have hs : B⊆Ioc 2 9 := by
      intro p hp
      obtain ⟨hp1,hp2⟩ := mem_Ioc.mp (hB hp)
      have hmax : y^2≤3^2 := Nat.pow_le_pow_left (by omega) 2
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    calc
      _ ≤ ∑ _p∈B,(1/2:ℝ) := sum_le_sum fun p hp => brunEulerWeight_le_half (h3 p hp)
      _ ≤ ∑ _p∈Ioc 2 9,(1/2:ℝ) := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by norm_num)
      _ ≤ _ := by norm_num
  have hyR : (4:ℝ)≤y := by exact_mod_cast Nat.le_of_not_gt h4
  have hy0 : (0:ℝ)<y := by linarith
  have hL : 0<Real.log y := Real.log_pos (by linarith)
  have hprime : B⊆(Ioc 0 (y^2)).filter Nat.Prime := by
    intro p hp
    have hi := mem_Ioc.mp (hB hp)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hpr p hp).pos,hi.2⟩,hpr p hp⟩
  have hmass : (∑ p ∈ B,Real.log p/(p:ℝ))≤2*Real.log y+Real.log 4 := by
    apply (sum_le_sum_of_subset_of_nonneg hprime
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))).trans
    calc
      _ ≤ Real.log ((y^2:ℕ):ℝ)+Real.log 4 := prime_log_reciprocal_upto (y^2) (by positivity)
      _ = _ := by push_cast; rw [Real.log_pow]; norm_num
  have hlg : Real.log 4≤Real.log y := Real.log_le_log (by norm_num) hyR
  apply (mul_le_mul_iff_left₀ hL).mp
  rw [sum_mul]
  calc
    _ ≤ ∑ p∈B, (4/3:ℝ)*(Real.log p/(p:ℝ)) := by
      refine sum_le_sum fun p hp => ?_
      have hip := (mem_Ioc.mp (hB hp)).1
      have hprR : (4:ℝ)<p := hyR.trans_lt (by exact_mod_cast hip)
      have hc : brunEulerWeight p ≤ (4/3:ℝ)/p := by
        unfold brunEulerWeight
        apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
        linarith
      have hlog := Real.log_le_log hy0 (by exact_mod_cast hip.le : (y:ℝ)≤p)
      exact (mul_le_mul hc hlog hL.le (by positivity)).trans_eq (by ring)
    _ ≤ _ := by rw [←mul_sum];linarith only [hmass,hlg]

/-- Generating-polynomial and density estimates for an individual block. -/
theorem brunBlock_product_bounds (y : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) :
    (∏p∈B,(1+2*brunEulerWeight p)) ≤ Real.exp 8 ∧
      Real.exp (-8) ≤ ∏p∈B,(1-brunEulerWeight p) := by
  have hs := brunBlockWeight_sum_le_four y B hy hB hpr
  have h3 (p : ℕ) (hp : p∈B) : 3≤p := by have hi := (mem_Ioc.mp (hB hp)).1;omega
  constructor
  · calc
      _ ≤ ∏p∈B, Real.exp (2*brunEulerWeight p) := by
        apply prod_le_prod₀
        · intro p hp
          linarith only [(brunEulerWeight_bounds (h3 p hp)).1]
        · intro p _
          linarith only [Real.add_one_le_exp (2*brunEulerWeight p)]
      _ ≤ _ := by rw [←Real.exp_sum,←mul_sum];exact Real.exp_le_exp.mpr (by linarith only [hs])
  · calc
      _ ≤ Real.exp (∑p∈B,-(2*brunEulerWeight p)) := by
        rw [sum_neg_distrib,←mul_sum]
        exact Real.exp_le_exp.mpr (by linarith only [hs])
      _ = ∏p∈B,Real.exp (-(2*brunEulerWeight p)) := Real.exp_sum _ _
      _ ≤ _ := by
        apply prod_le_prod₀ (fun p _ => (Real.exp_pos _).le)
        intro p hp
        let b := brunEulerWeight p
        have hb := (brunEulerWeight_bounds (h3 p hp)).1
        have hb' := brunEulerWeight_le_half (h3 p hp)
        change 0≤b at hb
        change b≤1/2 at hb'
        change Real.exp (-(2*b)) ≤ 1-b
        rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos _)]
        calc
          (1:ℝ) ≤ (1-b)*(1+2*b) := by nlinarith only [mul_nonneg hb (sub_nonneg.mpr hb')]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (2*b)])
            (by linarith only [hb'])

private theorem brunBlock_weighted_generating (K : ℕ) (B : Finset ℕ) (hB : ∀p∈B,3≤p) :
    (∑t ∈ B.powerset.filter (fun t => K≤t.card), ∏p∈t,brunEulerWeight p)*(2:ℝ)^K ≤
      ∏p∈B,(1+2*brunEulerWeight p) := by
  have hw (t : Finset ℕ) (ht : t∈B.powerset) : 0≤∏ p∈t,brunEulerWeight p :=
    prod_nonneg fun p hp => (brunEulerWeight_bounds (hB p (mem_powerset.mp ht hp))).1
  rw [sum_mul]
  calc
    _ ≤ ∑ t ∈ B.powerset.filter (fun t => K≤t.card),
        (∏ p ∈ t,brunEulerWeight p)*(2:ℝ)^t.card := by
      refine sum_le_sum fun t ht => ?_
      have hh := mem_filter.mp ht
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh.2) (hw t hh.1)
    _ ≤ ∑ t ∈ B.powerset, (∏ p ∈ t,brunEulerWeight p)*(2:ℝ)^t.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t ht _ => mul_nonneg (hw t ht) (by positivity))
    _ = ∏ p ∈ B, (1+2*brunEulerWeight p) := by
      rw [prod_one_add]
      refine sum_congr rfl fun t _ => ?_
      rw [prod_mul_distrib,prod_const,mul_comm]




theorem brunBlock_tail_relative (y j K : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) (hK : 49+2*j≤K) :
    (∑t ∈ B.powerset.filter (fun t => K≤t.card), ∏p∈t,brunEulerWeight p) ≤
      (∏p∈B,(1-brunEulerWeight p))/(2:ℝ)^(17+2*j) := by
  let D := ∏p∈B,(1-brunEulerWeight p)
  let T := ∑t ∈ B.powerset.filter (fun t => K≤t.card), ∏p∈t,brunEulerWeight p
  have h3 (p : ℕ) (hp : p∈B) : 3≤p := by have hi := (mem_Ioc.mp (hB hp)).1;omega
  have hT : 0≤T := sum_nonneg fun t ht => prod_nonneg fun p hp =>
    (brunEulerWeight_bounds (h3 p (mem_powerset.mp (mem_filter.mp ht).1 hp))).1
  obtain ⟨hgen,hD⟩ := brunBlock_product_bounds y B hy hB hpr
  change Real.exp (-8)≤D at hD
  have hD' : 1≤D*Real.exp 8 := by
    have h := mul_le_mul_of_nonneg_right hD (Real.exp_pos 8).le
    rwa [←Real.exp_add,show (-8:ℝ)+8=0 by norm_num,Real.exp_zero] at h
  have h16 : Real.exp 16≤(2:ℝ)^32 := by
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at hlog
    calc
      _ ≤ Real.exp (((32:ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr (by norm_num; linarith only [hlog])
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hfinal : T*(2:ℝ)^(49+2*j) ≤ D*(2:ℝ)^32 := by
    calc
      _ ≤ T*(2:ℝ)^K := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hK) hT
      _ ≤ _ := brunBlock_weighted_generating K B h3
      _ ≤ Real.exp 8 := hgen
      _ = Real.exp 8*1 := (mul_one _).symm
      _ ≤ Real.exp 8*(D*Real.exp 8) := mul_le_mul_of_nonneg_left hD' (Real.exp_pos _).le
      _ = D*Real.exp 16 := by rw [show (16:ℝ)=8+8 by norm_num, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h16 ((Real.exp_pos _).le.trans hD)
  apply (le_div_iff₀ (by positivity)).mpr
  apply (mul_le_mul_iff_left₀ (show (0:ℝ)<2^32 by positivity)).mp
  calc
    _ = T*(2:ℝ)^(49+2*j) := by
      change (T*(2:ℝ)^(17+2*j))*2^32=T*2^(49+2*j)
      rw [show 49+2*j=(17+2*j)+32 by omega, pow_add (2:ℝ) (17+2*j) 32, mul_assoc]
    _ ≤ _ := hfinal

theorem brunBlock_elementary_defect (y j : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) :
    (∑t∈B.powersetCard (49+2*j), ∏p∈t,brunEulerWeight p) ≤
      (∏p∈B,(1-brunEulerWeight p))/(2:ℝ)^(17+2*j) := by
  apply le_trans ?_ (brunBlock_tail_relative y j (49+2*j) B hy hB hpr le_rfl)
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨hs,hc⟩ := mem_powersetCard.mp ht
    exact mem_filter.mpr ⟨mem_powerset.mpr hs,hc.ge⟩
  · intro t ht _
    apply prod_nonneg
    intro p hp
    have hi := (mem_Ioc.mp (hB (mem_powerset.mp (mem_filter.mp ht).1 hp))).1
    exact (brunEulerWeight_bounds (by omega : 3≤p)).1

theorem brunBlock_signed_truncation_relative (y j K : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) (hK : 49+2*j≤K) :
    |(∑ t ∈ B.powerset.filter (fun t => t.card<K), ∏ p ∈ t, -brunEulerWeight p) -
      ∏ p ∈ B, (1-brunEulerWeight p)| ≤ (∏p∈B,(1-brunEulerWeight p))/(2:ℝ)^(17+2*j) := by
  classical
  let f (t : Finset ℕ) := ∏ p ∈ t, -brunEulerWeight p
  have hfull : (∏ p ∈ B,(1-brunEulerWeight p)) = ∑ t ∈ B.powerset, f t := by
    simp only [sub_eq_add_neg,prod_one_add,f]
  have hsplit := sum_filter_add_sum_filter_not B.powerset (fun t => t.card<K) f
  simp only [not_lt] at hsplit
  have he : (∑ t ∈ B.powerset.filter (fun t => t.card<K), f t) - ∏ p ∈ B,(1-brunEulerWeight p) =
      -(∑ t ∈ B.powerset.filter (fun t => K≤t.card), f t) := by rw [hfull,←hsplit];ring
  rw [he,abs_neg]
  apply (abs_sum_le_sum_abs ..).trans
  apply le_trans ?_ (brunBlock_tail_relative y j K B hy hB hpr hK)
  refine sum_le_sum fun t ht => le_of_eq ?_
  have hsub := mem_powerset.mp (mem_filter.mp ht).1
  dsimp only [f]
  rw [Finset.abs_prod]
  apply prod_congr rfl
  intro p hp
  have hi := (mem_Ioc.mp (hB (hsub hp))).1
  rw [abs_neg,abs_of_nonneg (brunEulerWeight_bounds (by omega : 3≤p)).1]



theorem brunBlock_elementary_defect_ratio (y j : ℕ) (B : Finset ℕ) (hy : 2≤y)
    (hB : B⊆Ioc y (y^2)) (hpr : ∀p∈B,p.Prime) :
    (∑t∈B.powersetCard (49+2*j), ∏p∈t,brunEulerWeight p)/
        (∏p∈B,(1-brunEulerWeight p)) ≤ 1/(2:ℝ)^(17+2*j) := by
  have hD := (brunBlock_product_bounds y B hy hB hpr).2
  apply (div_le_iff₀ ((Real.exp_pos _).trans_le hD)).mpr
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using brunBlock_elementary_defect y j B hy hB hpr

end GoldbachPartial