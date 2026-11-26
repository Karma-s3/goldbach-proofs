import VerifiedBlockBonferroni
namespace GoldbachPartial
open Finset
open scoped Classical

private theorem product_one_sub_leakage {κ : Type*} (J : Finset κ) (δ : κ→ℝ)
    (hδ : ∀ j∈J,0≤δ j ∧ δ j≤1) : 1-∑j∈J,δ j≤∏j∈J,(1-δ j) := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    have h := hδ j (mem_insert_self ..)
    have hJ := fun i hi => hδ i (mem_insert_of_mem hi)
    have hh := mul_le_mul_of_nonneg_left (ih hJ) (sub_nonneg.mpr h.2)
    rw [sum_insert hj,prod_insert hj]
    nlinarith only [hh,mul_nonneg h.1 (sum_nonneg (fun i hi => (hJ i hi).1))]

theorem block_model_half_of_relative_tail {κ : Type*} (J : Finset κ)
    (U V D δ : κ→ℝ) (hv : ∀ i∈J,0≤V i) (hδ : ∀ i∈J,0≤δ i)
    (hclose : ∀ i∈J,|U i-V i|≤δ i*V i) (hd : ∀ i∈J,D i≤δ i*V i)
    (hsmall : (∑ i∈J,δ i)≤1/8) :
    (1/2:ℝ)*(∏i∈J,V i) ≤ (∏i∈J,U i)-∑i∈J,D i*∏j∈J.erase i,U j := by
  let W := fun i => (1-δ i)*V i
  have hbound (i : κ) (hi : i∈J) : δ i≤1/8 := (single_le_sum hδ hi).trans hsmall
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
  have h7 : 7/8 ≤ ∏i∈J,(1-δ i) := by linarith only [hp,hsmall]
  have h3 : 3/4 ≤ 1-2*∑i∈J,δ i := by linarith only [hsmall]
  have ht := mul_le_mul h3 h7 (by norm_num) (by linarith only [h3])
  linarith only [ht]

end GoldbachPartial