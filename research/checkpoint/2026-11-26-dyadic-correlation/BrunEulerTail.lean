import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace GoldbachPartial
open Finset

noncomputable def brunEulerWeight (p : ℕ) : ℝ := 1/((p:ℝ)-1)

theorem brunEulerWeight_bounds {p : ℕ} (hp : 3≤p) : 0≤brunEulerWeight p ∧ brunEulerWeight p≤1 := by
  have hpr : (3:ℝ)≤p := by exact_mod_cast hp
  unfold brunEulerWeight
  exact ⟨div_nonneg zero_le_one (by linarith),(div_le_one (by linarith)).mpr (by linarith)⟩

private theorem brunEuler_integer_products (m : ℕ) :
    (∏ p ∈ Icc 3 (m+2), (1-brunEulerWeight p))=1/((m:ℝ)+1) ∧
    (∏ p ∈ Icc 3 (m+2), (1+2*brunEulerWeight p))=((m:ℝ)+2)*((m:ℝ)+3)/6 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m+1+2=m+2+1 by omega]
    simp only [prod_Icc_succ_top (by omega : 3≤m+2+1)]
    rw [ih.1,ih.2]
    unfold brunEulerWeight
    push_cast
    have h1 : (m:ℝ)+1≠0 := by positivity
    have h2 : (m:ℝ)+1+1≠0 := by positivity
    have h3 : (m:ℝ)+2+1-1≠0 := by linarith [Nat.cast_nonneg (α:=ℝ) m]
    constructor <;> field_simp <;> ring

/-- The remaining density dominates 1/(z+1) for any subset of [3,z]. -/
theorem brunEuler_product_lower (z : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 3 z) :
    1/((z:ℝ)+1) ≤ ∏ p ∈ B, (1-brunEulerWeight p) := by
  have hfull : 1/((z:ℝ)+1) ≤ ∏ p ∈ Icc 3 z, (1-brunEulerWeight p) := by
    obtain _ | _ | m := z
    · norm_num
    · norm_num
    · rw [(brunEuler_integer_products m).1]
      exact one_div_le_one_div_of_le (by positivity) (by push_cast;linarith)
  apply hfull.trans
  apply prod_le_prod_of_subset_of_le_one₀ hB
  · intro p hp
    exact sub_nonneg.mpr (brunEulerWeight_bounds (mem_Icc.mp hp).1).2
  · intro p hp _
    linarith only [(brunEulerWeight_bounds (mem_Icc.mp hp).1).1]

/-- The value at two of the generating polynomial for the positive subset weights. -/
theorem brunEuler_product_upper (z : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 3 z) :
    (∏ p ∈ B, (1+2*brunEulerWeight p)) ≤ ((z:ℝ)+1)^2 := by
  have hone (p : ℕ) (hp : p∈Icc 3 z) : 1≤1+2*brunEulerWeight p := by
    linarith only [(brunEulerWeight_bounds (mem_Icc.mp hp).1).1]
  apply (prod_le_prod_of_subset_of_one_le₀ hB (fun p hp => zero_le_one.trans (hone p (hB hp)))
    (fun p hp _ => hone p hp)).trans
  obtain _ | _ | m := z
  · norm_num
  · norm_num
  · rw [(brunEuler_integer_products m).2]
    push_cast
    nlinarith [sq_nonneg (m:ℝ),Nat.cast_nonneg (α:=ℝ) m]

theorem brunEuler_powerset_tail (z K : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 3 z) :
    (∑ t ∈ B.powerset.filter (fun t => K≤t.card), ∏ p ∈ t, brunEulerWeight p) ≤
      ((z:ℝ)+1)^2/(2:ℝ)^K := by
  have hw (t : Finset ℕ) (ht : t∈B.powerset) : 0≤∏ p∈t,brunEulerWeight p :=
    prod_nonneg fun p hp => (brunEulerWeight_bounds (mem_Icc.mp (hB (mem_powerset.mp ht hp))).1).1
  apply (le_div_iff₀ (by positivity)).mpr
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
    _ ≤ _ := brunEuler_product_upper z B hB

/-- Signed truncation differs from the full local density by at most the
positive powerset tail. This finite estimate holds for both parities of K. -/
theorem brunEuler_signed_truncation_error (z K : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 3 z) :
    |(∑ t ∈ B.powerset.filter (fun t => t.card<K), ∏ p ∈ t, -brunEulerWeight p) -
      ∏ p ∈ B, (1-brunEulerWeight p)| ≤ ((z:ℝ)+1)^2/(2:ℝ)^K := by
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
  apply le_trans ?_ (brunEuler_powerset_tail z K B hB)
  refine sum_le_sum fun t ht => le_of_eq ?_
  have hsub := mem_powerset.mp (mem_filter.mp ht).1
  dsimp only [f]
  rw [Finset.abs_prod]
  apply prod_congr rfl
  intro p hp
  rw [abs_neg,abs_of_nonneg (brunEulerWeight_bounds (mem_Icc.mp (hB (hsub hp))).1).1]

theorem brunEuler_truncation_half_density (z K : ℕ) (B : Finset ℕ) (hB : B⊆Icc 3 z)
    (hK : 2*(z+1)^3≤2^K) :
    1/(2*((z:ℝ)+1)) ≤ ∑ t ∈ B.powerset.filter (fun t => t.card<K), ∏ p ∈ t, -brunEulerWeight p := by
  have h := brunEuler_signed_truncation_error z K B hB
  have hz : 0<(z:ℝ)+1 := by positivity
  have hpow : 2*((z:ℝ)+1)^3 ≤ (2:ℝ)^K := by exact_mod_cast hK
  have hsmall : ((z:ℝ)+1)^2 / (2:ℝ)^K ≤ 1/(2*((z:ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hpow]
  have hd := brunEuler_product_lower z B hB
  have he : 2*(1/(2*((z:ℝ)+1)))=1/((z:ℝ)+1) := by field_simp
  linarith only [(abs_le.mp h).1,hsmall,hd,he]

end GoldbachPartial