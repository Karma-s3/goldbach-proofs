import VerifiedThirtyFactorGoldbach
import VerifiedMediumBrunSeven

namespace GoldbachPartial
open Finset Filter
open scoped Classical

theorem fixed_target_twentyseven_factors :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (balancedBrunSmall n) 27
      (n:ℝ)/(73728*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(73728*(Real.log n)^2) ≤ (S.card:ℝ) := by
  simpa only [show 9+18=27 by decide,Nat.cast_ofNat,show (4096:ℝ)*18=73728 by norm_num] using
    balanced_middle_of_weight 7 18 (by decide) (by norm_num) balancedBrun_medium_weight_seven

noncomputable def boundedAfterFixedRatio (c : ℝ) (n : ℕ) : Finset ℕ :=
  fixedTargetBoundedFactorPrimes n (balancedBrunSmall n) 27 \ thinFixedRatioPrimes c n

/-- A fixed even target still has this many squarefree rough complements of
at most 27 prime factors after removal of its near-square-root semiprimes. -/
theorem fixed_target_twentyseven_after_fixed_ratio (c : ℝ) (hc : 0<c) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (n:ℝ)/(147456*Real.log n) ≤ ∑p∈boundedAfterFixedRatio c n, Real.log p ∧
      (n:ℝ)/(147456*(Real.log n)^2) ≤ ((boundedAfterFixedRatio c n).card:ℝ) := by
  filter_upwards [fixed_target_twentyseven_factors,
    thinFixedRatioPrimes_weight_little_o c hc (1/147456) (by norm_num),eventually_ge_atTop (2:ℕ)] with n hB hT hn
  intro he
  let S := fixedTargetBoundedFactorPrimes n (balancedBrunSmall n) 27
  let T := thinFixedRatioPrimes c n
  let U := boundedAfterFixedRatio c n
  let L := Real.log n
  have hL : 0<L := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hp (p : ℕ) (h : p∈S) := (boundedFactorPrimes_iff n _ 27 p).mp h
  have hsplit : (∑p∈U,Real.log p)+(∑p∈S∩T,Real.log p)=∑p∈S,Real.log p := by
    have h := sum_filter_add_sum_filter_not S (fun p => p∈T) (fun p => Real.log p)
    have hi : S.filter (fun p => p∈T)=S∩T := by ext p;simp
    have hd : S.filter (fun p => p∉T)=U := by ext p;simp [U,boundedAfterFixedRatio,S,T]
    rw [hi,hd] at h
    rw [add_comm]; exact h
  have hRemoved : (∑p∈S∩T,Real.log p)≤∑p∈T,weight p := by
    calc
      _ = ∑p∈S∩T,weight p := sum_congr rfl fun p h =>
        (ite_eq_left (by exact (hp p (mem_inter.mp h).1).2.2.1) : weight p=Real.log p).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (inter_subset_right ..)
        (fun p _ _ => by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl)
  have hmass := (hB he).1
  have hLos := hT he
  change (n:ℝ)/(73728*L) ≤ ∑p∈S,Real.log p at hmass
  change (∑p∈T,weight p)≤(1/147456)*((n:ℝ)/L) at hLos
  have H : (n:ℝ)/(147456*L)≤∑p∈U,Real.log p := by
    have h1 : (n:ℝ)/(73728*L)=2*((n:ℝ)/(147456*L)) := by field_simp;ring
    have h2 : (1/147456)*((n:ℝ)/L)=((n:ℝ)/(147456*L)) := by ring
    linarith only [hsplit,hRemoved,hmass,hLos,h1,h2]
  refine ⟨H,?_⟩
  have hcnt : (∑p∈U,Real.log p)≤(U.card:ℝ)*L := by
    calc
      _ ≤ ∑_p∈U,L := by
        apply sum_le_sum
        intro p h
        obtain ⟨_,hpn,hpr,_⟩ := hp p (mem_sdiff.mp h).1
        exact Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast (by omega : p≤n))
      _ = _ := by simp
  change (n:ℝ)/(147456*L^2)≤(U.card:ℝ)
  apply (div_le_iff₀ (by positivity)).mpr
  have h := (div_le_iff₀ (by positivity)).mp (H.trans hcnt)
  linarith only [h]

end GoldbachPartial
