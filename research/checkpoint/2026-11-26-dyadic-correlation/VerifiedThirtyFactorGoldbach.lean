import VerifiedBalancedBrunParameters
import VerifiedMiddleFactorCount
import VerifiedMarkedBrunUpper
import VerifiedFixedRatioSemiprimes

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

set_option exponentiation.threshold 5200 in
theorem balanced_middle_of_weight (A : ℝ) (M : ℕ) (hM : 1≤M)
    (hnum : 1+(8/7:ℝ)*A ≤ (M:ℝ)/2)
    (hweight : ∀ᶠ n : ℕ in atTop, ∀ R ⊆ Ioc (balancedBrunSmall n) (balancedBrunLarge n),
      (∀ p∈R, p.Prime) → (∑ p∈R,brunEulerWeight p) ≤ A) :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (balancedBrunSmall n) (9+M)
      (n:ℝ)/(4096*(M:ℝ)*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(4096*(M:ℝ)*(Real.log n)^2) ≤ (S.card:ℝ) := by
  have h := middle_power_sieve_count balancedBrunIndex balancedBrunLarge 9 M 4905 hM A
    hnum balancedBrunSmall_tendsto
  have hg : ∀ᶠ n : ℕ in atTop, let y:=balancedBrunSmall n
      let w:=balancedBrunLarge n
      2≤y ∧ y≤w ∧ w≤n/4 ∧ (w*y^101)^4≤n/4 ∧ n<w^(9+1) ∧ n≤y^4905 := by
    filter_upwards [balancedBrun_geometry] with n hg
    obtain ⟨hy,_,hd,hb,hk⟩ := hg
    let y := balancedBrunSmall n
    let w := balancedBrunLarge n
    have hyw : y≤w := Nat.le_self_pow (by decide : 512≠0) y
    have hq : w ≤ w*y^101 := Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0<y) _)
    have hw := hq.trans ((Nat.le_self_pow (by decide : 4≠0) _).trans hd)
    exact ⟨hy,hyw,hw,hd,hb,hk.le⟩
  apply h hg
  filter_upwards [hweight] with n hbound
  intro he
  let y := balancedBrunSmall n
  let w := balancedBrunLarge n
  let R := middleBrunPrimes n y w
  have hR (r : ℕ) (hr : r∈R) : r.Prime ∧ y<r ∧ r≤w ∧ ¬r∣n := by
    obtain ⟨hi,hp,hd⟩ := mem_filter.mp hr
    exact ⟨hp,(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2,hd⟩
  have hsum := hbound R (filter_subset ..) (fun r hr => (hR r hr).1)
  have ht := fixedTargetMarkedPrimeMass_upper n y w (balancedBrunIndex n) R he le_rfl hR
  have hpr (p : ℕ) (hp : p∈fixedTargetBrunPrimes n y) : 3≤p ∧ p≤y ∧ p.Prime := by
    obtain ⟨hm,hprime,hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact ⟨by have := hprime.two_le;omega, mem_range_succ_iff.mp hm,hprime⟩
  have hprod := brunEuler_product_log_lower y (fixedTargetBrunPrimes n y)
    (fun p hp => mem_Icc.mpr ⟨(hpr p hp).1,(hpr p hp).2.1⟩) (fun p hp => (hpr p hp).2.2)
  have hpos := (by positivity : 0≤1/(128*(1+Real.log y))).trans hprod
  apply ht.trans
  apply add_le_add _ le_rfl
  rw [← mul_assoc (8/7:ℝ)]
  exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) hpos)

theorem fixed_target_thirty_factors :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (balancedBrunSmall n) 30
      (n:ℝ)/(86016*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(86016*(Real.log n)^2) ≤ (S.card:ℝ) := by
  simpa only [show 9+21=30 by decide,Nat.cast_ofNat,show (4096:ℝ)*21=86016 by norm_num] using
    balanced_middle_of_weight 8 21 (by decide) (by norm_num) balancedBrun_medium_weight

end GoldbachPartial