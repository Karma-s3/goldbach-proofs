import VerifiedPreciseMiddleFactorCount
import VerifiedShortMarkedBrun
namespace GoldbachPartial
open Finset Filter
open scoped Classical

theorem mixed_brunsieve_count (J w : ℕ→ℕ) (B M K : ℕ) (A : ℝ) (hM : 1≤M)
    (hbudget : 1/1024+(8/7:ℝ)*A ≤ (99/100:ℝ)*M)
    (ht : Tendsto (fun n=>brunBlockBoundary (J n)) atTop atTop)
    (hgeo : ∀ᶠ n : ℕ in atTop, let y := brunBlockBoundary (J n)
      2≤y ∧ y≤w n ∧ w n≤n/4 ∧ n<(w n)^(B+1) ∧ n≤y^K)
    (hError : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, let y := brunBlockBoundary (J n)
      fixedTargetBrunDistributionError n (y^101) ≤ ε*n/Real.log n ∧
      fixedTargetBrunDistributionError n (w n*y^29) ≤ ε*n/Real.log n)
    (hMass : ∀ᶠ n : ℕ in atTop, let y := brunBlockBoundary (J n)
      ∀ R ⊆ Ioc y (w n), (∀ r∈R,r.Prime) → (∑ r∈R,brunEulerWeight r)≤A) :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (brunBlockBoundary (J n)) (B+M-1)
      (n:ℝ)/(4194304*(M:ℝ)*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(4194304*(M:ℝ)*(Real.log n)^2) ≤ (S.card:ℝ) := by
  apply precise_power_sieve_count (fun n=>brunBlockBoundary (J n)) w B M K hM ((8/7:ℝ)*A) hbudget ht hgeo
  intro ε hε
  filter_upwards [hError ε hε,hMass,hgeo] with n hE hA hg
  intro he
  let y := brunBlockBoundary (J n)
  let h := ((n/2-n/4:ℕ):ℝ)
  let P := h*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))
  let R := middleBrunPrimes n y (w n)
  have hR (r : ℕ) (hr : r∈R) : r.Prime ∧ y<r ∧ r≤w n ∧ ¬r∣n := by
    obtain ⟨hi,hp,hd⟩ := mem_filter.mp hr
    exact ⟨hp,(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2,hd⟩
  have hsum := hA R (filter_subset ..) (fun r hr => (hR r hr).1)
  have hpr (p : ℕ) (hp : p∈fixedTargetBrunPrimes n y) : 3≤p ∧ p≤y ∧ p.Prime := by
    obtain ⟨hm,hprime,hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact ⟨by have := hprime.two_le;omega,mem_range_succ_iff.mp hm,hprime⟩
  have hprod := brunEuler_product_log_lower y (fixedTargetBrunPrimes n y)
    (fun p hp => mem_Icc.mpr ⟨(hpr p hp).1,(hpr p hp).2.1⟩) (fun p hp => (hpr p hp).2.2)
  have hpos := (by positivity : 0≤1/(128*(1+Real.log y))).trans hprod
  have hP : 0≤P := mul_nonneg (Nat.cast_nonneg _) hpos
  have hlow := fixedTarget_precise_brunsieve_lower n y (J n) he (hg.2.1.trans hg.2.2.1) le_rfl
  have hup := fixedTargetShortMarkedPrimeMass_upper n y (w n) (J n) R he le_rfl hR
  have h0 := hE.1
  have h1 := hE.2
  change fixedTargetBrunDistributionError n (y^101)≤_ at h0
  change fixedTargetBrunDistributionError n (w n*y^29)≤_ at h1
  rw [mul_assoc] at hlow
  change (99/100:ℝ)*P - _ ≤ _ at hlow
  rw [mul_assoc (8/7:ℝ)] at hup
  change _ ≤ (8/7:ℝ)*P*(∑r∈R,brunEulerWeight r)+_ at hup
  constructor
  · exact (sub_le_sub_left h0 _).trans hlow
  · exact hup.trans (add_le_add (by
      calc (8/7:ℝ)*P*(∑r∈R,brunEulerWeight r) ≤ (8/7)*P*A :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
           _ = _ := by ring) h1)

end GoldbachPartial