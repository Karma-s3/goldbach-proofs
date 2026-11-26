import VerifiedFarCenteredMinorReduction
import ExteriorShortTubeModes

namespace GoldbachPartial
open Finset Filter MeasureTheory

/-- The signed remainder after the same short nonzero band is removed on each region.
The small-cutoff zero coefficient on the exterior is retained explicitly. -/
noncomputable def bothFarMinorContribution (n : ℕ) : ℝ :=
  (∫ t in exteriorMinorTubeDomain n,
    exactWeightedFarOffTarget n (minorRamanujanCutoff n) (exactWeightedShortCutoff n) t).re +
  volume.real (exteriorMinorTubeDomain n) * exactWeightedZeroMode n (minorRamanujanCutoff n) +
  (∫ t in highNaturalPrimeTubes n,
    exactWeightedFarOffTarget n (medDeskQ n) (exactWeightedShortCutoff n) t).re

theorem bothFarMinorContribution_approx {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      |(1-volume.real (highNaturalPrimeTubes n))*corr n -
        adjustedMajorContribution n-bothFarMinorContribution n| ≤ ε*(n:ℝ) := by
  have hhalf : 0 < ε/2 := by positivity
  filter_upwards [farCenteredMinorContribution_approx hhalf,
    exteriorMinorTube_kernel_short_delete hhalf] with n h1 h2
  have hr := (Complex.abs_re_le_norm _).trans h2
  rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hr
  unfold farCenteredMinorContribution minorExactCenteredMass at h1
  rw [pinnedArcs_eq_rationalArcSet, ←exteriorMinorTubeDomain] at h1
  unfold bothFarMinorContribution
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp h1).1,(abs_le.mp hr).1],
    by linarith only [(abs_le.mp h1).2,(abs_le.mp hr).2]⟩

/-- This implication singles out the remaining pointwise lower bound. -/
theorem frozen_floor_of_bothFarMinor_bound
    (htail : ∀ᶠ n : ℕ in atTop,Even n → -(n:ℝ)/16 ≤ bothFarMinorContribution n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hall : ∀ᶠ n : ℕ in atTop, Even n → (1/32:ℝ)*n≤corr n := by
    filter_upwards [adjustedMajor_floor,htail,bothFarMinorContribution_approx (ε:=1/32) (by norm_num)]
      with n hm ht he
    intro h
    have hw (k : ℕ) : 0 ≤ weight k := by unfold weight;split_ifs <;> positivity
    have hc : 0 ≤ corr n := sum_nonneg (fun k _ => mul_nonneg (hw k) (hw _))
    have hv := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hc
    linarith only [hm h,ht h,(abs_le.mp he).1,hv]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/32,N,by norm_num,fun X n hX hXn _ h => hN n (hX.trans hXn) h⟩

end GoldbachPartial
