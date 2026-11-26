import VerifiedOffTargetMinorReduction
import MinorArcExactWeightCentering
import VerifiedExactWeightedShortTube

namespace GoldbachPartial
open Finset Filter MeasureTheory Pinned316.GoldbachMajorArc

noncomputable def farCenteredMinorContribution (n : ℕ) : ℝ :=
  minorExactCenteredMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n +
  (∫ t in highNaturalPrimeTubes n,
    exactWeightedFarOffTarget n (medDeskQ n) (exactWeightedShortCutoff n) t).re

theorem farCenteredMinorContribution_approx {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |(1-volume.real (highNaturalPrimeTubes n))*corr n -
      adjustedMajorContribution n-farCenteredMinorContribution n|≤ε*(n:ℝ) := by
  have hp : 0<ε/3 := by positivity
  filter_upwards [offTargetMinorContribution_approx hp,
    primeArcMass_originalMinorOutsideHigh_centered hp,
    exactWeighted_high_short_eventually hp] with n h1 h2 h3
  rw [←pinnedArcs_eq_rationalArcSet] at h2
  have hre := (Complex.abs_re_le_norm _).trans h3
  rw [Complex.sub_re] at hre
  unfold offTargetMinorContribution at h1
  unfold farCenteredMinorContribution
  dsimp only at h2
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp h1).1,(abs_le.mp h2).1,(abs_le.mp hre).1],
    by linarith only [(abs_le.mp h1).2,(abs_le.mp h2).2,(abs_le.mp hre).2]⟩

theorem frozen_floor_of_farCenteredMinor_bound
    (htail : ∀ᶠ n : ℕ in atTop,Even n → -(n:ℝ)/16≤farCenteredMinorContribution n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hall : ∀ᶠ n : ℕ in atTop, Even n → (1/32:ℝ)*n≤corr n := by
    filter_upwards [adjustedMajor_floor,htail,farCenteredMinorContribution_approx (ε:=1/32) (by norm_num)]
      with n hm ht he
    intro h
    have hw (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity
    have hc : 0≤corr n := sum_nonneg (fun k _ => mul_nonneg (hw k) (hw _))
    have hv := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hc
    linarith only [hm h,ht h,(abs_le.mp he).1,hv]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/32,N,by norm_num,fun X n hX hXn _ h => hN n (hX.trans hXn) h⟩

end GoldbachPartial