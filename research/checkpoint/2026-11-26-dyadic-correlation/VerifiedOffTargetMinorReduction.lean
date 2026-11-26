import VerifiedCorrectedMajorFloor
import VerifiedMedDeskZeroMode
import SmallCutoffExactWeightCentering
import ExactWeightedKernelZeroMode
import HighNaturalHalfVolume
import VerifiedCenteredArithmeticTail

namespace GoldbachPartial
open Finset Filter MeasureTheory Pinned316.GoldbachMajorArc

/-- The two remaining signed integrals. Within the high-denominator arcs, only
pairs of frequencies with k+l different from n contribute. -/
noncomputable def offTargetMinorContribution (n : ℕ) : ℝ :=
  primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n +
    (∫ t in highNaturalPrimeTubes n, exactWeightedOffTarget n (medDeskQ n) t).re

noncomputable def adjustedMajorContribution (n : ℕ) : ℝ :=
  (majorContribution n).re - volume.real (highNaturalPrimeTubes n)*
    (((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n (medDeskQ n))

theorem offTargetMinorContribution_approx {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |(1-volume.real (highNaturalPrimeTubes n))*corr n -
      adjustedMajorContribution n-offTargetMinorContribution n|≤ε*(n:ℝ) := by
  have hw := medDeskQ_exactWeight_kernel_small (ε:=ε/2) (by positivity)
  have hz := exactWeightedZeroMode_medDesk_approx_corr (ε:=ε/2) (by positivity)
  filter_upwards [hw,hz,highNaturalPrimeTubes_geometry,highNaturalPrimeTubes_outside_pinned_major,
    high_tube_volume_eventually_half] with n hW hZ hg hO hV
  let V := highNaturalPrimeTubes n
  let P := medDeskQ n
  let v := volume.real V
  let D := primeArcMass ((arcs n)ᶜ \ V) n
  let A := ∫t in V,primeSquareKernel n t
  let B := ∫t in V,exactWeightedOffTarget n P t
  let z := exactWeightedZeroMode n P
  let S : ℝ := ((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n P
  have hmA : MeasurableSet (arcs n) := ExtendedArcCoefficient.measurable_rational_arcs (medDeskQ n) n
  have hmV : MeasurableSet V := naturalTubeUnion_measurable ..
  have hsum := corr_eq_primeArcMass n _ hmA
  rw [primeArcMass_partition hmV hmA.compl hO n,primeArcMass_eq_setIntegral_re_of_subset_Icc n hmV hg.1] at hsum
  change corr n=primeArcMass (arcs n) n+(A.re+D) at hsum
  rw [←pinnedMajorContribution_real] at hsum
  rw [exactWeighted_kernel_setIntegral n P hg.1] at hW
  have hA : |A.re-(B.re+v*z)|≤(ε/2)*n :=
    (Complex.abs_re_le_norm (A-(B+(v*z:ℝ)))).trans hW
  have hv : 0≤v := measureReal_nonneg
  have hv' : v≤1 := hV.trans (by norm_num)
  have hB : |v*(z-(corr n-S))|≤(ε/2)*n := by
    rw [abs_mul,abs_of_nonneg hv]
    exact (mul_le_of_le_one_left (abs_nonneg _) hv').trans hZ
  change |(1-v)*corr n-((majorContribution n).re-v*S)-(D+B.re)|≤ε*n
  exact abs_le.mpr ⟨by linarith only [hsum,(abs_le.mp hA).1,(abs_le.mp hB).1],
    by linarith only [hsum,(abs_le.mp hA).2,(abs_le.mp hB).2]⟩

theorem adjustedMajor_floor :
    ∀ᶠ n : ℕ in atTop,Even n → (n:ℝ)/8≤adjustedMajorContribution n := by
  filter_upwards [correctedMajorContribution_floor] with n hn
  intro he
  unfold adjustedMajorContribution
  rw [pinnedMajorContribution_real,pinnedArcs_eq_rationalArcSet]
  simpa only [mul_assoc] using hn he

/-- A lower bound on just the displayed signed integrals suffices for the
original statement, after all arithmetic and zero-mode inputs have been proved. -/
theorem frozen_floor_of_offTargetMinor_bound
    (htail : ∀ᶠ n : ℕ in atTop,Even n → -(n:ℝ)/16≤offTargetMinorContribution n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hall : ∀ᶠ n : ℕ in atTop, Even n → (1/32:ℝ)*n≤corr n := by
    filter_upwards [adjustedMajor_floor,htail,offTargetMinorContribution_approx (ε:=1/32) (by norm_num)]
      with n hm ht he
    intro h
    have hw (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity
    have hc : 0≤corr n := sum_nonneg (fun k _ => mul_nonneg (hw k) (hw _))
    have hv := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hc
    linarith only [hm h,ht h,(abs_le.mp he).1,hv]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/32,N,by norm_num,fun X n hX hXn _ h => hN n (hX.trans hXn) h⟩

end GoldbachPartial