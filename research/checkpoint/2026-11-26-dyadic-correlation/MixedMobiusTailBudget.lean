import AllResonantMobiusReduction
import TerminalMobiusTailBudget
import PinnedMajorGeometry

namespace GoldbachPartial
open Filter MeasureTheory Pinned316.GoldbachMajorArc
open scoped Topology

/-- After the major arcs and the two rigorous high-denominator eliminations,
this is the remaining signed quantity to bound from below. -/
noncomputable def mixedMobiusTail (n : ℕ) : ℝ :=
  primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n +
    (nonresonantMobiusRemainderMass n (terminalPrimeArcCutoff n)
        (terminalPrimeArcCutoff n) (naturalTubeScale n)).re

theorem frozen_floor_from_mixed_mobius_tail
    (hsmall : Tendsto (fun n : ℕ => totalArcError n/n) atTop (𝓝 0))
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ)≤mixedMobiusTail n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hmajor := actual_floor_of_error_sublinear hsmall (c:=71/64) (by norm_num)
  suffices H : ∀ᶠ n : ℕ in atTop, Even n → (1/16:ℝ)*n≤corr n by
    obtain ⟨N,hN⟩ := eventually_atTop.mp H
    exact ⟨1/16,N,by norm_num,fun X n hX hXn _ he => hN n (hX.trans hXn) he⟩
  filter_upwards [htail,terminalMobius_kernel_budget,
    largeMobiusHighMass_remainder_eventually_small (ε:=1/64) (by norm_num),hmajor,
    highNaturalPrimeTubes_geometry,highNaturalPrimeTubes_outside_pinned_major]
    with n ht he₁ he₂ hm hg ho
  intro hev
  let V := highNaturalPrimeTubes n
  let R := terminalPrimeArcCutoff n
  let G := ∫t in V,largeMobiusKernel n R t
  let S := ∫t in V,primeSquareKernel n t
  let B := nonresonantMobiusRemainderMass n R R (naturalTubeScale n)
  have hm' := hm hev
  rw [pinnedMajorContribution_real] at hm'
  have hmA : MeasurableSet (arcs n) := ExtendedArcCoefficient.measurable_rational_arcs (medDeskQ n) n
  have hmV : MeasurableSet V := naturalTubeUnion_measurable ..
  have hsum := corr_eq_primeArcMass n _ hmA
  rw [primeArcMass_partition hmV hmA.compl ho n,primeArcMass_eq_setIntegral_re_of_subset_Icc n hmV hg.1] at hsum
  change corr n=primeArcMass (arcs n) n+(S.re+primeArcMass ((arcs n)ᶜ \ V) n) at hsum
  have herr₁ : |(S-G).re|≤(n:ℝ)/32 := (Complex.abs_re_le_norm _).trans he₁
  have herr₂ : |(G-B).re|≤(1/64:ℝ)*n := (Complex.abs_re_le_norm _).trans (he₂ R)
  have hlo := ht hev
  change -(n:ℝ)≤primeArcMass ((arcs n)ᶜ \ V) n + B.re at hlo
  rw [Complex.sub_re] at herr₁ herr₂
  linarith only [hm',hsum,hlo,(abs_le.mp herr₁).1,(abs_le.mp herr₂).1]

end GoldbachPartial