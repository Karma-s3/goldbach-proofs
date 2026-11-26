import PinnedMajorModelFloor
import LargeDivisorPrimeMass

namespace GoldbachPartial
open MeasureTheory Set Filter
open scoped Topology
open Pinned316.GoldbachMajorArc

theorem pinnedArcs_eq_rationalArcSet (n:ℕ) : arcs n=rationalArcSet (medDeskQ n) n := rfl

theorem pinnedMajorContribution_real (n:ℕ) :
    (majorContribution n).re=primeArcMass (arcs n) n := rfl

theorem pinnedCutoff_eventually_separated : ∀ᶠ n:ℕ in atTop,2*(cutoff n)^2<n := by
  filter_upwards [eventually_core_cutoffs] with n hn
  have hQD : medDeskQ n≤medDeskD n := hn.1.trans (hn.2.1.trans hn.2.2.1)
  change 2*(medDeskQ n)^2<n
  exact (show 2*(medDeskQ n)^2≤2*medDeskQ n*medDeskD n by rw [sq,←mul_assoc]; gcongr).trans_lt hn.2.2.2

theorem highNaturalPrimeTubes_outside_pinned_major :
    ∀ᶠ n:ℕ in atTop,highNaturalPrimeTubes n ⊆ (arcs n)ᶜ := by
  filter_upwards [highNaturalPrimeTubes_geometry,eventually_core_cutoffs] with n hg hc
  intro t ht hmaj
  have hout : t∉coreArcBand n (medDeskQ n) 0 (medDeskD n) := (hg.2 ht).1.1.1
  apply hout
  obtain ⟨q,a,hq,hQ,ha,hcop,hw⟩ := hmaj
  have hQD : medDeskQ n≤medDeskD n := hc.1.trans (hc.2.1.trans hc.2.2.1)
  exact ⟨q,a,hq,hQ.trans hQD,ha,hcop,hw⟩

/-- A signed lower bound on the remaining minor arcs and on the large-divisor wave
on the high-denominator tubes suffices for the frozen dyadic prime-correlation floor. -/
theorem pinned_dyadic_floor_of_largeMobius_budget (D:ℕ→ℕ)
    (herr : ∀ {n : ℕ}, 2*(cutoff n)^2<n →
      ‖majorContribution n-modeledContribution n‖ ≤ totalArcError n)
    (hsmall : Tendsto (fun n : ℕ => totalArcError n/n) atTop (𝓝 0))
    (hclose : ∀ᶠ n:ℕ in atTop,
      ‖(∫t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t)‖≤(n:ℝ)/32)
    (htail : ∀ᶠ n:ℕ in atTop,Even n→ -(n:ℝ) ≤
      primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n+
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t).re) :
    ∃ N : ℕ, ∀ X n:ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      (1/16:ℝ)*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hmajor := actual_floor_of_published_estimates pinnedCutoff_eventually_separated herr hsmall (c:=35/32) (by norm_num)
  suffices H : ∀ᶠ n:ℕ in atTop,Even n→(1/16:ℝ)*n≤corr n by
    obtain ⟨N,hN⟩ := eventually_atTop.mp H
    exact ⟨N,fun X n hX hXn _ hev => hN n (hX.trans hXn) hev⟩
  filter_upwards [hclose,htail,hmajor,highNaturalPrimeTubes_geometry,highNaturalPrimeTubes_outside_pinned_major] with n hcl htail' hma hg ho
  intro hev
  have hm : MeasurableSet (arcs n) := ExtendedArcCoefficient.measurable_rational_arcs (medDeskQ n) n
  have hv : MeasurableSet (highNaturalPrimeTubes n) := naturalTubeUnion_measurable ..
  have hsum := corr_eq_primeArcMass n _ hm
  rw [primeArcMass_partition hv hm.compl ho n,primeArcMass_eq_setIntegral_re_of_subset_Icc n hv hg.1] at hsum
  have hd := Complex.abs_re_le_norm ((∫t in highNaturalPrimeTubes n,primeSquareKernel n t)-
    (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t))
  rw [Complex.sub_re] at hd
  have hma' := hma hev
  rw [pinnedMajorContribution_real] at hma'
  linarith only [hsum,hma',htail' hev,(abs_le.mp (hd.trans hcl)).1]

theorem pinned_largeMobius_budget_of_sublinear (D:ℕ→ℕ)
    (h : Tendsto (fun n:ℕ=>‖(∫t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t)‖/(n:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n:ℕ in atTop, ‖(∫t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t)‖≤(n:ℝ)/32 := by
  filter_upwards [h.eventually_lt_const (by norm_num : (0:ℝ)<1/32),eventually_ge_atTop (1:ℕ)] with n hn hpos
  have hn' : (0:ℝ)<n := by exact_mod_cast hpos
  have h' := (div_lt_iff₀ hn').mp hn
  linarith

end GoldbachPartial