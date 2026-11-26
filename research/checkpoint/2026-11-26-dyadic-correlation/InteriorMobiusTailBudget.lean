import InteriorMixedMobiusTail

namespace GoldbachPartial
open Filter MeasureTheory Pinned316.GoldbachMajorArc
open scoped Topology

private theorem terminal_full_kernel_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
      (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (terminalPrimeArcCutoff n) t)‖≤ ε*n := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop
        ((1500000/ε)^2)
  filter_upwards [fullRange_largeMobius_high_error,hlog] with n h hl
  change (1500000/ε)^2≤Real.log (n:ℝ) at hl
  have hL : (0:ℝ)<1+Real.log (n:ℝ) := by linarith [Real.log_natCast_nonneg n]
  have hS : 1500000/ε≤Real.sqrt (1+Real.log (n:ℝ)) := Real.le_sqrt_of_sq_le (by linarith only [hl])
  apply h.trans
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hL)]
  have h' := (div_le_iff₀ hε).mp hS
  linarith only [mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg (α:=ℝ) n)]

/-- A pointwise approximation for every sufficiently large target, with all endpoints of the
true linear-in-resonance term already removed. -/
theorem corr_sub_major_interior_eventually_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |corr n-(majorContribution n).re-interiorMobiusTail n|≤ε*(n:ℝ) := by
  filter_upwards [terminal_full_kernel_small (ε:=ε/3) (by positivity),
    largeMobiusHighMass_remainder_eventually_small (ε:=ε/3) (by positivity),
    interiorMobiusTail_small (ε:=ε/3) (by positivity),
    highNaturalPrimeTubes_geometry,highNaturalPrimeTubes_outside_pinned_major]
    with n hG hM hI hg ho
  let V := highNaturalPrimeTubes n
  let R := terminalPrimeArcCutoff n
  let G := ∫t in V,largeMobiusKernel n R t
  let S := ∫t in V,primeSquareKernel n t
  let M := nonresonantMobiusRemainderMass n R R (naturalTubeScale n)
  have hmA : MeasurableSet (arcs n) := ExtendedArcCoefficient.measurable_rational_arcs (medDeskQ n) n
  have hmV : MeasurableSet V := naturalTubeUnion_measurable ..
  have hsum := corr_eq_primeArcMass n _ hmA
  rw [primeArcMass_partition hmV hmA.compl ho n,primeArcMass_eq_setIntegral_re_of_subset_Icc n hmV hg.1] at hsum
  change corr n=primeArcMass (arcs n) n+(S.re+primeArcMass ((arcs n)ᶜ \ V) n) at hsum
  have h₁ : |(S-G).re|≤(ε/3)*n := (Complex.abs_re_le_norm _).trans hG
  have h₂ : |(G-M).re|≤(ε/3)*n := (Complex.abs_re_le_norm _).trans (hM R)
  rw [Complex.sub_re] at h₁ h₂
  change |interiorMobiusTail n-(primeArcMass ((arcs n)ᶜ \ V) n+M.re)|≤(ε/3)*n at hI
  rw [pinnedMajorContribution_real]
  apply abs_le.mpr
  constructor
  · linarith only [hsum,(abs_le.mp h₁).1,(abs_le.mp h₂).1,(abs_le.mp hI).2]
  · linarith only [hsum,(abs_le.mp h₁).2,(abs_le.mp h₂).2,(abs_le.mp hI).1]

theorem dyadic_floor_from_interior_major_budget
    (major : ∀ᶠ n : ℕ in atTop, Even n → (35/32:ℝ)*(n:ℝ) ≤ (majorContribution n).re)
    (tail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ)≤ interiorMobiusTail n) :
    ∃ N : ℕ, ∀ X n:ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      (1/16:ℝ)*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  suffices H : ∀ᶠ n : ℕ in atTop, Even n → (1/16:ℝ)*n≤corr n by
    obtain ⟨N,hN⟩ := eventually_atTop.mp H
    exact ⟨N,fun X n hX hXn _ he => hN n (hX.trans hXn) he⟩
  filter_upwards [major,tail,corr_sub_major_interior_eventually_small (ε:=1/32) (by norm_num)] with n hm ht he
  intro hev
  linarith only [hm hev,ht hev,(abs_le.mp he).1]

end GoldbachPartial