import VerifiedFilteredMinorTail
import NonresonantZeroFrequency
import LargeDivisorZeroDecomposition
import CenteredDistantPrimeMass

namespace GoldbachPartial
open Finset Filter MeasureTheory Pinned316.GoldbachMajorArc
open scoped Topology

/-- All retained square frequencies other than zero. -/
noncomputable def nonresonantDistantSquare (n D R : ℕ) : ℂ :=
  nonresonantSquareModeMass n D R (naturalTubeScale n)
    ((Icc (-(n:ℤ)) (n:ℤ) \ shortNonzeroModes (nonresonantShortCutoff n)).erase 0)

theorem retainedSquare_split_zero (n D R : ℕ) :
    nonresonantSquareRetained n D R = nonresonantDistantSquare n D R +
      nonresonantSquareModeMass n D R (naturalTubeScale n) {0} := by
  let I := Icc (-(n:ℤ)) (n:ℤ) \ shortNonzeroModes (nonresonantShortCutoff n)
  have hz : 0∈I := by simp [I,shortNonzeroModes]
  unfold nonresonantSquareRetained nonresonantDistantSquare nonresonantSquareModeMass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [sum_singleton]
  exact (sum_erase_add I _ hz).symm

private theorem smallPrimePower_zero_error {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,4*Real.sqrt n*(Real.log n)^2≤ε*(n:ℝ) := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^2/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [h.eventually_lt_const (by positivity : (0:ℝ)<ε/4),
    eventually_ge_atTop (1:ℕ)] with n hu hn
  have hS : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h' := (div_lt_iff₀ hS).mp hu
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith only [mul_le_mul_of_nonneg_left h'.le hS.le,
    congrArg (fun x : ℝ => ε*x) hsq]

/-- The high-arc square contains only distant nonzero frequencies. Its diagonal
has been replaced by an explicitly signed correction involving small divisors. -/
noncomputable def centeredMobiusMinorTail (n : ℕ) : ℝ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let V := highNaturalPrimeTubes n
  primeArcMass ((arcs n)ᶜ \ V) n +
    (nonresonantDistantSquare n R R + trueMixedFrequencyBand n R R Q (mixedInteriorFrequencies n)).re +
    volume.real V*smallDivisorZeroCorrection n R

theorem centeredMobiusMinorTail_error {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,|(1-volume.real (highNaturalPrimeTubes n))*corr n -
      (majorContribution n).re-centeredMobiusMinorTail n|≤ε*(n:ℝ) := by
  filter_upwards [filteredMinorArcTail_approx (ε:=ε/3) (by positivity),
    zeroFrequency_mass_common_small (ε:=ε/3) (by positivity),
    smallPrimePower_zero_error (ε:=ε/3) (by positivity),eventually_ge_atTop (1:ℕ)] with n hF hZ hP hn
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let v := volume.real (highNaturalPrimeTubes n)
  let Z := nonresonantSquareModeMass n R R Q {0}
  let a := nonresonantSquareModeCoefficient n R 0 0
  let b := smallDivisorZeroCorrection n R
  have hz : |Z.re-v*a|≤(ε/3)*n := (Complex.abs_re_le_norm (Z-(v*a:ℝ))).trans (hZ R R)
  have hv : 0≤v := measureReal_nonneg
  have hv' : v≤1 := (high_tube_volume_upper hn).trans (by norm_num)
  have hp : |v*(a-(corr n+b))|≤(ε/3)*n := by
    rw [abs_mul,abs_of_nonneg hv]
    exact (mul_le_of_le_one_left (abs_nonneg _) hv').trans ((largeDivisor_zero_sub_corr_error hn R).trans hP)
  have he : filteredMinorArcTail n - centeredMobiusMinorTail n = Z.re - v*b := by
    unfold filteredMinorArcTail centeredMobiusMinorTail
    dsimp only
    rw [retainedSquare_split_zero]
    simp only [Complex.add_re]
    dsimp only [Z,v,R,Q,b];ring
  apply abs_le.mpr
  dsimp only [v] at hz hp he
  constructor <;> linarith only [(abs_le.mp hF).1,(abs_le.mp hF).2,(abs_le.mp hz).1,
    (abs_le.mp hz).2,(abs_le.mp hp).1,(abs_le.mp hp).2,he]

/-- A signed bound on the remaining tail gives every slope below 3/22. -/
theorem dyadic_floor_of_centered_mobius_minor_tail {c : ℝ} (hc : c<3/22)
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ)≤centeredMobiusMinorTail n) :
    ∃ N : ℕ, ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  let d := 11/12*c
  let δ : ℝ := (1/8-d)/2
  have hδ : 0<δ := by dsimp [δ,d];linarith
  have hm := GoldbachMajorArc.verified_major_floor_below_nine_eighths (9/8-δ) (by linarith)
  have hall : ∀ᶠ n : ℕ in atTop,Even n → c*n≤corr n := by
    filter_upwards [hm,htail,centeredMobiusMinorTail_error hδ,highNaturalPrimeTubes_volume_lower]
      with n hM hT hE hv
    intro hn
    have hm' : (9/8-δ)*(n:ℝ)≤(majorContribution n).re := hM hn
    have hpos (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity
    have hp : 0≤corr n := sum_nonneg (fun k _ => mul_nonneg (hpos k) (hpos _))
    have hc' := mul_le_mul_of_nonneg_right hv hp
    have hb : d*(n:ℝ)≤(1-volume.real (highNaturalPrimeTubes n))*corr n := by
      have hd : d = 9/8-δ-1-δ := by dsimp [δ];ring
      rw [hd]
      linarith only [hm',hT hn,(abs_le.mp hE).1]
    dsimp only [d] at hb
    linarith only [hb,hc']
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨N,fun X n hX hXn _ he => hN n (hX.trans hXn) he⟩

end GoldbachPartial