import VerifiedCenteredMobiusMinorTail
import SmallDivisorCompletedSquare
import TerminalRamanujanSquareTail

namespace GoldbachPartial
open Finset Filter MeasureTheory Pinned316.GoldbachMajorArc

/-- The completed square is needed only up to n^(1/3). The remaining
arithmetic progression error involves one von Mangoldt factor. -/
noncomputable def centeredArithmeticMinorTail (n : ℕ) : ℝ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let V := highNaturalPrimeTubes n
  primeArcMass ((arcs n)ᶜ \ V) n +
    (nonresonantDistantSquare n R R + trueMixedFrequencyBand n R R Q (mixedInteriorFrequencies n)).re +
    volume.real V*(((n-1:ℕ):ℝ)*(finiteRamanujanSquareDefect n R (medDeskD n)-
      finiteRamanujanSingularSum n R) - 2*weightedPrimeProgressionError n R)

theorem centeredArithmeticMinorTail_approx {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,|(1-volume.real (highNaturalPrimeTubes n))*corr n -
      (majorContribution n).re-centeredArithmeticMinorTail n|≤ε*(n:ℝ) := by
  filter_upwards [centeredMobiusMinorTail_error (ε:=ε/3) (by positivity),
    ramanujan_square_terminal_tail_small (ε:=ε/3) (by positivity),
    crtSmallEndpointError_terminal_small (ε:=ε/3) (by positivity),
    squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ)] with n he htail hcrt hg hn
  let R := terminalPrimeArcCutoff n
  let Y := medDeskD n
  let v := volume.real (highNaturalPrimeTubes n)
  let x : ℝ := ((n-1:ℕ):ℝ)
  have hx : x≤(n:ℝ) := by dsimp only [x]; exact_mod_cast Nat.sub_le n 1
  have hpos : 0≤x := by dsimp only [x]; positivity
  have hv : 0≤v := measureReal_nonneg
  have hv' : v≤1 := (high_tube_volume_upper hn).trans (by norm_num)
  let f := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)*
    (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2
  have hu : Icc 1 R = Ioc Y R ∪ Icc 1 Y := by
    have hYR : Y≤R := hg.2.1
    ext d;simp only [mem_union,mem_Icc,mem_Ioc];omega
  have hd : Disjoint (Ioc Y R) (Icc 1 Y) := by
    apply disjoint_left.mpr
    intro d ha hb
    exact (mem_Ioc.mp ha).1.not_ge (mem_Icc.mp hb).2
  have hh : |finiteRamanujanSquareDefect n R R-finiteRamanujanSquareDefect n R Y|≤ε/3 := by
    change |(∑ r∈Icc 1 R,f r)-(∑ r∈Icc 1 Y,f r)|≤_
    rw [hu,sum_union hd,add_sub_cancel_right]
    exact (abs_sum_le_sum_abs ..).trans htail
  let A := finiteRamanujanSquareDefect n R R - finiteRamanujanSquareDefect n R Y
  have hA : |x*A| ≤ (ε/3)*n := by
    rw [abs_mul,abs_of_nonneg hpos,mul_comm]
    exact mul_le_mul hh hx hpos (by positivity)
  have hc : |v*(x*A+crtSmallEndpointError n R)| ≤ 2*((ε/3)*n) := by
    rw [abs_mul,abs_of_nonneg hv]
    apply (mul_le_of_le_one_left (abs_nonneg _) hv').trans
    linarith only [abs_add_le (x*A) (crtSmallEndpointError n R),hA,hcrt]
  have hid : centeredMobiusMinorTail n-centeredArithmeticMinorTail n =
      v*(x*A+crtSmallEndpointError n R) := by
    unfold centeredMobiusMinorTail centeredArithmeticMinorTail
    dsimp only
    rw [smallDivisorZeroCorrection_completed_square]
    dsimp only [v,x,A,R,Y];ring
  rw [←hid] at hc
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp he).1,(abs_le.mp he).2,(abs_le.mp hc).1,(abs_le.mp hc).2]

theorem frozen_floor_of_centered_arithmetic_tail
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ) ≤ centeredArithmeticMinorTail n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hm := GoldbachMajorArc.verified_major_floor_below_nine_eighths (35/32) (by norm_num)
  have hall : ∀ᶠ n : ℕ in atTop,Even n → (1/16:ℝ)*n≤corr n := by
    filter_upwards [htail,hm,centeredArithmeticMinorTail_approx (ε:=1/32) (by norm_num)] with n ht hM he
    intro hn
    have hm' : (35/32:ℝ)*(n:ℝ)≤(majorContribution n).re := hM hn
    have hp (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity
    have hcorr : 0≤corr n := sum_nonneg (fun k _ => mul_nonneg (hp k) (hp _))
    have hvol := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hcorr
    linarith only [hm',ht hn,(abs_le.mp he).1,hvol]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/16,N,by norm_num,fun X n hX hXn _ he => hN n (hX.trans hXn) he⟩

end GoldbachPartial