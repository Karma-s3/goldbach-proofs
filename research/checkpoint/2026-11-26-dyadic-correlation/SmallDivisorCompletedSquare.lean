import TruncatedRamanujanMixed
import SmallDivisorCRTDiscrepancy
import RamanujanSquareDenominatorTail

namespace GoldbachPartial
open Finset Filter

noncomputable def finiteRamanujanSingularSum (n R : ℕ) : ℝ :=
  ∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2

noncomputable def finiteRamanujanSquareDefect (n R Y : ℕ) : ℝ :=
  ∑ r∈Icc 1 Y,(dyadicRamanujanDivisor n r:ℝ)*
    (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2

noncomputable def weightedPrimeProgressionError (n R : ℕ) : ℝ :=
  ∑ d∈Icc 1 R,crtLambdaCoefficient d*primeSmallProgressionError n d

theorem smallDivisorZeroCorrection_completed_square (n R : ℕ) :
    smallDivisorZeroCorrection n R =
      ((n-1:ℕ):ℝ)*(finiteRamanujanSquareDefect n R R-finiteRamanujanSingularSum n R)
        -2*weightedPrimeProgressionError n R + crtSmallEndpointError n R := by
  let I := Icc 1 R
  let c := fun r => (dyadicRamanujanDivisor n r:ℝ)
  let h := fun r => (ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ)
  let H := crtRamanujanTruncation R
  have hid : (∑ r∈I,c r*(H r)^2)-2*(∑ r∈I,c r*h r*H r) =
      (∑ r∈I,c r*(H r-h r)^2) - (∑ r∈I,c r*(h r)^2) := by
    rw [mul_sum,←sum_sub_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    ring
  unfold smallDivisorZeroCorrection
  rw [truncatedLambda_self_ramanujan,truncatedLambda_mixed_ramanujan]
  let X : ℝ := ((n-1:ℕ):ℝ)
  change X*(∑ r∈I,c r*(H r)^2) + crtSmallEndpointError n R -
    2*(X*(∑ r∈I,c r*h r*H r)+weightedPrimeProgressionError n R) =
    X*((∑ r∈I,c r*(H r-h r)^2) - ∑ r∈I,c r*(h r)^2) -
      2*weightedPrimeProgressionError n R + crtSmallEndpointError n R
  rw [←hid];ring

/-- An absolute estimate for the part of the completed square coming from
large denominators. It is uniform in the target n. -/
theorem finiteRamanujanSquareDefect_sub_bound (n Y R : ℕ) (hn : 0<n) (hY : 0<Y) (hYR : Y≤R) :
    |finiteRamanujanSquareDefect n R R-finiteRamanujanSquareDefect n R Y| ≤
      (ramanujanSquareScale R)^2*(2*(n.divisors.card:ℝ)/Y) := by
  let f := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)*
    (crtRamanujanTruncation R r-(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ))^2
  have hu : Icc 1 R = Ioc Y R ∪ Icc 1 Y := by
    ext d
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hd : Disjoint (Ioc Y R) (Icc 1 Y) := by
    apply disjoint_left.mpr
    intro d he hf
    exact (mem_Ioc.mp he).1.not_ge (mem_Icc.mp hf).2
  change |(∑ r∈Icc 1 R,f r)-(∑ r∈Icc 1 Y,f r)|≤_
  rw [hu,sum_union hd,add_sub_cancel_right]
  exact (abs_sum_le_sum_abs ..).trans (ramanujan_square_large_denominators n Y R hn hY)

end GoldbachPartial