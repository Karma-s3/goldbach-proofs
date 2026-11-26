import LogFourCorrelationReduction

namespace GoldbachPartial
open Set

noncomputable def halfPeriodWings (n : ℕ) : Set ℝ :=
  let a := (medDeskQ n : ℝ)/n
  let b := (n:ℝ)^(1/4:ℝ)/n
  Ioc (1/2+a) (1/2+b) ∪ Ico (1/2-b) (1/2-a)

theorem measurableSet_halfPeriodWings (n : ℕ) : MeasurableSet (halfPeriodWings n) :=
  measurableSet_Ioc.union measurableSet_Ico

end GoldbachPartial
