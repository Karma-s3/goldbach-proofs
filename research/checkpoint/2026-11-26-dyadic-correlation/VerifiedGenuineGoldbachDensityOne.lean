import VerifiedGoldbachExceptionTransfer
import VerifiedUniformPrimeMinorBound

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

/-- The true weighted prime-pair correlation exceeds m/36 at every even
frequency in [X,2X), apart from at most K X / log X exceptions. -/
theorem genuine_goldbach_dyadic_exceptional_bound :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop,
      ((dyadicGoldbachExceptions X).card:ℝ) ≤ K*X/Real.log X :=
  goldbach_exception_bound_of_minor 64 (by decide) 100000 (by norm_num) centralPrimeWave_uniform_minor64

theorem genuine_goldbach_dyadic_exceptional_density_zero :
    Tendsto (fun X : ℕ => ((dyadicGoldbachExceptions X).card:ℝ)/(X:ℝ)) atTop (𝓝 0) := by
  obtain ⟨K,_,hK⟩ := genuine_goldbach_dyadic_exceptional_bound
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun X : ℕ => K/Real.log (X:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  apply squeeze_zero' (Eventually.of_forall (fun X => by positivity)) _ hlim
  filter_upwards [hK,eventually_ge_atTop (1:ℕ)] with X h hx
  have hp : (0:ℝ)<X := by exact_mod_cast hx
  apply (div_le_div_of_nonneg_right h hp.le).trans_eq
  field_simp

end GoldbachPartial
