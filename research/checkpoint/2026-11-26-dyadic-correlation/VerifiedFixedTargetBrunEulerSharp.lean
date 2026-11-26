import VerifiedRegularPrimeEulerSharp
import FixedTargetBrunProgressions
namespace GoldbachPartial
open Finset
theorem fixedTargetBrunPrimes_eq_thinRegularPrimes (n z : ℕ) :
    fixedTargetBrunPrimes n z = thinRegularPrimes n z := by
  ext p
  simp only [fixedTargetBrunPrimes,thinRegularPrimes,mem_filter,mem_Icc,mem_range_succ_iff]
  constructor
  · rintro ⟨hz,hp,hd⟩
    exact ⟨⟨⟨hp.two_le,hz⟩,hp⟩,hd⟩
  · rintro ⟨⟨⟨_,hz⟩,hp⟩,hd⟩
    exact ⟨hz,hp,hd⟩

theorem fixedTarget_brunEuler_singular_upper (n z : ℕ) (hn : 0<n) (hz : 0<z) :
    (∏p∈fixedTargetBrunPrimes n z,(1-brunEulerWeight p)) ≤
      ((n:ℝ)/n.totient)/Real.log ((z:ℝ)+1) := by
  rw [fixedTargetBrunPrimes_eq_thinRegularPrimes]
  exact regularPrime_euler_singular_upper n z hn hz
end GoldbachPartial