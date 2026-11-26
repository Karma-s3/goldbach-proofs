import OddWheelHighArc

namespace GoldbachPartial

noncomputable def fejerWave (M : ℕ) (x : ℝ) : ℝ :=
  ‖dirichletGeometricKernel (M-1) x‖^2/(M:ℝ)

noncomputable def dyadicFejerEnvelope (Q : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 Q+1),fejerWave (2^j) x

end GoldbachPartial