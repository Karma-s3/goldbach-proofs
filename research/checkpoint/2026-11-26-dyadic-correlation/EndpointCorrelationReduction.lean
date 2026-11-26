import OneSidedArcDeletion
import QuarterEndpointGeometry
import QuarterEndpointWing

namespace GoldbachPartial
open Filter MeasureTheory
open scoped Topology

theorem measurableSet_quarterEndpointStrips (n : ℕ) : MeasurableSet (quarterEndpointStrips n) :=
  measurableSet_Ioc.union measurableSet_Ico

/-- A sufficient uniform lower bound after removing all near-root tubes and
the two enlarged arcs at the endpoints of the unit interval. -/
theorem dyadic_floor_after_near_root_and_endpoints
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (hψ : grhAllUniform)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      (((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ nearRootTubes n) \ quarterEndpointStrips n) n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  apply dyadic_floor_after_near_root_and_one_sided_arcs hm h₁ h₂ h₃ major hψ
    quarterEndpointStrips measurableSet_quarterEndpointStrips
    (quarterEndpointStrips_geometry.mono fun _ h => h.2.2) _ rest
  exact quarterEndpointStrips_mass_floor hψ

end GoldbachPartial
