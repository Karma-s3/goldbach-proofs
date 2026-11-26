import NearRootShell

namespace GoldbachPartial
open MeasureTheory
open GoldbachDeepFourth (deepTube deepPrimeWave)

/-- The radius is allowed to depend on the reduced denominator. -/
noncomputable def variableDenominatorTubes (Y R : ℕ) (ρ : ℕ → ℝ) : Set ℝ :=
  ⋃ i ∈ (Finset.Ico Y R).sigma intervalTubeNumerators, deepTube (ρ (i.1+1)) (i.1+1) i.2

def variableTubesDisjoint (Y R : ℕ) (ρ : ℕ → ℝ) : Prop :=
  (↑((Finset.Ico Y R).sigma intervalTubeNumerators) : Set (Σ _ : ℕ, ℕ)).Pairwise
    (fun i k => Disjoint (deepTube (ρ (i.1+1)) (i.1+1) i.2) (deepTube (ρ (k.1+1)) (k.1+1) k.2))

theorem measurableSet_variableDenominatorTubes (Y R : ℕ) (ρ : ℕ → ℝ) :
    MeasurableSet (variableDenominatorTubes Y R ρ) :=
  ((Finset.Ico Y R).sigma intervalTubeNumerators).measurableSet_biUnion (fun _ _ => measurableSet_Icc)

private theorem variable_row_integral (n j : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ a ∈ intervalTubeNumerators j, ∫ t in deepTube ρ (j+1) a, deepTruePrimeSignedIntegrand n t) =
      truePrimeSignedRow n (j+1) ρ := by
  classical
  symm
  unfold truePrimeSignedRow
  apply Finset.sum_bij (fun (a : (ZMod (j+1))ˣ) _ => (a : ZMod (j+1)).val)
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective (j+1) hab)
  · intro a ha
    obtain ⟨har,hac⟩ := Finset.mem_filter.mp ha
    refine ⟨ZMod.unitOfCoprime a hac, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (Finset.mem_range.mp har)]
  · intro a _
    let c : ℝ := ((a : ZMod (j+1)).val : ℝ)/(j+1:ℕ)
    change (∫ t in -ρ..ρ, deepTruePrimeSignedIntegrand n (t+c)) =
      ∫ t in Set.Icc (c-ρ) (c+ρ), deepTruePrimeSignedIntegrand n t
    rw [intervalIntegral.integral_comp_add_right, show -ρ+c = c-ρ by ring, add_comm ρ c,
      intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
private theorem variable_sum_succ {Y R : ℕ} (f : ℕ → ℂ) :
    (∑ j ∈ Finset.Ico Y R, f (j+1)) = ∑ q ∈ Finset.Ioc Y R, f q := by
  apply Finset.sum_bij (fun j _ => j+1)
  · intro j hj
    have h := Finset.mem_Ico.mp hj
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro j _ k _ h
    omega
  · intro q hq
    have h := Finset.mem_Ioc.mp hq
    exact ⟨q-1,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro _ _
    rfl

private theorem variable_integrand_cont (n : ℕ) : Continuous (deepTruePrimeSignedIntegrand n) := by
  unfold deepTruePrimeSignedIntegrand deepPrimeWave GoldbachDeepFourth.ExtendedArcCoefficient.E
  fun_prop

private theorem variable_integral_split (Y R : ℕ) (ρ : ℕ → ℝ) (F : ℝ → ℂ) (hF : Continuous F)
    (hd : variableTubesDisjoint Y R ρ) :
    (∫ t in variableDenominatorTubes Y R ρ, F t) =
      ∑ i ∈ (Finset.Ico Y R).sigma intervalTubeNumerators,
        ∫ t in deepTube (ρ (i.1+1)) (i.1+1) i.2, F t :=
  integral_biUnion_finset (f:=F) (μ:=volume) ((Finset.Ico Y R).sigma intervalTubeNumerators)
    (s:=fun i => deepTube (ρ (i.1+1)) (i.1+1) i.2)
    (fun _ _ => measurableSet_Icc) hd (fun _ _ => hF.continuousOn.integrableOn_Icc)

private theorem indexed_tube_rows (n Y R : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ q ∈ Finset.Ioc Y R, 0 ≤ ρ q) :
    (∑ j ∈ Finset.Ico Y R, ∑ a ∈ intervalTubeNumerators j,
      ∫ t in deepTube (ρ (j+1)) (j+1) a, deepTruePrimeSignedIntegrand n t) =
      ∑ j ∈ Finset.Ico Y R, truePrimeSignedRow n (j+1) (ρ (j+1)) := by
  apply Finset.sum_congr rfl
  intro j hj
  exact variable_row_integral n j (ρ:=ρ (j+1))
    (hρ (j+1) (Finset.mem_Ioc.mpr ⟨Nat.lt_succ_of_le (Finset.mem_Ico.mp hj).1,(Finset.mem_Ico.mp hj).2⟩))

private theorem variable_sum_rows (n Y R : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ q ∈ Finset.Ioc Y R, 0 ≤ ρ q) :
    (∑ i ∈ (Finset.Ico Y R).sigma intervalTubeNumerators,
      ∫ t in deepTube (ρ (i.1+1)) (i.1+1) i.2, deepTruePrimeSignedIntegrand n t) =
      ∑ j ∈ Finset.Ico Y R, truePrimeSignedRow n (j+1) (ρ (j+1)) := by
  rw [Finset.sum_sigma]
  exact indexed_tube_rows n Y R ρ hρ

theorem variableDenominatorTubes_signed_integral (n Y R : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ q ∈ Finset.Ioc Y R, 0 ≤ ρ q) (hd : variableTubesDisjoint Y R ρ) :
    (∫ t in variableDenominatorTubes Y R ρ, deepTruePrimeSignedIntegrand n t) =
      ∑ j ∈ Finset.Ico Y R, truePrimeSignedRow n (j+1) (ρ (j+1)) :=
  (variable_integral_split Y R ρ _ (variable_integrand_cont n) hd).trans (variable_sum_rows n Y R ρ hρ)

theorem variableDenominatorTubes_model_bound {n Y R : ℕ} (hn : 0<n) (hY : 0<Y)
    (ρ : ℕ → ℝ) (hw : ∀ q ∈ Finset.Ioc Y R, 0 ≤ ρ q ∧ ρ q ≤ 1/2)
    (hd : variableTubesDisjoint Y R ρ) :
    ‖(∫ t in variableDenominatorTubes Y R ρ, primeSquareKernel n t) -
      ∑ j ∈ Finset.Ico Y R, primeArcSignedChange (j+1) n (ρ (j+1))‖ ≤
      ((n:ℝ)+1)*((((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*(n.divisors.card:ℝ)/Y)) := by
  let m := fun q => actualRamanujanModel n q *
    ((∫ t in -(ρ q)..ρ q, ‖dirichletGeometricKernel n t‖^2:ℝ):ℂ)
  change ‖(∫ t in variableDenominatorTubes Y R ρ, deepTruePrimeSignedIntegrand n t) - _‖ ≤ _
  rw [variableDenominatorTubes_signed_integral n Y R ρ (fun q hq => (hw q hq).1) hd,
    ← Finset.sum_sub_distrib]
  have hsum : (∑ j ∈ Finset.Ico Y R, (truePrimeSignedRow n (j+1) (ρ (j+1)) -
      primeArcSignedChange (j+1) n (ρ (j+1)))) = ∑ q ∈ Finset.Ioc Y R, m q := by
    rw [← variable_sum_succ m]
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_Ico.mp hj
    rw [truePrimeSignedRow_eq_change_add_model n (j+1) (by omega)]
    exact add_sub_cancel_left _ _
  rw [hsum]
  exact geometricModel_interval_window_bound hn hY ρ hw

end GoldbachPartial
