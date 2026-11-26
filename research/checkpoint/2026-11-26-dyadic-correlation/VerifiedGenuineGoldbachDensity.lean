import VerifiedTotientFourthMoment
import VerifiedResidueWitnessCount
import VerifiedGoldbachUpperSieve
import VerifiedGenuineDyadicFirstMoment

namespace GoldbachPartial
open Finset Filter
open scoped Classical

noncomputable def dyadicGoldbachWitnesses (X : ℕ) : Finset ℕ :=
  ((Ico X (2*X)).filter Even).filter (fun n => (n:ℝ)/36 ≤ corr n)

/-- The total pair mass and a pointwise upper sieve give a positive proportion
of genuine even Goldbach coefficients above a linear threshold. -/
theorem dyadic_witnesses_of_first_moment {C : ℝ} (hC : 0<C)
    (hupper : ∀ᶠ n : ℕ in atTop, Even n → corr n ≤ C*n*((n:ℝ)/n.totient)^2)
    (hfirst : ∀ᶠ X : ℕ in atTop, (X:ℝ)^2/9 ≤ ∑ n ∈ (Ico X (2*X)).filter Even,corr n) :
    ∀ᶠ X : ℕ in atTop,
      (X:ℝ)/(2592*C^2*Real.exp 30) ≤ ((dyadicGoldbachWitnesses X).card:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp hupper
  filter_upwards [eventually_ge_atTop T,eventually_ge_atTop (1:ℕ),hfirst] with X hTX hX hlow
  let I : Finset ℕ := (Ico X (2*X)).filter Even
  let G := dyadicGoldbachWitnesses X
  let B := I.filter (fun (n : ℕ) => ¬ (n:ℝ)/36≤corr n)
  let f (n : ℕ) := ((n:ℝ)/n.totient)^2
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have split : (∑ n∈G,corr n)+(∑ n∈B,corr n) = ∑ n∈I,corr n :=
    sum_filter_add_sum_filter_not I (fun n : ℕ => (n:ℝ)/36≤corr n) corr
  have hsubG : G ⊆ I := filter_subset ..
  have hcardB : B.card ≤ X := by
    have h := card_le_card ((filter_subset ..).trans (filter_subset ..) : B ⊆ Ico X (2*X))
    rw [Nat.card_Ico] at h
    exact h.trans_eq (by omega)
  have hbad : (∑ n∈B,corr n) ≤ (X:ℝ)^2/18 := by
    calc _ ≤ ∑ _n∈B,(X:ℝ)/18 := by
           apply sum_le_sum
           intro n hn
           obtain ⟨hi,h⟩ := mem_filter.mp hn
           have hn2 := (mem_Ico.mp (mem_filter.mp hi).1).2.le
           have h' : (n:ℝ)≤2*(X:ℝ) := by exact_mod_cast hn2
           linarith only [not_le.mp h, h']
         _ = (B.card:ℝ)*((X:ℝ)/18) := by simp
         _ ≤ _ := by
           have hh := mul_le_mul_of_nonneg_right (by exact_mod_cast hcardB : (B.card:ℝ)≤X)
             (show 0≤(X:ℝ)/18 by positivity)
           linarith only [hh]
  have hg : (X:ℝ)^2/18 ≤ ∑ n∈G,corr n := by
    change _ ≤ ∑ n∈I,corr n at hlow
    linarith only [hlow,hbad,split]
  have hub : (∑ n∈G,corr n) ≤ (2*C*X)*(∑ n∈G,f n) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    obtain ⟨hmem,he⟩ := mem_filter.mp (hsubG hn)
    obtain ⟨hn1,hn2⟩ := mem_Ico.mp hmem
    apply (hT n (hTX.trans hn1) he).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (by exact_mod_cast hn2.le : (n:ℝ)≤2*(X:ℝ)) hC.le
    linarith only [hh]
  have hr : ((X:ℝ)/(36*C)) ≤ ∑ n∈G,f n := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply (mul_le_mul_iff_left₀ hx).mp
    nlinarith only [hg.trans hub]
  have hsub : G ⊆ Icc 1 (2*X) := by
    intro n hn
    have h := mem_Ico.mp (mem_filter.mp (hsubG hn)).1
    exact mem_Icc.mpr ⟨hX.trans h.1,h.2.le⟩
  have hmoment : (∑ n∈G,(f n)^2) ≤ (Real.exp 30)*(2*X) := by
    simp only [f,←pow_mul,show 2*2=4 by decide]
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans ?_
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using totient_ratio_fourth_moment (2*X)
  have hcauchy : (∑ n∈G,f n)^2 ≤ (G.card:ℝ)*∑ n∈G,(f n)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq G (fun _ => (1:ℝ)) f
  have hsq := (pow_le_pow_left₀ (by positivity) hr 2).trans
    (hcauchy.trans (mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg _)))
  change (X:ℝ)/(2592*C^2*Real.exp 30) ≤ (G.card:ℝ)
  apply (div_le_iff₀ (by positivity)).mpr
  apply (mul_le_mul_iff_left₀ hx).mp
  rw [div_pow] at hsq
  have h4 := (div_le_iff₀ (sq_pos_of_pos (by positivity : 0<36*C))).mp hsq
  linarith only [h4]

/-- A positive fraction of every sufficiently large dyadic interval meets the
original prime-pair floor with the explicit coefficient 1/36. -/
theorem genuine_goldbach_dyadic_positive_proportion :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop,
      δ*X ≤ ((dyadicGoldbachWitnesses X).card:ℝ) := by
  let C : ℝ := (Real.exp 1+3)*808^2
  have hc : 0<C := by dsimp [C];positivity
  refine ⟨1/(2592*C^2*Real.exp 30),by positivity,?_⟩
  have hu : ∀ᶠ n : ℕ in atTop, Even n → corr n ≤ C*n*((n:ℝ)/n.totient)^2 :=
    Eventually.of_forall (fun n hn => corr_upper_totient_sq n hn)
  filter_upwards [dyadic_witnesses_of_first_moment hc hu genuine_dyadic_correlation_first_moment] with X h
  simpa only [one_div_mul_eq_div] using h

end GoldbachPartial