import WeightedTerminalCentering
import ExactRamanujanZeroCorrection

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable def exactCenteredMangoldt (R k : ℕ) : ℝ :=
  Λ k - finiteDivisorWeightSum R (exactRamanujanWeight R) k

noncomputable def exactWeightedZeroMode (n R : ℕ) : ℝ :=
  ∑ k ∈ Ioo 0 n, exactCenteredMangoldt R k * exactCenteredMangoldt R (n-k)

/-- Ordered pairs of positive frequencies k,l outside k+l=n. -/
noncomputable def exactWeightedOffTarget (n R : ℕ) (t : ℝ) : ℂ :=
  ∑ u ∈ (Icc 1 n ×ˢ Icc 1 n).filter (fun u => u.1+u.2≠n),
    ((exactCenteredMangoldt R u.1 * exactCenteredMangoldt R u.2 : ℝ) : ℂ) *
      E (((u.1:ℝ)+u.2-n)*t)

private theorem exactCentered_wave (n R : ℕ) (t : ℝ) :
    centralPrimeWave n t -
      (smallDivisorWave n (Icc 1 R) (fun d => (exactRamanujanWeight R d:ℂ)) t -
        properPrimePowerWave n t) =
    ∑ k ∈ Icc 1 n, (exactCenteredMangoldt R k:ℂ) * E ((k:ℝ)*t) := by
  have hfull : centralPrimeWave n t + properPrimePowerWave n t =
      ∑ k ∈ Icc 1 n, ((Λ k:ℝ):ℂ)*E ((k:ℝ)*t) := by
    unfold centralPrimeWave properPrimePowerWave
    rw [←sum_add_distrib]
    have hi : range (n+1) = insert 0 (Icc 1 n) := by
      ext k
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hi, sum_insert (by simp)]
    simp only [weight,Nat.not_prime_zero,ite_false,Complex.ofReal_zero,zero_mul,
      ArithmeticFunction.map_zero,sub_zero,add_zero,zero_add]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [sub_sub_eq_add_sub, hfull, smallDivisorWave_coefficients, ←sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  unfold exactCenteredMangoldt finiteDivisorWeightSum
  push_cast
  ring

theorem exactWeighted_kernel_partition (n R : ℕ) (t : ℝ) :
    weightedMangoldtKernel n R (fun d => (exactRamanujanWeight R d:ℂ)) t =
      exactWeightedOffTarget n R t + (exactWeightedZeroMode n R:ℂ) := by
  let P := Icc 1 n ×ˢ Icc 1 n
  let w (u : ℕ × ℕ) : ℂ := ((exactCenteredMangoldt R u.1 * exactCenteredMangoldt R u.2 : ℝ) : ℂ) *
    E (((u.1:ℝ)+u.2-n)*t)
  have hall : weightedMangoldtKernel n R (fun d => (exactRamanujanWeight R d:ℂ)) t = ∑ u ∈ P, w u := by
    unfold weightedMangoldtKernel centeredTruePrimeKernel
    rw [exactCentered_wave, sq, sum_mul_sum, sum_mul]
    unfold P
    rw [sum_product]
    apply sum_congr rfl
    intro k _
    rw [sum_mul]
    apply sum_congr rfl
    intro l _
    dsimp only [w]
    push_cast
    rw [show ((k:ℝ)+l-n)*t=k*t+l*t+(-(n:ℝ)*t) by ring, phase_add, phase_add]
    ring
  have hon : ∑ u ∈ P.filter (fun u => u.1+u.2=n), w u = (exactWeightedZeroMode n R:ℂ) := by
    unfold exactWeightedZeroMode
    rw [Complex.ofReal_sum]
    symm
    apply sum_bij (fun k _ => (k,n-k))
    · intro k hk
      obtain ⟨h0,hkn⟩ := mem_Ioo.mp hk
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
        mem_Icc.mpr ⟨by omega,by omega⟩⟩,by dsimp; omega⟩
    · intro k _ j _ h
      exact congrArg Prod.fst h
    · rintro ⟨k,l⟩ h
      obtain ⟨hr,he⟩ := mem_filter.mp h
      obtain ⟨hk,hl⟩ := mem_product.mp hr
      have h₁ := (mem_Icc.mp hk).1
      have h₂ := (mem_Icc.mp hl).1
      change k+l=n at he
      exact ⟨k,mem_Ioo.mpr ⟨by omega,by omega⟩,Prod.ext rfl (by dsimp; omega)⟩
    · intro k hk
      have hkn := (mem_Ioo.mp hk).2.le
      have hzero : (k:ℝ)+((n-k:ℕ):ℝ)-n=0 := by rw [Nat.cast_sub hkn]; ring
      dsimp only [w]
      simp [hzero,E]
  have hpart := sum_filter_add_sum_filter_not P (fun u : ℕ×ℕ => u.1+u.2=n) w
  rw [hall, ← hpart, hon, add_comm]
  rfl

theorem exactWeightedZeroMode_arithmetic (n R : ℕ) :
    exactWeightedZeroMode n R = crtLambdaConvolution n + exactRamanujanZeroCorrection n R := by
  let s := finiteDivisorWeightSum R (exactRamanujanWeight R)
  have href : (∑ k ∈ Ioo 0 n, s k * Λ (n-k)) = ∑ k ∈ Ioo 0 n, Λ k * s (n-k) := by
    apply sum_bij (fun k _ => n-k)
    · intro k hk
      obtain ⟨h0,hkn⟩ := mem_Ioo.mp hk
      exact mem_Ioo.mpr ⟨by omega,by omega⟩
    · intro k hk j hj he
      have h1 := mem_Ioo.mp hk
      have h2 := mem_Ioo.mp hj
      omega
    · intro j hj
      have h := mem_Ioo.mp hj
      exact ⟨n-j,mem_Ioo.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro k hk
      rw [show n-(n-k)=k by have h := mem_Ioo.mp hk; omega, mul_comm]
  have he : exactWeightedZeroMode n R =
      ∑ k ∈ Ioo 0 n, (Λ k*Λ (n-k)+s k*s (n-k)-Λ k*s (n-k)-s k*Λ (n-k)) := by
    unfold exactWeightedZeroMode
    apply sum_congr rfl
    intro k _
    dsimp only [exactCenteredMangoldt,s]
    ring
  rw [he, sum_sub_distrib, sum_sub_distrib, sum_add_distrib, href]
  unfold crtLambdaConvolution exactRamanujanZeroCorrection
  dsimp only [s]
  ring

theorem continuous_exactWeightedOffTarget (n R : ℕ) : Continuous (exactWeightedOffTarget n R) := by
  unfold exactWeightedOffTarget E
  fun_prop

/-- On any subset of the unit interval the zero frequency contributes precisely
the volume times its real coefficient. -/
theorem exactWeighted_kernel_setIntegral (n R : ℕ) {V : Set ℝ} (hV : V ⊆ Set.Icc 0 1) :
    (∫ t in V, weightedMangoldtKernel n R (fun d => (exactRamanujanWeight R d:ℂ)) t) =
      (∫ t in V, exactWeightedOffTarget n R t) +
        ((volume.real V * exactWeightedZeroMode n R : ℝ) : ℂ) := by
  have hf : IntegrableOn (exactWeightedOffTarget n R) V :=
    (continuous_exactWeightedOffTarget n R).integrableOn_Icc.mono_set hV
  have hc : IntegrableOn (fun _ : ℝ => (exactWeightedZeroMode n R:ℂ)) V :=
    continuous_const.integrableOn_Icc.mono_set hV
  simp_rw [exactWeighted_kernel_partition]
  rw [integral_add hf hc, setIntegral_const, Complex.real_smul, Complex.ofReal_mul]

theorem exactWeighted_highTubes_partition :
    ∀ᶠ n : ℕ in atTop, ∀ R : ℕ,
      (∫ t in highNaturalPrimeTubes n,
        weightedMangoldtKernel n R (fun d => (exactRamanujanWeight R d:ℂ)) t) =
      (∫ t in highNaturalPrimeTubes n, exactWeightedOffTarget n R t) +
        ((volume.real (highNaturalPrimeTubes n) *
          (crtLambdaConvolution n + exactRamanujanZeroCorrection n R) : ℝ) : ℂ) := by
  filter_upwards [highNaturalPrimeTubes_geometry] with n hg
  intro R
  rw [exactWeighted_kernel_setIntegral n R hg.1, exactWeightedZeroMode_arithmetic]

end GoldbachPartial