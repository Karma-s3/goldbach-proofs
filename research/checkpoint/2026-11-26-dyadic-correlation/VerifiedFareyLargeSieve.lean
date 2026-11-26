import VerifiedPrimitiveSieveTransfer
import AbelParsevalPrimeArc
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace GoldbachPartial
open MeasureTheory Finset ExtendedArcCoefficient

private theorem packed_integral_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i + δ ≤ 1)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j|)
    (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ t, 0 ≤ f t) :
    (∑ i ∈ s, ∫ t in x i..x i + δ, f t) ≤ ∫ t in (0:ℝ)..1, f t := by
  classical
  let I (i : ι) := Set.Ioc (x i) (x i + δ)
  have hp : Set.PairwiseDisjoint (↑s) I := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t ht ht'
    have hw := hd i hi j hj hij
    change x i < t ∧ t ≤ x i + δ at ht
    change x j < t ∧ t ≤ x j + δ at ht'
    rcases le_abs.mp hw with hw | hw <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hs : (⋃ i ∈ s, I i) ⊆ Set.Ioc (0:ℝ) 1 := by
    intro t ht
    rcases Set.mem_iUnion₂.mp ht with ⟨i,hi,ht⟩
    exact ⟨lt_of_le_of_lt (hx i hi).1 ht.1, ht.2.trans (hx i hi).2⟩
  have he (i : ι) : (∫ t in x i..x i + δ, f t) = ∫ t in I i, f t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [he]
  change (∑ i ∈ s, ∫ t in I i, f t) ≤ _
  rw [← integral_biUnion_finset s (fun _ _ => measurableSet_Ioc) hp
    (fun i _ => hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact setIntegral_mono_set (hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall hn) hs.eventuallySubset

private theorem sampling_of_derivative_majorant {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i + δ ≤ 1)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j|)
    (f df g : ℝ → ℝ) (hf : Continuous f) (hdf : Continuous df) (hg : Continuous g)
    (hn : ∀ t, 0 ≤ f t) (hfg : ∀ t, |df t| ≤ g t)
    (hder : ∀ t, HasDerivAt f (df t) t) :
    (∑ i ∈ s, f (x i)) ≤ (∫ t in (0:ℝ)..1, f t)/δ + ∫ t in (0:ℝ)..1, g t := by
  have hg0 (t : ℝ) : 0 ≤ g t := (abs_nonneg _).trans (hfg t)
  have local_bound (y : ℝ) :
      δ * f y ≤ (∫ t in y..y+δ, f t) + δ * (∫ t in y..y+δ, g t) := by
    have hy : y ≤ y+δ := by linarith
    have hpt (t : ℝ) (ht : t ∈ Set.Icc y (y+δ)) :
        f y ≤ f t + ∫ v in y..y+δ, g v := by
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=y) (b:=t)
        (fun v _ => hder v) (hdf.intervalIntegrable _ _)
      have h1 := intervalIntegral.norm_integral_le_integral_norm (f:=df) (μ:=volume) ht.1
      simp only [Real.norm_eq_abs, hFTC] at h1
      have h2 := intervalIntegral.integral_mono_on (μ:=volume) ht.1 (hdf.abs.intervalIntegrable _ _)
        (hg.intervalIntegrable _ _) (fun v _ => hfg v)
      have h3 := intervalIntegral.integral_mono_interval (μ:=volume) (a:=y) (b:=t) (c:=y) (d:=y+δ)
        le_rfl ht.1 ht.2 (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable _ _)
      linarith [neg_abs_le (f t - f y), h1.trans (h2.trans h3)]
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hy (f:=fun _ => f y)
      (g:=fun t => f t + ∫ v in y..y+δ, g v) intervalIntegrable_const
      ((hf.intervalIntegrable _ _).add intervalIntegrable_const) hpt
    rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) intervalIntegrable_const] at hh
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] using hh
  have h := Finset.sum_le_sum (s:=s) (fun i _ => local_bound (x i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have hp := packed_integral_le s x hδ hx hd f hf hn
  have hq := packed_integral_le s x hδ hx hd g hg hg0
  have ht := h.trans (add_le_add hp (mul_le_mul_of_nonneg_left hq hδ.le))
  rw [div_add', le_div_iff₀ hδ] <;> linarith

private theorem finite_wave_energy_zero_one (s : Finset ℕ) (a : ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖finiteAbelWave s a t‖^2) = ∑ k ∈ s, ‖a k‖^2 := by
  have hn (k : ℕ) : E k = 1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by
      push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hper : Function.Periodic (finiteAbelWave s a) 1 := by
    intro t
    unfold finiteAbelWave
    simp_rw [mul_add, mul_one, phase_add, hn, mul_one]
  have hper' : Function.Periodic (fun t => ‖finiteAbelWave s a t‖^2) 1 :=
    fun t => congrArg (fun z:ℂ => ‖z‖^2) (hper t)
  have h := hper'.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at h
  rw [← h,finiteAbelWave_unit_energy]

private noncomputable def waveDerivativeCoeff (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  a k * ((2 * Real.pi * k : ℝ) : ℂ) * Complex.I

private theorem finite_wave_derivative (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (finiteAbelWave s a) (finiteAbelWave s (waveDerivativeCoeff a) t) t := by
  apply HasDerivAt.fun_sum
  intro k _
  have h := (((((hasDerivAt_id t).const_mul (k:ℝ)).const_mul (2*Real.pi)).ofReal_comp.mul_const
    Complex.I).cexp.const_mul (a k))
  convert h using 1 <;> dsimp [waveDerivativeCoeff, E]; push_cast; ring

theorem finiteAbelWave_separated_sampling {ι : Type*} (p : Finset ι) (x : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hx : ∀ i ∈ p, 0 ≤ x i ∧ x i + δ ≤ 1)
    (hd : ∀ i ∈ p, ∀ j ∈ p, i ≠ j → δ ≤ |x i - x j|)
    (s : Finset ℕ) (a : ℕ → ℂ) (N : ℕ) (hN : ∀ k ∈ s, k ≤ N) :
    (∑ i ∈ p, ‖finiteAbelWave s a (x i)‖^2) ≤
      (1/δ + (1+4*Real.pi^2)*((N:ℝ)+1)) * ∑ k ∈ s, ‖a k‖^2 := by
  let F := finiteAbelWave s a
  let D := finiteAbelWave s (waveDerivativeCoeff a)
  let K := (N:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hF : Continuous F := by unfold F finiteAbelWave E; fun_prop
  have hD : Continuous D := by unfold D finiteAbelWave E; fun_prop
  let g (t : ℝ) := K * ‖F t‖^2 + K⁻¹ * ‖D t‖^2
  have hg (t : ℝ) : |2 * inner ℝ (F t) (D t)| ≤ g t := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    refine (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num : (0:ℝ) ≤ 2)).trans ?_
    dsimp only [g]
    field_simp
    nlinarith only [sq_nonneg (K*‖F t‖-‖D t‖)]
  have h := sampling_of_derivative_majorant p x hδ hx hd (fun t => ‖F t‖^2)
    (fun t => 2 * inner ℝ (F t) (D t)) g (hF.norm.pow 2)
    (by fun_prop) (by dsimp [g]; fun_prop) (fun t => sq_nonneg _) hg
    (fun t => (finite_wave_derivative s a t).norm_sq)
  let A := ∑ k ∈ s, ‖a k‖^2
  have hE : (∫ t in (0:ℝ)..1, ‖F t‖^2) = A := finite_wave_energy_zero_one s a
  have hED : (∫ t in (0:ℝ)..1, ‖D t‖^2) ≤ (4*Real.pi^2*K^2)*A := by
    rw [show (∫ t in (0:ℝ)..1, ‖D t‖^2) = _ from finite_wave_energy_zero_one s (waveDerivativeCoeff a)]
    dsimp only [A]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkK : (k:ℝ) ≤ K := by dsimp [K]; exact_mod_cast Nat.le_succ_of_le (hN k hk)
    have hk0 : (0:ℝ) ≤ k := by positivity
    have hw := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 hkK 2)
      (show 0 ≤ (4*Real.pi^2)*‖a k‖^2 by positivity)
    simp only [waveDerivativeCoeff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg hk0, abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [hw]
  have hig : (∫ t in (0:ℝ)..1, g t) =
      K*A + K⁻¹*(∫ t in (0:ℝ)..1, ‖D t‖^2) := by
    dsimp only [g]
    rw [intervalIntegral.integral_add (f:=fun t => K * ‖F t‖^2) (g:=fun t => K⁻¹ * ‖D t‖^2) (((hF.norm.pow 2).intervalIntegrable _ _).const_mul _)
      (((hD.norm.pow 2).intervalIntegrable _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hE]
  rw [hE,hig] at h
  refine h.trans ?_
  have hq := mul_le_mul_of_nonneg_left hED (inv_nonneg.mpr hK.le)
  have hcancel : K⁻¹*((4*Real.pi^2*K^2)*A) = 4*Real.pi^2*K*A := by field_simp
  rw [hcancel] at hq
  change _ ≤ (1/δ+(1+4*Real.pi^2)*K)*A
  simp only [div_eq_mul_inv, one_mul] at *
  linarith only [hq]

private abbrev FareySample := (j : ℕ) × (ZMod (j+1))ˣ

private def fareyNum (i : FareySample) : ℕ := (i.2 : ZMod (i.1+1)).val

private theorem fareyNum_coprime (i : FareySample) : (fareyNum i).Coprime (i.1+1) := by
  rw [← ZMod.isUnit_iff_coprime]
  simp [fareyNum]

private theorem farey_eq_of_cross {i j : FareySample}
    (h : fareyNum i*(j.1+1) = fareyNum j*(i.1+1)) : i = j := by
  have hi : i.1+1 ∣ j.1+1 := (fareyNum_coprime i).symm.dvd_of_dvd_mul_left
    (h ▸ dvd_mul_left _ _)
  have hj : j.1+1 ∣ i.1+1 := (fareyNum_coprime j).symm.dvd_of_dvd_mul_left
    (h.symm ▸ dvd_mul_left _ _)
  have he := Nat.dvd_antisymm hi hj
  obtain ⟨i,a⟩ := i
  obtain ⟨j,b⟩ := j
  change i+1=j+1 at he
  obtain rfl : i = j := by omega
  congr 1
  apply Units.ext
  apply ZMod.val_injective
  exact Nat.eq_of_mul_eq_mul_right (show 0 < i+1 by omega) h

private noncomputable def fareyPoint (i : FareySample) : ℝ :=
  (fareyNum i : ℝ) / ((i.1+1 : ℕ):ℝ)

private theorem farey_ordered_gap {i j : FareySample} {R : ℕ} (hR : 0 < R)
    (hi : i.1 < R) (hj : j.1 < R)
    (h : fareyNum i*(j.1+1) < fareyNum j*(i.1+1)) :
    1/(R:ℝ)^2 ≤ fareyPoint j - fareyPoint i := by
  have h0i : (0:ℝ) < ((i.1+1 : ℕ):ℝ) := by positivity
  have h0j : (0:ℝ) < ((j.1+1 : ℕ):ℝ) := by positivity
  have h0R : (0:ℝ) < R := by exact_mod_cast hR
  have hn : (fareyNum i:ℝ)*((j.1+1 : ℕ):ℝ) + 1 ≤ (fareyNum j:ℝ)*((i.1+1 : ℕ):ℝ) := by
    exact_mod_cast h
  have hd : ((i.1+1 : ℕ):ℝ)*((j.1+1 : ℕ):ℝ) ≤ (R:ℝ)^2 := by
    rw [sq]
    apply mul_le_mul (by exact_mod_cast hi) (by exact_mod_cast hj) h0j.le h0R.le
  unfold fareyPoint
  rw [div_sub_div _ _ h0j.ne' h0i.ne', div_le_div_iff₀ (sq_pos_of_pos h0R) (mul_pos h0j h0i)]
  have hu : (1:ℝ) ≤ (fareyNum j:ℝ)*((i.1+1 : ℕ):ℝ) - (fareyNum i:ℝ)*((j.1+1 : ℕ):ℝ) := by linarith
  have hw := mul_le_mul_of_nonneg_left hu (sq_nonneg (R:ℝ))
  nlinarith only [hd, hw]

private theorem farey_sample_geometry (R : ℕ) (hR : 0 < R) :
    let s := (range R).sigma (fun j => (univ : Finset (ZMod (j+1))ˣ))
    (∀ i ∈ s, 0 ≤ fareyPoint i ∧ fareyPoint i + 1/(R:ℝ)^2 ≤ 1) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1/(R:ℝ)^2 ≤ |fareyPoint i-fareyPoint j|) := by
  classical
  dsimp only
  have h0R : (0:ℝ) < R := by exact_mod_cast hR
  constructor
  · intro i hi
    have hiR := mem_range.mp (mem_sigma.mp hi).1
    have hq : (0:ℝ) < ((i.1+1:ℕ):ℝ) := by positivity
    have hnum : (fareyNum i:ℝ)+1 ≤ ((i.1+1:ℕ):ℝ) := by
      exact_mod_cast (show fareyNum i+1 ≤ i.1+1 from ZMod.val_lt _)
    have hden : ((i.1+1:ℕ):ℝ) ≤ (R:ℝ)^2 := by
      exact_mod_cast (show i.1+1 ≤ R^2 by nlinarith)
    unfold fareyPoint
    refine ⟨by positivity, ?_⟩
    have hgap := one_div_le_one_div_of_le hq hden
    have hlast : (fareyNum i:ℝ) / ((i.1+1:ℕ):ℝ) + 1/((i.1+1:ℕ):ℝ) ≤ 1 := by
      rw [← add_div, div_le_iff₀ hq, one_mul]
      exact hnum
    linarith
  · intro i hi j hj hne
    have hiR := mem_range.mp (mem_sigma.mp hi).1
    have hjR := mem_range.mp (mem_sigma.mp hj).1
    rcases lt_trichotomy (fareyNum i*(j.1+1)) (fareyNum j*(i.1+1)) with H | H | H
    · rw [abs_sub_comm]
      exact (farey_ordered_gap hR hiR hjR H).trans (le_abs_self _)
    · exact (hne (farey_eq_of_cross H)).elim
    · exact (farey_ordered_gap hR hjR hiR H).trans (le_abs_self _)

private theorem fareyWave_eq (s : Finset ℕ) (a : ℕ → ℂ) (i : FareySample) :
    finiteAbelWave s a (fareyPoint i) = sieveFareyWave (i.1+1) s a i.2 := by
  unfold finiteAbelWave sieveFareyWave fareyPoint fareyNum
  simp only [mul_div_assoc]

/-- Large sieve for all reduced fractions of denominator at most R, with an explicit constant. -/
theorem farey_additive_large_sieve (R N : ℕ) (J s : Finset ℕ) (a : ℕ → ℂ)
    (hJ : ∀ j ∈ J, j < R) (hN : ∀ k ∈ s, k ≤ N) :
    (∑ j ∈ J, ∑ u : (ZMod (j+1))ˣ, ‖sieveFareyWave (j+1) s a u‖^2) ≤
      ((R:ℝ)^2+(1+4*Real.pi^2)*((N:ℝ)+1)) * ∑ k ∈ s, ‖a k‖^2 := by
  classical
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · have he : J = ∅ := eq_empty_iff_forall_notMem.mpr (fun j hj => Nat.not_lt_zero _ (hJ j hj))
    rw [he, sum_empty]
    positivity
  let p := (range R).sigma (fun j => (univ : Finset (ZMod (j+1))ˣ))
  obtain ⟨hx,hd⟩ := farey_sample_geometry R hR
  have h := finiteAbelWave_separated_sampling p fareyPoint (show 0 < 1/(R:ℝ)^2 by positivity)
    hx hd s a N hN
  simp_rw [fareyWave_eq] at h
  rw [show p = _ from rfl, sum_sigma] at h
  simp only [one_div_one_div] at h
  refine le_trans ?_ h
  apply sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (hJ j hj))
  intro j _ _
  exact sum_nonneg fun _ _ => sq_nonneg _

/-- The multiplicative large sieve for actual primitive Dirichlet characters. -/
theorem primitive_character_large_sieve (R N : ℕ) (J s : Finset ℕ) (a : ℕ → ℂ)
    (hJ : ∀ j ∈ J, j < R) (hN : ∀ k ∈ s, k ≤ N) :
    (∑ j ∈ J, (((j+1:ℕ):ℝ)/(j+1).totient) *
      ∑ χ ∈ sievePrimitiveCharacters (j+1), ‖sieveCharacterWave s a χ‖^2) ≤
      ((R:ℝ)^2+(1+4*Real.pi^2)*((N:ℝ)+1)) * ∑ k ∈ s, ‖a k‖^2 :=
  (primitive_sieve_family_le_additive J s a).trans (farey_additive_large_sieve R N J s a hJ hN)

theorem primitive_bilinear_large_sieve (R M N : ℕ) (J A B : Finset ℕ) (a b : ℕ → ℂ)
    (hJ : ∀ j ∈ J, j < R) (hM : ∀ m ∈ A, m ≤ M) (hN : ∀ n ∈ B, n ≤ N) :
    (∑ j ∈ J, (((j+1:ℕ):ℝ)/(j+1).totient) *
      ∑ χ ∈ sievePrimitiveCharacters (j+1), ‖sieveCharacterWave A a χ * sieveCharacterWave B b χ‖) ≤
    Real.sqrt ((((R:ℝ)^2+(1+4*Real.pi^2)*((M:ℝ)+1))) * ∑ k ∈ A, ‖a k‖^2) *
    Real.sqrt ((((R:ℝ)^2+(1+4*Real.pi^2)*((N:ℝ)+1))) * ∑ k ∈ B, ‖b k‖^2) :=
  (vaughan_bilinear_le_farey J A B a b).trans (mul_le_mul
    (Real.sqrt_le_sqrt (farey_additive_large_sieve R M J A a hJ hM))
    (Real.sqrt_le_sqrt (farey_additive_large_sieve R N J B b hJ hN))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end GoldbachPartial