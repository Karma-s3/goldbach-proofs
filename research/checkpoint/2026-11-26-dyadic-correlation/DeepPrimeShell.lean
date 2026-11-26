import PrimeArcModelBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import DeepArcMoments

/-!
The prime tubes immediately beyond the denominator cutoff carry large fourth
moment. For the very same set, a uniform centered character prefix estimate
implies second energy o(n) and a signed Goldbach coefficient o(n). The
theorem `frozen_prime_shell_from_prefix` states this input explicitly.
-/

namespace GoldbachPartial

open MeasureTheory Finset ExtendedArcCoefficient

/-- True log-prime energy on the tubes of denominator `q`, in the original circle coordinates. -/
noncomputable def truePrimeTubeEnergy (n q : ℕ) (ρ : ℝ) : ℝ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q),
    ∫ t in ((a : ℝ)/q-ρ)..((a : ℝ)/q+ρ),
      ‖∑ k ∈ range (n+1), (weight k : ℂ) * E ((k : ℝ)*t)‖^2

theorem truePrimeTubeEnergy_eq_units (n q : ℕ) [NeZero q] (ρ : ℝ) :
    truePrimeTubeEnergy n q ρ =
      ∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, ‖shiftedTruePrimeWave q a n t‖^2 := by
  classical
  symm
  unfold truePrimeTubeEnergy
  apply sum_bij (fun (a : (ZMod q)ˣ) _ => (a : ZMod q).val)
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective q hab)
  · intro a ha
    rcases mem_filter.mp ha with ⟨har, hac⟩
    refine ⟨ZMod.unitOfCoprime a hac, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (mem_range.mp har)]
  · intro a _
    let c : ℝ := ((a : ZMod q).val : ℝ)/q
    let f := fun t : ℝ => ‖∑ k ∈ range (n+1), (weight k : ℂ) * E ((k : ℝ)*t)‖^2
    change (∫ t in -ρ..ρ, f (t+c)) = ∫ t in (c-ρ)..(c+ρ), f t
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring

private theorem truePrimeWave_sq_split (v m : ℂ) :
    ‖v‖^2 ≤ 2*‖v-m‖^2 + 2*‖m‖^2 := by
  have h : ‖v‖ ≤ ‖v-m‖+‖m‖ := by simpa using norm_add_le (v-m) m
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖v-m‖-‖m‖)]

theorem truePrimeTubeEnergy_le_of_prefix (n q : ℕ) [NeZero q] {ρ D : ℝ}
    (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) (hD : 0 ≤ D)
    (hG : ‖unitGaussCoefficient q 1‖ ≤ 1)
    (hp : ∀ χ, ∀ j ≤ n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    truePrimeTubeEnergy n q ρ ≤
      8*ρ*(q.totient:ℝ)*(D^2*(1+2*Real.pi*n*ρ)^2+(Real.log q)^2) +
      2*((n:ℝ)+1)/(q.totient:ℝ) := by
  classical
  let F := fun a => shiftedTruePrimeWave q a n
  let M := geometricPrimeArcModel q n
  have hf (a : (ZMod q)ˣ) : Continuous (F a) := by unfold F shiftedTruePrimeWave E; fun_prop
  have hm : Continuous M := by unfold M geometricPrimeArcModel E; fun_prop
  have row (a : (ZMod q)ˣ) :
      (∫ t in -ρ..ρ, ‖F a t‖^2) ≤
        2*(∫ t in -ρ..ρ, ‖F a t-M t‖^2) + 2*(∫ t in -ρ..ρ, ‖M t‖^2) := by
    let e := fun t => ‖F a t-M t‖^2
    let g := fun t => ‖M t‖^2
    have he : Continuous e := ((hf a).sub hm).norm.pow 2
    have hg : Continuous g := hm.norm.pow 2
    have h2e : Continuous (fun t => 2*e t) := continuous_const.mul he
    have h2g : Continuous (fun t => 2*g t) := continuous_const.mul hg
    calc
      _ ≤ ∫ t in -ρ..ρ, (2*e t+2*g t) :=
        intervalIntegral.integral_mono_on (by linarith) (((hf a).norm.pow 2).intervalIntegrable _ _)
          ((h2e.add h2g).intervalIntegrable _ _) (fun t _ => truePrimeWave_sq_split _ _)
      _ = _ := by
        rw [intervalIntegral.integral_add (h2e.intervalIntegrable _ _) (h2g.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum := Finset.sum_le_sum (s := (univ : Finset (ZMod q)ˣ)) (fun a _ => row a)
  rw [sum_add_distrib, ← mul_sum] at hsum
  have he := primeArc_tube_of_prefix q n hρ hD hp
  have hx : (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, ‖F a t-M t‖^2) =
      ∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy q a n t (dirichletGeometricKernel n t)‖^2 :=
    (intervalIntegral.integral_finsetSum (fun a _ => (((hf a).sub hm).norm.pow 2).intervalIntegrable _ _)).symm
  rw [hx] at hsum
  simp only [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul] at hsum
  have hmodel := geometricPrimeArcModel_window_energy q n hρ hhalf hG
  change (q.totient:ℝ)*(∫ t in -ρ..ρ, ‖M t‖^2) ≤ _ at hmodel
  change (∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy q a n t (dirichletGeometricKernel n t)‖^2) ≤ _ at he
  rw [truePrimeTubeEnergy_eq_units]
  change (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, ‖F a t‖^2) ≤ _
  apply hsum.trans
  rw [mul_left_comm (q.totient : ℝ) 2]
  refine (add_le_add (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hmodel (by norm_num : (0:ℝ) ≤ 2))).trans_eq ?_
  ring

section ActualTubeUnion
open MeasureTheory Set
open GoldbachDeepFourth (deepTube deepPrimeWave)
open GoldbachDeepFourth.FourthMomentBand (primes mem_primes)

/-- The same prime denominators and nonzero numerators as in the deep fourth-moment tubes. -/
noncomputable def primeBandTubeUnion (Y : ℕ) (ρ : ℝ) : Set ℝ :=
  ⋃ q ∈ primes Y, ⋃ a ∈ Finset.Ico 1 q, deepTube ρ q a

private theorem integral_finite_union_le {ι : Type*} (s : Finset ι)
    (V : ι → Set ℝ) (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hm : ∀ i, MeasurableSet (V i)) (hi : ∀ i, IntegrableOn F (V i)) :
    (∫ x in ⋃ i ∈ s, V i, F x) ≤ ∑ i ∈ s, ∫ x in V i, F x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    let C := ⋃ i ∈ s, V i
    have hC : MeasurableSet C := s.measurableSet_biUnion fun i _ => hm i
    have hiC : IntegrableOn F C := integrableOn_finset_iUnion.mpr fun i _ => hi i
    change (∫ x in V a ∪ C, F x) ≤ _
    rw [← Set.sdiff_union_self (s := V a) (t := C),
      setIntegral_union disjoint_sdiff_self_left hC ((hi a).mono_set sdiff_subset) hiC]
    exact add_le_add (setIntegral_mono_set (hi a) (Filter.Eventually.of_forall hF)
      (Filter.Eventually.of_forall sdiff_subset)) ih

private theorem prime_numerator_finset {q : ℕ} (hq : q.Prime) :
    Finset.Ico 1 q = (Finset.range q).filter fun a => a.Coprime q := by
  ext a
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha, haq⟩
    exact ⟨haq, (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha haq)).symm⟩
  · rintro ⟨haq, hcop⟩
    refine ⟨?_, haq⟩
    by_contra! h
    have hzero : a = 0 := by omega
    subst a
    exact hq.ne_one (by simpa using hcop)

theorem primeBandTubeUnion_energy_le (n Y : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫ t in primeBandTubeUnion Y ρ, ‖deepPrimeWave n t‖^2) ≤
      ∑ q ∈ primes Y, truePrimeTubeEnergy n q ρ := by
  classical
  let F := fun t => ‖deepPrimeWave n t‖^2
  let V := fun q => ⋃ a ∈ Finset.Ico 1 q, deepTube ρ q a
  have hF : Continuous F := by
    dsimp [F,deepPrimeWave,GoldbachDeepFourth.ExtendedArcCoefficient.E]
    fun_prop
  have hpos : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  have hm (q : ℕ) : MeasurableSet (V q) :=
    (Finset.Ico 1 q).measurableSet_biUnion fun _ _ => measurableSet_Icc
  have hi (q : ℕ) : IntegrableOn F (V q) :=
    integrableOn_finset_iUnion.mpr fun _ _ => hF.continuousOn.integrableOn_Icc
  refine (integral_finite_union_le (primes Y) V F hpos hm hi).trans ?_
  refine Finset.sum_le_sum fun q hq => ?_
  refine (integral_finite_union_le (Finset.Ico 1 q) (deepTube ρ q) F hpos
    (fun _ => measurableSet_Icc) (fun _ => hF.continuousOn.integrableOn_Icc)).trans_eq ?_
  unfold truePrimeTubeEnergy
  rw [prime_numerator_finset (mem_primes.mp hq).2.2]
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  rfl

theorem primeBandTubeUnion_signed_le (n Y : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖∫ t in primeBandTubeUnion Y ρ,
        (deepPrimeWave n t)^2 * GoldbachDeepFourth.ExtendedArcCoefficient.E (-(n:ℝ)*t)‖ ≤
      ∑ q ∈ primes Y, truePrimeTubeEnergy n q ρ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hphase (t : ℝ) :
      ‖GoldbachDeepFourth.ExtendedArcCoefficient.E (-(n:ℝ)*t)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  simpa only [norm_mul,norm_pow,hphase,mul_one] using primeBandTubeUnion_energy_le n Y hρ

end ActualTubeUnion

section MediumCutoffLimits
open Filter
open scoped Topology
theorem medDeskD_coe_tendsto_atTop :
    Tendsto (fun n : ℕ => (medDeskD n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
      tendsto_natCast_atTop_atTop))

theorem medDeskD_prefix_ratio_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ =>
      (C * Real.sqrt n * Real.log (2*(n : ℝ)^2)^2) / (medDeskD n : ℝ)^2) atTop (𝓝 0) := by
  let p := fun n : ℕ => (n : ℝ)^(1/12 : ℝ)
  let u := fun n : ℕ => (n : ℝ)^(1/3 : ℝ)
  have hp : Tendsto p atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/12)).comp
    tendsto_natCast_atTop_atTop
  have hu : Tendsto u atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
    tendsto_natCast_atTop_atTop
  have hf : Tendsto (fun n : ℕ => (medDeskD n : ℝ)/u n) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hu
  have hlog : Tendsto (fun n : ℕ => Real.log n / p n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/12)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hlog₂ : Tendsto (fun n : ℕ => Real.log (2*(n : ℝ)^2)/p n) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := Real.log 2)).mul hp.inv_tendsto_atTop).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hlog)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnx : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    change Real.log 2 * (p n)⁻¹ + 2*(Real.log n/p n) = Real.log (2*(n:ℝ)^2)/p n
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hnx), Real.log_pow]
    push_cast
    ring
  have h := ((tendsto_const_nhds (x := C)).mul (hlog₂.pow 2)).div (hf.pow 2) (by norm_num)
  simp only [zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hx : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : p n ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hu0 : u n ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hid : Real.sqrt n * (p n)^2 = (u n)^2 := by
    dsimp only [p,u]
    rw [Real.sqrt_eq_rpow]
    simp only [sq, ← Real.rpow_add hx]
    norm_num
  change C*(Real.log (2*(n : ℝ)^2)/p n)^2 / ((medDeskD n : ℝ)/u n)^2 =
    C*Real.sqrt n*Real.log (2*(n : ℝ)^2)^2 / (medDeskD n : ℝ)^2
  by_cases hd : (medDeskD n : ℝ) = 0
  · simp [hd]
  · field_simp
    rw [← hid]
    ring

theorem medDeskD_eventually_prefix_le (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*Real.sqrt n*Real.log (2*(n : ℝ)^2)^2 ≤ ε*(medDeskD n : ℝ)^2 := by
  filter_upwards [(medDeskD_prefix_ratio_tendsto_zero C).eventually (gt_mem_nhds hε),
    medDeskD_coe_tendsto_atTop.eventually_gt_atTop 0] with n hbound hd
  exact (div_le_iff₀ (sq_pos_of_pos hd)).mp hbound.le

end MediumCutoffLimits

section FrozenFourthShell
open Filter MeasureTheory Set
open GoldbachDeepFourth (deepPrimeWave deepTube)

theorem eventually_primeBandTubeUnion_fourth_lower :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^(7/3:ℝ)/(320*64^4*Real.log n) ≤
      ∫ t in primeBandTubeUnion (GoldbachDeepFourth.medDeskD n) (1/(20*(n:ℝ))), ‖deepPrimeWave n t‖^4 := by
  filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget] with n hn
  rcases hn with ⟨hn, hb, hy, _, _⟩
  let Y := GoldbachDeepFourth.medDeskD n
  let ρ : ℝ := 1/(20*(n:ℝ))
  let U := primeBandTubeUnion Y ρ
  let F := fun t : ℝ => ‖deepPrimeWave n t‖^4
  have hF : Continuous F := by
    dsimp [F,deepPrimeWave,GoldbachDeepFourth.ExtendedArcCoefficient.E]
    fun_prop
  have hU : MeasurableSet U :=
    (GoldbachDeepFourth.FourthMomentBand.primes Y).measurableSet_biUnion fun q _ =>
      (Finset.Ico 1 q).measurableSet_biUnion fun _ _ => measurableSet_Icc
  have hi : IntegrableOn F U :=
    integrableOn_finset_iUnion.mpr fun _ _ =>
      integrableOn_finset_iUnion.mpr fun _ _ => hF.continuousOn.integrableOn_Icc
  apply GoldbachDeepFourth.fourth_mass_quantitative_of_row_bound hn hb hy
  refine (GoldbachDeepFourth.deepFourth_prime_tubes_on hn (by omega : 256 ≤ GoldbachDeepFourth.medDeskD n) hy U hU ?_).trans ?_
  · intro q hq a ha t ht
    exact mem_iUnion₂.mpr ⟨q,hq,mem_iUnion₂.mpr ⟨a,ha,ht⟩⟩
  · change (∫ t in (0:ℝ)..1, U.indicator F t) ≤ ∫ t in U, F t
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator hU]
    exact setIntegral_mono_set hi (Filter.Eventually.of_forall (fun t => by
      dsimp [F]; positivity)) (Filter.Eventually.of_forall inter_subset_right)

end FrozenFourthShell

section SignedPrimeShell

open Finset MeasureTheory

/-- True-prime square energy on the prime-denominator part of a deep dyadic shell. -/
theorem truePrimeShell_energy_of_prefix {n Y : ℕ} (hY : 2 ≤ Y) {ρ D : ℝ}
    (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) (hD : 0 ≤ D)
    (hp : ∀ q ∈ (Ioc Y (2*Y)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    (∑ q ∈ (Ioc Y (2*Y)).filter Nat.Prime, truePrimeTubeEnergy n q ρ) ≤
      8*ρ*(2*(Y:ℝ))^2*((D*(1+2*Real.pi*n*ρ))^2+(Real.log (2*(Y:ℝ)))^2) +
      4*((n:ℝ)+1)*Real.log 4/Real.log Y := by
  let J := (Ioc Y (2*Y)).filter Nat.Prime
  let A := (D*(1+2*Real.pi*n*ρ))^2+(Real.log (2*(Y:ℝ)))^2
  have hcard : J.card ≤ 2*Y := by
    have he := Finset.card_le_card (Finset.filter_subset Nat.Prime (Ioc Y (2*Y)))
    simp only [Nat.card_Ioc] at he
    exact he.trans (Nat.sub_le ..)
  have hprop {q : ℕ} (hq : q∈J) : (Y<q ∧ q≤2*Y) ∧ q.Prime := by simpa [J] using hq
  have hrow (q : ℕ) (hq : q∈J) : truePrimeTubeEnergy n q ρ ≤ 8*ρ*(2*(Y:ℝ))*A +
      (2*((n:ℝ)+1))*(1/(q.totient:ℝ)) := by
    have h := hprop hq
    let _ : NeZero q := ⟨h.2.ne_zero⟩
    have ht : (q.totient:ℝ) ≤ 2*(Y:ℝ) := by exact_mod_cast (Nat.totient_le _).trans h.1.2
    have hl : (Real.log (q:ℝ))^2 ≤ (Real.log (2*(Y:ℝ)))^2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast h.2.one_le))
        (Real.log_le_log (by exact_mod_cast h.2.pos) (by exact_mod_cast h.1.2)) 2
    refine (truePrimeTubeEnergy_le_of_prefix n q hρ hhalf hD (principal_unitGauss_norm_le_one q) (hp q hq)).trans ?_
    apply add_le_add
    · dsimp [A]
      rw [← mul_pow D]
      gcongr
    · exact le_of_eq (by ring)
  calc
    _ ≤ ∑ q ∈ J, (8*ρ*(2*(Y:ℝ))*A + (2*((n:ℝ)+1))*(1/(q.totient:ℝ))) :=
      Finset.sum_le_sum hrow
    _ = (J.card:ℝ)*(8*ρ*(2*(Y:ℝ))*A) + (2*((n:ℝ)+1))*(∑ q ∈ J, 1/(q.totient:ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (2*(Y:ℝ))*(8*ρ*(2*(Y:ℝ))*A) + (2*((n:ℝ)+1))*(2*Real.log 4/Real.log Y) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        dsimp [A]; positivity
      · exact mul_le_mul_of_nonneg_left (prime_shell_reciprocal_totient hY) (by positivity)
    _ = _ := by dsimp [A]; ring

/-- The same radius 1/(20n) used in the fourth-moment obstruction. -/
theorem truePrimeShell_normalized {n Y : ℕ} (hY : 2 ≤ Y) (hYn : Y^3 ≤ n) {D : ℝ}
    (hD : 0 ≤ D)
    (hp : ∀ q ∈ (Ioc Y (2*Y)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
      ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    (∑ q ∈ (Ioc Y (2*Y)).filter Nat.Prime, truePrimeTubeEnergy n q (1/(20*(n:ℝ))))/(n:ℝ) ≤
      (8/5:ℝ)*(((D/(Y:ℝ)^2)*(1+Real.pi/10))^2+(2/(Y:ℝ))^2) +
      8*Real.log 4/Real.log Y := by
  have hy : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  have hcube : (Y:ℝ)^3 ≤ n := by exact_mod_cast hYn
  have hn0 : 0 < n := (Nat.pow_pos (by omega : 0<Y)).trans_le hYn
  have hn : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn0
  have hlog : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hlog2 : 0 ≤ Real.log (2*(Y:ℝ)) := Real.log_nonneg (by linarith [show 2 ≤ (Y:ℝ) by exact_mod_cast hY])
  have hlogU : Real.log (2*(Y:ℝ)) ≤ 2*Y := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0<2*(Y:ℝ))]
  have hrat : (Y:ℝ)/n ≤ 1/(Y:ℝ)^2 := by
    apply (div_le_div_iff₀ hn (by positivity)).mpr
    simpa [pow_succ, mul_comm] using hcube
  have h1 : 0 ≤ 1+Real.pi/10 := by positivity
  have hpart : ((Y:ℝ)/n*(D*(1+Real.pi/10)))^2 ≤ ((D/(Y:ℝ)^2)*(1+Real.pi/10))^2 := by
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ (1/(Y:ℝ)^2)*(D*(1+Real.pi/10)) := mul_le_mul_of_nonneg_right hrat (by positivity)
      _ = _ := by ring
  have hpart' : ((Y:ℝ)/n*Real.log (2*(Y:ℝ)))^2 ≤ (2/(Y:ℝ))^2 := by
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ (1/(Y:ℝ)^2)*(2*Y) := mul_le_mul hrat hlogU hlog2 (by positivity)
      _ = _ := by field_simp
  have hratio : ((n:ℝ)+1)/n ≤ 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hh := truePrimeShell_energy_of_prefix hY (by positivity : 0 ≤ 1/(20*(n:ℝ)))
    (show 1/(20*(n:ℝ))≤1/2 by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith) hD hp
  refine (div_le_div_of_nonneg_right hh hn.le).trans ?_
  calc
    _ = (8/5:ℝ)*((((Y:ℝ)/n)*(D*(1+Real.pi/10)))^2+((Y:ℝ)/n*Real.log (2*(Y:ℝ)))^2) +
        (((n:ℝ)+1)/n)*(4*Real.log 4/Real.log Y) := by field_simp; ring
    _ ≤ (8/5:ℝ)*(((D/(Y:ℝ)^2)*(1+Real.pi/10))^2+(2/(Y:ℝ))^2) +
        2*(4*Real.log 4/Real.log Y) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (add_le_add hpart hpart') (by norm_num)
      · exact mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring


open Filter
open scoped Topology

theorem truePrimeTubeEnergy_nonneg (n q : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ truePrimeTubeEnergy n q ρ := by
  unfold truePrimeTubeEnergy
  apply Finset.sum_nonneg
  intro a _
  exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)

/-- A uniform prefix error of little-o(Y²) removes the entire prime-denominator shell
from the signed problem at radius 1/(20n), including the fourth-moment counterexample tubes. -/
theorem truePrimeShell_normalized_tendsto (Y : ℕ → ℕ) (D : ℕ → ℝ)
    (hY : Tendsto (fun n => (Y n:ℝ)) atTop atTop)
    (hD : Tendsto (fun n => D n/(Y n:ℝ)^2) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, (Y n)^3 ≤ n ∧ 0 ≤ D n ∧
      ∀ q ∈ (Ioc (Y n) (2*Y n)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
        ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D n) :
    Tendsto (fun n => (∑ q ∈ (Ioc (Y n) (2*Y n)).filter Nat.Prime,
      truePrimeTubeEnergy n q (1/(20*(n:ℝ))))/(n:ℝ)) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp hY
  have hl := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hY)
  have hb := (((((hD.mul_const (1+Real.pi/10)).pow 2).add ((hi.const_mul 2).pow 2)).const_mul (8/5:ℝ)).add
    (hl.const_mul (8*Real.log 4)))
  have hU : Tendsto (fun n => (8/5:ℝ)*(((D n/(Y n:ℝ)^2)*(1+Real.pi/10))^2+(2/(Y n:ℝ))^2) +
      8*Real.log 4/Real.log (Y n)) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_eq_mul_inv] using hb
  apply squeeze_zero' _ _ hU
  · exact Filter.Eventually.of_forall fun n => div_nonneg (Finset.sum_nonneg
      (fun q _ => truePrimeTubeEnergy_nonneg n q (by positivity))) (Nat.cast_nonneg n)
  · filter_upwards [hw,hY.eventually_ge_atTop 2] with n h hh
    exact truePrimeShell_normalized (by exact_mod_cast hh) h.1 h.2.1 h.2.2

end SignedPrimeShell

section DeepCounterexampleTubes

open Filter MeasureTheory Finset
open scoped Topology

/-- The very same union admits an arbitrarily large fourth moment and, under this prefix
estimate, a signed second coefficient of size o(n). -/
theorem primeBandTubeUnion_coefficient_tendsto (Y : ℕ → ℕ) (D : ℕ → ℝ)
    (hY : Tendsto (fun n => (Y n:ℝ)) atTop atTop)
    (hD : Tendsto (fun n => D n/(Y n:ℝ)^2) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, (Y n)^3 ≤ n ∧ 0 ≤ D n ∧
      ∀ q ∈ (Ioc (Y n) (2*Y n)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
        ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D n) :
    Tendsto (fun n => ‖∫ t in primeBandTubeUnion (Y n) (1/(20*(n:ℝ))),
      (GoldbachDeepFourth.deepPrimeWave n t)^2 * GoldbachDeepFourth.ExtendedArcCoefficient.E (-(n:ℝ)*t)‖/(n:ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (truePrimeShell_normalized_tendsto Y D hY hD hw)
  · exact Filter.Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)
  · exact Filter.Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (primeBandTubeUnion_signed_le n (Y n) (by positivity)) (Nat.cast_nonneg n)

theorem primeBandTubeUnion_energy_tendsto (Y : ℕ → ℕ) (D : ℕ → ℝ)
    (hY : Tendsto (fun n => (Y n:ℝ)) atTop atTop)
    (hD : Tendsto (fun n => D n/(Y n:ℝ)^2) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, (Y n)^3 ≤ n ∧ 0 ≤ D n ∧
      ∀ q ∈ (Ioc (Y n) (2*Y n)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
        ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D n) :
    Tendsto (fun n => (∫ t in primeBandTubeUnion (Y n) (1/(20*(n:ℝ))),
      ‖GoldbachDeepFourth.deepPrimeWave n t‖^2)/(n:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (truePrimeShell_normalized_tendsto Y D hY hD hw)
  · exact Filter.Eventually.of_forall fun n => div_nonneg (integral_nonneg fun t => sq_nonneg _) (Nat.cast_nonneg n)
  · exact Filter.Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (primeBandTubeUnion_energy_le n (Y n) (by positivity)) (Nat.cast_nonneg n)

end DeepCounterexampleTubes

section FrozenShellEstimate
open Filter MeasureTheory Finset
open scoped Topology

/-- A uniform centered character-sum estimate, including all prefixes. -/
def shellPrimePrefixBound (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Ioc (medDeskD n) (2*medDeskD n)).filter Nat.Prime,
    ∀ [NeZero q], ∀ χ, ∀ j ≤ n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤
      C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2

theorem frozen_prime_shell_from_prefix {C : ℝ} (hC : 0 ≤ C) (h : shellPrimePrefixBound C) :
    Tendsto (fun n : ℕ => (∫ t in primeBandTubeUnion (medDeskD n) (1/(20*(n:ℝ))),
      ‖GoldbachDeepFourth.deepPrimeWave n t‖^2)/(n:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ‖∫ t in primeBandTubeUnion (medDeskD n) (1/(20*(n:ℝ))),
      (GoldbachDeepFourth.deepPrimeWave n t)^2 * GoldbachDeepFourth.ExtendedArcCoefficient.E (-(n:ℝ)*t)‖/(n:ℝ))
      atTop (𝓝 0) := by
  let D := fun n : ℕ => C*Real.sqrt n*(Real.log (2*(n:ℝ)^2))^2
  have hh : ∀ᶠ n : ℕ in atTop, (medDeskD n)^3 ≤ n ∧ 0 ≤ D n ∧
      ∀ q ∈ (Ioc (medDeskD n) (2*medDeskD n)).filter Nat.Prime, ∀ [NeZero q], ∀ χ, ∀ j ≤ n,
        ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D n := by
    filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget,h] with n hn hq
    exact ⟨hn.2.2.1,by dsimp [D]; positivity,hq⟩
  exact ⟨primeBandTubeUnion_energy_tendsto medDeskD D medDeskD_coe_tendsto_atTop
      (medDeskD_prefix_ratio_tendsto_zero C) hh,
    primeBandTubeUnion_coefficient_tendsto medDeskD D medDeskD_coe_tendsto_atTop
      (medDeskD_prefix_ratio_tendsto_zero C) hh⟩

end FrozenShellEstimate

/-- Signed true-prime contribution of all reduced numerators at a single denominator. -/
noncomputable def truePrimeSignedRow (n q : ℕ) [NeZero q] (ρ : ℝ) : ℂ :=
  ∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ,
    (shiftedTruePrimeWave q a n t)^2 * E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))

theorem truePrimeSignedRow_eq_change_add_model (n q : ℕ) [NeZero q] (hq : 1 < q) (ρ : ℝ) :
    truePrimeSignedRow n q ρ = primeArcSignedChange q n ρ +
      actualRamanujanModel n q * ((∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2 : ℝ):ℂ) := by
  classical
  rw [← geometricPrimeArcModel_row_integral_norm_sq n q hq ρ]
  unfold truePrimeSignedRow primeArcSignedChange
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  let phase := fun t : ℝ => E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))
  have hF : Continuous (shiftedTruePrimeWave q a n) := by unfold shiftedTruePrimeWave E; fun_prop
  have hM : Continuous (geometricPrimeArcModel q n) := by unfold geometricPrimeArcModel E; fun_prop
  have hP : Continuous phase := by unfold phase E; fun_prop
  let F := fun t => (shiftedTruePrimeWave q a n t)^2 * phase t
  let M := fun t => (geometricPrimeArcModel q n t)^2 * phase t
  have hFi : Continuous F := (hF.pow 2).mul hP
  have hMi : Continuous M := (hM.pow 2).mul hP
  have hsplit (t : ℝ) : ((shiftedTruePrimeWave q a n t)^2-(geometricPrimeArcModel q n t)^2) *
      E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q)) = F t - M t := sub_mul .. 
  simp_rw [hsplit]
  change (∫ t in -ρ..ρ, F t) = (∫ t in -ρ..ρ, F t-M t) + ∫ t in -ρ..ρ, M t
  rw [intervalIntegral.integral_sub (hFi.intervalIntegrable _ _) (hMi.intervalIntegrable _ _), sub_add_cancel]

private theorem sum_successor_dyadic (Y : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Ico Y (2*Y), f (j+1)) = ∑ q ∈ Ioc Y (2*Y), f q := by
  apply sum_bij (fun j _ => j+1)
  · intro j hj
    have h := mem_Ico.mp hj
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro j _ k _ h
    omega
  · intro q hq
    have h := mem_Ioc.mp hq
    exact ⟨q-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro _ _
    rfl

theorem truePrimeSignedRow_dyadic_bound {n Y : ℕ} (hn : 0<n) (hY : 0<Y) (ρ : ℕ → ℝ)
    (hw : ∀ q ∈ Ioc Y (2*Y), 0 ≤ ρ q ∧ ρ q ≤ 1/2) :
    ‖∑ j ∈ Ico Y (2*Y), truePrimeSignedRow n (j+1) (ρ (j+1))‖ ≤
      ‖∑ j ∈ Ico Y (2*Y), primeArcSignedChange (j+1) n (ρ (j+1))‖ +
      ((n:ℝ)+1)*((((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y) := by
  let M := fun q : ℕ => actualRamanujanModel n q *
    ((∫ t in -(ρ q)..ρ q, ‖dirichletGeometricKernel n t‖^2 : ℝ):ℂ)
  have hsplit : (∑ j ∈ Ico Y (2*Y), truePrimeSignedRow n (j+1) (ρ (j+1))) =
      (∑ j ∈ Ico Y (2*Y), primeArcSignedChange (j+1) n (ρ (j+1))) +
      ∑ q ∈ Ioc Y (2*Y), M q := by
    rw [← sum_successor_dyadic Y M,← sum_add_distrib]
    refine sum_congr rfl (fun j hj => ?_)
    exact truePrimeSignedRow_eq_change_add_model n (j+1)
      (by have h := mem_Ico.mp hj; omega) _
  rw [hsplit]
  have hm : ‖∑ q ∈ Ioc Y (2*Y), M q‖ ≤ _ := geometricModel_dyadic_window_bound hn hY ρ hw
  exact (norm_add_le _ _).trans (add_le_add le_rfl hm)

private theorem exponent_four_le_two_pow (a : ℕ) : (a+1)^4 ≤ 2^8*2^a := by
  have ha : a+1 ≤ 4*(a/4+1) := by omega
  have hk : a/4+1 ≤ 2^(a/4) := Nat.lt_two_pow_self
  calc
    _ ≤ (4*2^(a/4))^4 := Nat.pow_le_pow_left (ha.trans (Nat.mul_le_mul_left 4 hk)) _
    _ = 2^8*2^(4*(a/4)) := by rw [mul_pow,← pow_mul, Nat.mul_comm (a/4) 4]; norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- A uniform fourth-power divisor bound, with one constant per prime below sixteen. -/
theorem divisor_count_fourth_le (n : ℕ) : n.divisors.card^4 ≤ 2^48*n := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let K := fun p : ℕ => if p<16 then (2:ℕ)^8 else 1
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p+1)^4 ≤ K p * p^(n.factorization p) := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    by_cases hs : p<16
    · simpa [K,hs] using
        (exponent_four_le_two_pow (n.factorization p)).trans
          (Nat.mul_le_mul_left (2^8) (Nat.pow_le_pow_left hpr.two_le _))
    · simp only [K,hs,ite_false,one_mul]
      calc
        _ ≤ (2^(n.factorization p))^4 := Nat.pow_le_pow_left Nat.lt_two_pow_self _
        _ = 16^(n.factorization p) := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  have hc : (n.primeFactors.filter (fun p => p<16)).card ≤ 6 := by
    calc
      _ ≤ ((Finset.range 16).filter Nat.Prime).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨hpn,hp16⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp16,Nat.prime_of_mem_primeFactors hpn⟩
      _ = 6 := by decide
  have hK : (∏ p ∈ n.primeFactors, K p) ≤ 2^48 := by
    dsimp only [K]
    rw [← Finset.prod_filter, Finset.prod_const, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  rw [Nat.card_divisors hn,← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (K p*p^(n.factorization p)) := Finset.prod_le_prod hlocal
    _ = (∏ p ∈ n.primeFactors, K p)*n := by
      rw [Finset.prod_mul_distrib,← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ _ := Nat.mul_le_mul_right n hK



section CompositeThresholds
open Filter
open scoped Topology
theorem medDesk_composite_shell_thresholds (C : ℝ) (_hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      let T := (n:ℝ)^(1/48:ℝ)
      let Y := medDeskD n
      let K := Nat.log 2 (2*Y)+1
      1 ≤ T ∧ T^48 = (n:ℝ) ∧ 0 < Y ∧ (Y:ℝ) ≤ T^16 ∧ T^16/2 ≤ (Y:ℝ) ∧
      C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 ≤ T^28 ∧
      0 ≤ Real.log (2*(Y:ℝ)) ∧ Real.log (2*(Y:ℝ)) ≤ T^28 ∧ (K:ℝ) ≤ T := by
  let t (n : ℕ) := (n:ℝ)^(1/48:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n / t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/48)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ), ht.eventually_ge_atTop 10,
    ht.eventually_ge_atTop C, hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/10))]
    with n hn hten hCt hsmall
  let T := t n
  let Y := medDeskD n
  change 1 ≤ T ∧ T^48 = (n:ℝ) ∧ 0 < Y ∧ (Y:ℝ) ≤ T^16 ∧ T^16/2 ≤ (Y:ℝ) ∧
    C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 ≤ T^28 ∧ 0 ≤ Real.log (2*(Y:ℝ)) ∧
    Real.log (2*(Y:ℝ)) ≤ T^28 ∧ ((Nat.log 2 (2*Y)+1 : ℕ):ℝ) ≤ T
  change 10 ≤ T at hten
  change C ≤ T at hCt
  have ht1 : 1 ≤ T := by linarith
  have ht0 : 0 < T := by linarith
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hlogn : Real.log n ≤ T/10 := by
    change Real.log n/T < 1/10 at hsmall
    linarith [(div_lt_iff₀ ht0).mp hsmall]
  have hp (a : ℕ) : T^a = (n:ℝ)^((1/48:ℝ)*a) := by
    dsimp only [T,t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  have h48 : T^48 = (n:ℝ) := by rw [hp]; norm_num
  have h16 : T^16 = (n:ℝ)^(1/3:ℝ) := by rw [hp]; norm_num
  have h24 : T^24 = Real.sqrt n := by rw [hp, Real.sqrt_eq_rpow]; norm_num
  have hle (a : ℕ) (ha : 1 ≤ a) : T ≤ T^a := by
    simpa only [pow_one] using (pow_le_pow_right₀ ht1 ha)
  have hf : (Y:ℝ) ≤ T^16 := by rw [h16]; exact Nat.floor_le (by positivity)
  have hnext : T^16 < (Y:ℝ)+1 := by rw [h16]; exact Nat.lt_floor_add_one _
  have hhalf : T^16/2 ≤ (Y:ℝ) := by linarith [hle 16 (by decide)]
  have hy : 0 < Y := by
    have h : (0:ℝ)<Y := by linarith [hle 16 (by decide)]
    exact_mod_cast h
  have hyn : (Y:ℝ) ≤ n :=
    hf.trans ((pow_le_pow_right₀ ht1 (by decide : 16≤48)).trans_eq h48)
  have h2lo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x:=2) (by norm_num)
    norm_num at h ⊢
    linarith
  have h2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x:=2) (by norm_num)
    linarith
  have helog : Real.log (2*(n:ℝ)^2) ≤ T := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow]
    push_cast
    linarith
  have helog0 : 0 ≤ Real.log (2*(n:ℝ)^2) := Real.log_nonneg (by nlinarith [sq_nonneg ((n:ℝ)-1)])
  have herror : C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2 ≤ T^28 := calc
    _ ≤ T * T^24 * T^2 := by rw [h24]; gcongr
    _ = T^27 := by ring
    _ ≤ T^28 := pow_le_pow_right₀ ht1 (by decide)
  have hy1 : (1:ℝ) ≤ Y := by exact_mod_cast hy
  have hlog0 : 0 ≤ Real.log (2*(Y:ℝ)) := Real.log_nonneg (by linarith)
  have hlogy : Real.log (2*(Y:ℝ)) ≤ 1+T/10 := by
    have h := Real.log_le_log (by linarith : (0:ℝ) < 2*Y)
      (mul_le_mul_of_nonneg_left hyn (by norm_num : (0:ℝ)≤2))
    rw [Real.log_mul (by norm_num) hn0.ne'] at h
    linarith
  refine ⟨ht1,h48,hy,hf,hhalf,herror,hlog0,?_,?_⟩
  · linarith [hle 28 (by decide)]
  · have hk := Real.natLog_le_logb (2*Y) 2
    simp only [Real.logb, Nat.cast_mul, Nat.cast_ofNat] at hk
    have hdiv : Real.log (2*(Y:ℝ)) / Real.log 2 ≤ T-1 := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h2lo)]
    push_cast
    linarith

end CompositeThresholds

section IntervalRamanujanBounds

open Finset

private theorem reciprocal_square_interval (M R : ℕ) (hm : M ≤ R) :
    (∑ m ∈ Ico (M+1) (R+1), 1/(m:ℝ)^2) ≤ 2/((M:ℝ)+1) := by
  let f := fun m : ℕ => -(2/(m:ℝ))
  have step (m : ℕ) (hm' : m ∈ Ico (M+1) (R+1)) :
      1/(m:ℝ)^2 ≤ f (m+1)-f m := by
    have hr : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by have := (mem_Ico.mp hm').1; omega)
    dsimp [f]
    push_cast
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : (0:ℝ) ≤ m)]
  calc
    _ ≤ ∑ m ∈ Ico (M+1) (R+1), (f (m+1)-f m) := Finset.sum_le_sum step
    _ = f (R+1)-f (M+1) := Finset.sum_Ico_sub f (by omega)
    _ ≤ _ := by dsimp [f]; push_cast; linarith [show 0 ≤ 2/((R:ℝ)+1) by positivity]

private theorem interval_divisor_fiber {Y R d : ℕ} (hY : 0<Y) (hYR : Y≤R) (hd : 0<d)
    (s : Finset ℕ) (hs : ∀ q ∈ s, Y<q ∧ q≤R ∧ d∣q) :
    (∑ q ∈ s, (d:ℝ)/(q:ℝ)^2) ≤ 2/(Y:ℝ) := by
  classical
  let M := Y/d
  let T := s.image (fun q => q/d)
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hY' : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hbase : M*d ≤ Y := Nat.div_mul_le_self Y d
  have hstep := Nat.lt_mul_div_succ Y hd
  have hstep' : (Y:ℝ) ≤ (d:ℝ)*((M:ℝ)+1) := by exact_mod_cast hstep.le
  have hr (q : ℕ) (hq : q∈s) : M < q/d ∧ q/d ≤ R := by
    obtain ⟨hy,hR,hdiv⟩ := hs q hq
    refine ⟨?_,(Nat.div_le_self q d).trans hR⟩
    by_contra! h
    have he := Nat.mul_le_mul_right d h
    rw [Nat.div_mul_cancel hdiv] at he
    omega
  have hsub : T ⊆ Ico (M+1) (R+1) := by
    intro m hm
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hm
    have h := hr q hq
    exact mem_Ico.mpr ⟨h.1,by omega⟩
  have hinj : Set.InjOn (fun q : ℕ => q/d) (s : Set ℕ) := by
    intro a ha b hb he
    have h := congrArg (fun k => k*d) he
    simpa only [Nat.div_mul_cancel (hs a ha).2.2,Nat.div_mul_cancel (hs b hb).2.2] using h
  calc
    _ = (1/(d:ℝ))*(∑ m ∈ T, 1/(m:ℝ)^2) := by
      dsimp only [T]
      rw [sum_image hinj,Finset.mul_sum]
      apply sum_congr rfl
      intro q hq
      have he : (q:ℝ) = ((q/d:ℕ):ℝ)*(d:ℝ) := by exact_mod_cast (Nat.div_mul_cancel (hs q hq).2.2).symm
      rw [he]; field_simp
    _ ≤ (1/(d:ℝ))*(∑ m ∈ Ico (M+1) (R+1), 1/(m:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
    _ ≤ (1/(d:ℝ))*(2/((M:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_interval M R ((Nat.div_le_self Y d).trans hYR)) (by positivity)
    _ = 2/((d:ℝ)*((M:ℝ)+1)) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hY' hstep'

theorem interval_gcd_over_sq (n Y R : ℕ) (hn : 0<n) (hY : 0<Y) :
    (∑ q ∈ Ioc Y R, (q.gcd n:ℝ)/(q:ℝ)^2) ≤ 2*(n.divisors.card:ℝ)/Y := by
  classical
  by_cases hYR : Y≤R
  · let s := Ioc Y R
    have hmap (q : ℕ) (_ : q∈s) : q.gcd n ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q n,hn.ne'⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun q => (q.gcd n:ℝ)/(q:ℝ)^2)]
    calc
      _ ≤ ∑ _d ∈ n.divisors, 2/(Y:ℝ) := by
        apply sum_le_sum
        intro d hd
        let t := s.filter (fun q => q.gcd n=d)
        have he (q : ℕ) (hq : q∈t) := (mem_filter.mp hq).2
        change ∑ q ∈ t, (q.gcd n:ℝ)/(q:ℝ)^2 ≤ _
        calc
          _ = ∑ q ∈ t, (d:ℝ)/(q:ℝ)^2 := sum_congr rfl (fun q hq => by rw [he q hq])
          _ ≤ _ := interval_divisor_fiber hY hYR (Nat.pos_of_mem_divisors hd) t (by
            intro q hq
            obtain ⟨hlo,hhi⟩ := mem_Ioc.mp (mem_filter.mp hq).1
            exact ⟨hlo,hhi,he q hq ▸ Nat.gcd_dvd_left q n⟩)
      _ = _ := by simp; ring
  · rw [Ioc_eq_empty_of_le (by omega : R≤Y),sum_empty]
    positivity

theorem actualRamanujanModel_interval_norm_bound (n Y R : ℕ) (hn : 0<n) (hY : 0<Y) :
    (∑ q ∈ Ioc Y R, ‖actualRamanujanModel n q‖) ≤
      (((Nat.log 2 R:ℕ):ℝ)+1)^2 * (2*(n.divisors.card:ℝ)/Y) := by
  let K : ℝ := ((Nat.log 2 R:ℕ):ℝ)+1
  have hrow (q : ℕ) (hq : q ∈ Ioc Y R) :
      ‖actualRamanujanModel n q‖ ≤ K^2*((q.gcd n:ℝ)/(q:ℝ)^2) := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hq
    have hp : 0<q := by omega
    rw [norm_actualRamanujanModel n q (by omega)]
    split_ifs with hs
    · have hcr : |(dyadicRamanujanDivisor n q:ℝ)| ≤ (q.gcd n:ℝ) := by
        exact_mod_cast (abs_dyadicRamanujanDivisor_squarefree hs).le.trans
          (show ((q.gcd n).totient:ℤ) ≤ (q.gcd n:ℤ) by exact_mod_cast Nat.totient_le _)
      have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hp
      have hqr : 0<(q:ℝ) := by exact_mod_cast hp
      have ratio : (q:ℝ) ≤ K*(q.totient:ℝ) := by
        dsimp [K]
        exact_mod_cast (nat_le_totient_mul_log2_succ hp).trans
          (Nat.mul_le_mul_right q.totient (Nat.add_le_add_right (Nat.log_mono_right (b:=2) hhi) 1))
      have hsq := pow_le_pow_left₀ hqr.le ratio 2
      calc
        _ ≤ (q.gcd n:ℝ)/(q.totient:ℝ)^2 := by gcongr
        _ ≤ _ := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (q.gcd n))]
    · positivity
  calc
    _ ≤ ∑ q ∈ Ioc Y R, K^2*((q.gcd n:ℝ)/(q:ℝ)^2) := sum_le_sum hrow
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (interval_gcd_over_sq n Y R hn hY) (sq_nonneg _)

theorem geometricModel_interval_window_bound {n Y R : ℕ} (hn : 0<n) (hY : 0<Y) (ρ : ℕ → ℝ)
    (hw : ∀ q ∈ Ioc Y R, 0 ≤ ρ q ∧ ρ q ≤ 1/2) :
    ‖∑ q ∈ Ioc Y R, actualRamanujanModel n q *
      ((∫ t in -(ρ q)..ρ q, ‖dirichletGeometricKernel n t‖^2:ℝ):ℂ)‖ ≤
      ((n:ℝ)+1)*((((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*(n.divisors.card:ℝ)/Y)) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ Ioc Y R, ((n:ℝ)+1)*‖actualRamanujanModel n q‖ := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hl,hr⟩ := hw q hq
      rw [norm_mul,mul_comm ((n:ℝ)+1),Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
        (intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (geometricKernel_window_energy n hl hr) (norm_nonneg _)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (actualRamanujanModel_interval_norm_bound n Y R hn hY) (by positivity)

end IntervalRamanujanBounds

section AllDenominatorTubeGeometry

open MeasureTheory Set
open GoldbachDeepFourth (deepTube deepPrimeWave deepTube_cross deepTube_separation)

def intervalTubeNumerators (j : ℕ) := (Finset.range (j+1)).filter (fun a => a.Coprime (j+1))

noncomputable def allDenominatorIntervalTubeUnion (n Y R : ℕ) : Set ℝ :=
  ⋃ i ∈ (Finset.Ico Y R).sigma intervalTubeNumerators, deepTube (1/(20*(n:ℝ))) (i.1+1) i.2

theorem measurableSet_allDenominatorIntervalTubeUnion (n Y R : ℕ) : MeasurableSet (allDenominatorIntervalTubeUnion n Y R) :=
  ((Finset.Ico Y R).sigma intervalTubeNumerators).measurableSet_biUnion (fun _ _ => measurableSet_Icc)

theorem allDenominatorIntervalTubeUnion_eq (n Y R : ℕ) :
    allDenominatorIntervalTubeUnion n Y R =
      ⋃ q ∈ Finset.Ioc Y R, ⋃ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        deepTube (1/(20*(n:ℝ))) q a := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hi
    have hlo : Y≤j := (Finset.mem_Ico.mp hj).1
    have hhi : j<R := (Finset.mem_Ico.mp hj).2
    exact Set.mem_iUnion₂.mpr ⟨j+1,Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,
      Set.mem_iUnion₂.mpr ⟨a,ha,ht⟩⟩
  · intro ht
    obtain ⟨q,hq,h⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp h
    have hq' := Finset.mem_Ioc.mp hq
    have he : q-1+1=q := by omega
    have hj : q-1 ∈ Finset.Ico Y R := Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    refine Set.mem_iUnion₂.mpr ⟨⟨q-1,a⟩,Finset.mem_sigma.mpr ⟨hj,?_⟩,?_⟩
    · change a ∈ (Finset.range (q-1+1)).filter (fun a => a.Coprime (q-1+1))
      simpa only [he] using ha
    · change t ∈ deepTube (1/(20*(n:ℝ))) (q-1+1) a
      simpa only [he] using ht

noncomputable def deepTruePrimeSignedIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  (deepPrimeWave n t)^2 * GoldbachDeepFourth.ExtendedArcCoefficient.E (-(n:ℝ)*t)

private theorem continuous_deepSigned (n : ℕ) : Continuous (deepTruePrimeSignedIntegrand n) := by
  unfold deepTruePrimeSignedIntegrand deepPrimeWave GoldbachDeepFourth.ExtendedArcCoefficient.E
  fun_prop

private theorem reduced_tubes_disjoint {n R q r a b : ℕ} (hn : 0 < n) (hsize : R^2 ≤ n)
    (hq : 0<q) (hr : 0<r) (hqY : q ≤ R) (hrY : r ≤ R)
    (ha : a.Coprime q) (hb : b.Coprime r) (hne : (q,a) ≠ (r,b)) :
    Disjoint (deepTube (1/(20*(n:ℝ))) q a) (deepTube (1/(20*(n:ℝ))) r b) := by
  have hsep := deepTube_separation hq hr (deepTube_cross hq hr ha hb hne)
  have hqr : q*r ≤ n := (Nat.mul_le_mul hqY hrY).trans (by simpa [pow_two] using hsize)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hrec : 1/(n:ℝ) ≤ 1/((q:ℝ)*r) :=
    one_div_le_one_div_of_le (mul_pos hq0 hr0) (by exact_mod_cast hqr)
  have hlen : 1/(20*(n:ℝ)) + 1/(20*n) < 1/n := by field_simp; linarith
  refine Set.disjoint_left.mpr ?_
  rintro t ⟨ht₁,ht₂⟩ ⟨ht₃,ht₄⟩
  have hd : |(a:ℝ)/q-b/r| ≤ 1/(20*(n:ℝ))+1/(20*n) := abs_le.mpr ⟨by linarith,by linarith⟩
  linarith only [hrec,hsep,hd,hlen]

private theorem reduced_tube_row_integral (n j : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
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

theorem allDenominatorIntervalTubes_pairwise {n Y R : ℕ} (hsize : R^2≤n) :
    (↑((Finset.Ico Y R).sigma intervalTubeNumerators) : Set (Σ _ : ℕ, ℕ)).Pairwise
      (fun i k => Disjoint (deepTube (1/(20*(n:ℝ))) (i.1+1) i.2)
        (deepTube (1/(20*(n:ℝ))) (k.1+1) k.2)) := by
  rintro ⟨j,a⟩ hj ⟨k,b⟩ hk hne
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hj
  obtain ⟨hk,hb⟩ := Finset.mem_sigma.mp hk
  have hj' : j < R := (Finset.mem_Ico.mp hj).2
  have hk' : k < R := (Finset.mem_Ico.mp hk).2
  have hn0 : 0<n := (Nat.pow_pos (by omega : 0<R) (n:=2)).trans_le hsize
  apply reduced_tubes_disjoint hn0 hsize (Nat.succ_pos j) (Nat.succ_pos k)
    (by omega) (by omega) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  rintro he
  have ej : j=k := by have := congrArg Prod.fst he; simpa using this
  have ea : a=b := congrArg Prod.snd he
  exact hne (by subst k; subst b; rfl)

theorem allDenominatorIntervalTubeUnion_signed_integral {n Y R : ℕ} (hsize : R^2 ≤ n) :
    (∫ t in allDenominatorIntervalTubeUnion n Y R, deepTruePrimeSignedIntegrand n t) =
      ∑ j ∈ Finset.Ico Y R, truePrimeSignedRow n (j+1) (1/(20*(n:ℝ))) := by
  classical
  let s := (Finset.Ico Y R).sigma intervalTubeNumerators
  let I := fun i : Σ _ : ℕ, ℕ => deepTube (1/(20*(n:ℝ))) (i.1+1) i.2
  have hd : (↑s : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i j => Disjoint (I i) (I j)) :=
    allDenominatorIntervalTubes_pairwise hsize
  change (∫ t in ⋃ i ∈ s, I i, deepTruePrimeSignedIntegrand n t) = _
  rw [integral_biUnion_finset (s := I) s (fun _ _ => measurableSet_Icc) hd
    (fun _ _ => (continuous_deepSigned n).continuousOn.integrableOn_Icc)]
  dsimp only [s,I]
  rw [Finset.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => reduced_tube_row_integral n j (by positivity)

private theorem reducedTube_inside_unit {n q a : ℕ} (hn : 0<n) (hq : 0<q)
    (hqn : q ≤ n) (ha : 0<a) (haq : a<q) :
    deepTube (1/(20*(n:ℝ))) q a ⊆ Set.Icc 0 1 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrad : 1/(20*(n:ℝ)) ≤ 1/q :=
    one_div_le_one_div_of_le hq0 (by linarith [show (q:ℝ) ≤ n by exact_mod_cast hqn])
  have hlo : 1/(q:ℝ) ≤ (a:ℝ)/q := (div_le_div_iff_of_pos_right hq0).mpr (by exact_mod_cast ha)
  have hsum : (a:ℝ)/q+1/q ≤ 1 := by
    rw [← add_div, div_le_one hq0]
    exact_mod_cast (Nat.succ_le_of_lt haq)
  rintro t ⟨ht₁,ht₂⟩
  exact ⟨by linarith,by linarith⟩

theorem allDenominatorIntervalTubeUnion_inside_unit {n Y R : ℕ} (hY : 0 < Y) (hn : R^2 ≤ n) :
    allDenominatorIntervalTubeUnion n Y R ⊆ Set.Icc 0 1 := by
  intro t ht
  obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hi
  obtain ⟨haj,hcop⟩ := Finset.mem_filter.mp ha
  have hlt : a < j+1 := Finset.mem_range.mp haj
  have hlo : Y ≤ j := (Finset.mem_Ico.mp hj).1
  have hhi : j < R := (Finset.mem_Ico.mp hj).2
  have hsize : R ≤ n := by
    have hR : 1 ≤ R := by omega
    nlinarith only [hn,Nat.mul_le_mul_left R hR]
  have hapos : 0<a := by
    by_contra! hz
    have h0 : a=0 := by omega
    have hb : j+1=1 := by simpa [h0] using hcop
    omega
  exact reducedTube_inside_unit (by omega) (Nat.succ_pos j) (by omega) hapos hlt ht

theorem allDenominatorIntervalTubeUnion_inside_deep {n Y R H : ℕ}
    (hsep : R*(H+Y) < n) :
    allDenominatorIntervalTubeUnion n Y R ⊆ (GoldbachDeepFourth.coreArcBand n H 0 Y)ᶜ := by
  intro t ht hcore
  obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hi
  let q := j+1
  have hq : 0<q := Nat.succ_pos j
  have hlo : Y < q := Nat.lt_succ_of_le (Finset.mem_Ico.mp hj).1
  have hhi : q ≤ R := (Finset.mem_Ico.mp hj).2
  have hc : a.Coprime q := (Finset.mem_filter.mp ha).2
  rcases hcore with ⟨r,b,hr,hrY,_,hb,htb⟩
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hH0 : 0 ≤ (H:ℝ) := Nat.cast_nonneg _
  have hA := deepTube_separation hq hr (deepTube_cross hq hr hc hb (by
    intro e
    have he : q=r := congrArg Prod.fst e
    omega))
  have hle : 1/(20*(n:ℝ)) ≤ 1/n :=
    one_div_le_one_div_of_le hn0 (by linarith)
  have hnum : q*(H+r) < n :=
    lt_of_le_of_lt (Nat.mul_le_mul hhi (Nat.add_le_add_left hrY H)) hsep
  have hgap : 1/(n:ℝ)+H/(r*n) < 1/(q*r) := calc
    _ = ((q:ℝ)*(H+r))/(q*r*n) := by field_simp; ring
    _ < (n:ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hnum)
    _ = _ := by field_simp
  change t ∈ deepTube (1/(20*(n:ℝ))) q a at ht
  obtain ⟨ht1,ht2⟩ := ht
  obtain ⟨hb1,hb2⟩ := abs_le.mp htb
  have hclose : |(a:ℝ)/q-b/r| ≤ 1/(n:ℝ)+H/(r*n) := abs_le.mpr ⟨by linarith,by linarith⟩
  exact (not_lt_of_ge (hA.trans hclose)) hgap

private theorem sum_succ_interval {Y R : ℕ} (f : ℕ → ℂ) :
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

theorem allDenominatorIntervalTubeUnion_signed_sub_change {n Y R : ℕ} (hY : 0<Y) (hsize : R^2 ≤ n) :
    (∫ t in allDenominatorIntervalTubeUnion n Y R, deepTruePrimeSignedIntegrand n t) -
      (∑ j ∈ Finset.Ico Y R, primeArcSignedChange (j+1) n (1/(20*(n:ℝ)))) =
      ∑ q ∈ Finset.Ioc Y R, actualRamanujanModel n q *
        ((∫ t in -(1/(20*(n:ℝ)))..(1/(20*(n:ℝ))), ‖dirichletGeometricKernel n t‖^2:ℝ):ℂ) := by
  let ρ := 1/(20*(n:ℝ))
  let m := fun q => actualRamanujanModel n q * ((∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2:ℝ):ℂ)
  rw [allDenominatorIntervalTubeUnion_signed_integral hsize]
  change (∑ j ∈ Finset.Ico Y R, truePrimeSignedRow n (j+1) ρ) -
    (∑ j ∈ Finset.Ico Y R, primeArcSignedChange (j+1) n ρ) = ∑ q ∈ Finset.Ioc Y R, m q
  rw [← sum_succ_interval m,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := Finset.mem_Ico.mp hj
  rw [truePrimeSignedRow_eq_change_add_model n (j+1) (by omega)]
  exact add_sub_cancel_left _ _

theorem allDenominatorIntervalTubeUnion_model_bound {n Y R : ℕ} (hn : 0<n) (hY : 0<Y)
    (hsize : R^2 ≤ n) :
    ‖(∫ t in allDenominatorIntervalTubeUnion n Y R, deepTruePrimeSignedIntegrand n t) -
      (∑ j ∈ Finset.Ico Y R, primeArcSignedChange (j+1) n (1/(20*(n:ℝ))))‖ ≤
       ((n:ℝ)+1)*((((Nat.log 2 R:ℕ):ℝ)+1)^2*(2*(n.divisors.card:ℝ)/Y)) := by
  rw [allDenominatorIntervalTubeUnion_signed_sub_change hY hsize]
  apply geometricModel_interval_window_bound hn hY (fun _ => 1/(20*(n:ℝ)))
  intro q _
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by positivity, (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<2)).mpr (by linarith)⟩

/-- The original dyadic family as a specialization of the interval family. -/
noncomputable abbrev allDenominatorTubeUnion (n Y : ℕ) := allDenominatorIntervalTubeUnion n Y (2*Y)

theorem measurableSet_allDenominatorTubeUnion (n Y : ℕ) : MeasurableSet (allDenominatorTubeUnion n Y) :=
  measurableSet_allDenominatorIntervalTubeUnion n Y (2*Y)

private theorem dyadic_tube_size {n Y : ℕ} (hY : 4≤Y) (hn : Y^3≤n) : (2*Y)^2 ≤ n := by
  nlinarith only [hn,Nat.mul_le_mul_left (Y*Y) hY]

theorem allDenominatorTubeUnion_signed_integral {n Y : ℕ} (hY : 4≤Y) (hn : Y^3≤n) :
    (∫ t in allDenominatorTubeUnion n Y, deepTruePrimeSignedIntegrand n t) =
      ∑ j ∈ Finset.Ico Y (2*Y), truePrimeSignedRow n (j+1) (1/(20*(n:ℝ))) :=
  allDenominatorIntervalTubeUnion_signed_integral (dyadic_tube_size hY hn)

theorem allDenominatorTubeUnion_inside_unit {n Y : ℕ} (hY : 4≤Y) (hn : Y^3≤n) :
    allDenominatorTubeUnion n Y ⊆ Set.Icc 0 1 :=
  allDenominatorIntervalTubeUnion_inside_unit (by omega) (dyadic_tube_size hY hn)

theorem allDenominatorTubeUnion_inside_deep {n Y H : ℕ} (hH : 2*Y≤H) (hsep : 2*H*(2*Y)<n) :
    allDenominatorTubeUnion n Y ⊆ (GoldbachDeepFourth.coreArcBand n H 0 Y)ᶜ := by
  apply allDenominatorIntervalTubeUnion_inside_deep
  have h1 : H+Y ≤ 2*H := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left (2*Y) h1) (by simpa only [Nat.mul_comm (2*H) (2*Y)] using hsep)

theorem primeBandTubeUnion_subset_allDenominator (n Y : ℕ) :
    primeBandTubeUnion Y (1/(20*(n:ℝ))) ⊆ allDenominatorTubeUnion n Y := by
  intro t ht
  obtain ⟨q,hq,ha⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp ha
  obtain ⟨hlo,hhi,hprime⟩ := GoldbachDeepFourth.FourthMomentBand.mem_primes.mp hq
  obtain ⟨ha1,haq⟩ := Finset.mem_Ico.mp ha
  have he : q-1+1 = q := by omega
  have hidx : q-1 ∈ Finset.Ico Y (2*Y) := Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  refine Set.mem_iUnion₂.mpr ⟨⟨q-1,a⟩, Finset.mem_sigma.mpr ⟨hidx,?_⟩,?_⟩
  · change a ∈ (Finset.range (q-1+1)).filter (fun a => a.Coprime (q-1+1))
    rw [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haq,
      (hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha1 haq)).symm⟩
  · change t ∈ deepTube (1/(20*(n:ℝ))) (q-1+1) a
    simpa only [he] using ht

end AllDenominatorTubeGeometry

section NarrowCoreDeletion

open Filter MeasureTheory

open scoped Topology

private theorem coreArcBand_measurable_for_deletion (n R A B : ℕ) :
    MeasurableSet (coreArcBand n R A B) := by
  simp only [coreArcBand, Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  apply (MeasurableSet.const _).inter
  exact measurableSet_le
    (show Continuous (fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|) by fun_prop).measurable measurable_const

theorem primeArcMass_eq_setIntegral_re_of_subset_Icc (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) (hi : s ⊆ Set.Icc 0 1) :
    primeArcMass s n = (∫ t in s, primeSquareKernel n t).re := by
  unfold primeArcMass
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator hs, Set.inter_eq_right.mpr hi]

theorem dyadic_floor_from_narrow_core_after_deletion
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (S : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (S n))
    (hi : ∀ᶠ n in atTop, S n ⊆ Set.Icc 0 1)
    (hd : ∀ᶠ n in atTop, S n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ)
    (hsmall : Tendsto (fun n : ℕ => ‖∫ t in S n, primeSquareKernel n t‖ / (n:ℝ))
      atTop (𝓝 0))
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(n:ℝ)/300 ≤ primeArcMass ((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ S n) n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n := by
  have hrest : ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(n:ℝ)/288 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ n := by
    obtain ⟨N,hN⟩ := rest
    apply eventually_atTop.mp
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1:ℕ), hi, hd,
      hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/7200))] with n hn hn1 hin hdn hsn
    intro he
    have hp : (0:ℝ)<n := by exact_mod_cast hn1
    have hlt : ‖∫ t in S n, primeSquareKernel n t‖ < (1/7200)*(n:ℝ) :=
      (div_lt_iff₀ hp).mp hsn
    have hneg := (abs_le.mp (Complex.abs_re_le_norm (∫ t in S n, primeSquareKernel n t))).1
    rw [primeArcMass_partition (hs n) (coreArcBand_measurable_for_deletion ..).compl hdn,
      primeArcMass_eq_setIntegral_re_of_subset_Icc n (hs n) hin]
    linarith only [hlt,hneg,hN n hn he]
  obtain ⟨N,hN⟩ := dyadic_floor_from_narrow_core_budget hm h₁ h₂ h₃ major hrest
  refine ⟨1/576,N,by norm_num,fun X n hX hXn hn he => ?_⟩
  linarith only [hN X n hX hXn hn he]

end NarrowCoreDeletion

section CompositeShell
open Finset MeasureTheory

theorem signed_change_on_dyadic_shell {n Y : ℕ} (hY : 0<Y) {ρ D s : ℝ}
    (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) (hD : 0 ≤ D) (hs : 0 < s)
    (hp : ∀ j ∈ Ico Y (2*Y), ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ D) :
    ‖∑ j ∈ Ico Y (2*Y), primeArcSignedChange (j+1) n ρ‖ ≤
      (1+s)*(8*ρ*(Y:ℝ)^2*((D*(1+2*Real.pi*n*ρ))^2+(Real.log (2*(Y:ℝ)))^2)) +
      s⁻¹*((n:ℝ)+1)*((Nat.log 2 (2*Y):ℕ)+1:ℝ) := by
  let J := Ico Y (2*Y)
  let A := (D*(1+2*Real.pi*n*ρ))^2+(Real.log (2*(Y:ℝ)))^2
  let K := Nat.log 2 (2*Y)+1
  have hy : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hc : J.card = Y := by simp [J,Nat.card_Ico]; omega
  have he : (∑ j ∈ J, 4*ρ*((j+1).totient:ℝ)*((D*(1+2*Real.pi*n*ρ))^2+(Real.log (j+1:ℕ))^2)) ≤
      8*ρ*(Y:ℝ)^2*A := by
    calc
      _ ≤ ∑ _j ∈ J, 4*ρ*(2*(Y:ℝ))*A := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hq : j+1 ≤ 2*Y := (Finset.mem_Ico.mp hj).2
        have ht : ((j+1).totient:ℝ) ≤ 2*(Y:ℝ) := by exact_mod_cast (Nat.totient_le _).trans hq
        have hlog : 0 ≤ Real.log (j+1:ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j+1 by omega))
        have hl := Real.log_le_log (by positivity : 0 < ((j+1:ℕ):ℝ)) (by exact_mod_cast hq : ((j+1:ℕ):ℝ) ≤ 2*(Y:ℝ))
        have hsq := pow_le_pow_left₀ hlog hl 2
        dsimp [A]; gcongr
      _ = _ := by rw [Finset.sum_const,hc,nsmul_eq_mul]; ring
  have hm : (∑ j ∈ J, ((j+1).totient:ℝ)*∫ t in -ρ..ρ, ‖geometricPrimeArcModel (j+1) n t‖^2) ≤
      ((n:ℝ)+1)*(K:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ J, ((n:ℝ)+1)*((K:ℝ)/Y) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hq := Finset.mem_Ico.mp hj
        have hφ : 0 < (((j+1).totient):ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos j)
        have hrat : 1/(((j+1).totient):ℝ) ≤ (K:ℝ)/Y := by
          apply (div_le_div_iff₀ hφ hy).mpr
          rw [one_mul]
          have hK : Nat.log 2 (j+1)+1 ≤ K := Nat.succ_le_succ (Nat.log_mono_right hq.2)
          exact_mod_cast hq.1.trans ((Nat.le_succ j).trans ((nat_le_totient_mul_log2_succ (Nat.succ_pos j)).trans
            (Nat.mul_le_mul_right _ hK)))
        refine (geometricPrimeArcModel_window_energy (j+1) n hρ hhalf (principal_unitGauss_norm_le_one _)).trans ?_
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ (n:ℝ)+1)
      _ = _ := by rw [Finset.sum_const,hc,nsmul_eq_mul]; field_simp
  have h := primeArc_signed_band_of_prefix J n (fun _ => ρ) (fun _ => D) (fun _ _ => hρ)
    (fun _ _ => hD) hs hp
  refine h.trans ?_
  change _ ≤ (1+s)*(8*ρ*(Y:ℝ)^2*A) + _
  have hpK : (K:ℝ) = ((Nat.log 2 (2*Y):ℕ):ℝ)+1 := by simp [K]
  rw [← hpK, mul_assoc s⁻¹]
  exact add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) (mul_le_mul_of_nonneg_left hm (by positivity))
end CompositeShell


open Finset in
theorem trueSigned_dyadic_prefix_bound {n Y : ℕ} (hn : 0<n) (hY : 0<Y) {ρ D s : ℝ}
    (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) (hD : 0 ≤ D) (hs : 0 < s)
    (hp : ∀ j ∈ Ico Y (2*Y), ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ D) :
    ‖∑ j ∈ Ico Y (2*Y), truePrimeSignedRow n (j+1) ρ‖ ≤
      (1+s)*(8*ρ*(Y:ℝ)^2*((D*(1+2*Real.pi*n*ρ))^2+(Real.log (2*(Y:ℝ)))^2)) +
      s⁻¹*((n:ℝ)+1)*((Nat.log 2 (2*Y):ℕ)+1:ℝ) +
      ((n:ℝ)+1)*((((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y) := by
  refine (truePrimeSignedRow_dyadic_bound hn hY (fun _ => ρ) (fun _ _ => ⟨hρ,hhalf⟩)).trans ?_
  exact add_le_add (signed_change_on_dyadic_shell hY hρ hhalf hD hs hp) le_rfl

private theorem dyadic_budget_power_bound {T Y D L K d A : ℝ} (ht : 1 ≤ T)
    (hy : 0 < Y) (hy₁ : Y ≤ T^16) (hy₂ : T^16/2 ≤ Y)
    (hd : 0 ≤ D) (hdu : D ≤ T^28) (hl : 0 ≤ L) (hlu : L ≤ T^28)
    (hk : 0 ≤ K) (hku : K ≤ T) (hdv : 0 ≤ d) (hA : 0 ≤ A) (hdc : d ≤ A*T^12) :
    (1+T^4)*(8*(1/(20*T^48))*Y^2*((D*(1+2*Real.pi*T^48*(1/(20*T^48))))^2+L^2)) +
      (T^4)⁻¹*(T^48+1)*K + (T^48+1)*(K^2*d/Y) ≤
      (4*((1+Real.pi/10)^2+1)+2+4*A)*T^46 := by
  have ht0 : 0<T := by linarith
  have he4 : 1 ≤ T^4 := one_le_pow₀ ht
  have he48 : 1 ≤ T^48 := one_le_pow₀ ht
  have hx : 1+T^4 ≤ 2*T^4 := by linarith
  have hx' : T^48+1 ≤ 2*T^48 := by linarith
  have hI : 1/Y ≤ 2/T^16 := (div_le_div_iff₀ hy (by positivity)).mpr (by linarith)
  have hπ : 0 ≤ 1+Real.pi/10 := by positivity
  let P := (1+Real.pi/10)^2+1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hf : 1+2*Real.pi*T^48*(1/(20*T^48)) = 1+Real.pi/10 := by field_simp; ring
  rw [hf]
  have hz : (D*(1+Real.pi/10))^2+L^2 ≤ T^56*P := by
    calc
      _ ≤ (T^28*(1+Real.pi/10))^2+(T^28)^2 := by gcongr
      _ = _ := by dsimp [P]; ring
  have h1 : (1+T^4)*(8*(1/(20*T^48))*Y^2*((D*(1+Real.pi/10))^2+L^2)) ≤
      4*P*T^46 := by
    calc
      _ ≤ (2*T^4)*(8*(1/(20*T^48))*(T^16)^2*(T^56*P)) := by gcongr
      _ = (4/5:ℝ)*P*T^44 := by field_simp; ring
      _ ≤ 4*P*T^46 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by norm_num) hP
        · exact pow_le_pow_right₀ ht (by decide)
        · positivity
        · positivity
  have h2 : (T^4)⁻¹*(T^48+1)*K ≤ 2*T^46 := by
    calc
      _ ≤ (T^4)⁻¹*(2*T^48)*T := by gcongr
      _ = 2*T^45 := by field_simp
      _ ≤ _ := by gcongr; decide
  have h3 : (T^48+1)*(K^2*d/Y) ≤ 4*A*T^46 := by
    rw [show K^2*d/Y = K^2*d*(1/Y) by ring]
    calc
      _ ≤ (2*T^48)*(T^2*(A*T^12)*(2/T^16)) := by gcongr
      _ = _ := by field_simp; ring
  change _ ≤ (4*P+2+4*A)*T^46
  linarith only [h1,h2,h3]

open Finset in
theorem trueSigned_shell_power_at_scale {n Y : ℕ} {T : ℝ} (hn : 0<n) (hY : 0<Y)
    (ht : 1≤T) (h48 : T^48 = (n:ℝ)) (hy₁ : (Y:ℝ) ≤ T^16) (hy₂ : T^16/2 ≤ (Y:ℝ))
    (hlu : Real.log (2*(Y:ℝ)) ≤ T^28) (hku : ((Nat.log 2 (2*Y):ℕ):ℝ)+1 ≤ T)
    (hp : ∀ j ∈ Ico Y (2*Y), ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ T^28) :
    ‖∑ j ∈ Ico Y (2*Y), truePrimeSignedRow n (j+1) (1/(20*(n:ℝ)))‖ ≤ (4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12)*T^46 := by
  have ht0 : 0<T := by linarith
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hyR : 1 ≤ (Y:ℝ) := by exact_mod_cast hY
  have hτ : (n.divisors.card:ℝ) ≤ (2:ℝ)^12*T^12 := by
    apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by positivity)
    have h : (n.divisors.card:ℝ)^4 ≤ (2:ℝ)^48*n := by exact_mod_cast divisor_count_fourth_le n
    refine h.trans_eq ?_
    rw [← h48]
    ring
  have hh := trueSigned_dyadic_prefix_bound hn hY (by positivity : 0 ≤ 1/(20*(n:ℝ)))
    (show 1/(20*(n:ℝ))≤1/2 by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith)
    (by positivity : 0 ≤ T^28) (by positivity : 0 < T^4) hp
  refine hh.trans ?_
  rw [← h48]
  exact dyadic_budget_power_bound ht (by exact_mod_cast hY) hy₁ hy₂ (by positivity) le_rfl
    (Real.log_nonneg (by linarith)) hlu (by positivity) hku (by positivity) (by positivity) hτ

section FullDenominatorBand

open Finset Filter
open scoped Topology

/-- Uniform centered prefix estimate at the denominators used in the shell. -/
def dyadicCharacterPrefixBound (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j ∈ Ico (medDeskD n) (2*medDeskD n), ∀ χ, ∀ k ≤ n,
    ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2

/-- A power saving for the signed sum over the whole denominator shell at radius 1/(20n). -/
theorem trueSigned_shell_power {C : ℝ} (hc : 0 ≤ C) (hp : dyadicCharacterPrefixBound C) :
    ∀ᶠ n : ℕ in atTop, ‖∑ j ∈ Ico (medDeskD n) (2*medDeskD n),
      truePrimeSignedRow n (j+1) (1/(20*(n:ℝ)))‖ ≤
      (4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12)*(n:ℝ)^(23/24:ℝ) := by
  filter_upwards [medDesk_composite_shell_thresholds C hc,hp,eventually_ge_atTop (1:ℕ)] with n h hχ hn
  let T := (n:ℝ)^(1/48:ℝ)
  obtain ⟨ht,h48,hy,h16,hlow,hd,_,hl,hk⟩ := h
  change 1 ≤ T at ht
  change T^48 = (n:ℝ) at h48
  have hK : ((Nat.log 2 (2*medDeskD n):ℕ):ℝ)+1 ≤ T := by simpa [T] using hk
  have he := trueSigned_shell_power_at_scale hn hy ht h48 h16 hlow hl hK
    (fun j hj χ k hk => (hχ j hj χ k hk).trans hd)
  have h46 : T^46 = (n:ℝ)^(23/24:ℝ) := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  rwa [h46] at he

theorem trueSigned_shell_over_n_tendsto {C : ℝ} (hc : 0 ≤ C) (hp : dyadicCharacterPrefixBound C) :
    Tendsto (fun n : ℕ => ‖∑ j ∈ Ico (medDeskD n) (2*medDeskD n),
      truePrimeSignedRow n (j+1) (1/(20*(n:ℝ)))‖/(n:ℝ)) atTop (𝓝 0) := by
  let A : ℝ := 4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/24)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun n : ℕ => A*(n:ℝ)^(-(1/24:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hpow.const_mul A
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)
  · filter_upwards [trueSigned_shell_power hc hp,eventually_ge_atTop (1:ℕ)] with n h hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    refine (div_le_div_of_nonneg_right h hnR.le).trans_eq ?_
    change A*(n:ℝ)^(23/24:ℝ)/n = _
    rw [mul_div_assoc]
    rw [show (n:ℝ)^(23/24:ℝ)/(n:ℝ) = (n:ℝ)^(-(1/24:ℝ)) by
      conv_lhs => rhs; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_sub hnR]; norm_num]
end FullDenominatorBand
section ParentAfterShell
open Filter MeasureTheory
open scoped Topology

theorem frozen_shell_geometry :
    ∀ᶠ n : ℕ in atTop, allDenominatorTubeUnion n (medDeskD n) ⊆ Set.Icc 0 1 ∧
      allDenominatorTubeUnion n (medDeskD n) ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ := by
  filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget] with n hn
  obtain ⟨_,hy,hcube,hH,hsep⟩ := hn
  refine ⟨allDenominatorTubeUnion_inside_unit ((by decide : 4 ≤ 192^4).trans hy) hcube,?_⟩
  intro t ht ht'
  apply allDenominatorTubeUnion_inside_deep hH hsep ht
  obtain ⟨q,a,hq,hu,ha,hcop,hw⟩ := ht'
  refine ⟨q,a,hq,hu,ha,hcop,hw.trans ?_⟩
  have he : medDeskQ n ≤ (256*medDeskD n)*medDeskQ n := by
    have hpos : 1 ≤ 256*medDeskD n := by change 192^4 ≤ medDeskD n at hy; omega
    simpa using Nat.mul_le_mul_right (medDeskQ n) hpos
  apply div_le_div_of_nonneg_right (by exact_mod_cast he) (by positivity)

theorem frozen_shell_integral_eq :
    ∀ᶠ n : ℕ in atTop, (∫ t in allDenominatorTubeUnion n (medDeskD n), primeSquareKernel n t) =
      ∑ j ∈ Finset.Ico (medDeskD n) (2*medDeskD n), truePrimeSignedRow n (j+1) (1/(20*(n:ℝ))) := by
  filter_upwards [GoldbachDeepFourth.eventually_deep_fourth_budget] with n hn
  exact allDenominatorTubeUnion_signed_integral ((by decide : 4 ≤ 192^4).trans hn.2.1) hn.2.2.1

theorem frozen_shell_integral_power {C : ℝ} (hc : 0 ≤ C) (hp : dyadicCharacterPrefixBound C) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in allDenominatorTubeUnion n (medDeskD n), primeSquareKernel n t‖ ≤
      (4*((1+Real.pi/10)^2+1)+2+4*(2:ℝ)^12)*(n:ℝ)^(23/24:ℝ) := by
  filter_upwards [frozen_shell_integral_eq,trueSigned_shell_power hc hp] with n he h
  rwa [he]

theorem dyadic_floor_after_denominator_shell
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    {C : ℝ} (hc : 0 ≤ C) (hp : dyadicCharacterPrefixBound C)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/300 ≤ primeArcMass
      ((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ allDenominatorTubeUnion n (medDeskD n)) n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n := by
  apply dyadic_floor_from_narrow_core_after_deletion hm h₁ h₂ h₃ major
    (fun n => allDenominatorTubeUnion n (medDeskD n)) (fun _ => measurableSet_allDenominatorTubeUnion ..)
    (frozen_shell_geometry.mono fun _ h => h.1) (frozen_shell_geometry.mono fun _ h => h.2) _ rest
  apply (trueSigned_shell_over_n_tendsto hc hp).congr'
  filter_upwards [frozen_shell_integral_eq] with n he
  rw [he]

end ParentAfterShell

end GoldbachPartial
