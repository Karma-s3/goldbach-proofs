import PinnedUpstream316
import SmallDivisorCompletedSquare
import FejerMajorWindow
import HighNaturalHalfVolume

namespace GoldbachPartial
open Finset Filter MeasureTheory
open scoped Topology
open GoldbachMajorArc

theorem pinnedCoefficient_eq_ramanujan (n q:ℕ) (hq:0<q) :
    (GoldbachMajorArc.coefficient q n).re = (dyadicRamanujanDivisor n q:ℝ)*
      ((ArithmeticFunction.moebius q:ℝ)/(q.totient:ℝ))^2 := by
  have hr (h:ℕ) : ram q h=(dyadicRamanujanDivisor h q:ℂ) := actualRamanujan_eq_divisor h q hq
  have hμ : dyadicRamanujanDivisor 1 q=ArithmeticFunction.moebius q := by simp [dyadicRamanujanDivisor]
  rw [GoldbachMajorArc.coefficient,hr,hr,hμ]
  rw [←Complex.ofReal_intCast,←Complex.ofReal_natCast,←Complex.ofReal_div,←Complex.ofReal_pow,
    ←Complex.ofReal_intCast,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re]
  ring

theorem correctedMajorModel_floor {n:ℕ} (he:Even n) (hsep:2*(cutoff n)^2<n) (hQ:8≤cutoff n)
    {v:ℝ} (hv:v≤1/2) :
    7*(n:ℝ)/48 ≤ (modeledContribution n).re-
      v*((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n (medDeskQ n) := by
  let P := cutoff n
  let T := v*((n-1:ℕ):ℝ)
  let W (q:ℕ) := if q∈Icc 1 P then kernelMass n (width n q)-T else 0
  have hn : 0<n := by omega
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hP8 : (8:ℝ)≤P := by exact_mod_cast hQ
  have hP : (0:ℝ)<P := by linarith
  have hPn : 2*(P:ℝ)≤n := by
    exact_mod_cast (show 2*P≤n by have hh : P≤P^2 := Nat.le_self_pow (by decide:2≠0) _;change 2*P^2<n at hsep;omega)
  have hT : T≤(n:ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) (n-1))
    have h' : ((n-1:ℕ):ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
    dsimp only [T];linarith
  have hmass {q:ℕ} (hq:q∈Icc 1 P) :
      (n:ℝ)+2-(q:ℝ)*n/(2*P) ≤kernelMass n (width n q) := by
    obtain ⟨hl,_hr⟩ := mem_Icc.mp hq
    have hqr : (1:ℝ)≤q := by exact_mod_cast hl
    have hw : (P:ℝ)/((q:ℝ)*n)≤1/2 := by
      apply (div_le_iff₀ (mul_pos (by linarith) hN)).mpr
      nlinarith only [hPn,mul_nonneg (sub_nonneg.mpr hqr) hN.le]
    exact fejer_denominator_window_lower hn hl hP hw
  have hW (q:ℕ) : 0≤W q := by
    by_cases hq : q∈Icc 1 P
    · have hqP : (q:ℝ)≤P := by exact_mod_cast (mem_Icc.mp hq).2
      have hfrac : (q:ℝ)*n/(2*P)≤(n:ℝ)/2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hqP) hN.le]
      rw [show W q=kernelMass n (width n q)-T by simp only [W,ite_eq_left hq]]
      linarith only [hmass hq,hT,hfrac]
    · simp only [W,ite_eq_right hq,le_refl]
  have hmono (i j:ℕ) (hi : 0 < i) (hij:i≤j) : W j≤W i := by
    by_cases hj : j∈Icc 1 P
    · have hi' := mem_Icc.mpr (And.intro hi (hij.trans (mem_Icc.mp hj).2))
      simp only [W,ite_eq_left hj,ite_eq_left hi',sub_le_sub_iff_right]
      apply kernelMass_mono (by unfold width;positivity)
      unfold width
      exact div_le_div_of_nonneg_left hP.le (mul_pos (by exact_mod_cast hi) hN)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hN.le)
    · simpa only [W,ite_eq_right hj] using hW i
  have hzero (q:ℕ) (hq:P<q) : W q=0 := by
    exact ite_eq_right (fun hh=>Nat.not_le_of_lt hq (mem_Icc.mp hh).2)
  have har := arithmetic_floor (Q:=P) he W hW hmono hzero
  have h₁ : 1∈Icc 1 P := mem_Icc.mpr ⟨le_rfl,by change 8≤P at hQ;omega⟩
  have hf1 : (1:ℝ)*n/(2*P)≤(n:ℝ)/16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hP8) hN.le]
  have hone : 7*(n:ℝ)/48≤W 1/3 := by
    simp only [W,ite_eq_left h₁];have h := hmass h₁
    simp only [Nat.cast_one] at h
    linarith only [h,hf1,hT]
  apply (hone.trans har).trans_eq
  unfold modeledContribution finiteRamanujanSingularSum
  rw [Complex.re_sum,mul_sum,show medDeskQ n=cutoff n from rfl,←sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [show W q=kernelMass n (width n q)-T by simp only [W,ite_eq_left hq],Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,pinnedCoefficient_eq_ramanujan n q (mem_Icc.mp hq).1]
  dsimp only [T]
  ring

theorem correctedMajorContribution_floor :
    ∀ᶠ n:ℕ in atTop,Even n →
      (n:ℝ)/8 ≤ primeArcMass (rationalArcSet (medDeskQ n) n) n -
        volume.real (highNaturalPrimeTubes n)*((n-1:ℕ):ℝ)*
          finiteRamanujanSingularSum n (medDeskQ n) := by
  have hsmall := totalArcError_sublinear.eventually_lt_const (by norm_num : (0:ℝ)<1/48)
  have hcut := Pinned316.GoldbachMajorArc.cutoff_tendsto.eventually_ge_atTop 8
  filter_upwards [hsmall,hcut,cutoff_separated,high_tube_volume_eventually_half] with n herr hQ hsep hv
  intro he
  have hn : 0<n := by omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have he' := (div_lt_iff₀ hn').mp herr
  have hm := correctedMajorModel_floor he hsep hQ hv
  have hd := Complex.re_le_norm (modeledContribution n-majorContribution n)
  rw [Complex.sub_re,norm_sub_rev] at hd
  change (n:ℝ)/8 ≤ (majorContribution n).re-_
  linarith only [hm,hd,major_error hsep,he']
end GoldbachPartial
