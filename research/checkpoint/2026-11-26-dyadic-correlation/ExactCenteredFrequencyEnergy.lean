import ExactWeightedKernelZeroMode
import ExactRamanujanWeightBound
import ResonantModelEnergy
import PinnedMajorGeometry

namespace GoldbachPartial
open Finset Filter MeasureTheory
open scoped Topology ArithmeticFunction.vonMangoldt

private theorem square_projection_prefix_exact (P N : ℕ) :
    (∑ k∈Ioc 0 N,(finiteDivisorWeightSum P (exactRamanujanWeight P) k)^2)=
    ∑ d∈Icc 1 P,∑ e∈Icc 1 P, exactRamanujanWeight P d*exactRamanujanWeight P e*
      ((N/(d.lcm e):ℕ):ℝ) := by
  let F := exactRamanujanWeight P
  let I := Icc 1 P
  let K := Ioc 0 N
  let z := fun k d e : ℕ => F d*F e*(if d.lcm e∣k then (1:ℝ) else 0)
  have hk (k : ℕ) : (finiteDivisorWeightSum P F k)^2=∑ d∈I,∑ e∈I,z k d e := by
    unfold finiteDivisorWeightSum
    rw [sum_filter,pow_two,sum_mul]
    apply sum_congr rfl
    intro d _
    rw [mul_sum]
    apply sum_congr rfl
    intro e _
    by_cases hd : d∣k <;> by_cases he : e∣k <;> simp [z,Nat.lcm_dvd_iff,hd,he]
  change (∑ k∈K,(finiteDivisorWeightSum P F k)^2)=_
  simp_rw [hk]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  dsimp only [z,K]
  rw [←mul_sum,←sum_filter,sum_const,nsmul_eq_mul,mul_one,Nat.Ioc_filter_dvd_card_eq_div]

noncomputable def projectionSquareMean (P : ℕ) : ℝ :=
  ∑ q∈Icc 1 P,((ArithmeticFunction.moebius q:ℝ)^2/(q.totient:ℝ))

theorem projectionSquareMean_bound (P : ℕ) :
    projectionSquareMean P≤4*(1+Real.log P) := by
  have hh := modelTotientReciprocal_sum 0 P
  rw [Finset.sum_Ico_add' (fun k : ℕ => 1/(k.totient:ℝ)) 0 P (c:=1)] at hh
  simp only [zero_add,Finset.Ico_add_one_right_eq_Icc] at hh
  apply le_trans _ hh
  unfold projectionSquareMean
  apply sum_le_sum
  intro q _
  have hm : |(ArithmeticFunction.moebius q:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=q)
  exact div_le_div_of_nonneg_right ((sq_le_one_iff_abs_le_one _).mpr hm) (Nat.cast_nonneg _)

private theorem projected_square_main_exact (P N : ℕ) :
    (∑ d∈Icc 1 P,∑ e∈Icc 1 P,exactRamanujanWeight P d*exactRamanujanWeight P e*
      ((N:ℝ)/(d.lcm e:ℝ)))=(N:ℝ)*projectionSquareMean P := by
  have hh := finiteWeight_square_main 0 P (exactRamanujanWeight P) (N:ℝ)
  simp only [Nat.dvd_zero,ite_true] at hh
  rw [hh]
  congr 1
  apply sum_congr rfl
  intro q hq
  have hq0 := (mem_Icc.mp hq).1
  let : NeZero q := ⟨by omega⟩
  have hz := unit_exp_ramanujan_eq_divisor 0 q
  simp [ExtendedArcCoefficient.E,ZMod.card_units_eq_totient] at hz
  have h0 : dyadicRamanujanDivisor 0 q=(q.totient:ℤ) := by exact_mod_cast hz.symm
  rw [exactRamanujanWeight_transform P hq,h0]
  have hp : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  push_cast;field_simp

theorem projectionSquare_prefix_error (P N : ℕ) :
    |(∑ k∈Ioc 0 N,(finiteDivisorWeightSum P (exactRamanujanWeight P) k)^2)-
      (N:ℝ)*projectionSquareMean P|≤(P:ℝ)^2*(8*(1+Real.log P))^2 := by
  let C := 8*(1+Real.log P)
  have hC : 0≤C := by dsimp [C]; positivity
  rw [square_projection_prefix_exact,←projected_square_main_exact,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have hrow (d e : ℕ) (hd : d∈Icc 1 P) (he : e∈Icc 1 P) :
      |exactRamanujanWeight P d*exactRamanujanWeight P e*((N/(d.lcm e):ℕ):ℝ) -
       exactRamanujanWeight P d*exactRamanujanWeight P e*((N:ℝ)/(d.lcm e:ℝ))|≤C^2 := by
    let l := d.lcm e
    have hl : 0<l := Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1
    have hl' : (0:ℝ)<l := by exact_mod_cast hl
    have h1 : ((N/l:ℕ):ℝ)≤(N:ℝ)/l := Nat.cast_div_le
    have h2 : (N:ℝ)<((N/l:ℕ)+1:ℝ)*(l:ℝ) := by
      exact_mod_cast (show N<(N/l+1)*l by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ N hl)
    have ht : |((N/l:ℕ):ℝ)-(N:ℝ)/l|≤1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr h1)]
      linarith only [(div_lt_iff₀ hl').mpr h2]
    rw [←mul_sub,abs_mul,abs_mul]
    change _*|((N/l:ℕ):ℝ)-(N:ℝ)/l|≤_
    apply (mul_le_of_le_one_right (by positivity) ht).trans
    exact (mul_le_mul (exactRamanujanWeight_abs_le_log P d) (exactRamanujanWeight_abs_le_log P e) (abs_nonneg _) hC).trans_eq (by ring)
  calc
    _ ≤ ∑ _d∈Icc 1 P,∑ _e∈Icc 1 P,C^2 := by
      apply sum_le_sum
      intro d hd
      rw [←sum_sub_distrib]
      exact (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun e he => hrow d e hd he))
    _ = _ := by simp [C,Nat.card_Icc];ring

theorem exactProjection_interval_energy (P b J : ℕ) :
    (∑ k∈Ioc b (b+J),(finiteDivisorWeightSum P (exactRamanujanWeight P) k)^2) ≤
      4*(J:ℝ)*(1+Real.log P)+2*(P:ℝ)^2*(8*(1+Real.log P))^2 := by
  let f := fun k => (finiteDivisorWeightSum P (exactRamanujanWeight P) k)^2
  have hu : Ioc 0 (b+J)=Ioc 0 b ∪ Ioc b (b+J) := by ext k;simp only [mem_Ioc,mem_union];omega
  have hd : Disjoint (Ioc 0 b) (Ioc b (b+J)) := by
    apply disjoint_left.mpr;intro k hk he;exact (mem_Ioc.mp he).1.not_ge (mem_Ioc.mp hk).2
  have h1 := (abs_le.mp (projectionSquare_prefix_error P (b+J))).2
  have h2 := (abs_le.mp (projectionSquare_prefix_error P b)).1
  rw [hu,sum_union hd,Nat.cast_add] at h1
  have hh := mul_le_mul_of_nonneg_left (projectionSquareMean_bound P) (Nat.cast_nonneg (α:=ℝ) J)
  linarith only [h1,h2,hh]

theorem medDesk_projection_parameters :
    ∀ᶠ n : ℕ in atTop, let P := medDeskQ n
      0<P ∧ P≤n ∧ 2*(P:ℝ)^2*(8*(1+Real.log P))^2≤Real.sqrt n := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ha : Tendsto (fun n : ℕ => (Real.log n)^6/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [eventually_ge_atTop (2:ℕ),hl.eventually_ge_atTop 1,ha.eventually_lt_const
    (by norm_num : (0:ℝ)<1/131072),eventually_core_cutoffs] with n hn hlog ht hc
  let P := medDeskQ n
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hp : 0<P := pow_pos (Nat.log_pos (by decide) (by omega : 2≤n+2)) 2
  have hP : P≤n := (hc.1.trans (hc.2.1.trans hc.2.2.1)).trans
    (Nat.floor_le_of_le (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3:ℝ)≤1)))
  have hPr : (P:ℝ)≤16*(Real.log n)^2 := Pinned316.GoldbachMajorArc.cutoff_le_log_sq hn
  have hlP : Real.log P≤Real.log n := Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hP)
  change 1≤Real.log (n:ℝ) at hlog
  have hb : 1+Real.log P≤2*Real.log n := by linarith
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨hp,hP,?_⟩
  calc
    _ ≤ 2*(16*(Real.log n)^2)^2*(8*(2*Real.log n))^2 := by gcongr
    _ = 131072*(Real.log n)^6 := by ring
    _ ≤ _ := by linarith only [(div_lt_iff₀ hs).mp ht]

theorem exactCentered_interval_energy (P b J n : ℕ) (hbn : b+J≤n) :
    (∑ k∈Ioc b (b+J),(exactCenteredMangoldt P k)^2) ≤
      2*Real.log n*(∑ k∈Ioc b (b+J),Λ k) +
      2*(4*(J:ℝ)*(1+Real.log P)+2*(P:ℝ)^2*(8*(1+Real.log P))^2) := by
  let S := finiteDivisorWeightSum P (exactRamanujanWeight P)
  calc
    _ ≤ ∑ k∈Ioc b (b+J),(2*Real.log n*Λ k+2*(S k)^2) := by
      apply sum_le_sum
      intro k hk
      have hpos : 0<k := (Nat.zero_le b).trans_lt (mem_Ioc.mp hk).1
      have hlog : Λ k≤Real.log n := ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast (mem_Ioc.mp hk).2.trans hbn))
      change (Λ k-S k)^2≤_
      have hh := mul_le_mul_of_nonneg_right hlog (ArithmeticFunction.vonMangoldt_nonneg (n:=k))
      nlinarith only [hh,sq_nonneg (Λ k+S k)]
    _ ≤ _ := by
      rw [sum_add_distrib,←mul_sum,←mul_sum]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (exactProjection_interval_energy P b J) (by norm_num))

theorem exactCentered_full_energy :
    ∀ᶠ n : ℕ in atTop, (∑ k∈Icc 1 n,(exactCenteredMangoldt (medDeskQ n) k)^2) ≤
      28*(n:ℝ)*(1+Real.log n) := by
  filter_upwards [medDesk_projection_parameters,eventually_ge_atTop (1:ℕ)] with n h hn
  let P := medDeskQ n
  have hh := exactCentered_interval_energy P 0 n n (by omega)
  rw [zero_add] at hh
  have hψ : (∑k∈Ioc 0 n,Λ k)≤(Real.log 4+4)*(n:ℝ) := by
    simpa only [Chebyshev.psi,Nat.floor_natCast] using Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) n)
  have hL : Real.log P≤Real.log n := Real.log_le_log (by exact_mod_cast h.1) (by exact_mod_cast h.2.1)
  have h4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hS : Real.sqrt n≤(n:ℝ) := by
    rw [Real.sqrt_eq_rpow];simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn : (1:ℝ)≤n) (by norm_num : (1/2:ℝ)≤1)
  rw [show Icc 1 n=Ioc 0 n by ext k; simp only [mem_Icc,mem_Ioc];omega]
  apply hh.trans
  calc
    _ ≤ 2*Real.log n*((4+4)*(n:ℝ))+2*(4*(n:ℝ)*(1+Real.log n)+(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hψ.trans (mul_le_mul_of_nonneg_right (show Real.log 4+4≤4+4 by linarith only [h4]) (Nat.cast_nonneg _))) (by positivity)
      · exact mul_le_mul_of_nonneg_left (add_le_add (by gcongr) (h.2.2.trans hS)) (by norm_num)
    _ ≤ _ := by nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (Real.log_natCast_nonneg n),Nat.cast_nonneg (α:=ℝ) n]

end GoldbachPartial