import VerifiedCorrectedMajorFloor
import TruePrimeCenteringYoung
import ExactRamanujanWeightBound
import Batteries.Tactic.OpenPrivate

open private GoldbachPartial.weightTotientIcc from ExactRamanujanWeightBound
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open GoldbachMajorArc
open scoped Topology

private theorem major_num_card {q:ℕ} (hq:0<q) : (numerators q).card≤2*q.totient := by
  have hc : ((range q).filter (fun a=>a.Coprime q)).card=q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext p
    simp [Nat.coprime_comm]
  have hw : numerators q ⊆ insert q ((range q).filter fun a=>a.Coprime q) := by
    intro a ha
    obtain ⟨hm,hh⟩ := mem_filter.mp ha
    by_cases he:a=q
    · simp [he]
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hm;omega),hh⟩)
  have hh := (card_le_card hw).trans (card_insert_le ..)
  rw [hc] at hh
  have ht:=Nat.totient_pos.mpr hq
  omega

private theorem major_unit_small {q a:ℕ} (hq:0<q) (ha:a.Coprime q) :
    ‖unitMean q a‖≤1/(q.totient:ℝ) := by
  rw [unitMean_eq_ram ha,show ram q 1=(dyadicRamanujanDivisor 1 q:ℂ) from actualRamanujan_eq_divisor 1 q hq]
  rw [norm_div,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [show dyadicRamanujanDivisor 1 q=ArithmeticFunction.moebius q by simp [dyadicRamanujanDivisor]]
  rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs,←Int.cast_abs]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))

private theorem prime_window_upper {q n a:ℕ} (hq:0<q) (ha:a.Coprime q)
    (hw:width n q≤1/2) :
    (∫t in window n q a,‖centralPrimeWave n t‖^2) ≤
      (∫β in -(width n q)..width n q,modelError n q a β) + ((n:ℝ)+1)/(q.totient:ℝ)^2 := by
  let r := center q a
  let w := width n q
  have hw0 : 0≤w := width_nonneg n q
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcont : Continuous (fun β=>modelError n q a β) := by
    unfold modelError integrand primeSum kernel phase;fun_prop
  have hkc : Continuous (fun β=>‖dirichletGeometricKernel n β‖^2) := by
    unfold dirichletGeometricKernel E;fun_prop
  have hc : Continuous (fun β=>‖centralPrimeWave n (r+β)‖^2) := by
    unfold centralPrimeWave E;fun_prop
  have hpoint (β:ℝ) :
      ‖centralPrimeWave n (r+β)‖^2 ≤ modelError n q a β + (1/(q.totient:ℝ))^2*‖dirichletGeometricKernel n β‖^2 := by
    have h := norm_le_insert' (integrand n (r+β)) (modelPoint n q a β)
    have hp (x:ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
    conv at h => rhs;rw [add_comm]
    change ‖integrand n (r+β)‖≤modelError n q a β+‖modelPoint n q a β‖ at h
    simp only [integrand,modelPoint,norm_mul,norm_pow,hp,mul_one] at h
    change ‖centralPrimeWave n (r+β)‖^2 ≤ modelError n q a β+(‖unitMean q a‖*‖dirichletGeometricKernel n β‖)^2 at h
    apply h.trans
    rw [mul_pow]
    gcongr
    exact major_unit_small hq ha
  have hid : (∫t in window n q a,‖centralPrimeWave n t‖^2)=
      ∫β in -w..w,‖centralPrimeWave n (r+β)‖^2 := by
    rw [intervalIntegral.integral_comp_add_left (fun t=>‖centralPrimeWave n t‖^2) r,intervalIntegral.integral_of_le (by linarith : r+ -w≤r+w),←integral_Icc_eq_integral_Ioc]
    simp only [window,r,w,sub_eq_add_neg]
  rw [hid]
  have hb := intervalIntegral.integral_mono_on («μ»:=volume) (by linarith : -w≤w) (hc.intervalIntegrable _ _)
    ((hcont.add (continuous_const.mul hkc)).intervalIntegrable _ _) (fun x _=>hpoint x)
  apply hb.trans
  change (∫β in -w..w,modelError n q a β+(1/(q.totient:ℝ))^2*‖dirichletGeometricKernel n β‖^2) ≤ _
  rw [intervalIntegral.integral_add (g:=fun β=>(1/(q.totient:ℝ))^2*‖dirichletGeometricKernel n β‖^2) (hcont.intervalIntegrable _ _) ((continuous_const.mul hkc).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  apply add_le_add_right
  apply (mul_le_mul_of_nonneg_left (geometricKernel_window_energy n hw0 hw) (sq_nonneg _)).trans_eq
  field_simp
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
      setIntegral_union disjoint_sdiff_self_left hC ((hi a).mono_set Set.sdiff_subset) hiC]
    exact add_le_add (setIntegral_mono_set (hi a) (Filter.Eventually.of_forall hF)
      (Filter.Eventually.of_forall fun _ ht=>ht.1)) ih


theorem truePrime_major_energy (n:ℕ) (hQ:2*(cutoff n)^2<n) :
    (∫t in Set.Icc (0:ℝ) 1 ∩ arcs n,‖centralPrimeWave n t‖^2) ≤
      totalArcError n + 8*((n:ℝ)+1)*(1+Real.log (cutoff n)) := by
  classical
  let F (t:ℝ) := ‖centralPrimeWave n t‖^2
  let V (q:ℕ) := ⋃a∈numerators q,window n q a
  let I := Icc 1 (cutoff n)
  have hF : Continuous F := by dsimp [F,centralPrimeWave,E];fun_prop
  have hm (q:ℕ) : MeasurableSet (V q) := (numerators q).measurableSet_biUnion fun _ _=>measurableSet_Icc
  have hi (q:ℕ) : IntegrableOn F (V q) := integrableOn_finset_iUnion.mpr fun _ _=>hF.integrableOn_Icc
  have hu : Set.Icc (0:ℝ) 1 ∩ arcs n⊆⋃q∈I,V q := by
    intro t ht
    obtain ⟨q,a,hq,hQ,ha,hc,ht⟩:=ht.2
    exact Set.mem_iUnion₂.mpr ⟨q,mem_Icc.mpr ⟨hq,hQ⟩,Set.mem_iUnion₂.mpr
      ⟨a,mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩,(mem_window n q a t).mpr ht⟩⟩
  have hcov := setIntegral_mono_set (integrableOn_finset_iUnion.mpr fun q (_:q∈I)=>hi q)
    (Filter.Eventually.of_forall (fun t=>sq_nonneg ‖centralPrimeWave n t‖)) hu.eventuallySubset
  change (∫t in Set.Icc (0:ℝ) 1 ∩ arcs n,F t) ≤ _
  apply hcov.trans ((integral_finite_union_le I V F (fun _=>sq_nonneg _) hm hi).trans _)
  let err (q a:ℕ) := ∫β in -(width n q)..width n q,modelError n q a β
  have he (q a:ℕ) : 0≤err q a := intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) (fun _ _=>norm_nonneg _)
  have hr (q:ℕ) (hq:q∈I) :
      (∫t in V q,F t) ≤ (∑a∈range (q+1),err q a) + 2*((n:ℝ)+1)*(1/(q.totient:ℝ)) := by
    obtain ⟨hq1,hqQ⟩:=mem_Icc.mp hq
    have hq' : (1:ℝ)≤q := by exact_mod_cast hq1
    have hn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hcut : 2*(cutoff n:ℝ)≤(n:ℝ) := by
      have hh : cutoff n≤(cutoff n)^2 := Nat.le_self_pow (by decide) _
      exact_mod_cast (show 2*cutoff n≤n by omega)
    have hw : width n q≤1/2 := by
      unfold width;apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hcut,mul_nonneg (sub_nonneg.mpr hq') hn.le]
    have hA := integral_finite_union_le (numerators q) (window n q) F (fun _=>sq_nonneg _)
      (fun _=>measurableSet_Icc) (fun _=>hF.integrableOn_Icc)
    apply hA.trans ((sum_le_sum (fun a ha=>prime_window_upper hq1 (mem_filter.mp ha).2 hw)).trans _)
    rw [sum_add_distrib]
    apply add_le_add (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun a _ _=>he q a))
    simp only [sum_const,nsmul_eq_mul]
    have hcc : ((numerators q).card:ℝ)≤2*(q.totient:ℝ) := by exact_mod_cast major_num_card hq1
    calc _ ≤ (2*(q.totient:ℝ))*(((n:ℝ)+1)/(q.totient:ℝ)^2) := mul_le_mul_of_nonneg_right hcc (by positivity)
         _ = _ := by field_simp
  apply (sum_le_sum hr).trans
  rw [sum_add_distrib,←mul_sum]
  apply add_le_add le_rfl
  calc _ ≤ (2*((n:ℝ)+1))*(4*(1+Real.log (cutoff n))) := mul_le_mul_of_nonneg_left (GoldbachPartial.weightTotientIcc _) (by positivity)
       _ = _ := by ring

theorem truePrime_full_energy_sum (n:ℕ) :
    (∫t in Set.Icc (0:ℝ) 1,‖centralPrimeWave n t‖^2)=∑k∈range (n+1),(weight k)^2 := by
  let F (t:ℝ) := ‖centralPrimeWave n t‖^2
  have hn (k:ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I)=(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast;ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hper : Function.Periodic (centralPrimeWave n) 1 := by
    intro t;unfold centralPrimeWave;simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
  have hfper : Function.Periodic F 1 := fun t=>congrArg (fun z:ℂ=>‖z‖^2) (hper t)
  have hs:=hfper.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at hs
  change (∫t in Set.Icc (0:ℝ) 1,F t)=_
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,←hs]
  have he := finiteAbelWave_unit_energy (range (n+1)) (fun k=>(weight k:ℂ))
  change (∫t in (-(1/2):ℝ)..(1/2),F t)=_ at he
  rw [he]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem truePrime_full_energy_large :
    ∀ᶠ n:ℕ in atTop,(n:ℝ)*Real.log n/32 ≤ ∫t in Set.Icc (0:ℝ) 1,‖centralPrimeWave n t‖^2 := by
  filter_upwards [eventually_ge_atTop (2*192^4+8:ℕ)] with n hn
  let m:=n/2
  have hm : 192^4≤m := by dsimp [m];omega
  have hm4 : 4≤m := by omega
  have hn3 : n≤3*m := by dsimp [m];omega
  have hmN : 2*m≤n := by dsimp [m];omega
  have hm' : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hlog : Real.log n≤2*Real.log m := by
    have hh : (n:ℝ)≤(m:ℝ)^2 := by exact_mod_cast (show n≤m^2 by nlinarith [Nat.mul_le_mul_right m hm4])
    have hh' := Real.log_le_log (show 0<(n:ℝ) by exact_mod_cast (show 0<n by omega)) hh
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh'
  have hnr : (n:ℝ)≤3*(m:ℝ) := by exact_mod_cast hn3
  let S := (Ioc m (2*m)).filter Nat.Prime
  have hS : S⊆range (n+1) := fun p hp=>mem_range.mpr (by have := (mem_Ioc.mp (mem_filter.mp hp).1).2;omega)
  have hmL := Real.log_natCast_nonneg m
  have hL := Real.log_natCast_nonneg n
  rw [truePrime_full_energy_sum]
  calc _ ≤ (Real.log m)*((m:ℝ)/4) := by nlinarith only [mul_le_mul hnr hlog hL (by positivity : (0:ℝ)≤3*m),mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) hmL]
       _ ≤ (Real.log m)*(∑p∈S,Real.log p) := mul_le_mul_of_nonneg_left (dyadic_prime_mass m hm) hmL
       _ ≤ ∑p∈S,(weight p)^2 := by
         rw [mul_sum];apply sum_le_sum;intro p hp
         have hh:=mem_filter.mp hp
         have hmp : (m:ℝ)≤p := by exact_mod_cast (mem_Ioc.mp hh.1).1.le
         rw [weight,ite_eq_left hh.2,sq]
         exact mul_le_mul_of_nonneg_right (Real.log_le_log hm' hmp) (Real.log_natCast_nonneg _)
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS (fun _ _ _=>sq_nonneg _)

theorem truePrime_minor_energy_large :
    ∀ᶠ n:ℕ in atTop,(n:ℝ)*Real.log n/64 ≤
      ∫t in Set.Icc (0:ℝ) 1 ∩ (arcs n)ᶜ,‖centralPrimeWave n t‖^2 := by
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hll : Tendsto (fun n:ℕ=>Real.log (Real.log n)/Real.log n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp hln)
  filter_upwards [eventually_ge_atTop (2:ℕ),cutoff_separated,truePrime_full_energy_large,
    totalArcError_sublinear.eventually_lt_const zero_lt_one,
    hln.eventually_ge_atTop (131072:ℝ),hll.eventually_lt_const (show 0<(1:ℝ)/131072 by norm_num)] with n hn hs hf he hu hv
  let L:=Real.log (n:ℝ)
  change 131072≤L at hu
  have hL : 0<L := by linarith
  have hN : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn' : 0<(n:ℝ) := by linarith
  have hQ : 0<cutoff n := by
    change 0<(Nat.log 2 (n+2))^2
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQ' : (0:ℝ)<cutoff n := by exact_mod_cast hQ
  have hlog := Real.log_le_log hQ' (GoldbachMajorArc.cutoff_le_log_sq hn)
  change Real.log (cutoff n)≤Real.log (16*L^2) at hlog
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Nat.cast_ofNat] at hlog
  have hl16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)
  change Real.log L/L<1/131072 at hv
  have hlog' : 1+Real.log (cutoff n)≤L/4096 := by linarith only [hlog,hl16,(div_lt_iff₀ hL).mp hv,hu]
  have he' : totalArcError n≤(n:ℝ) := by simpa using ((div_lt_iff₀ hn').mp he).le
  have hm := truePrime_major_energy n hs
  have hi : IntegrableOn (fun t=>‖centralPrimeWave n t‖^2) (Set.Icc (0:ℝ) 1) := by
    apply Continuous.integrableOn_Icc;unfold centralPrimeWave E;fun_prop
  have hAm : MeasurableSet (Set.Icc (0:ℝ) 1∩arcs n) := measurableSet_Icc.inter (measurable_rational_arcs _ _)
  have hset : Set.Icc (0:ℝ) 1 ∩ (arcs n)ᶜ = Set.Icc 0 1 \ (Set.Icc 0 1∩arcs n) := by ext t;simp
  rw [hset,setIntegral_sdiff hAm hi Set.inter_subset_left]
  have hb := mul_le_mul (show 8*((n:ℝ)+1)≤16*(n:ℝ) by linarith) hlog'
    (show 0≤1+Real.log (cutoff n) by positivity) (by positivity : (0:ℝ)≤16*n)
  change (n:ℝ)*L/32≤_ at hf
  change (n:ℝ)*L/64≤_
  nlinarith only [hf,hm,hb,he',mul_le_mul_of_nonneg_left hu hn'.le]

end GoldbachPartial
