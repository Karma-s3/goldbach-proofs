import VerifiedFixedArcBessel
import NaturalDirichletTubeGeometry
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology Classical

def fixedUniformNumerators (q:ℕ):Finset ℕ := (range q).filter (fun a=>a.Coprime q)

noncomputable def fixedUniformMajorPiece (ρ:ℝ)(q a:ℕ):Set ℝ :=
  if a=0 then Set.Icc 0 ρ ∪ Set.Icc (1-ρ) 1
  else Set.Icc ((a:ℝ)/q-ρ) ((a:ℝ)/q+ρ)

noncomputable def fixedUniformMajorArcs (Q:ℕ)(ρ:ℝ):Set ℝ :=
  ⋃ i∈(Icc 1 Q).sigma fixedUniformNumerators, fixedUniformMajorPiece ρ i.1 i.2

theorem fixedUniformMajorPiece_measurable (ρ:ℝ)(q a:ℕ):MeasurableSet (fixedUniformMajorPiece ρ q a) := by
  unfold fixedUniformMajorPiece
  split_ifs
  · exact measurableSet_Icc.union measurableSet_Icc
  · exact measurableSet_Icc

theorem fixedUniformMajorArcs_measurable (Q:ℕ)(ρ:ℝ):MeasurableSet (fixedUniformMajorArcs Q ρ) :=
  ((Icc 1 Q).sigma fixedUniformNumerators).measurableSet_biUnion (fun i _=>fixedUniformMajorPiece_measurable ρ i.1 i.2)

private theorem uniform_radii_gap {Q q r:ℕ}{ρ:ℝ}(hQ:0<Q)(hq:q∈Icc 1 Q)(hr:r∈Icc 1 Q)
    (hρ:ρ≤1/(4*(Q:ℝ)^2)) : ρ+ρ<1/((q:ℝ)*r) := by
  have hQR:(0:ℝ)<Q:=by exact_mod_cast hQ
  have hqr:(0:ℝ)<q:=by exact_mod_cast (mem_Icc.mp hq).1
  have hrr:(0:ℝ)<r:=by exact_mod_cast (mem_Icc.mp hr).1
  have hden:(q:ℝ)*r≤(Q:ℝ)^2:=by
    rw [sq];exact_mod_cast Nat.mul_le_mul (mem_Icc.mp hq).2 (mem_Icc.mp hr).2
  apply lt_of_lt_of_le _ (one_div_le_one_div_of_le (by positivity) hden)
  have hb:2/(4*(Q:ℝ)^2)<1/(Q:ℝ)^2 := by field_simp;linarith
  exact ((add_le_add hρ hρ).trans_eq (by ring)).trans_lt hb

private theorem uniform_interior_gap {Q q a:ℕ}{ρ:ℝ}(hQ:0<Q)(hq:q∈Icc 1 Q)
    (ha:a∈fixedUniformNumerators q)(ha0:a≠0)(hρ:ρ≤1/(4*(Q:ℝ)^2)):
    ρ<(a:ℝ)/q-ρ ∧ (a:ℝ)/q+ρ<1-ρ := by
  have hr : (0:ℝ)<q:=by exact_mod_cast (mem_Icc.mp hq).1
  have hh:=uniform_radii_gap hQ hq (mem_Icc.mpr ⟨le_rfl,hQ⟩:1∈Icc 1 Q) hρ
  simp only [Nat.cast_one,mul_one] at hh
  have h1 : 1/(q:ℝ)≤(a:ℝ)/q:=div_le_div_of_nonneg_right (by exact_mod_cast Nat.pos_of_ne_zero ha0) hr.le
  have h2:(a:ℝ)/q+1/q≤1:=by
    rw [←add_div,div_le_one hr]
    exact_mod_cast Nat.succ_le_of_lt (mem_range.mp (mem_filter.mp ha).1)
  constructor <;> linarith only [h1,h2,hh]

theorem fixedUniformMajorArcs_subset {Q:ℕ}{ρ:ℝ}(hQ:0<Q)(hρ0:0≤ρ)(hρ:ρ≤1/(4*(Q:ℝ)^2)):
    fixedUniformMajorArcs Q ρ⊆Set.Icc 0 1 := by
  intro t ht
  obtain ⟨⟨q,a⟩,hi,ht⟩:=Set.mem_iUnion₂.mp ht
  obtain ⟨hq,ha⟩:=mem_sigma.mp hi
  obtain rfl|ha0:=eq_or_ne a 0
  · have hr:=uniform_radii_gap hQ (q:=1) (r:=1) (mem_Icc.mpr ⟨le_rfl,hQ⟩) (mem_Icc.mpr ⟨le_rfl,hQ⟩) hρ
    norm_num at hr
    change t∈fixedUniformMajorPiece ρ q 0 at ht
    simp only [fixedUniformMajorPiece,ite_true,Set.mem_union,Set.mem_Icc] at ht
    rcases ht with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> constructor <;> linarith
  · have ⟨hlo,hhi⟩:=uniform_interior_gap hQ hq ha ha0 hρ
    change t∈fixedUniformMajorPiece ρ q a at ht
    rw [fixedUniformMajorPiece,ite_eq_right ha0] at ht
    exact ⟨hρ0.trans (hlo.le.trans ht.1),ht.2.trans (by linarith only [hhi,hρ0])⟩

open private tubes_separate from NaturalDirichletTubeGeometry

theorem fixedUniformMajorPieces_disjoint {Q:ℕ}{ρ:ℝ}(hQ:0<Q)(hρ:ρ≤1/(4*(Q:ℝ)^2)) :
    (↑((Icc 1 Q).sigma fixedUniformNumerators):Set (Σ _:ℕ,ℕ)).Pairwise
      (fun i j=>Disjoint (fixedUniformMajorPiece ρ i.1 i.2) (fixedUniformMajorPiece ρ j.1 j.2)) := by
  have hzero {q:ℕ}(ha:0∈fixedUniformNumerators q):q=1:=by
    have h:Nat.Coprime 0 q:=(mem_filter.mp ha).2
    simpa using h
  have hz {q a r:ℕ}(hq:q∈Icc 1 Q)(ha:a∈fixedUniformNumerators q)(ha0:a≠0) :
      Disjoint (fixedUniformMajorPiece ρ r 0) (fixedUniformMajorPiece ρ q a):=by
    obtain ⟨hl,hr⟩:=uniform_interior_gap hQ hq ha ha0 hρ
    apply Set.disjoint_left.mpr
    intro t ht hs
    rw [fixedUniformMajorPiece,ite_eq_right ha0] at hs
    have ⟨hs₁,hs₂⟩:=hs
    simp only [fixedUniformMajorPiece,ite_true,Set.mem_union,Set.mem_Icc] at ht
    rcases ht with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> linarith
  rintro ⟨q,a⟩ hi ⟨r,b⟩ hj hne
  obtain ⟨hq,ha⟩:=mem_sigma.mp hi
  obtain ⟨hr,hb⟩:=mem_sigma.mp hj
  rcases eq_or_ne a 0 with rfl|ha0
  · rcases eq_or_ne b 0 with rfl|hb0
    · have hq':q=1:=hzero ha
      have hr':r=1:=hzero hb
      exact (hne (by rw [hq',hr'])).elim
    · exact hz hr hb hb0
  · rcases eq_or_ne b 0 with rfl|hb0
    · exact (hz hq ha ha0).symm
    · simp only [fixedUniformMajorPiece,ite_eq_right ha0,ite_eq_right hb0]
      apply tubes_separate (mem_Icc.mp hq).1 (mem_Icc.mp hr).1 (mem_filter.mp ha).2 (mem_filter.mp hb).2 _ (uniform_radii_gap hQ hq hr hρ)
      intro he
      obtain rfl:=congrArg Prod.fst he
      obtain rfl:=congrArg Prod.snd he
      exact hne rfl


private theorem fixedUniform_piece_integral (ρ:ℝ)(q a:ℕ)(F:ℝ→ℂ)(hF:Continuous F)
    (hper:Function.Periodic F 1)(hρ0:0≤ρ)(hρ:ρ+ρ<1):
    (∫t in fixedUniformMajorPiece ρ q a,F t)=∫β in -ρ..ρ,F ((a:ℝ)/q+β) := by
  by_cases ha:a=0
  · subst a
    simp only [fixedUniformMajorPiece,ite_true,Nat.cast_zero,zero_div,zero_add]
    have hd:Disjoint (Set.Icc (0:ℝ) ρ) (Set.Icc (1-ρ) 1):=
      Set.disjoint_left.mpr (fun _ hx hy=>by have :=hx.2;have:=hy.1;linarith)
    rw [setIntegral_union hd measurableSet_Icc hF.integrableOn_Icc hF.integrableOn_Icc,
      integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hρ0,
      integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show 1-ρ≤1 by linarith)]
    have hh : (∫t in -ρ..0,F t)=∫t in 1-ρ..1,F t := by
      have he (t:ℝ): F (1+t)=F t:=by rw [add_comm];exact hper t
      have hv:=intervalIntegral.integral_comp_add_left (a:= -ρ) (b:=0) F 1
      simpa only [he,←sub_eq_add_neg,add_zero] using hv
    rw [←hh,add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)
  · rw [fixedUniformMajorPiece,ite_eq_right ha,intervalIntegral.integral_comp_add_left,←sub_eq_add_neg,
      intervalIntegral.integral_of_le (show (a:ℝ)/q-ρ≤a/q+ρ by linarith),integral_Icc_eq_integral_Ioc]

theorem fixedUniformMajorArcs_integral {Q:ℕ}{ρ:ℝ}(hQ:0<Q)(hρ0:0≤ρ)(hρ:ρ≤1/(4*(Q:ℝ)^2))
    (F:ℝ→ℂ)(hF:Continuous F)(hper:Function.Periodic F 1):
    (∫t in fixedUniformMajorArcs Q ρ,F t)=
      ∑q∈Icc 1 Q,∑a∈fixedUniformNumerators q,∫β in -ρ..ρ,F ((a:ℝ)/q+β) := by
  have hg:=uniform_radii_gap hQ (q:=1) (r:=1) (mem_Icc.mpr ⟨le_rfl,hQ⟩) (mem_Icc.mpr ⟨le_rfl,hQ⟩) hρ
  norm_num at hg
  rw [fixedUniformMajorArcs,integral_biUnion_finset ((Icc 1 Q).sigma fixedUniformNumerators)
    (fun i _=>fixedUniformMajorPiece_measurable ρ i.1 i.2) (fixedUniformMajorPieces_disjoint hQ hρ),sum_sigma]
  · apply sum_congr rfl;intro q _
    apply sum_congr rfl;intro a _
    exact fixedUniform_piece_integral ρ q a F hF hper hρ0 hg
  · intro i _
    unfold fixedUniformMajorPiece
    split_ifs
    · exact hF.integrableOn_Icc.union hF.integrableOn_Icc
    · exact hF.integrableOn_Icc

private theorem uniform_integer_phase (m:ℤ) : E m=1:=by
  unfold E
  convert Complex.exp_int_mul_two_pi_mul_I m using 2
  push_cast
  ring

private theorem cutPrimeMode_periodic (N:ℕ)(m:ℤ):
    Function.Periodic (fun t:ℝ=>(centralPrimeWave N t)^2*E (-(m:ℝ)*t)) 1 := by
  have hn (k:ℕ):E k=1 := by simpa using uniform_integer_phase (k:ℤ)
  have hF:Function.Periodic (centralPrimeWave N) 1:=by
    intro t;unfold centralPrimeWave;simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
  intro t
  dsimp only
  rw [hF,mul_add,mul_one,phase_add,show E (-(m:ℝ))=1 by simpa using uniform_integer_phase (-m),mul_one]

theorem fixedUniformMajorArcs_true_split {Q:ℕ}{ρ:ℝ}(hQ:0<Q)(hρ0:0≤ρ)(hρ:ρ≤1/(4*(Q:ℝ)^2))
    (N:ℕ)(m:ℤ):
    fixedPrimeArcMode (fixedUniformMajorArcs Q ρ) N m =
      ∑q∈Icc 1 Q,∑a∈fixedUniformNumerators q,∫β in -ρ..ρ,
        (centralPrimeWave N ((a:ℝ)/q+β))^2*E (-(m:ℝ)*((a:ℝ)/q+β)) :=
  fixedUniformMajorArcs_integral hQ hρ0 hρ _ (by unfold centralPrimeWave E;fun_prop) (cutPrimeMode_periodic N m)

noncomputable def fixedUniformModelKernel (N:ℕ)(m:ℤ)(ρ:ℝ):ℂ :=
  ∫β in -ρ..ρ, (dirichletGeometricKernel N β)^2*E (-(m:ℝ)*β)

noncomputable def fixedUniformModelPiece (N m q a:ℕ)(ρ:ℝ):ℂ :=
  ∫β in -ρ..ρ,(GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β)^2*
    E (-(m:ℝ)*((a:ℝ)/q+β))

theorem fixedUniformMajorArcs_model_factor (N m Q:ℕ)(ρ:ℝ):
    (∑q∈Icc 1 Q,∑a∈fixedUniformNumerators q,fixedUniformModelPiece N m q a ρ)=
      (∑q∈Icc 1 Q,GoldbachMajorArc.coefficient q m)*fixedUniformModelKernel N (m:ℤ) ρ := by
  rw [sum_mul];apply sum_congr rfl;intro q _
  rw [←GoldbachMajorArc.sum_centers_eq_coefficient,sum_mul]
  apply sum_congr rfl;intro a _
  have hh (β:ℝ): (GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β)^2*E (-(m:ℝ)*((a:ℝ)/q+β))=
      (GoldbachMajorArc.unitMean q a^2*E (-(m:ℝ)*((a:ℝ)/q)))*((dirichletGeometricKernel N β)^2*E (-(m:ℝ)*β)) := by rw [mul_add,phase_add];ring
  unfold fixedUniformModelPiece fixedUniformModelKernel
  simp_rw [hh]
  rw [intervalIntegral.integral_const_mul]
  rfl


open private GoldbachMajorArc.unitMean_norm from PinnedUpstream316

private theorem uniform_prime_norm (N:ℕ)(t:ℝ):‖centralPrimeWave N t‖≤3*(N:ℝ):=by
  have hθ:(∑k∈range (N+1),weight k)=Chebyshev.theta N:=by
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_range,sum_filter];rfl
  calc _ ≤ ∑k∈range (N+1),‖(weight k:ℂ)*E ((k:ℝ)*t)‖ := norm_sum_le .. 
       _ = ∑k∈range (N+1),weight k := by
         apply sum_congr rfl;intro k _
         have hk:0≤weight k:=by unfold weight;split_ifs <;> positivity
         rw [norm_mul,show ‖E ((k:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
       _ ≤ _ := by
         rw [hθ]
         apply (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)).trans
         apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
         linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]

private theorem uniform_model_norm {q:ℕ}(hq:0<q)(a N:ℕ)(β:ℝ):
    ‖GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β‖≤(N:ℝ)+1:=by
  rw [norm_mul]
  apply (mul_le_mul (GoldbachMajorArc.unitMean_norm q a hq) (norm_sum_le (range (N+1)) _) (norm_nonneg _) zero_le_one).trans_eq
  simp only [E,Complex.norm_exp_ofReal_mul_I,sum_const,card_range,nsmul_eq_mul,mul_one,one_mul,Nat.cast_add,Nat.cast_one]

theorem fixedUniformMajorArcs_error {Q:ℕ}{ρ D:ℝ}(hQ:0<Q)(hρ0:0≤ρ)(hρ:ρ≤1/(4*(Q:ℝ)^2))
    (hD:0≤D)(N m:ℕ)
    (hclose:∀q∈Icc 1 Q,∀a∈fixedUniformNumerators q,∀β∈Set.Icc (-ρ) ρ,
      ‖centralPrimeWave N ((a:ℝ)/q+β)-GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β‖≤D):
    ‖fixedPrimeArcMode (fixedUniformMajorArcs Q ρ) N (m:ℤ)-
      (∑q∈Icc 1 Q,GoldbachMajorArc.coefficient q m)*fixedUniformModelKernel N (m:ℤ) ρ‖ ≤
      8*(Q:ℝ)^2*ρ*D*((N:ℝ)+1) := by
  let C:=4*D*((N:ℝ)+1)
  let G (q a:ℕ)(t:ℝ):=(centralPrimeWave N ((a:ℝ)/q+t))^2*E (-(m:ℝ)*((a:ℝ)/q+t))
  let M (q a:ℕ)(t:ℝ):=(GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N t)^2*E (-(m:ℝ)*((a:ℝ)/q+t))
  have hC:0≤C:=by dsimp [C];positivity
  have row {q a:ℕ}(hq:q∈Icc 1 Q)(ha:a∈fixedUniformNumerators q):
      ‖(∫t in -ρ..ρ,G q a t)-(∫t in -ρ..ρ,M q a t)‖≤C*(2*ρ):=by
    have hG:Continuous (G q a):=by dsimp [G,centralPrimeWave,E];fun_prop
    have hM:Continuous (M q a):=by dsimp [M,dirichletGeometricKernel,E];fun_prop
    rw [←intervalIntegral.integral_sub (hG.intervalIntegrable _ _) (hM.intervalIntegrable _ _)]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=C) _).trans_eq
    · rw [abs_of_nonneg (by linarith)];ring
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    let x:=centralPrimeWave N ((a:ℝ)/q+t)
    let z:=GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N t
    change ‖x^2*E _-z^2*E _‖≤_
    rw [←sub_mul,norm_mul,show ‖E (-(m:ℝ)*((a:ℝ)/q+t))‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,sq_sub_sq,norm_mul]
    have hplus:‖x+z‖≤4*((N:ℝ)+1):=by
      apply (norm_add_le x z).trans
      linarith only [uniform_prime_norm N ((a:ℝ)/q+t),uniform_model_norm (mem_Icc.mp hq).1 a N t]
    have hd:‖x-z‖≤D:=hclose q hq a ha t ⟨ht.1.le,ht.2⟩
    calc _ ≤ (4*((N:ℝ)+1))*D:=mul_le_mul hplus hd (norm_nonneg _) (by positivity)
         _ = _:=by dsimp [C];ring
  rw [fixedUniformMajorArcs_true_split hQ hρ0 hρ,←fixedUniformMajorArcs_model_factor,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  have hrow {q:ℕ}(hq:q∈Icc 1 Q):
      ‖(∑a∈fixedUniformNumerators q,∫t in -ρ..ρ,G q a t)-
        (∑a∈fixedUniformNumerators q, ∫t in -ρ..ρ,M q a t)‖≤(Q:ℝ)*(C*(2*ρ)):=by
    rw [←sum_sub_distrib]
    apply (norm_sum_le ..).trans
    apply (sum_le_sum (fun a ha=>row hq ha)).trans
    simp only [sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (card_filter_le ..).trans ((by simp : (range q).card=q).le.trans (mem_Icc.mp hq).2)
  calc _ ≤ ∑_q∈Icc 1 Q,(Q:ℝ)*(C*(2*ρ)) := by
         apply sum_le_sum;intro q hq;exact hrow hq
       _ = _ := by simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,C];ring

end GoldbachPartial
