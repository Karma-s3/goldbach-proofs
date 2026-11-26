import NaturalDirichletTubeGeometry
import OddWheelHighArc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace GoldbachPartial
open Finset Set MeasureTheory
open GoldbachDeepFourth (deepTube)

theorem naturalTube_dilate_integer_separation {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    {t : ℝ} (ht : t ∈ naturalTubeUnion R Q (3*Q)) (z : ℤ) :
    (2/3:ℝ)/Q ≤ |(d:ℝ)*t-z| := by
  obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨hj,ha⟩ := mem_sigma.mp hi
  let q := j+1
  have hdq : d<q := by
    have h : R≤j := (mem_Ico.mp hj).1
    dsimp [q]; omega
  have hqQ : q≤Q := (mem_Ico.mp hj).2
  have hq : (0:ℝ)<q := by exact_mod_cast Nat.succ_pos j
  have hQ : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hcop : a.Coprime q := (mem_filter.mp ha).2
  have hz : (d:ℤ)*a-z*q ≠ 0 := by
    intro he
    have hv : (q:ℤ) ∣ (d:ℤ)*a := ⟨z,by linarith only [he]⟩
    have hv' : q ∣ d*a := by exact_mod_cast hv
    have hqd := Nat.le_of_dvd hd (hcop.symm.dvd_of_dvd_mul_right hv')
    omega
  have hone : (1:ℝ)≤|(d:ℝ)*a-z*q| := by
    exact_mod_cast (show (1:ℤ)≤|(d:ℤ)*a-z*q| by have hp := abs_pos.mpr hz; omega)
  change t∈deepTube (naturalTubeRadius (3*Q) q) q a at ht
  obtain ⟨hl,hu⟩ := ht
  have hdist : |t-a/(q:ℝ)|≤naturalTubeRadius (3*Q) q := abs_le.mpr ⟨by linarith,by linarith⟩
  have hterm : |(q:ℝ)*t-a|≤1/(3*(Q:ℝ)) := by
    calc
      _ = (q:ℝ)*|t-a/(q:ℝ)| := by
        rw [show (q:ℝ)*t-a = (q:ℝ)*(t-a/(q:ℝ)) by field_simp]
        rw [abs_mul,abs_of_nonneg hq.le]
      _ ≤ (q:ℝ)*naturalTubeRadius (3*Q) q := mul_le_mul_of_nonneg_left hdist hq.le
      _ = _ := by unfold naturalTubeRadius; push_cast; field_simp
  have hnear : (d:ℝ)*|(q:ℝ)*t-a|≤1/3 := by
    calc
      _ ≤ (Q:ℝ)*(1/(3*(Q:ℝ))) := mul_le_mul (by exact_mod_cast hdq.le.trans hqQ) hterm
        (abs_nonneg _) hQ.le
      _ = _ := by field_simp
  have htri : |(d:ℝ)*a-z*q|≤(d:ℝ)*|(q:ℝ)*t-a|+(q:ℝ)*|(d:ℝ)*t-z| := by
    calc
      _ = |(-((d:ℝ)*((q:ℝ)*t-a)))+(q:ℝ)*((d:ℝ)*t-z)| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_neg,abs_mul,abs_of_nonneg hq.le,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using
        abs_add_le (-((d:ℝ)*((q:ℝ)*t-a))) ((q:ℝ)*((d:ℝ)*t-z))
  apply (div_le_iff₀ hQ).mpr
  have hqr : (q:ℝ)≤Q := by exact_mod_cast hqQ
  have hmono := mul_le_mul_of_nonneg_right hqr (abs_nonneg ((d:ℝ)*t-z))
  linarith only [hone,htri,hnear,hmono]

theorem naturalTube_dilate_circle_separation {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    {t : ℝ} (ht : t ∈ naturalTubeUnion R Q (3*Q)) :
    (2/3:ℝ)/Q ≤ ‖(((d:ℝ)*t:ℝ):UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  exact naturalTube_dilate_integer_separation hd hdR ht _

theorem unit_interval_integral_dilate {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : ∀ a b, IntervalIntegrable f volume a b) {d : ℕ} (hd : 0<d) :
    (∫ t in (0:ℝ)..1, f ((d:ℝ)*t)) = ∫ t in (0:ℝ)..1, f t := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have h := hp.intervalIntegral_add_zsmul_eq (d:ℤ) 0 hf
  simp only [zsmul_eq_mul,Int.cast_natCast,mul_one,zero_add] at h
  rw [intervalIntegral.integral_comp_mul_left _ hd'.ne',mul_zero,mul_one,h,smul_eq_mul]
  field_simp

theorem naturalTube_dilate_integral_le_tail {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    {a : ℝ} (ha : 0<a) (hab : a≤(2/3:ℝ)/Q) (hab' : a≤1/2) {f : ℝ→ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0≤f x) (hp : Function.Periodic f 1) :
    (∫ t in naturalTubeUnion R Q (3*Q), f ((d:ℝ)*t)) ≤ ∫ t in a..(1-a), f t := by
  classical
  let V := naturalTubeUnion R Q (3*Q)
  let U := {x : ℝ | a≤‖(x:UnitAddCircle)‖}
  let g := U.indicator f
  have hc : Continuous (fun x : ℝ => ‖(x:UnitAddCircle)‖) := by fun_prop
  have hu : MeasurableSet U := (isClosed_le continuous_const hc).measurableSet
  have hgper : Function.Periodic g 1 := by
    intro x
    have h : (x+1∈U) ↔ x∈U := by
      change (a≤‖((x+1:ℝ):UnitAddCircle)‖) ↔ _
      simp [U]
    by_cases hx : x∈U
    · simp [g,Set.indicator_of_mem hx,Set.indicator_of_mem (h.mpr hx),hp x]
    · simp [g,Set.indicator_of_notMem hx,Set.indicator_of_notMem (fun h' => hx (h.mp h'))]
  have hint (x y : ℝ) : IntervalIntegrable g volume x y :=
    intervalIntegrable_iff.mpr ((hf.intervalIntegrable x y).def'.integrable.indicator hu)
  have hreal (t : ℝ) (ht : t∈V) : g ((d:ℝ)*t) = f ((d:ℝ)*t) :=
    Set.indicator_of_mem (hab.trans (naturalTube_dilate_circle_separation hd hdR ht)) _
  have hpre : MeasurableSet ((fun t : ℝ => (d:ℝ)*t)⁻¹' U) := hu.preimage (by fun_prop)
  have hcomp : IntegrableOn (fun t : ℝ => g ((d:ℝ)*t)) (Set.Icc 0 1) := by
    have hbase : IntegrableOn (fun t : ℝ => f ((d:ℝ)*t)) (Set.Icc 0 1) :=
      (hf.comp (by fun_prop)).integrableOn_Icc
    exact hbase.indicator hpre
  have hq : 0<Q ∨ V=∅ := by
    by_cases h : 0<Q
    · exact Or.inl h
    · right
      have he : Q=0 := by omega
      simp [V,naturalTubeUnion,naturalTubeIndices,he]
  have hV : V⊆Set.Icc 0 1 := by
    rcases hq with h|h
    · exact naturalTubeUnion_inside_unit (hd.trans_le hdR) (by omega)
    · simp [h]
  have hset : Set.Ioc (0:ℝ) 1 ∩ U = Set.Icc a (1-a) := by
    ext x
    have hchar (hx : 0≤x) (hx' : x<1) : x∈U ↔ a≤x ∧ x≤1-a := by
      change (a≤‖(x:UnitAddCircle)‖) ↔ _
      rw [UnitAddCircle.norm_eq,abs_sub_round_eq_min,Int.fract_eq_self.mpr ⟨hx,hx'⟩,le_min_iff]
      constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁,by linarith⟩
    constructor
    · rintro ⟨⟨hx,hx'⟩,hu'⟩
      rcases hx'.lt_or_eq with hlt|rfl
      · exact (hchar hx.le hlt).mp hu'
      · have hn : ¬(1:ℝ)∈U := by
          change ¬a≤‖((1:ℝ):UnitAddCircle)‖
          rw [UnitAddCircle.norm_eq]
          simpa using not_le.mpr ha
        exact (hn hu').elim
    · rintro ⟨h₁,h₂⟩
      have hx := ha.trans_le h₁
      have hx' : x<1 := by linarith
      exact ⟨⟨hx,hx'.le⟩,(hchar hx.le hx').mpr ⟨h₁,h₂⟩⟩
  calc
    _ = ∫ t in V, g ((d:ℝ)*t) :=
      setIntegral_congr_fun (naturalTubeUnion_measurable ..) (fun t ht => (hreal t ht).symm)
    _ ≤ ∫ t in Set.Icc (0:ℝ) 1, g ((d:ℝ)*t) := by
      apply setIntegral_mono_set hcomp _ (Filter.Eventually.of_forall fun _ ht => hV ht)
      exact Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun x _ => hpos x) _)
    _ = ∫ t in (0:ℝ)..1, g ((d:ℝ)*t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0:ℝ)..1,g t := unit_interval_integral_dilate hgper hint hd
    _ = ∫ t in a..(1-a),f t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      change (∫ t in Set.Ioc (0:ℝ) 1,U.indicator f t)=_
      rw [setIntegral_indicator hu,hset,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith)]

open ExtendedArcCoefficient

theorem naturalTube_dilate_geometricKernel_energy {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    (m : ℕ) :
    (∫ t in naturalTubeUnion R Q (3*Q), ‖dirichletGeometricKernel m ((d:ℝ)*t)‖^2)
      ≤ 12*(Q:ℝ) := by
  by_cases hRQ : R<Q
  · have hQ : (2:ℝ)≤Q := by exact_mod_cast (show 2≤Q by omega)
    have hQ' : (0:ℝ)<Q := by linarith
    let a := (2/3:ℝ)/Q
    have ha : 0<a := by dsimp [a]; positivity
    have ha' : a≤1/2 := (div_le_iff₀ hQ').mpr (by linarith)
    have hp : Function.Periodic (dirichletGeometricKernel m) 1 := by
      have hn (k:ℕ) : E k=1 := by
        unfold E
        rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
        exact Complex.exp_nat_mul_two_pi_mul_I k
      intro t
      unfold dirichletGeometricKernel
      simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
    have hrow := naturalTube_dilate_integral_le_tail hd hdR ha le_rfl ha'
      (f:=fun t => ‖dirichletGeometricKernel m t‖^2)
      (by unfold dirichletGeometricKernel E; fun_prop)
      (fun x => sq_nonneg _) (fun x => by dsimp only; rw [hp x])
    calc
      _ ≤ _ := hrow
      _ ≤ 8/a := geometricKernel_single_period_tail m ha ha'
      _ = _ := by dsimp [a]; field_simp; ring
  · have he : naturalTubeUnion R Q (3*Q)=∅ := by
      simp [naturalTubeUnion,naturalTubeIndices,Finset.Ico_eq_empty_of_le (le_of_not_gt hRQ)]
    rw [he,setIntegral_empty]
    positivity

end GoldbachPartial