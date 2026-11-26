import PinnedMajorModelFloor
import Mathlib.Analysis.SpecialFunctions.Log.Base

/- Finite geometry and the trigonometric comparison are selected from
DFQDZZ/goldbach-proofs e4ab24712555ae8c2c926adf19d368a9fb392c35,
lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean. The spacing proof
in that source credits wzhxzkk, PR 153, 93d33090fdfc93fb272dde08cb463f3bff3c64ce.
-/
namespace Pinned316
namespace GoldbachMajorArc
open Finset Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop


private theorem nat_log_two_le {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ 2 * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h₂
  have h := Real.natLog_le_logb u 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

theorem cutoff_le_log_sq {n : ℕ} (hn : 2 ≤ n) :
    (cutoff n : ℝ) ≤ 16 * (Real.log n) ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have harg : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) harg
  rw [Real.log_pow] at hl
  norm_num1 at hl
  have hnat := nat_log_two_le (u := n + 2) (by omega)
  push_cast at hnat
  have h : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by linarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n + 2)) (α := ℝ)) h 2
  change (((Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith only [hsq]


private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

private theorem conj_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem kernel_square_twist (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [conj_phase, ← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]


def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width n q) (center q a + width n q)
def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a
def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem cutoff_separated : ∀ᶠ n : ℕ in atTop, 2 * (cutoff n)^2 < n := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^4 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop (2 : ℕ), h.eventually_lt_const (by norm_num : (0:ℝ) < 1/512)] with n hn hl
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl' := (div_lt_iff₀ hn').mp hl
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 2
  have h' : 2 * (cutoff n : ℝ)^2 < n := by nlinarith only [hb, hl']
  exact_mod_cast h'

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window n q a ↔ |t - center q a| ≤ width n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * (cutoff n)^2 < n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : t ∈ window n q a) (hb : t ∈ window n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let Q := cutoff n
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window n q a t).mp ha
  have h₂ := (mem_window n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*(cutoff n)^2<n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window n q a) (htb : t ∈ window n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum {n : ℕ} (hn : 2*(cutoff n)^2<n) (t : ℝ) :
    (arcs n).indicator (integrand n) t =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (window n q a).indicator (integrand n) t := by
  classical
  by_cases ht : t ∈ arcs n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window n q b).indicator (integrand n) t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window n q a).indicator (integrand n) t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width n q ≤ leftEnd n q a ∧ leftEnd n q a ≤ rightEnd n q a ∧ rightEnd n q a ≤ width n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window n q a).indicator F t) =
    ∫ β in leftEnd n q a..rightEnd n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width n q) 0 ≤ min (center q a+width n q) 1),
    ← integral_Icc_eq_integral_Ioc]

def actualPiece (n q a : ℕ) : ℂ := ∫ β in leftEnd n q a..rightEnd n q a, integrand n (center q a+β)

theorem major_split {n : ℕ} (hn : 2*(cutoff n)^2<n) : majorContribution n =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, actualPiece n q a := by
  have hcont := continuous_integrand n
  have hInt (q a : ℕ) : IntervalIntegrable ((window n q a).indicator (integrand n)) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold majorContribution
  simp_rw [arc_indicator_sum hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
noncomputable section

def modelPoint (n q a : ℕ) (β : ℝ) : ℂ :=
  (unitMean q a * kernel n β)^2 * phase (-(n:ℝ) * (center q a + β))

def modelPiece (n q a : ℕ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n:ℝ)*center q a)) *
    ((∫ β in leftEnd n q a..rightEnd n q a, ‖kernel n β‖^2 : ℝ) : ℂ)

theorem model_piece_eq (n q a : ℕ) :
    (∫ β in leftEnd n q a..rightEnd n q a, modelPoint n q a β) = modelPiece n q a := by
  have h (β : ℝ) : modelPoint n q a β =
      (unitMean q a ^2 * phase (-(n:ℝ)*center q a)) * ((‖kernel n β‖^2 : ℝ) : ℂ) := by
    rw [modelPoint, ← kernel_square_twist, mul_add, phase_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rfl

private theorem error_cont (n q a : ℕ) :
    Continuous (fun β => integrand n (center q a+β) - modelPoint n q a β) := by
  unfold integrand modelPoint primeSum kernel phase
  fun_prop

theorem piece_error_le {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    ‖actualPiece n q a - modelPiece n q a‖ ≤ ∫ β in -(width n q)..width n q, modelError n q a β := by
  have hi : Continuous (fun β => integrand n (center q a+β)) := by unfold integrand primeSum phase; fun_prop
  have hm : Continuous (modelPoint n q a) := by unfold modelPoint kernel phase; fun_prop
  have ⟨hl,hord,hr⟩ := clipped_order (n := n) hq ha
  rw [actualPiece, ← model_piece_eq, ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm hord).trans
  exact intervalIntegral.integral_mono_interval hl hord hr (Eventually.of_forall fun _ => norm_nonneg _)
    ((error_cont n q a).norm.intervalIntegrable _ _)

theorem width_le_unit {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0<q) :
    width n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : cutoff n ≤ n := by nlinarith [cutoff_positive n]
  calc
    width n q = ((cutoff n:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd n q a = -(width n q) ∧ rightEnd n q a = width n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem denom_one_phase (n : ℕ) : phase (-(n:ℝ)) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
  push_cast
  ring

/-- The two boundary half intervals together give the full kernel mass for q = 1. -/
private theorem endpoint_models {n : ℕ} (hn : 2*(cutoff n)^2<n) :
    (∑ a ∈ numerators 1, modelPiece n 1 a) = (kernelMass n (width n 1) : ℂ) := by
  let w := width n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit hn (by decide : 0<1)
  have h0 : leftEnd n 1 0 = 0 ∧ rightEnd n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd n 1 1 = -w ∧ rightEnd n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp), ram_one]; simp
  have hker : Continuous (fun β => ‖kernel n β‖^2) := (continuous_kernel n).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hker.intervalIntegrable (μ := volume) (-w) 0) (hker.intervalIntegrable 0 w)
  have hnSet : numerators 1 = {0,1} := by decide
  rw [hnSet]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2,hu,
    center, Nat.cast_zero,Nat.cast_one,div_one,mul_zero,mul_one,one_pow,one_mul,denom_one_phase]
  have hz : phase 0=1 := by simp [phase]
  rw [hz,one_mul,add_comm,← Complex.ofReal_add,hadd]
  rfl

theorem model_by_denominator {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece n q a) = coefficient q n * (kernelMass n (width n q):ℂ) := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    rw [coefficient_one,one_mul]
    exact endpoint_models hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← sum_centers_eq_coefficient, ← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece,hl,hr,kernelMass,center]

end
end GoldbachMajorArc
namespace GoldbachMajorArc
open Finset Filter MeasureTheory
noncomputable section
theorem major_error {n : ℕ} (hn : 2*(cutoff n)^2<n) :
    ‖majorContribution n - modeledContribution n‖ ≤ totalArcError n := by
  have hmodels : modeledContribution n =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, modelPiece n q a :=
    sum_congr rfl fun q hq => (model_by_denominator hn (mem_Icc.mp hq).1).symm
  rw [major_split hn, hmodels, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold totalArcError
  apply sum_le_sum
  intro q hq
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ numerators q, ∫ β in -(width n q)..width n q, modelError n q a β :=
      sum_le_sum fun a ha => piece_error_le (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) fun _ _ => norm_nonneg _

open scoped Topology in
theorem actual_floor_of_error_sublinear
    (hsmall : Tendsto (fun n : ℕ => totalArcError n/n) atTop (𝓝 0))
    {c : ℝ} (hc : c < 9/8) :
    ∀ᶠ n : ℕ in atTop, Even n → c*n ≤ (majorContribution n).re :=
  actual_floor_of_published_estimates cutoff_separated major_error hsmall hc

end
end GoldbachMajorArc
end Pinned316
