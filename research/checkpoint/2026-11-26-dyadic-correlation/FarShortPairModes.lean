import HighDenominatorCorrelationReduction
import ShortNonzeroModes

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

def farPairFrequency (n p r : ℕ) : ℤ := (p:ℤ)+r-n

abbrev shortNonzeroPairModes (H : ℕ) : Finset ℤ := shortNonzeroModes H

theorem mem_shortNonzeroPairModes {H : ℕ} {m : ℤ} :
    m∈shortNonzeroPairModes H ↔ m≠0 ∧ m.natAbs≤H := by
  have h : m.natAbs≤H ↔ |m|≤(H:ℤ) := by
    rw [←Int.natCast_natAbs]; exact_mod_cast Iff.rfl
  rw [h,abs_le]; simp only [shortNonzeroPairModes,shortNonzeroModes,mem_erase,mem_Icc]

def farPairSupport (n H : ℕ) : Finset (ℕ×ℕ) :=
  ((range (n+1)) ×ˢ (range (n+1))).filter fun u => u.1+H<u.2 ∨ u.2+H<u.1

noncomputable def farPairModeWeight (n H : ℕ) (m : ℤ) : ℝ :=
  ∑ u∈(farPairSupport n H).filter (fun u => farPairFrequency n u.1 u.2=m),
    weight u.1*weight u.2

noncomputable def farPairKernelAtModes (n H : ℕ) (S : Finset ℤ) (t : ℝ) : ℂ :=
  ∑ p∈range (n+1),∑ r∈range (n+1),
    if (p+H<r ∨ r+H<p) ∧ farPairFrequency n p r∈S then primePairMode n p r t else 0

noncomputable abbrev farShortOffTargetKernel (n H : ℕ) :=
  farPairKernelAtModes n H (shortNonzeroPairModes H)

theorem primePairMode_frequency (n p r : ℕ) (t : ℝ) :
    primePairMode n p r t = ((weight p*weight r:ℝ):ℂ)*E ((farPairFrequency n p r:ℝ)*t) := by
  unfold primePairMode farPairFrequency
  push_cast
  rw [show ((p:ℝ)+r-n)*t=p*t+r*t+(-(n:ℝ)*t) by ring,phase_add,phase_add]
  ring

theorem farPairKernelAtModes_grouped (n H : ℕ) (S : Finset ℤ) (t : ℝ) :
    farPairKernelAtModes n H S t = ∑ m∈S, (farPairModeWeight n H m:ℂ)*E ((m:ℝ)*t) := by
  let P := farPairSupport n H
  let freq := fun u : ℕ×ℕ => farPairFrequency n u.1 u.2
  let f := fun u : ℕ×ℕ => primePairMode n u.1 u.2 t
  have hbox : farPairKernelAtModes n H S t = ∑ u∈P.filter (fun u => freq u∈S), f u := by
    unfold farPairKernelAtModes
    dsimp only [P,farPairSupport]
    rw [sum_filter,sum_filter,sum_product]
    refine sum_congr rfl fun p _ => sum_congr rfl fun r _ => ?_
    dsimp only [freq,f]
    by_cases h : p+H<r ∨ r+H<p <;> simp [h]
  rw [hbox,←sum_fiberwise_eq_sum_filter P S freq f]
  refine sum_congr rfl fun m _ => ?_
  rw [farPairModeWeight,Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro u hu
  have hm := (mem_filter.mp hu).2
  change farPairFrequency n u.1 u.2 = m at hm
  exact (primePairMode_frequency n u.1 u.2 t).trans (by rw [hm])

private theorem farPairWeight_nonneg (k : ℕ) : 0≤weight k := by
  unfold weight; split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

theorem farPairModeWeight_bounds (n H : ℕ) (m : ℤ) :
    0≤farPairModeWeight n H m ∧ farPairModeWeight n H m ≤ ((n:ℝ)+1)*Real.log n^2 := by
  let s := (farPairSupport n H).filter (fun u => farPairFrequency n u.1 u.2=m)
  have hmem {u : ℕ×ℕ} (hu : u∈s) :
      u.1∈range (n+1) ∧ u.2∈range (n+1) :=
    mem_product.mp (mem_filter.mp (mem_filter.mp hu).1).1
  have hinj : (↑s : Set (ℕ×ℕ)).InjOn Prod.fst := by
    rintro ⟨p,r⟩ hpr ⟨p',r'⟩ hpr' he
    have h₁ := (mem_filter.mp hpr).2
    have h₂ := (mem_filter.mp hpr').2
    change (p:ℤ)+r-n=m at h₁
    change (p':ℤ)+r'-n=m at h₂
    change p=p' at he
    exact Prod.ext he (by omega)
  have hcard : s.card≤n+1 :=
    (card_le_card_of_injOn Prod.fst (fun _ h => (hmem h).1) hinj).trans_eq (card_range _)
  have hle {p : ℕ} (hp : p∈range (n+1)) : weight p ≤ Real.log n := by
    unfold weight
    split_ifs with h
    · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hp))
    · exact Real.log_natCast_nonneg _
  refine ⟨sum_nonneg fun u _ => mul_nonneg (farPairWeight_nonneg _) (farPairWeight_nonneg _),?_⟩
  calc
    _ ≤ ∑ _u∈s, (Real.log n)^2 := by
      apply sum_le_sum
      intro u hu
      rw [sq]
      exact mul_le_mul (hle (hmem hu).1) (hle (hmem hu).2)
        (farPairWeight_nonneg _) (Real.log_natCast_nonneg _)
    _ = (s.card:ℝ)*Real.log n^2 := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

theorem farPairKernelAtModes_integral (n H : ℕ) (S : Finset ℤ) {V : Set ℝ}
    (hV : V⊆Set.Icc 0 1) :
    (∫ t in V, farPairKernelAtModes n H S t) =
      ∑ m∈S, (farPairModeWeight n H m:ℂ)*(∫ t in V,E ((m:ℝ)*t)) := by
  have hi (m : ℤ) : IntegrableOn (fun t : ℝ => (farPairModeWeight n H m:ℂ)*E ((m:ℝ)*t)) V := by
    have hc : Continuous (fun t : ℝ => (farPairModeWeight n H m:ℂ)*E ((m:ℝ)*t)) := by unfold E; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set hV
  simp_rw [farPairKernelAtModes_grouped]
  rw [integral_finsetSum S (fun m _ => hi m)]
  exact sum_congr rfl fun m _ => integral_const_mul .. 

theorem farPairKernelAtModes_fourier_l1 (n H : ℕ) (S : Finset ℤ) {V : Set ℝ}
    (hV : V⊆Set.Icc 0 1) :
    ‖∫ t in V, farPairKernelAtModes n H S t‖ ≤
      (((n:ℝ)+1)*Real.log n^2)*(∑ m∈S, ‖∫ t in V,E ((m:ℝ)*t)‖) := by
  rw [farPairKernelAtModes_integral n H S hV,mul_sum]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun m _ => ?_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (farPairModeWeight_bounds n H m).1]
  exact mul_le_mul_of_nonneg_right (farPairModeWeight_bounds n H m).2 (norm_nonneg _)

end GoldbachPartial