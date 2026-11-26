import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A counterexample to the registered deep-arc fourth moment

The theorem `not_frontier_deep_fourth_moment_conjecture` negates the
literal Lean statement published in the Goldbach Research production
catalogue at revision 4c2190575625a6193ee5dbba0c3960e07cd3ce94.
The exponent 1/6 already fails on arbitrarily large even inputs.

Let n=t^12 and Y=t^4. For every prime Y<q<=2Y, use the short intervals
of radius 1/(20n) about the reduced fractions a/q. They are pairwise
disjoint and lie outside every excluded wide arc. For small beta, the
sum over nonzero residues of the actual prime exponential sums is
q log(q) e(q beta) - S(beta). The unshifted sum has norm at least
half the prime mass. Two applications of Cauchy-Schwarz give a fourth
moment lower bound for each row. A binomial-coefficient bound supplies
enough primes q to exceed n^(2+1/6). All these steps are proved below.

The final signed-row identities retain the additive phase in the
Goldbach coefficient. The fourth moment counterexample concerns the
auxiliary absolute-value estimate. The pointwise Goldbach lower bound
requires a signed estimate.

The conventions for E and its addition law follow the project's
Apache-2.0 PR 158, by TranswarpDrive:
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/158 .
Catalogue: https://www.movan.tech/goldbach/api/status?view=web-gzip .
-/

namespace GoldbachDeepFourth

open MeasureTheory

noncomputable def weight (p : ℕ) : ℝ := if Nat.Prime p then Real.log p else 0

private theorem weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  by_cases hp : Nat.Prime p
  · simp only [weight, ite_eq_left hp]
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · simp [weight, hp]

namespace ExtendedArcCoefficient

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end ExtendedArcCoefficient

/-- Splitting the prime factors of the central binomial coefficient at
sqrt(2n), 2n/3 and n leaves the product of primes in (n, 2n]. -/
private theorem centralBinom_le_with_interval_primes (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n) ^ (2*n).sqrt * 4 ^ (2*n/3) *
      ∏ p ∈ (Finset.Ioc n (2*n)).filter Nat.Prime, p := by
  let f := fun p : ℕ => p ^ n.centralBinom.factorization p
  let P := (Finset.range (2*n+1)).filter Nat.Prime
  let S := (Finset.range (2*n/3+1)).filter Nat.Prime
  have hP : (∏ p ∈ P, f p) = n.centralBinom := by
    rw [← n.prod_pow_factorization_centralBinom]
    apply Finset.prod_filter_of_ne
    intro p _ h
    contrapose h
    simp [f, Nat.factorization_eq_zero_of_not_prime n.centralBinom h]
  have hS : S ⊆ P.filter (· ≤ n) := by
    intro p hp
    have ⟨hr, hpr⟩ := Finset.mem_filter.mp hp
    have hd := Finset.mem_range.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr⟩, by omega⟩
  have hsmall : (∏ p ∈ S, f p) = ∏ p ∈ P.filter (· ≤ n), f p := by
    apply Finset.prod_subset hS
    intro p hp hnS
    obtain ⟨hpP,hpn⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp hpP).2
    have hcut : 2*n < 3*p := by
      by_contra! h
      apply hnS
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩
    simp [f, Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hcut]
  have hlarge : P.filter (fun p => ¬p ≤ n) = (Finset.Ioc n (2*n)).filter Nat.Prime := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨h,hp⟩,hnp⟩
      exact ⟨⟨hnp,by omega⟩,hp⟩
    · rintro ⟨⟨hnp,h⟩,hp⟩
      exact ⟨⟨by omega,hp⟩,hnp⟩
  have hpos : 0 < 2*n := by omega
  have hSbound : (∏ p ∈ S, f p) ≤ (2*n) ^ (2*n).sqrt * 4 ^ (2*n/3) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ (2*n).sqrt)]
    apply Nat.mul_le_mul
    · refine (Finset.prod_le_prod fun p _ => (show f p ≤ 2*n from Nat.pow_factorization_choose_le hpos)).trans ?_
      rw [Finset.prod_const]
      apply pow_right_mono₀ (by omega : 1 ≤ 2*n)
      calc
        _ ≤ (Finset.Icc 1 (2*n).sqrt).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_le,hcut⟩)
        _ = _ := by simp
    · refine le_trans ?_ (primorial_le_four_pow (2*n/3))
      refine (Finset.prod_le_prod fun p hp => (show f p ≤ p from ?_)).trans ?_
      · obtain ⟨hpS, hp⟩ := Finset.mem_filter.mp hp
        refine (pow_right_mono₀ (Finset.mem_filter.mp hpS).2.one_le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hp))
      · exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ S)
          (fun p hp _ => (Finset.mem_filter.mp hp).2.one_le)
  rw [← hP, ← Finset.prod_filter_mul_prod_filter_not P (· ≤ n), ← hsmall, hlarge]
  apply Nat.mul_le_mul hSbound
  apply Finset.prod_le_prod
  intro p hp
  obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
  have hpn := (Finset.mem_Ioc.mp hI).1
  refine (pow_right_mono₀ hprime.one_le ?_).trans (pow_one p).le
  apply Nat.factorization_choose_le_one
  nlinarith [sq_nonneg (p-1 : ℤ)]

/-- An elementary, explicit lower bound for the mass of primes in (n, 2n]. -/
theorem dyadic_prime_mass (n : ℕ) (hn : 192 ^ 4 ≤ n) :
    (n : ℝ) / 4 ≤ ∑ p ∈ (Finset.Ioc n (2*n)).filter Nat.Prime, Real.log p := by
  have hn4 : 4 ≤ n := le_trans (by norm_num : 4 ≤ 192 ^ 4) hn
  have hprod : 4 ^ n ≤ n * (2 * n) ^ (2 * n).sqrt *
      4 ^ (2 * n / 3) * ∏ p ∈ (Finset.Ioc n (2*n)).filter Nat.Prime, p := by
    have h := (Nat.four_pow_lt_mul_centralBinom n hn4).le.trans
      (Nat.mul_le_mul_left n (centralBinom_le_with_interval_primes n (by omega)))
    simpa only [Nat.mul_assoc] using h
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2x : 0 < 2 * (n : ℝ) := by positivity
  let t : ℝ := √(√(2 * (n : ℝ)))
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = √(2 * (n : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht4 : t ^ 4 = 2 * (n : ℝ) := by
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
         _ = _ := by rw [ht2, Real.sq_sqrt h2x.le]
  have ht : 192 ≤ t := by
    have hn' : (192 : ℝ) ^ 4 ≤ n := by exact_mod_cast hn
    by_contra! h
    have := pow_lt_pow_left₀ h ht0 (by decide : 4 ≠ 0)
    linarith
  have hlog : Real.log (2 * (n : ℝ)) ≤ 4 * t := by
    rw [← ht4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
    norm_num
    linarith
  have hs : ((2 * n).sqrt : ℝ) ≤ t ^ 2 := by
    rw [ht2, Real.le_sqrt (by positivity) h2x.le]
    exact_mod_cast Nat.sqrt_le' (2*n)
  have hlogs : Real.log n + ((2*n).sqrt : ℝ) * Real.log (2*(n : ℝ)) ≤ (n : ℝ)/12 := by
    have h1 := Real.log_le_log hx (by linarith : (n : ℝ) ≤ 2*n)
    have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ (2*n).sqrt)
    have h3 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 4*t)
    have h4 := mul_nonneg (sub_nonneg.mpr ht) (pow_nonneg ht0 3)
    have h5 := mul_nonneg (by linarith : 0 ≤ t-1) (by positivity : 0 ≤ t*(t+1))
    nlinarith
  have hfour : 1 ≤ Real.log 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    have h' := Real.log_pow (2:ℝ) 2
    norm_num at h h'
    linarith
  let P := (Finset.Ioc n (2*n)).filter Nat.Prime
  have hP (p : ℕ) (hp : p ∈ P) : (0 : ℝ) < p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hcast : (4:ℝ)^n ≤ (n:ℝ) * (2*n : ℝ)^((2*n).sqrt) *
        4^(2*n/3) * ∏ p ∈ P, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  have hsum := Real.log_le_log (by positivity) hcast
  have hPlog := Real.log_prod (s := P) (f := fun p : ℕ => (p : ℝ))
    (fun p hp => (hP p hp).ne')
  have hPpos := Finset.prod_pos hP
  rw [Real.log_mul (by positivity) hPpos.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul hx.ne' (by positivity), hPlog, Real.log_pow, Real.log_pow, Real.log_pow] at hsum
  have hd : (2*n/3 : ℕ) * (3 : ℝ) ≤ 2*(n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2*n) 3
  have ha := mul_nonneg (sub_nonneg.mpr hd) (le_trans (by norm_num : (0:ℝ) ≤ 1) hfour)
  have hb := mul_nonneg hx.le (sub_nonneg.mpr hfour)
  change (n : ℝ)/4 ≤ ∑ p ∈ P, Real.log p
  linarith

def coreArcBand (n R A B : ℕ) : Set ℝ :=
  {u | ∃ q a : ℕ, A < q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
    |u-(a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))}

private theorem measurable_coreArcBand (n R A B : ℕ) :
    MeasurableSet (coreArcBand n R A B) := by
  unfold coreArcBand
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : A < q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q
  · have hm : MeasurableSet {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a:ℝ)/(q:ℝ)|) by fun_prop).measurable measurable_const
    convert hm using 1
    ext t
    exact ⟨fun h' => h'.2.2.2.2, fun h' => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,h'⟩⟩
  · have he : {t : ℝ | A < q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨h₁,h₂,h₃,h₄,_⟩
      exact h ⟨h₁,h₂,h₃,h₄⟩
    rw [he]
    exact MeasurableSet.empty

/-- Generalizes the interval-radius comparison in goldbach-proofs PRs
153 and 316 to independent denominator and width cutoffs. -/
private theorem coreArcBand_disjoint {n R A B C : ℕ} (hB : B ≤ C) (hs : 2*R*C < n) :
    Disjoint (coreArcBand n R A B) (coreArcBand n R B C) := by
  refine Set.disjoint_left.mpr ?_
  rintro t ⟨q,a,hA,hq,_,ha,hx⟩ ⟨r,b,hB',hr,_,hb,hy⟩
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnum : R*r+R*q < n := by
    have h₁ := Nat.mul_le_mul_left R hr
    have h₂ := Nat.mul_le_mul_left R (hq.trans hB)
    nlinarith only [h₁,h₂,hs]
  have hrad : (R:ℝ)/(q*n)+R/(r*n) < 1/(q*r) := calc
    _ = ((R:ℝ)*r+R*q)/(q*r*n) := by field_simp
    _ < (n:ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hnum)
    _ = _ := by field_simp
  have hne : a*r ≠ b*q := by
    intro e
    have hqr := ha.symm.dvd_of_dvd_mul_left (e ▸ dvd_mul_left q b)
    have hrq := hb.symm.dvd_of_dvd_mul_left (e.symm ▸ dvd_mul_left r a)
    have := Nat.dvd_antisymm hqr hrq
    omega
  have hsep : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
    rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp,abs_div,abs_of_pos (mul_pos hq0 hr0)]
    apply (div_le_div_iff_of_pos_right (mul_pos hq0 hr0)).mpr
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt h
      linarith [neg_le_abs ((a:ℝ)*r-b*q)]
    · have h' : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt h
      linarith [le_abs_self ((a:ℝ)*r-b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  linarith

abbrev medDeskQ (n : ℕ) := (Nat.log 2 (n+2))^2

noncomputable abbrev medDeskD (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

section DeepPrimeFourth
open ExtendedArcCoefficient
noncomputable def deepPrimeWave (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (weight k : ℂ) * E ((k:ℝ)*t)

private theorem deepPhaseRow {k q : ℕ} (hq : q.Prime) (hk : k.Prime) :
    ∑ a ∈ Finset.range q, E ((k:ℝ)*((a:ℝ)/q)) = if k=q then (q:ℂ) else 0 := by
  have hz : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  by_cases h : k=q
  · subst k
    simp only [ite_true]
    have h1 (a : ℕ) : E ((q:ℝ)*((a:ℝ)/q)) = 1 := by
      rw [show (q:ℝ)*((a:ℝ)/q) = a by field_simp]
      unfold E
      convert Complex.exp_nat_mul_two_pi_mul_I a using 2
      push_cast
      ring
    simp [h1]
  · simp only [h, ↓reduceIte]
    have hc := (Nat.coprime_primes hk hq).mpr h
    have hp := Complex.isPrimitiveRoot_exp_of_coprime k q hq.ne_zero hc
    convert hp.geom_sum_eq_zero hq.one_lt using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [← Complex.exp_nat_mul]
    unfold E
    congr 1
    push_cast
    ring

theorem deepPrimeWave_row {n q : ℕ} (hq : q.Prime) (hqn : q≤n) (β : ℝ) :
    (∑ a ∈ (Finset.range q).erase 0, deepPrimeWave n (β+(a:ℝ)/q)) +
      deepPrimeWave n β = (q:ℂ)*(weight q:ℂ)*E ((q:ℝ)*β) := by
  classical
  have hz : 0 ∈ Finset.range q := Finset.mem_range.mpr hq.pos
  have hfull : ∑ a ∈ Finset.range q, deepPrimeWave n (β+(a:ℝ)/q) =
      (q:ℂ)*(weight q:ℂ)*E ((q:ℝ)*β) := by
    unfold deepPrimeWave
    simp_rw [mul_add,phase_add,←mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single q]
    · rw [deepPhaseRow hq hq]; simp only [ite_true]; ring
    · intro p _ hpq
      by_cases hp : p.Prime
      · simp [deepPhaseRow hq hp,hpq]
      · simp [weight,hp]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  simpa using (Finset.sum_erase_add (Finset.range q) (fun a : ℕ => deepPrimeWave n (β+(a:ℝ)/q)) hz).trans hfull

private theorem deepFourthHolder {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖^4 ≤ (s.card:ℝ)^3 * ∑ a ∈ s, ‖f a‖^4 := by
  have h₁ : (∑ a ∈ s, ‖f a‖)^2 ≤ (s.card:ℝ)*∑ a ∈ s, ‖f a‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => ‖f i‖)
  have h₂ : (∑ a ∈ s, ‖f a‖^2)^2 ≤ (s.card:ℝ)*∑ a ∈ s, ‖f a‖^4 := by
    calc
      _ ≤ (s.card:ℝ)*∑ a ∈ s, (‖f a‖^2)^2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => ‖f i‖^2)
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    _ ≤ (∑ a ∈ s, ‖f a‖)^4 := by gcongr; exact norm_sum_le _ _
    _ = ((∑ a ∈ s, ‖f a‖)^2)^2 := by ring
    _ ≤ ((s.card:ℝ)*∑ a ∈ s, ‖f a‖^2)^2 := by gcongr
    _ = (s.card:ℝ)^2 * (∑ a ∈ s, ‖f a‖^2)^2 := by ring
    _ ≤ (s.card:ℝ)^2 * ((s.card:ℝ)*∑ a ∈ s, ‖f a‖^4) := by gcongr
    _ = _ := by ring

theorem deepPrimeWave_near_zero (n : ℕ) {β : ℝ} (hβ : 6*(n:ℝ)*|β| ≤ 1) :
    (∑ k ∈ Finset.range (n+1), weight k)/2 ≤ ‖deepPrimeWave n β‖ := by
  have hp := Real.pi_pos
  have hcos (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      1/2 ≤ (E ((k:ℝ)*β)).re := by
    have hkn : (k:ℝ) ≤ n := by exact_mod_cast (show k≤n by simpa using hk)
    have hb : (k:ℝ)*|β| ≤ (n:ℝ)*|β| := mul_le_mul_of_nonneg_right hkn (abs_nonneg _)
    have hsmall : |2*Real.pi*((k:ℝ)*β)| ≤ Real.pi/3 := by
      simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤(k:ℝ)),abs_of_pos hp,abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith [mul_le_mul_of_nonneg_left (show (k:ℝ)*|β| ≤ 1/6 by linarith) hp.le]
    unfold E
    rw [Complex.exp_ofReal_mul_I_re,← Real.cos_abs,← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hsmall
  calc
    _ = ∑ k ∈ Finset.range (n+1), weight k*(1/2) := by rw [← Finset.sum_mul]; ring
    _ ≤ ∑ k ∈ Finset.range (n+1), weight k*(E ((k:ℝ)*β)).re :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcos k hk) (weight_nonneg k)
    _ = (deepPrimeWave n β).re := by simp [deepPrimeWave,Complex.mul_re]
    _ ≤ _ := Complex.re_le_norm _

theorem deepPrimeFourth_row_lower {n q : ℕ} (hq : q.Prime) (hqn : q≤n) {β A : ℝ}
    (hβ : 6*(n:ℝ)*|β| ≤ 1) (hA : 0≤A)
    (hm : A + (q:ℝ)*Real.log q ≤ (∑ k ∈ Finset.range (n+1), weight k)/2) :
    A^4 ≤ (q:ℝ)^3 * ∑ a ∈ (Finset.range q).erase 0, ‖deepPrimeWave n (β+(a:ℝ)/q)‖^4 := by
  let s := (Finset.range q).erase 0
  let f := fun a : ℕ => deepPrimeWave n (β+(a:ℝ)/q)
  have hid := deepPrimeWave_row hq hqn β
  have hd : deepPrimeWave n β = (q:ℂ)*(weight q:ℂ)*E ((q:ℝ)*β) - ∑ a ∈ s, f a := by
    change (∑ a ∈ s, f a) + deepPrimeWave n β = _ at hid
    linear_combination hid
  have hn := norm_sub_le ((q:ℂ)*(weight q:ℂ)*E ((q:ℝ)*β)) (∑ a ∈ s, f a)
  rw [← hd, norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg _),show ‖E ((q:ℝ)*β)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one] at hn
  simp only [weight,hq,↓reduceIte] at hn
  have hpeak : A ≤ ‖∑ a ∈ s, f a‖ := by linarith [deepPrimeWave_near_zero n hβ]
  have hcard : (s.card:ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q by simpa only [Finset.card_range] using Finset.card_le_card (Finset.erase_subset 0 (Finset.range q)))
  calc
    A^4 ≤ ‖∑ a ∈ s, f a‖^4 := pow_le_pow_left₀ hA hpeak _
    _ ≤ _ := deepFourthHolder s f
    _ ≤ _ := by
      change (s.card:ℝ)^3 * ∑ a ∈ s, ‖f a‖^4 ≤ (q:ℝ)^3 * ∑ a ∈ s, ‖f a‖^4
      gcongr

set_option maxHeartbeats 800000 in
open MeasureTheory in
theorem deepPrimeFourth_integrated_row {n q : ℕ} (hq : q.Prime) (hqn : q≤n) {r A : ℝ}
    (hr : 0≤r) (hsmall : 6*(n:ℝ)*r ≤ 1) (hA : 0≤A)
    (hm : A+(q:ℝ)*Real.log q ≤ (∑ k ∈ Finset.range (n+1), weight k)/2) :
    (2*r)*A^4 ≤ (q:ℝ)^3 * ∑ a ∈ (Finset.range q).erase 0,
      ∫ t in (-r+(a:ℝ)/q)..(r+(a:ℝ)/q), ‖deepPrimeWave n t‖^4 := by
  let s := (Finset.range q).erase 0
  let f := fun (a : ℕ) (β : ℝ) => ‖deepPrimeWave n (β+(a:ℝ)/q)‖^4
  have hc (a : ℕ) : Continuous (f a) := by
    unfold f deepPrimeWave E
    fun_prop
  have htot : Continuous (fun β => (q:ℝ)^3 * ∑ a ∈ s, f a β) := by fun_prop
  have h := intervalIntegral.integral_mono_on (show -r ≤ r by linarith)
    (g := fun β => (q:ℝ)^3 * ∑ a ∈ s, f a β)
    (intervalIntegrable_const (a := -r) (b := r) (c := A^4))
    (htot.intervalIntegrable (-r) r («μ» := volume)) (fun β hβ =>
      deepPrimeFourth_row_lower hq hqn
        ((mul_le_mul_of_nonneg_left (abs_le.mpr hβ) (by positivity : 0≤6*(n:ℝ))).trans hsmall) hA hm)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun a _ => (hc a).intervalIntegrable _ _)] at h
  have htr (a : ℕ) : (∫ β in -r..r, f a β) =
      ∫ t in (-r+(a:ℝ)/q)..(r+(a:ℝ)/q), ‖deepPrimeWave n t‖^4 :=
    intervalIntegral.integral_comp_add_right (f := fun t => ‖deepPrimeWave n t‖^4) ((a:ℝ)/q)
  simp only [htr,smul_eq_mul,sub_neg_eq_add] at h
  simpa only [two_mul] using h

end DeepPrimeFourth

namespace FourthMomentBand

open Filter

def primes (y : ℕ) : Finset ℕ := (Finset.Ioc y (2*y)).filter Nat.Prime

@[simp] theorem mem_primes {q y : ℕ} : q ∈ primes y ↔ y < q ∧ q ≤ 2*y ∧ q.Prime := by
  simp [primes, and_assoc]

theorem band_cube_identity (t : ℕ) : (t^4)^3 = t^12 := by ring

private theorem mass_to_count (y : ℕ) (hy : 192^4 ≤ y) :
    (y : ℝ)/4 ≤ ((primes y).card : ℝ) * Real.log (2*(y : ℝ)) := by
  have hmass := GoldbachDeepFourth.dyadic_prime_mass y hy
  change (y : ℝ)/4 ≤ ∑ p ∈ primes y, Real.log p at hmass
  calc
    _ ≤ _ := hmass
    _ ≤ ∑ _p ∈ primes y, Real.log (2*(y : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := Finset.mem_filter.mp hp
      exact Real.log_le_log (by exact_mod_cast h.2.pos) (by exact_mod_cast (Finset.mem_Ioc.mp h.1).2)
    _ = _ := by simp

theorem prime_band_card (y : ℕ) (hy : 192^4 ≤ y) :
    (y : ℝ)/(4*Real.log (2*(y : ℝ))) ≤ ((primes y).card : ℝ) := by
  have hy1 : 1 ≤ y := by omega
  have hL : 0 < Real.log (2*(y:ℝ)) := Real.log_pos (by
    have : (1:ℝ) ≤ y := by exact_mod_cast hy1
    linarith)
  apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
  linarith [mass_to_count y hy]

theorem cube_cutoff (y : ℕ) : ⌊((y^3 : ℕ) : ℝ)^(1/3 : ℝ)⌋₊ = y := by
  push_cast
  rw [← Real.rpow_natCast (y : ℝ) 3, ← Real.rpow_mul (Nat.cast_nonneg y)]
  norm_num

theorem prime_band_count_power (t : ℕ) (h192 : 192 ≤ t) :
    (t:ℝ)^3 ≤ 20*((primes (t^4)).card:ℝ) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast (show 0<t by omega)
  let P := primes (t^4)
  have hc := mass_to_count (t^4) (Nat.pow_le_pow_left h192 4)
  push_cast at hc
  change (t:ℝ)^4/4 ≤ (P.card : ℝ) * Real.log (2*(t:ℝ)^4) at hc
  have hlog : Real.log (2*(t:ℝ)^4) ≤ 5*(t:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h₂ : Real.log (2:ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num) using 1
      norm_num
    have htlog := Real.log_le_sub_one_of_pos htR
    change Real.log 2 + (4:ℝ) * Real.log t ≤ 5*t
    linarith
  have hcard : (t:ℝ)^3 ≤ 20*(P.card:ℝ) := by
    apply le_of_mul_le_mul_right (a := (t : ℝ)) _ htR
    nlinarith [hc.trans (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤(P.card:ℝ)))]
  exact hcard

theorem exponent_identity (t : ℕ) : ((t^12:ℕ):ℝ)^(2+(1/6:ℝ)) = (t:ℝ)^26 := by
  push_cast
  rw [← Real.rpow_natCast (t:ℝ) 12, ← Real.rpow_mul (Nat.cast_nonneg t)]
  norm_num

theorem prime_band_power_lower (t : ℕ) (h192 : 192 ≤ t) :
    (t:ℝ)^27/160 ≤ ((t^12:ℕ):ℝ)^3 * ∑ q ∈ primes (t^4), ((q:ℝ)⁻¹)^3 := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast (show 0<t by omega)
  let P := primes (t^4)
  let V : ℝ := ∑ q ∈ P, ((q:ℝ)⁻¹)^3
  have hcard := prime_band_count_power t h192
  change (t:ℝ)^3 ≤ 20*(P.card:ℝ) at hcard
  have hsum : (P.card:ℝ) * ((2*(t:ℝ)^4)⁻¹)^3 ≤ V := by
    calc
      _ = ∑ _q ∈ P, ((2*(t:ℝ)^4)⁻¹)^3 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        have h := Finset.mem_filter.mp hq
        have hqpos : (0:ℝ)<q := by exact_mod_cast h.2.pos
        apply pow_le_pow_left₀ (by positivity)
        apply inv_anti₀ hqpos
        exact_mod_cast (Finset.mem_Ioc.mp h.1).2
  have hV : (P.card:ℝ) ≤ 8*(t:ℝ)^12 * V := by
    calc
      _ = (8*(t:ℝ)^12) * ((P.card:ℝ) * ((2*(t:ℝ)^4)⁻¹)^3) := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hlower : (t:ℝ)^3/160 ≤ (t:ℝ)^12*V := by linarith
  push_cast
  change (t:ℝ)^27/160 ≤ ((t:ℝ)^12)^3 * V
  calc
    _ = (t:ℝ)^24 * ((t:ℝ)^3/160) := by ring
    _ ≤ (t:ℝ)^24 * ((t:ℝ)^12*V) := mul_le_mul_of_nonneg_left hlower (by positivity)
    _ = _ := by ring

/-- Along n=t^12 and y=t^4, the reciprocal-cube band majorizes every
fixed multiple of n^(2+1/6). This also applies along even t. -/
theorem prime_band_growth (C : ℝ) : ∀ᶠ t : ℕ in atTop,
    C * ((t^12 : ℕ) : ℝ)^(2+(1/6 : ℝ)) ≤
      ((t^12 : ℕ) : ℝ)^3 * ∑ q ∈ primes (t^4), ((q : ℝ)⁻¹)^3 := by
  obtain ⟨T,hT⟩ := exists_nat_gt (160*C)
  filter_upwards [eventually_ge_atTop (max T 192)] with t ht
  have h192 : 192 ≤ t := (le_max_right T 192).trans ht
  have hT' : (T:ℝ) ≤ t := by exact_mod_cast ((le_max_left T 192).trans ht)
  have hcost : C ≤ (t : ℝ)/160 := by linarith
  rw [exponent_identity]
  calc
    _ ≤ ((t:ℝ)/160) * (t:ℝ)^26 := mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = (t:ℝ)^27/160 := by ring
    _ ≤ _ := prime_band_power_lower t h192

/-- The desk's cube-root denominator and logarithmic radii fit between
the next dyadic rational centers on this same sequence. -/
theorem prime_band_geometry (t : ℕ) (ht : 1024 ≤ t) :
    4 * (2*t^4+1) * (256*t^4*(Nat.log 2 (t^12+2))^2+1) < t^12 := by
  have ht1 : 1 ≤ t := by omega
  have ht2 : 2 ≤ t := by omega
  have hp : t ≤ 2^t := (show t < 2^t from Nat.lt_two_pow_self).le
  have he : t^12 ≤ 2^(12*t) := by
    calc
      _ ≤ (2^t)^12 := Nat.pow_le_pow_left hp 12
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have htwo : 2 ≤ 2^(12*t) := by
    calc 2 = 2^1 := by norm_num
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hg : t^12+2 ≤ 2^(12*t+1) := by
    rw [show 2^(12*t+1) = 2^(12*t)*2 by rw [pow_succ]]
    omega
  have hlog : Nat.log 2 (t^12+2) ≤ 13*t := by
    have h := Nat.log_mono_right (b:=2) hg
    rw [Nat.log_pow (by decide)] at h
    omega
  have h4 : 1 ≤ t^4 := Nat.one_le_pow _ _ ht1
  have h6 : 1 ≤ t^6 := Nat.one_le_pow _ _ ht1
  have hbound : 256*t^4*(Nat.log 2 (t^12+2))^2+1 ≤ 43265*t^6 := by
    calc
      _ ≤ 256*t^4*(13*t)^2+1 := by gcongr
      _ = 43264*t^6+1 := by ring
      _ ≤ _ := by omega
  calc
    _ ≤ 4*(3*t^4)*(43265*t^6) := by gcongr; omega
    _ = 519180*t^10 := by ring
    _ < t^2*t^10 := by
      apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
      exact lt_of_lt_of_le (by norm_num : 519180 < 1024^2) (Nat.pow_le_pow_left ht 2)
    _ = _ := by ring

end FourthMomentBand

section FourthTubeIntegral
open MeasureTheory Set
open scoped BigOperators Interval
/-- Translate disjoint rational intervals back to a common offset and sum
a lower bound for every denominator's row over a measurable set. -/
theorem deep_tube_row_integral_le
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (D : Set ℝ) (hD : MeasurableSet D) (F : ℝ → ℝ)
    (hF : Continuous F) (hpos : ∀ x, 0 ≤ F x) (k : ℕ → ℝ)
    (hint : ∀ q ∈ s, ∀ a ∈ t q,
      Icc ((a : ℝ) / q - ρ) ((a : ℝ) / q + ρ) ⊆ Icc (0 : ℝ) 1)
    (hdeep : ∀ q ∈ s, ∀ a ∈ t q,
      Icc ((a : ℝ) / q - ρ) ((a : ℝ) / q + ρ) ⊆ D)
    (hdis : ∀ q ∈ s, ∀ a ∈ t q, ∀ r ∈ s, ∀ b ∈ t r,
      (q, a) ≠ (r, b) → Disjoint (Icc ((a : ℝ) / q - ρ) ((a : ℝ) / q + ρ))
        (Icc ((b : ℝ) / r - ρ) ((b : ℝ) / r + ρ)))
    (hrow : ∀ q ∈ s, ∀ β ∈ Icc (-ρ) ρ, k q ≤ ∑ a ∈ t q, F ((a : ℝ) / q + β)) :
    (∑ q ∈ s, (2 * ρ) * k q) ≤ ∫ x in (0 : ℝ)..1, D.indicator F x := by
  classical
  let I := fun j : Σ _ : ℕ, ℕ =>
    Icc ((j.2 : ℝ) / j.1 - ρ) ((j.2 : ℝ) / j.1 + ρ)
  have hr : -ρ ≤ ρ := by linarith
  have hlocal (q : ℕ) (hq : q ∈ s) :
      (2 * ρ) * k q ≤ ∑ a ∈ t q, ∫ x in I ⟨q, a⟩, F x := by
    have hcont (a : ℕ) : Continuous (fun β : ℝ => F ((a : ℝ) / q + β)) :=
      hF.comp (continuous_const.add continuous_id)
    calc
      (2 * ρ) * k q = ∫ _ in (-ρ)..ρ, k q := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ ∫ β in (-ρ)..ρ, ∑ a ∈ t q, F ((a : ℝ) / q + β) :=
        intervalIntegral.integral_mono_on hr (continuous_const.intervalIntegrable _ _)
          ((continuous_finsetSum _ (fun a _ => hcont a)).intervalIntegrable _ _) (hrow q hq)
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum (fun a _ => (hcont a).intervalIntegrable _ _)]
        apply Finset.sum_congr rfl
        intro a _
        rw [intervalIntegral.integral_comp_add_left]
        dsimp only [I]
        simp only [← sub_eq_add_neg]
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hd : (↑(s.sigma t) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i j => Disjoint (I i) (I j)) := by
    rintro ⟨q,a⟩ hi ⟨r,b⟩ hj hne
    obtain ⟨hq, ha⟩ := Finset.mem_sigma.mp hi
    obtain ⟨hr', hb⟩ := Finset.mem_sigma.mp hj
    apply hdis q hq a ha r hr' b hb
    rintro he
    cases he
    exact hne rfl
  have hun : (⋃ i ∈ s.sigma t, I i) ⊆ Icc (0 : ℝ) 1 ∩ D := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hq, ha⟩ := Finset.mem_sigma.mp hi
    exact ⟨hint i.1 hq i.2 ha hx, hdeep i.1 hq i.2 ha hx⟩
  calc
    _ ≤ ∑ q ∈ s, ∑ a ∈ t q, ∫ x in I ⟨q, a⟩, F x := Finset.sum_le_sum hlocal
    _ = ∫ x in ⋃ i ∈ s.sigma t, I i, F x := by
      rw [integral_biUnion_finset (s.sigma t) (fun _ _ => measurableSet_Icc) hd
        (fun _ _ => hF.continuousOn.integrableOn_Icc), Finset.sum_sigma]
    _ ≤ ∫ x in Icc (0 : ℝ) 1 ∩ D, F x :=
      setIntegral_mono_set (hF.continuousOn.integrableOn_Icc.mono_set Set.inter_subset_left)
        (Filter.Eventually.of_forall hpos) (Filter.Eventually.of_forall hun)
    _ = _ := by
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
        setIntegral_indicator hD]


end FourthTubeIntegral

section DeepFourthGeometry
open MeasureTheory

noncomputable def deepTube (ρ : ℝ) (q a : ℕ) : Set ℝ :=
  Set.Icc ((a:ℝ)/q-ρ) ((a:ℝ)/q+ρ)

private theorem deepTube_coprime {q a : ℕ} (hq : q.Prime) (ha : 0 < a) (haq : a < q) :
    a.Coprime q := (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha haq)).symm

theorem deepTube_cross {q r a b : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (hne : (q,a) ≠ (r,b)) : a*r ≠ b*q := by
  intro e
  have hqr := ha.symm.dvd_of_dvd_mul_left (e ▸ dvd_mul_left q b)
  have hrq := hb.symm.dvd_of_dvd_mul_left (e.symm ▸ dvd_mul_left r a)
  have eq := Nat.dvd_antisymm hqr hrq
  subst r
  have eab := (Nat.mul_left_inj hq.ne').mp e
  exact hne (by rw [eab])

theorem deepTube_separation {q r a b : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hne : a*r ≠ b*q) : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hq0 hr0)]
  apply (div_le_div_iff_of_pos_right (mul_pos hq0 hr0)).mpr
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [neg_le_abs ((a:ℝ)*r-b*q)]
  · have h' : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [le_abs_self ((a:ℝ)*r-b*q)]

theorem deepTubes_disjoint {n Y q r a b : ℕ} (hn : 0 < n) (hsize : (2*Y)^2 ≤ n)
    (hq : q.Prime) (hr : r.Prime) (hqY : q ≤ 2*Y) (hrY : r ≤ 2*Y)
    (ha : a ∈ Finset.Ico 1 q) (hb : b ∈ Finset.Ico 1 r) (hne : (q,a) ≠ (r,b)) :
    Disjoint (deepTube (1/(20*(n:ℝ))) q a) (deepTube (1/(20*(n:ℝ))) r b) := by
  obtain ⟨ha1,ha2⟩ := Finset.mem_Ico.mp ha
  obtain ⟨hb1,hb2⟩ := Finset.mem_Ico.mp hb
  have hsep := deepTube_separation hq.pos hr.pos (deepTube_cross hq.pos hr.pos
    (deepTube_coprime hq ha1 ha2) (deepTube_coprime hr hb1 hb2) hne)
  have hqr : q*r ≤ n := (Nat.mul_le_mul hqY hrY).trans (by simpa [pow_two] using hsize)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr.pos
  have hrec : 1/(n:ℝ) ≤ 1/((q:ℝ)*r) :=
    one_div_le_one_div_of_le (mul_pos hq0 hr0) (by exact_mod_cast hqr)
  have hlen : 1/(20*(n:ℝ)) + 1/(20*n) < 1/n := by
    field_simp
    linarith
  refine Set.disjoint_left.mpr ?_
  intro t ht ht'
  obtain ⟨haL,haR⟩ := ht
  obtain ⟨hbL,hbR⟩ := ht'
  have hd : |(a:ℝ)/q-b/r| ≤ 1/(20*(n:ℝ))+1/(20*n) := abs_le.mpr ⟨by linarith,by linarith⟩
  linarith only [hrec,hsep,hd,hlen]

theorem deepTube_inside_unit {n q a : ℕ} (hn : 0 < n) (hq : q.Prime) (hqn : q ≤ n)
    (ha : a ∈ Finset.Ico 1 q) : deepTube (1/(20*(n:ℝ))) q a ⊆ Set.Icc 0 1 := by
  obtain ⟨ha1,ha2⟩ := Finset.mem_Ico.mp ha
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hrad : 1/(20*(n:ℝ)) ≤ 1/q :=
    one_div_le_one_div_of_le hq0 (by linarith [show (q:ℝ) ≤ n by exact_mod_cast hqn])
  have hlo : 1/(q:ℝ) ≤ (a:ℝ)/q := (div_le_div_iff_of_pos_right hq0).mpr (by exact_mod_cast ha1)
  have hsum : (a:ℝ)/q+1/q ≤ 1 := by
    rw [← add_div, div_le_one hq0]
    exact_mod_cast (Nat.succ_le_of_lt ha2)
  rintro t ⟨ht₁,ht₂⟩
  exact ⟨by linarith,by linarith⟩

theorem deepTube_inside_deep {n B H q a : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqB : B < q) (hqB' : q ≤ 2*B) (hH : 2*B ≤ H) (hsep : 2*H*(2*B) < n)
    (ha : a ∈ Finset.Ico 1 q) :
    deepTube (1/(20*(n:ℝ))) q a ⊆ (coreArcBand n H 0 B)ᶜ := by
  obtain ⟨ha1,ha2⟩ := Finset.mem_Ico.mp ha
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hqH : (q:ℝ) ≤ H := by exact_mod_cast hqB'.trans hH
  have hrad : 1/(20*(n:ℝ)) ≤ (H:ℝ)/(q*n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hqH hn0.le, mul_nonneg (show 0 ≤ (H:ℝ) by positivity) hn0.le]
  rintro t ⟨ht₁,ht₂⟩ ht
  have hbig : t ∈ coreArcBand n H B (2*B) :=
    ⟨q,a,hqB,hqB',ha2.le,deepTube_coprime hq ha1 ha2,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  exact (Set.disjoint_left.mp (coreArcBand_disjoint (by omega : B ≤ 2*B) hsep)) ht hbig

end DeepFourthGeometry

section DeepFourthPrimeMass

private theorem fourth_total_prime_mass {n : ℕ} (hn : 2*192^4 ≤ n) :
    (n:ℝ)/16 ≤ ∑ k ∈ Finset.range (n+1), weight k := by
  have hhalf : 192^4 ≤ n/2 := by omega
  have inc : (Finset.Ioc (n/2) (2*(n/2))).filter Nat.Prime ⊆ Finset.range (n+1) := by
    intro p hp
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    exact Finset.mem_range.mpr (by omega)
  have hweight : (∑ p ∈ (Finset.Ioc (n/2) (2*(n/2))).filter Nat.Prime, Real.log p) =
      ∑ p ∈ (Finset.Ioc (n/2) (2*(n/2))).filter Nat.Prime, weight p :=
    Finset.sum_congr rfl fun p hp => by simp [weight,(Finset.mem_filter.mp hp).2]
  have hsum := dyadic_prime_mass (n/2) hhalf
  rw [hweight] at hsum
  have hg := hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg inc (fun i _ _ => weight_nonneg i))
  have hh : n ≤ 4*(n/2) := by omega
  have hhr : (n:ℝ) ≤ 4*↑(n/2) := by exact_mod_cast hh
  linarith only [hg,hhr]

theorem fourth_row_mass_budget {n Y q : ℕ} (hn : 2*192^4 ≤ n) (hY : 256 ≤ Y)
    (hy : Y^3 ≤ n) (hq : q.Prime) (hqY : q ≤ 2*Y) :
    (n:ℝ)/64 + (q:ℝ)*Real.log q ≤ (∑ k ∈ Finset.range (n+1), weight k)/2 := by
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hlog : Real.log (q:ℝ) ≤ q := by linarith [Real.log_le_sub_one_of_pos hq0]
  have hqr : (q:ℝ) ≤ 2*Y := by exact_mod_cast hqY
  have hsize : (256:ℝ) ≤ Y := by exact_mod_cast hY
  have hcube : (Y:ℝ)^3 ≤ n := by exact_mod_cast hy
  have hsq : (q:ℝ)^2 ≤ (2*(Y:ℝ))^2 := by gcongr
  have hpow := mul_nonneg (sq_nonneg (Y:ℝ)) (sub_nonneg.mpr hsize)
  nlinarith only [fourth_total_prime_mass hn, mul_le_mul_of_nonneg_left hlog hq0.le,hsq,hpow,hcube]

end DeepFourthPrimeMass

section DeepFourthLower
open MeasureTheory FourthMomentBand

noncomputable def deepFourthMass (n : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, ((coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n))ᶜ).indicator
    (fun u => ‖deepPrimeWave n u‖^4) x

theorem deepFourth_prime_tubes_on {n Y : ℕ}
    (hn : 2*192^4 ≤ n) (hY : 256 ≤ Y) (hYn : Y^3 ≤ n)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hcover : ∀ q ∈ primes Y, ∀ a ∈ Finset.Ico 1 q, deepTube (1/(20*(n:ℝ))) q a ⊆ D) :
    (n:ℝ)^3/(10*64^4) * (∑ q ∈ primes Y, ((q:ℝ)⁻¹)^3) ≤
      ∫ x in (0:ℝ)..1, D.indicator (fun u => ‖deepPrimeWave n u‖^4) x := by
  let ρ : ℝ := 1/(20*(n:ℝ))
  let V := fun u : ℝ => ‖deepPrimeWave n u‖^4
  let k := fun q : ℕ => ((n:ℝ)/64)^4/(q:ℝ)^3
  have hnp : 0 < n := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hnp
  have hsize : (2*Y)^2 ≤ n := by
    have hc := Nat.mul_le_mul_left (Y*Y) (show 4 ≤ Y by omega)
    nlinarith only [hc,hYn]
  have hqn {q : ℕ} (hq : q ∈ primes Y) : q ≤ n := by
    have hy := (mem_primes.mp hq).2.1
    have ht := Nat.mul_le_mul_left (2*Y) (show 1 ≤ 2*Y by omega)
    nlinarith only [hy,ht,hsize]
  have hc : Continuous V := by dsimp [V,deepPrimeWave,ExtendedArcCoefficient.E]; fun_prop
  have hj := deep_tube_row_integral_le (primes Y) (fun q => Finset.Ico 1 q) ρ (by positivity)
    D hD V hc (fun _ => by dsimp [V]; positivity) k
    (fun q hq a ha => deepTube_inside_unit hnp (mem_primes.mp hq).2.2 (hqn hq) ha)
    hcover
    (fun q hq a ha r hr b hb hne => deepTubes_disjoint hnp hsize (mem_primes.mp hq).2.2
      (mem_primes.mp hr).2.2 (mem_primes.mp hq).2.1 (mem_primes.mp hr).2.1 ha hb hne) ?_
  · calc
      _ = ∑ q ∈ primes Y, 2*ρ*k q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (mem_primes.mp hq).2.2.ne_zero
        dsimp [ρ,k]
        field_simp
        ring
      _ ≤ _ := hj
  · intro q hq β hβ
    have hq' := (mem_primes.mp hq).2.2
    have hqpos : 0 < (q:ℝ) := by exact_mod_cast hq'.pos
    have habs := abs_le.mpr hβ
    have hsmall : 6*(n:ℝ)*|β| ≤ 1 := calc
      _ ≤ 6*(n:ℝ)*ρ := mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 1 := by dsimp [ρ]; field_simp; linarith
    have hrow := deepPrimeFourth_row_lower hq' (hqn hq) hsmall (by positivity : 0 ≤ (n:ℝ)/64)
      (fourth_row_mass_budget hn hY hYn hq' (mem_primes.mp hq).2.1)
    have he : (Finset.range q).erase 0 = Finset.Ico 1 q := by ext a; simp; omega
    rw [he] at hrow
    dsimp only [k,V]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [add_comm β, mul_comm ((q:ℝ)^3)] using hrow

theorem deepFourth_prime_tubes {n Y H : ℕ}
    (hn : 2*192^4 ≤ n) (hY : 256 ≤ Y) (hYn : Y^3 ≤ n) (hH : 2*Y ≤ H)
    (hsep : 2*H*(2*Y) < n) :
    (n:ℝ)^3/(10*64^4) * (∑ q ∈ primes Y, ((q:ℝ)⁻¹)^3) ≤
      ∫ x in (0:ℝ)..1, (coreArcBand n H 0 Y)ᶜ.indicator (fun u => ‖deepPrimeWave n u‖^4) x := by
  apply deepFourth_prime_tubes_on hn hY hYn _ (measurable_coreArcBand ..).compl
  intro q hq a ha
  exact deepTube_inside_deep (by omega : 0 < n) (mem_primes.mp hq).2.2
    (mem_primes.mp hq).1 (mem_primes.mp hq).2.1 hH hsep ha

end DeepFourthLower

section FrozenDeepFourth
open MeasureTheory FourthMomentBand Filter

theorem deepFourth_sequence_lower (t : ℕ) (ht : 1024 ≤ t) :
    ((t^12:ℕ):ℝ)^3/(10*64^4) * (∑ q ∈ primes (t^4), ((q:ℝ)⁻¹)^3) ≤
      deepFourthMass (t^12) := by
  have hcut : medDeskD (t^12) = t^4 := by
    dsimp only [medDeskD]
    rw [← band_cube_identity t]
    exact cube_cutoff _
  let H := 256*t^4*medDeskQ (t^12)
  have hlog := Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ t^12+2)
  have hQ : 1 ≤ medDeskQ (t^12) := Nat.one_le_pow _ _ hlog
  have hH : 2*t^4 ≤ H := by
    dsimp [H]
    have h := Nat.mul_le_mul_left (256*t^4) hQ
    omega
  have hg := prime_band_geometry t ht
  change 4 * (2*t^4+1) * (H+1) < t^12 at hg
  have hs : 2*H*(2*t^4) < t^12 := by
    nlinarith only [hg, Nat.zero_le H, Nat.zero_le (t^4), Nat.zero_le (H*t^4)]
  have hn : 2*192^4 ≤ t^12 := (by norm_num : 2*192^4 ≤ 1024^12).trans (Nat.pow_le_pow_left ht 12)
  have hY : 256 ≤ t^4 := (by norm_num : 256 ≤ 1024^4).trans (Nat.pow_le_pow_left ht 4)
  unfold deepFourthMass
  rw [hcut]
  exact deepFourth_prime_tubes hn hY (band_cube_identity t).le hH hs

/-- Even at the fixed exponent 1/6, arbitrarily large even targets
violate the proposed deep-arc fourth moment estimate. -/
theorem deepFourth_even_counterexamples (N : ℕ) :
    ∃ n ≥ N, Even n ∧ (n:ℝ)^(2+(1/6:ℝ)) < deepFourthMass n := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (prime_band_growth (20*64^4))
  let a := max N (max T 1024)+1
  let t := 2*a
  have ht : 1024 ≤ t := by dsimp [t,a]; omega
  have htT : T ≤ t := by dsimp [t,a]; omega
  have htN : N ≤ t := by dsimp [t,a]; omega
  have ht1 : 1 ≤ t := by omega
  have h12 : N ≤ t^12 := by
    have hh := Nat.mul_le_mul_left t (Nat.one_le_pow 11 t ht1)
    calc N ≤ t := htN
         _ ≤ t*t^11 := by simpa only [Nat.mul_one] using hh
         _ = t^12 := by ring
  refine ⟨t^12,h12,⟨t^11*a,?_⟩,?_⟩
  · rw [pow_succ]
    dsimp [t]
    ring
  · have hp : 0 < ((t^12:ℕ):ℝ)^(2+(1/6:ℝ)) := by
      have hh : 0 < t := by omega
      positivity
    have hg := hT t htT
    have hl := deepFourth_sequence_lower t ht
    nlinarith only [hp,hg,hl]

/-- Negation of the production registry's exact frozen statement for
L-goldbach-frontier-deep-fourth-moment-conjecture. -/
theorem not_frontier_deep_fourth_moment_conjecture :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)) := by
  change ¬ (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N, deepFourthMass n ≤ (n:ℝ)^(2+η))
  intro h
  obtain ⟨N,hN⟩ := h (1/6) (by norm_num)
  obtain ⟨n,hn,_,hl⟩ := deepFourth_even_counterexamples N
  exact (not_lt_of_ge (hN n hn)) hl

end FrozenDeepFourth

section AllDenominatorBands
open MeasureTheory FourthMomentBand

private theorem reciprocal_cube_mass {Y : ℕ} (hY : 192^4 ≤ Y) :
    1/(32*(Y:ℝ)^2*Real.log (2*Y)) ≤ ∑ q ∈ primes Y, ((q:ℝ)⁻¹)^3 := by
  have hy0 : 0 < Y := by omega
  have hyr : 0 < (Y:ℝ) := by exact_mod_cast hy0
  have hl : 0 < Real.log (2*(Y:ℝ)) := Real.log_pos (by
    have hy1 : 1 ≤ (Y:ℝ) := by exact_mod_cast hy0
    linarith)
  have hcount := prime_band_card Y hY
  calc
    _ = ((Y:ℝ)/(4*Real.log (2*Y)))*((2*Y:ℝ)⁻¹)^3 := by field_simp; ring
    _ ≤ ((primes Y).card:ℝ)*((2*Y:ℝ)⁻¹)^3 :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ∑ _q ∈ primes Y, ((2*Y:ℝ)⁻¹)^3 := by simp
    _ ≤ _ := by
      refine Finset.sum_le_sum fun q hq => ?_
      have h := mem_primes.mp hq
      apply pow_le_pow_left₀ (by positivity)
      exact inv_anti₀ (by exact_mod_cast h.2.2.pos) (by exact_mod_cast h.2.1)

theorem fourth_mass_quantitative_of_row_bound {n : ℕ} (hn : 2*192^4 ≤ n)
    (hb : 192^4 ≤ medDeskD n) (hy : (medDeskD n)^3 ≤ n) {M : ℝ}
    (hraw : (n:ℝ)^3/(10*64^4)*(∑ q ∈ primes (medDeskD n), ((q:ℝ)⁻¹)^3) ≤ M) :
    (n:ℝ)^(7/3:ℝ)/(320*64^4*Real.log n) ≤ M := by
  let Y := medDeskD n
  have hn2 : 2 ≤ n := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast (show 0 < medDeskD n by omega)
  have hYr1 : 1 ≤ (Y:ℝ) := by exact_mod_cast (show 1 ≤ medDeskD n by omega)
  have hlY : 0 < Real.log (2*(Y:ℝ)) := Real.log_pos (by linarith)
  have hln : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hY2 : (Y:ℝ)^2 ≤ (n:ℝ)^(2/3:ℝ) := by
    have hfloor : (Y:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Y) hfloor 2
    rwa [← Real.rpow_mul_natCast hnr.le, show (1/3:ℝ)*(2:ℕ)=2/3 by norm_num] at hh
  have hYn : 2*Y ≤ n := by
    change Y^3 ≤ n at hy
    have h1 : 2 ≤ Y := by dsimp [Y]; omega
    have h2 := Nat.mul_le_mul_left Y h1
    have h3 := Nat.mul_le_mul_left (Y*Y) (show 1 ≤ Y by omega)
    nlinarith only [hy,h2,h3]
  have hLy : Real.log (2*(Y:ℝ)) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hYn)
  have hden : 32*(Y:ℝ)^2*Real.log (2*Y) ≤ 32*(n:ℝ)^(2/3:ℝ)*Real.log n := by gcongr
  have hmass := (one_div_le_one_div_of_le (by positivity) hden).trans (reciprocal_cube_mass hb)
  have hproduct : (n:ℝ)^(7/3:ℝ)*(n:ℝ)^(2/3:ℝ) = (n:ℝ)^3 := by
    rw [← Real.rpow_add hnr, show (7/3:ℝ)+2/3 = (3:ℝ) by norm_num]
    norm_cast
  calc
    _ = (n:ℝ)^3/(10*64^4)*(1/(32*(n:ℝ)^(2/3:ℝ)*Real.log n)) := by
      rw [← hproduct]
      field_simp
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hmass (by positivity)).trans hraw

theorem fourth_mass_quantitative {n : ℕ} (hn : 2*192^4 ≤ n)
    (hb : 192^4 ≤ medDeskD n) (hy : (medDeskD n)^3 ≤ n)
    (hH : 2*(medDeskD n) ≤ 256*(medDeskD n)*(medDeskQ n))
    (hsep : 2*(256*(medDeskD n)*(medDeskQ n))*(2*(medDeskD n)) < n) :
    (n:ℝ)^(7/3:ℝ)/(320*64^4*Real.log n) ≤ deepFourthMass n := by
  exact fourth_mass_quantitative_of_row_bound hn hb hy
    (deepFourth_prime_tubes hn (by omega : 256 ≤ medDeskD n) hy hH hsep)

end AllDenominatorBands

section AllDeepFourthCutoffs
open Filter
set_option maxHeartbeats 700000 in
theorem eventually_deep_fourth_budget :
    ∀ᶠ n : ℕ in atTop,
      2*192^4 ≤ n ∧ 192^4 ≤ medDeskD n ∧ (medDeskD n)^3 ≤ n ∧
      2*medDeskD n ≤ 256*medDeskD n*medDeskQ n ∧
      2*(256*medDeskD n*medDeskQ n)*(2*medDeskD n) < n := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 3000000, eventually_ge_atTop ((192^4)^3:ℕ)] with n hlog hn
  have hlarge : 2*192^4 ≤ n := le_trans (by decide) hn
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  let L := Real.log (n:ℝ)
  let m := Nat.log 2 (n+2)
  have hL : 3000000 ≤ L := hlog
  have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hm : (m:ℝ) ≤ 4*L := by
    have he : (2:ℝ)^m ≤ (n:ℝ)+2 := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
    have hl := Real.log_le_log (by positivity) he
    rw [Real.log_pow] at hl
    have hn2 : (n:ℝ)+2 ≤ (n:ℝ)^2 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast (show 2≤n by omega)
      nlinarith [sq_nonneg ((n:ℝ)-2)]
    have hl' := Real.log_le_log (by positivity) hn2
    rw [Real.log_pow] at hl'
    norm_num at hl'
    have hmul := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) m)
    change _ ≤ 4*Real.log n
    nlinarith only [hl,hl',hmul]
  have hgap : 1024*medDeskQ n < medDeskD n := by
    have hp := Real.pow_div_factorial_le_exp (L/3) (by linarith : 0 ≤ L/3) 3
    norm_num [Nat.factorial] at hp
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hm 2
    have hr : ((1024*m^2+1:ℕ):ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
      push_cast
      rw [Real.rpow_def_of_pos hn0]
      change _ ≤ Real.exp (L*(1/3))
      rw [show L*(1/3) = L/3 by ring]
      nlinarith only [hp,hs,mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL),sq_nonneg (L-1),hL]
    exact Nat.le_floor hr
  have hroot : ((n:ℝ)^(1/3:ℝ))^3 = (n:ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have hB : 192^4 ≤ medDeskD n := by
    apply Nat.le_floor
    have hnr : ((192^4:ℕ):ℝ)^3 ≤ n := by exact_mod_cast hn
    by_contra! hnot
    have hlt := pow_lt_pow_left₀ hnot (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by decide : 3≠0)
    rw [hroot] at hlt
    exact (not_lt_of_ge hnr) hlt
  have hcube : (medDeskD n)^3 ≤ n := by
    have h := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ))
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (medDeskD n)) h 3
    rw [hroot] at hh
    exact_mod_cast hh
  have hQ : 1 ≤ medDeskQ n := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have hBpos : 0 < medDeskD n := by omega
  refine ⟨hlarge,hB,hcube,?_,?_⟩
  · have h := Nat.mul_le_mul_left (256*medDeskD n) hQ
    nlinarith only [h]
  · have h := Nat.mul_lt_mul_of_pos_right hgap (Nat.mul_pos hBpos hBpos)
    nlinarith only [h,hcube]
end AllDeepFourthCutoffs

/-- Every sufficiently large index has more deep-arc fourth mass than this explicit lower bound. -/
theorem eventually_fourth_mass_lower : ∀ᶠ n : ℕ in Filter.atTop,
    (n:ℝ)^(7/3:ℝ)/(320*64^4*Real.log n) ≤ deepFourthMass n := by
  filter_upwards [eventually_deep_fourth_budget] with n hn
  obtain ⟨a,b,c,d,e⟩ := hn
  exact fourth_mass_quantitative a b c d e

section SignedPrimePeak
open ExtendedArcCoefficient
abbrev peakNum (q : ℕ) := (Finset.range q).erase 0
noncomputable def peakMean (n q : ℕ) (β : ℝ) : ℂ :=
  ((q:ℂ)*(weight q:ℂ)*E ((q:ℝ)*β) - deepPrimeWave n β) / ((q:ℂ)-1)
noncomputable def peakFluct (n q : ℕ) (β : ℝ) (a : ℕ) : ℂ :=
  deepPrimeWave n (β+(a:ℝ)/q) - peakMean n q β
noncomputable def peakChar (n q a : ℕ) : ℂ := E (-(n:ℝ)*((a:ℝ)/q))
noncomputable def peakSigned (n q : ℕ) (β : ℝ) : ℂ :=
  ∑ a ∈ peakNum q, (deepPrimeWave n (β+(a:ℝ)/q))^2 * E (-(n:ℝ)*(β+(a:ℝ)/q))
noncomputable def peakVariance (n q : ℕ) (β : ℝ) : ℝ :=
  ∑ a ∈ peakNum q, ‖peakFluct n q β a‖^2

private lemma peakCard {q : ℕ} (hq : q.Prime) : ((peakNum q).card:ℂ) = (q:ℂ)-1 := by
  rw [peakNum,Finset.card_erase_of_mem (Finset.mem_range.mpr hq.pos),Finset.card_range]
  exact_mod_cast Nat.cast_sub (R := ℤ) hq.one_le

theorem peakFluct_sum {n q : ℕ} (hq : q.Prime) (hn : q≤n) (β : ℝ) :
    ∑ a ∈ peakNum q, peakFluct n q β a = 0 := by
  have h := deepPrimeWave_row hq hn β
  have hz : (q:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.one_lt.ne')
  simp only [peakFluct,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,peakCard hq,peakMean]
  rw [show ∀ x : ℂ, ((q:ℂ)-1)*(x/((q:ℂ)-1)) = x by intro x; field_simp]
  change (∑ a ∈ peakNum q, _) + _ = _ at h
  linear_combination h

private lemma peakChar_one {n q : ℕ} (hq : q.Prime) (hd : q∣n) (a : ℕ) :
    peakChar n q a = 1 := by
  obtain ⟨k,rfl⟩ := hd
  unfold peakChar E
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne_zero
  rw [show -(↑(q*k):ℝ)*((a:ℝ)/q) = -((k*a:ℕ):ℝ) by push_cast; field_simp]
  rw [show (((2*Real.pi*(-((k*a:ℕ):ℝ)) : ℝ):ℂ)*Complex.I) =
    -(((k*a:ℕ):ℂ)*(2*Real.pi*Complex.I)) by push_cast; ring,Complex.exp_neg,
    Complex.exp_nat_mul_two_pi_mul_I,inv_one]

theorem peakChar_sum {n q : ℕ} (hq : q.Prime) :
    ∑ a ∈ peakNum q, peakChar n q a = if q∣n then (q:ℂ)-1 else -1 := by
  by_cases hd : q∣n
  · simp [hd,peakChar_one hq hd,peakCard hq]
  · have hc := (hq.coprime_iff_not_dvd.mpr hd).symm
    have hp := (Complex.isPrimitiveRoot_exp_of_coprime n q hq.ne_zero hc).inv
    have hall : ∑ a ∈ Finset.range q, peakChar n q a = 0 := by
      convert hp.geom_sum_eq_zero hq.one_lt using 1
      apply Finset.sum_congr rfl
      intro a _
      rw [← Complex.exp_neg,← Complex.exp_nat_mul]
      unfold peakChar E
      congr 1
      push_cast
      ring
    have hz : peakChar n q 0 = 1 := by simp [peakChar,E]
    have h := (Finset.sum_erase_add (Finset.range q) (peakChar n q) (Finset.mem_range.mpr hq.pos)).trans hall
    rw [hz] at h
    simp only [hd,↓reduceIte]
    exact eq_neg_of_add_eq_zero_left h

theorem peakSigned_exact {n q : ℕ} (hq : q.Prime) (β : ℝ) :
    peakSigned n q β = E (-(n:ℝ)*β) *
      ((peakMean n q β)^2*(if q∣n then (q:ℂ)-1 else -1) +
       2*peakMean n q β*(∑ a ∈ peakNum q, peakChar n q a * peakFluct n q β a) +
       ∑ a ∈ peakNum q, peakChar n q a*(peakFluct n q β a)^2) := by
  rw [← peakChar_sum hq,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  unfold peakSigned
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_add,phase_add]
  unfold peakFluct peakChar
  ring

private lemma peakRemainder_norm (n q : ℕ) (β : ℝ) :
    ‖E (-(n:ℝ)*β) * ∑ a ∈ peakNum q, peakChar n q a*(peakFluct n q β a)^2‖ ≤
      peakVariance n q β := by
  have he (t : ℝ) : ‖E t‖=1 := Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul,he,one_mul]
  refine (norm_sum_le _ _).trans_eq ?_
  simp [peakVariance,peakChar,norm_pow,he]

theorem peakSigned_fixed_frequency_floor {n q : ℕ} (hq : q.Prime) (β : ℝ) :
    (E (-(n:ℝ)*β) *
      ((peakMean n q β)^2*(if q∣n then (q:ℂ)-1 else -1) +
       2*peakMean n q β*(∑ a ∈ peakNum q, peakChar n q a * peakFluct n q β a))).re
      - peakVariance n q β ≤ (peakSigned n q β).re := by
  rw [peakSigned_exact hq]
  conv_rhs => rw [mul_add,Complex.add_re]
  have h := peakRemainder_norm n q β
  have ha := Complex.abs_re_le_norm (E (-(n:ℝ)*β) * ∑ a ∈ peakNum q, peakChar n q a*(peakFluct n q β a)^2)
  linarith [neg_abs_le (E (-(n:ℝ)*β) * ∑ a ∈ peakNum q, peakChar n q a*(peakFluct n q β a)^2).re]

theorem peakSigned_divisor_floor {n q : ℕ} (hq : q.Prime) (hn : q≤n) (hd : q∣n) (β : ℝ) :
    (E (-(n:ℝ)*β) * ((peakMean n q β)^2 * ((q:ℂ)-1))).re -
      peakVariance n q β ≤ (peakSigned n q β).re := by
  simpa only [hd,↓reduceIte,peakChar_one hq hd,one_mul,peakFluct_sum hq hn,mul_zero,add_zero]
    using peakSigned_fixed_frequency_floor hq (n := n) β

private lemma peakProjection_norm (n q : ℕ) (β : ℝ) :
    ‖∑ a ∈ peakNum q, peakChar n q a * peakFluct n q β a‖ ≤
      Real.sqrt ((peakNum q).card * peakVariance n q β) := by
  have he (a : ℕ) : ‖peakChar n q a‖=1 := Complex.norm_exp_ofReal_mul_I _
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul,he,one_mul]
  have h : (∑ a ∈ peakNum q, ‖peakFluct n q β a‖)^2 ≤ (peakNum q).card * peakVariance n q β := by
    simpa [peakVariance] using Finset.sum_mul_sq_le_sq_mul_sq (peakNum q) (fun _ => (1:ℝ)) (fun a => ‖peakFluct n q β a‖)
  exact Real.le_sqrt_of_sq_le h

theorem peakSigned_variance_floor {n q : ℕ} (hq : q.Prime) (β : ℝ) :
    (E (-(n:ℝ)*β) * ((peakMean n q β)^2*(if q∣n then (q:ℂ)-1 else -1))).re -
    2*‖peakMean n q β‖*Real.sqrt ((peakNum q).card*peakVariance n q β) -
    peakVariance n q β ≤ (peakSigned n q β).re := by
  let z := E (-(n:ℝ)*β) * (2*peakMean n q β*(∑ a ∈ peakNum q, peakChar n q a * peakFluct n q β a))
  have hz : ‖z‖ ≤ 2*‖peakMean n q β‖*Real.sqrt ((peakNum q).card*peakVariance n q β) := by
    unfold z
    simp only [norm_mul,show ‖E (-(n:ℝ)*β)‖=1 from Complex.norm_exp_ofReal_mul_I _,
      one_mul,Complex.norm_ofNat]
    gcongr
    exact peakProjection_norm n q β
  have h := peakSigned_fixed_frequency_floor (n := n) hq β
  rw [mul_add,Complex.add_re] at h
  change (_ + z.re) - _ ≤ _ at h
  linarith [Complex.abs_re_le_norm z,neg_abs_le z.re]

end SignedPrimePeak

section SignedPeakProgression
open ExtendedArcCoefficient

noncomputable def peakPrimeProgression (n q : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => q ∣ n-k), (weight k:ℂ)*E ((k:ℝ)*β)

theorem peakFluct_projection {n q : ℕ} (hq : q.Prime) (β : ℝ) :
    ∑ a ∈ peakNum q, peakChar n q a * peakFluct n q β a =
      (q:ℂ)*peakPrimeProgression n q β - deepPrimeWave n β -
      peakMean n q β*(if q∣n then (q:ℂ)-1 else -1) := by
  have factor (k a : ℕ) (hk : k≤n) :
      peakChar n q a * E ((k:ℝ)*(β+(a:ℝ)/q)) =
      E ((k:ℝ)*β)*peakChar (n-k) q a := by
    unfold peakChar
    rw [← phase_add,← phase_add,Nat.cast_sub hk]
    congr 1
    ring
  have full : ∑ a ∈ peakNum q, peakChar n q a * deepPrimeWave n (β+(a:ℝ)/q) =
      (q:ℂ)*peakPrimeProgression n q β - deepPrimeWave n β := by
    unfold deepPrimeWave
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold peakPrimeProgression
    rw [Finset.sum_filter,Finset.mul_sum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hterm (a : ℕ) : peakChar n q a * ((weight k:ℂ)*E ((k:ℝ)*(β+(a:ℝ)/q))) =
        ((weight k:ℂ)*E ((k:ℝ)*β))*peakChar (n-k) q a := by
      rw [mul_left_comm, factor k a (by simpa using hk), mul_assoc]
    simp_rw [hterm]
    rw [← Finset.mul_sum,peakChar_sum hq]
    split_ifs <;> ring
  simp only [peakFluct,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  rw [full,peakChar_sum hq,mul_comm (peakMean n q β)]

theorem peakSigned_AP_floor {n q : ℕ} (hq : q.Prime) (β : ℝ) :
    (E (-(n:ℝ)*β) *
      (2*peakMean n q β*((q:ℂ)*peakPrimeProgression n q β - deepPrimeWave n β) -
       (peakMean n q β)^2*(if q∣n then (q:ℂ)-1 else -1))).re -
    peakVariance n q β ≤ (peakSigned n q β).re := by
  have h := peakSigned_fixed_frequency_floor (n := n) hq β
  rw [peakFluct_projection hq] at h
  convert h using 3
  ring

end SignedPeakProgression

end GoldbachDeepFourth
