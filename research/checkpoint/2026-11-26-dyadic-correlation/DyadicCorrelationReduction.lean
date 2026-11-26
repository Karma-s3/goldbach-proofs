import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Reductions for the dyadic Goldbach correlation floor

The divisor weights agree with log p at primes and eliminate squarefree
integers with three or more prime factors. Only products of two distinct
primes contribute an excess. At order ceil((log n)^4) the full excess
in the correlation is at most 8 n/log n for log n >= 2.
The theorem polylog_smooth_relative_error_tendsto proves convergence
after division by n. The proofs also give finite lower certificates.

Theorem dyadic_one_eighth_of_infinitePrimeArcMass uses the actual
infinite singular series. The signed complementary arc bound and the
expanded major-arc estimate are the two analytic inputs. Comments
identify calculations on paper and give their sources.


The theorem `dyadic_count_whole` gives an unconditional, explicit count of
even integers reaching a linear lower bound in each large dyadic interval.
`exists_dyadic_witness` extracts a single such integer. The signed-tail
calculation at the end is an analytic derivation recorded outside Lean's
theorem statements.

`dyadic_floor_iff_count` proves the equivalence of the frozen target to a
pointwise lower bound for ordered prime-pair counts. The uniform count bound
and the signed minor-arc hypothesis in `floor_of_signed_minor` remain open.

Besides the direct count equivalence, this file gives a prime-indicator
divisor expansion and separates the contribution of small moduli, for which
Dirichlet GRH supplies progression estimates, from the signed large-divisor
sum. The uniform lower bound on the resulting model plus remainder is open.

The local file proves the finite transfers. The external Dirichlet GRH proof
and its analytic application to prime progressions are used in the accompanying
mathematical argument.
-/

namespace GoldbachPartial

/-- Ordered prime representations, indexed by their first summand. -/
def reps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (n - p)

noncomputable def weight (p : ℕ) : ℝ := if Nat.Prime p then Real.log p else 0

noncomputable def corr (n : ℕ) : ℝ := ∑ p ∈ Finset.range (n + 1), weight p * weight (n-p)

private theorem weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  by_cases hp : Nat.Prime p
  · simp only [weight, ite_eq_left hp]
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · simp [weight, hp]

private theorem shortSideCount (S : Finset ℕ) (n B : ℕ) (hS : S ⊆ Finset.range (n+1)) :
    (S.filter (fun p => min p (n-p) < B)).card ≤ 2 * B := by
  let R := Finset.range B
  have hsub : S.filter (fun p => min p (n-p) < B) ⊆ R ∪ R.image (fun q => n-q) := by
    intro p hp
    obtain ⟨hpS, hshort⟩ := Finset.mem_filter.mp hp
    have hn := Finset.mem_range.mp (hS hpS)
    rcases lt_or_ge p B with hp | hp
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hp)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n-p, Finset.mem_range.mpr (by omega), by omega⟩
  calc
    _ ≤ (R ∪ R.image (fun q => n-q)).card := Finset.card_le_card hsub
    _ ≤ R.card + (R.image (fun q => n-q)).card := Finset.card_union_le _ _
    _ ≤ R.card + R.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * B := by simp [R, Nat.two_mul]

/-- Removing prime pairs with a summand below B costs at most 2B ordered pairs. -/
theorem count_to_correlation (n B : ℕ) (hB : 1 ≤ B) :
    (((reps n).card - 2*B : ℕ) : ℝ) * (Real.log B)^2 ≤ corr n := by
  let G := (reps n).filter fun p => B ≤ min p (n-p)
  have hsub : reps n ⊆ Finset.range (n+1) := Finset.filter_subset _ _
  have hcard : (reps n).card - 2*B ≤ G.card := by
    have h := shortSideCount (reps n) n B hsub
    have hs := Finset.card_filter_add_card_filter_not (s := reps n) (fun p => min p (n-p) < B)
    simp only [not_lt] at hs
    dsimp [G]
    omega
  have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  calc
    _ ≤ (G.card : ℝ) * (Real.log B)^2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = ∑ _p ∈ G, (Real.log B)^2 := by simp
    _ ≤ ∑ p ∈ G, weight p * weight (n-p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpS, hcut⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, hp', hq'⟩ := Finset.mem_filter.mp hpS
      obtain ⟨hb₁, hb₂⟩ := le_min_iff.mp hcut
      simp only [weight, ite_eq_left hp', ite_eq_left hq', pow_two]
      have h₁ := Real.log_le_log hBpos (show (B : ℝ) ≤ p by exact_mod_cast hb₁)
      have h₂ := Real.log_le_log hBpos (show (B : ℝ) ≤ ((n-p : ℕ) : ℝ) by exact_mod_cast hb₂)
      exact mul_le_mul h₁ h₂ hlog (hlog.trans h₁)
    _ ≤ corr n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hsub)
      intro p _ _
      exact mul_nonneg (weight_nonneg p) (weight_nonneg (n-p))

/-- Each ordered pair contributes at most the square of log n. -/
theorem correlation_to_count (n : ℕ) (hn : 1 ≤ n) :
    corr n ≤ ((reps n).card : ℝ) * (Real.log n)^2 := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have cap (p : ℕ) (hp : p ≤ n) : weight p ≤ Real.log n := by
    unfold weight
    split
    next h => exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
    next => exact hlog
  unfold corr reps
  calc
    _ ≤ ∑ p ∈ Finset.range (n + 1),
          if Nat.Prime p ∧ Nat.Prime (n - p) then (Real.log n)^2 else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : Nat.Prime p ∧ Nat.Prime (n - p)
      · rw [ite_eq_left h, pow_two]
        exact mul_le_mul (cap p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))
          (cap (n-p) (Nat.sub_le ..)) (weight_nonneg _) hlog
      · rw [ite_eq_right h]
        by_cases h₁ : Nat.Prime p
        · have h₂ : ¬ Nat.Prime (n-p) := fun h₂ => h ⟨h₁,h₂⟩
          simp [weight, h₂]
        · simp [weight, h₁]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]

/-- With the square-root cutoff the unweighted count controls the correlation,
up to an endpoint term that is sublinear in n. -/
theorem count_sqrt_cutoff (n : ℕ) (hn : 1 ≤ n) :
    ((reps n).card : ℝ) * (Real.log n)^2 ≤
      4 * corr n + ((2 * (n.sqrt + 1) : ℕ) : ℝ) * (Real.log n)^2 := by
  let B := n.sqrt + 1
  let A := (reps n).card
  have hB : 1 ≤ B := Nat.le_add_left 1 n.sqrt
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnB : (n : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have hlog := Real.log_le_log hn' hnB
  rw [Real.log_pow] at hlog
  have hp : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hsq : (Real.log n)^2 ≤ 4 * (Real.log B)^2 := by
    have hh := mul_self_le_mul_self hp hlog
    norm_num at hh
    nlinarith [hh]
  have hc : (A : ℝ) ≤ ((A - 2*B : ℕ) : ℝ) + ((2*B : ℕ) : ℝ) := by
    exact_mod_cast (show A ≤ (A - 2*B) + (2*B) by omega)
  have h₁ := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log (n : ℝ)))
  have h₂ := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (A - 2*B))
  have h₃ := count_to_correlation n B hB
  change ((A - 2*B : ℕ) : ℝ) * (Real.log B)^2 ≤ corr n at h₃
  change (A : ℝ) * (Real.log n)^2 ≤ 4 * corr n + ((2*B : ℕ) : ℝ) * (Real.log n)^2
  linarith only [h₁, h₂, h₃]

open Filter in
private theorem endpoint_error (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) * Real.log (n : ℝ) ^ 2 ≤ ε * (n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [ht.eventually_ge_atTop (192 / ε), Filter.eventually_ge_atTop (1 : ℕ)]
    with n hb hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hlog0 := Real.log_nonneg hn1
  have htay := Real.pow_div_factorial_le_exp _ (show 0 ≤ Real.log (n : ℝ) / 2 by linarith) 3
  rw [← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.2 hn0), Real.log_sqrt hn0.le] at htay
  norm_num [Nat.factorial] at htay
  have hscale : 192 ≤ Real.log (n : ℝ) * ε := (div_le_iff₀ hε).mp hb
  have hlog : Real.log (n : ℝ) ^ 2 ≤ ε / 4 * Real.sqrt (n : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right hscale (sq_nonneg (Real.log (n : ℝ))),
      mul_le_mul_of_nonneg_left htay hε.le]
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hbox : ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
    push_cast
    linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
  calc
    _ ≤ (4 * Real.sqrt (n : ℝ)) * (ε / 4 * Real.sqrt (n : ℝ)) :=
      mul_le_mul hbox hlog (sq_nonneg _) (by linarith)
    _ = ε * Real.sqrt (n : ℝ) ^ 2 := by ring
    _ = ε * (n : ℝ) := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The frozen dyadic target is equivalent to a uniform lower bound of order
n / (log n)^2 on the number of ordered prime representations. -/
theorem dyadic_floor_iff_count :
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2 * X →
        Even n → c * (n : ℝ) ≤ corr n) ↔
      ∃ (a : ℝ) (M : ℕ), 0 < a ∧ ∀ n ≥ M, Even n →
        a * (n : ℝ) ≤ ((reps n).card : ℝ) * (Real.log n)^2 := by
  constructor
  · rintro ⟨c, N, hc, hf⟩
    refine ⟨c, max N 1, hc, ?_⟩
    intro n hn he
    have hn₁ : 1 ≤ n := (le_max_right N 1).trans hn
    exact (hf n n ((le_max_left N 1).trans hn) le_rfl (by omega) he).trans
      (correlation_to_count n hn₁)
  · rintro ⟨a, M, ha, hcount⟩
    obtain ⟨K, hK⟩ := endpoint_error (a/2) (half_pos ha)
    refine ⟨a/8, max 1 (max M K), by positivity, ?_⟩
    intro X n hX hXn _ he
    have hn := le_trans hX hXn
    have h₁ : 1 ≤ n := (le_max_left _ _).trans hn
    have hMK : max M K ≤ n := (le_max_right _ _).trans hn
    have h₂ := hcount n ((le_max_left M K).trans hMK) he
    have h₃ := count_sqrt_cutoff n h₁
    have h₄ := hK n ((le_max_right M K).trans hMK)
    linarith only [h₂, h₃, h₄]

/-- A signed minor-arc estimate with half the major-arc constant suffices. -/
theorem floor_of_signed_minor (major minor : ℕ → ℝ)
    (hsplit : ∀ n, corr n = major n + minor n)
    (a : ℝ) (ha : 0 < a) (N₁ N₂ : ℕ)
    (hmajor : ∀ n ≥ N₁, Even n → a * (n : ℝ) ≤ major n)
    (hminor : ∀ n ≥ N₂, Even n → -(a/2 * (n : ℝ)) ≤ minor n) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c * (n : ℝ) ≤ corr n := by
  refine ⟨a/2, max N₁ N₂, half_pos ha, ?_⟩
  intro X n hX hXn _ he
  have hn := le_trans hX hXn
  have hA := hmajor n ((le_max_left _ _).trans hn) he
  have hM := hminor n ((le_max_right _ _).trans hn) he
  rw [hsplit]
  linarith

/-- The sign distinguishes primes from products of two primes, including squares. -/
def paritySign (m : ℕ) : ℝ := (-1 : ℝ) ^ m.primeFactorsList.length

/-- The candidate set may include any subset supplied by a sieve. -/
theorem chen_parity_identity (n : ℕ) (s : Finset ℕ) (v : ℕ → ℝ)
    (hs : ∀ p ∈ s, Nat.Prime (n-p) ∨
      ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ n-p = a*b) :
    (∑ p ∈ s, v p) - (∑ p ∈ s, v p * paritySign (n-p)) =
      2 * ∑ p ∈ s.filter (fun p => Nat.Prime (n-p)), v p := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : Nat.Prime (n-p)
  · simp [h, paritySign, Nat.primeFactorsList_prime h]
    ring
  · obtain ⟨a,b,ha,hb,hab⟩ := (hs p hp).resolve_left h
    have hlen : (n-p).primeFactorsList.length = 2 := by
      rw [hab, (Nat.perm_primeFactorsList_mul ha.ne_zero hb.ne_zero).length_eq]
      simp [Nat.primeFactorsList_prime ha, Nat.primeFactorsList_prime hb]
    simp [h, paritySign, hlen]

/-- A one-sided bound on the parity sum of any selected Chen candidates
implies the same target's lower bound for the actual prime correlation. -/
theorem correlation_of_chen_parity (n : ℕ) (s : Finset ℕ)
    (hsub : s ⊆ Finset.range (n+1))
    (hs : ∀ p ∈ s, Nat.Prime (n-p) ∨
      ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ n-p = a*b)
    (t : ℝ)
    (hpar : (∑ p ∈ s, weight p * Real.log ((n-p : ℕ) : ℝ) * paritySign (n-p)) ≤
      (∑ p ∈ s, weight p * Real.log ((n-p : ℕ) : ℝ)) - 2 * t) :
    t ≤ corr n := by
  let v := fun p : ℕ => weight p * Real.log ((n-p : ℕ) : ℝ)
  have hid := chen_parity_identity n s v hs
  change (∑ p ∈ s, v p * paritySign (n-p)) ≤ (∑ p ∈ s, v p) - 2*t at hpar
  have hmass : t ≤ ∑ p ∈ s.filter (fun p => Nat.Prime (n-p)), v p := by
    linarith only [hid, hpar]
  refine hmass.trans ?_
  calc
    _ = ∑ p ∈ s.filter (fun p => Nat.Prime (n-p)), weight p * weight (n-p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [show weight (n-p) = Real.log ((n-p : ℕ) : ℝ) by
        simp [weight, (Finset.mem_filter.mp hp).2]]
    _ ≤ corr n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hsub)
      intro p _ _
      exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

private theorem odd_pair_no_alias {n q p r : ℕ} (hn : Even n) (hq : Odd q)
    (hlarge : n < 2*q) (hp : p ≤ n) (hr : r ≤ n) (hop : Odd p) (hor : Odd r) :
    (p+r) % q = n % q ↔ p+r = n := by
  constructor
  · intro h
    have h₂ : p+r ≡ n [MOD 2] := by
      obtain ⟨a, ha⟩ := hn
      obtain ⟨b, hb⟩ := hop
      obtain ⟨c, hc⟩ := hor
      change (p+r)%2 = n%2
      omega
    have hm : p+r ≡ n [MOD 2*q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hq.coprime_two_left).mp ⟨h₂,h⟩
    exact Nat.le_antisymm (hm.le_of_lt_add (by omega)) (hm.symm.le_of_lt_add (by omega))
  · intro h
    rw [h]

/-- At an odd modulus above n/2, the modular sum of two odd primes isolates
the desired even target exactly. -/
theorem large_odd_modulus_correlation {n q : ℕ} (hn : Even n) (hn4 : 4 < n)
    (hq : Odd q) (hlarge : n < 2*q) :
    (∑ p ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n+1),
      if Odd p ∧ Odd r ∧ (p+r)%q = n%q then weight p * weight r else 0) = corr n := by
  classical
  unfold corr
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  have hcomp : p+(n-p)=n := by omega
  rw [Finset.sum_eq_single_of_mem (n-p) (Finset.mem_range.mpr (by omega))]
  · by_cases h₁ : p.Prime
    · by_cases h₂ : (n-p).Prime
      · have e₁ := h₁.eq_two_or_odd
        have e₂ := h₂.eq_two_or_odd
        obtain ⟨a, ha⟩ := hn
        have hp2 : p ≠ 2 := by omega
        have hr2 : n-p ≠ 2 := by omega
        exact ite_eq_left ⟨h₁.odd_of_ne_two hp2,h₂.odd_of_ne_two hr2,by rw [hcomp]⟩
      · simp [weight, h₂]
    · simp [weight, h₁]
  · intro r hr hne
    apply ite_eq_right
    rintro ⟨hop,hor,hm⟩
    have hrn := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have he := (odd_pair_no_alias hn hq hlarge hpn hrn hop hor).mp hm
    omega

private theorem two_point_lower {ι : Type*} (s : Finset ι) (k : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hk : ∀ j ∈ s, 1 ≤ k j) {z : ℝ} (hz : 0 ≤ z) :
    4 * (∑ j ∈ s, w j * z ^ k j) - (∑ j ∈ s, w j * (2*z) ^ k j) ≤
      2*z * ∑ j ∈ s.filter (fun j => k j = 1), w j := by
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  by_cases he : k j = 1
  · simp [he]
    ring_nf
    exact le_rfl
  · have hbase : (4 : ℝ) ≤ 2 ^ k j := by
      calc
        (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k j := pow_le_pow_right₀ (by norm_num) (by have := hk j hj; omega)
    have hprod := mul_le_mul_of_nonneg_right hbase
      (mul_nonneg (hw j hj) (pow_nonneg hz (k j)))
    simp only [he, ite_false, mul_zero, mul_pow]
    linarith only [hprod]

private theorem two_point_error {ι : Type*} (s : Finset ι) (k : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hk : ∀ j ∈ s, 1 ≤ k j) {z : ℝ} (hz : 0 ≤ z)
    (hz' : 2*z ≤ 1) :
    2*z * (∑ j ∈ s.filter (fun j => k j = 1), w j) ≤
      4 * (∑ j ∈ s, w j * z ^ k j) - (∑ j ∈ s, w j * (2*z) ^ k j)
        + (2*z)^3 * (∑ j ∈ s, w j) := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have h0 : 0 ≤ 2*z := by linarith
  have hn := mul_nonneg (pow_nonneg h0 3) (hw j hj)
  by_cases h1 : k j = 1
  · simp only [h1, ite_true, pow_one]
    linarith only [hn]
  · simp only [h1, ite_false, mul_zero]
    by_cases h2 : k j = 2
    · rw [h2]
      linarith only [hn]
    · have h3 : 3 ≤ k j := by have := hk j hj; omega
      have hpow := pow_le_pow_of_le_one h0 hz' h3
      have hwz := mul_nonneg (hw j hj) (pow_nonneg hz (k j))
      linarith only [hwz, mul_le_mul_of_nonneg_left hpow (hw j hj)]

/-- A generating polynomial in the number of prime factors of the complement,
counted with multiplicity. Complements 0 and 1 are excluded. -/
noncomputable def factorSpectrum (n : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (n+1)).filter (fun p => 2 ≤ n-p),
    (weight p * Real.log (n-p : ℕ)) * z ^ (n-p).primeFactorsList.length

private theorem factor_length_one_iff (m : ℕ) (hm : 2 ≤ m) :
    m.primeFactorsList.length = 1 ↔ m.Prime := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp h
    have hp := Nat.prime_of_mem_primeFactorsList (n := m) (p := q) (by simp [hq])
    have he : q = m := by simpa [hq] using (Nat.prod_primeFactorsList (n := m) (by omega))
    exact he ▸ hp
  · intro h
    simp [Nat.primeFactorsList_prime h]

/-- Two positive evaluations cancel the semiprimes exactly and bound all
remaining terms of degree at least three. -/
theorem factorSpectrum_bounds (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz' : 2*z ≤ 1) :
    4 * factorSpectrum n z - factorSpectrum n (2*z) ≤ 2*z * corr n ∧
    2*z * corr n ≤ 4 * factorSpectrum n z - factorSpectrum n (2*z) +
      (2*z)^3 * factorSpectrum n 1 := by
  let s := (Finset.range (n+1)).filter (fun p => 2 ≤ n-p)
  let k := fun p : ℕ => (n-p).primeFactorsList.length
  let w := fun p : ℕ => weight p * Real.log (n-p : ℕ)
  have hs (p : ℕ) (hp : p ∈ s) : 2 ≤ n-p := (Finset.mem_filter.mp hp).2
  have hw (p : ℕ) (hp : p ∈ s) : 0 ≤ w p := by
    have h := hs p hp
    exact mul_nonneg (weight_nonneg p) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n-p by omega)))
  have hk (p : ℕ) (hp : p ∈ s) : 1 ≤ k p := by
    exact List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil _).mpr (hs p hp))
  have hone : (∑ p ∈ s, w p) = factorSpectrum n 1 := by simp [s,w,factorSpectrum]
  have heq : (∑ p ∈ s.filter (fun p => k p = 1), w p) = corr n := by
    simp only [s, corr, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h2 : 2 ≤ n-p
    · by_cases h : (n-p).Prime
      · simp [w, k, h2, (factor_length_one_iff _ h2).mpr h, weight, h]
      · simp [w, k, h2, (factor_length_one_iff _ h2).not.mpr h, weight, h]
    · have h : ¬ (n-p).Prime := fun h => h2 h.two_le
      simp [h2, weight, h]
  constructor
  · calc
      _ ≤ 2*z * (∑ p ∈ s.filter (fun p => k p = 1), w p) :=
        two_point_lower s k w hw hk hz
      _ = 2*z * corr n := by rw [heq]
  · calc
      _ = 2*z * (∑ p ∈ s.filter (fun p => k p = 1), w p) := by rw [heq]
      _ ≤ 4 * factorSpectrum n z - factorSpectrum n (2*z) + (2*z)^3 * (∑ p ∈ s, w p) :=
        two_point_error s k w hw hk hz hz'
      _ = _ := by rw [hone]

/-- Discrete summation by parts with decreasing weight log(n-i);
the endpoint weight is zero. -/
theorem reflected_log_of_prefix (n : ℕ) (hn : 2 ≤ n) (u : ℕ → ℝ) (E : ℝ)
    (hu : ∀ t ≤ n-1, |∑ i ∈ Finset.range t, u i| ≤ E) :
    |∑ i ∈ Finset.range (n-1), u i * Real.log ((n-i : ℕ) : ℝ)| ≤ E * Real.log (n : ℝ) := by
  let P (m : ℕ) := ∑ i ∈ Finset.range m, u i
  let w (m : ℕ) := Real.log ((n-m : ℕ) : ℝ)
  let S (m : ℕ) := ∑ i ∈ Finset.range m, u i * w i
  have hmono (m : ℕ) (hm : m+1 ≤ n-1) : w (m+1) ≤ w m := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < n-(m+1) by omega)
    · exact_mod_cast (show n-(m+1) ≤ n-m by omega)
  have hbound (m : ℕ) : m ≤ n-1 → |S m - P m * w m| ≤ E * (w 0 - w m) := by
    induction m with
    | zero => simp [S,P]
    | succ m ih =>
      intro hm
      have hd := sub_nonneg.mpr (hmono m hm)
      have hstep : S (m+1) - P (m+1) * w (m+1) =
          (S m - P m * w m) + P (m+1) * (w m - w (m+1)) := by
        simp only [S, P, Finset.sum_range_succ]
        ring
      rw [hstep]
      calc
        _ ≤ |S m - P m * w m| + |P (m+1) * (w m - w (m+1))| := abs_add_le _ _
        _ ≤ E * (w 0 - w m) + E * (w m - w (m+1)) := by
          rw [abs_mul, abs_of_nonneg hd]
          exact add_le_add (ih (by omega)) (mul_le_mul_of_nonneg_right (hu _ hm) hd)
        _ = _ := by ring
  have hw : w (n-1) = 0 := by simp [w, show n - (n-1) = 1 by omega]
  simpa only [hw, mul_zero, sub_zero, S, w, Nat.sub_zero] using (hbound (n-1) le_rfl)

/-- The prime-progression sum appearing in the divisor expansion of the two evaluations. -/
noncomputable def progression (n d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n-1),
    (if i % d = n % d then weight i else 0) * Real.log ((n-i : ℕ) : ℝ)

/-- Transfer a discrepancy bound without discarding the dependence on each
divisor coefficient. This permits using the prime indicator directly. -/
private theorem progression_error_weighted (n : ℕ) (hn : 2 ≤ n) (D : Finset ℕ)
    (a density : ℕ → ℝ) (E : ℝ)
    (hprefix : ∀ d ∈ D, ∀ t ≤ n-1,
      |∑ i ∈ Finset.range t, ((if i % d = n % d then weight i else 0) - density d)| ≤ E) :
    |(∑ d ∈ D, a d * progression n d) -
       (∑ d ∈ D, a d * (density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)))|
       ≤ (∑ d ∈ D, |a d|) * (E * Real.log (n : ℝ)) := by
  let M (d : ℕ) := density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)
  have he (d) (hd : d ∈ D) : |progression n d - M d| ≤ E * Real.log (n : ℝ) := by
    have h := reflected_log_of_prefix n hn
      (fun i => (if i % d = n % d then weight i else 0) - density d) E (hprefix d hd)
    simpa only [M, progression, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] using h
  change |(∑ d ∈ D, a d * progression n d) - (∑ d ∈ D, a d * M d)| ≤ _
  calc
    _ = |∑ d ∈ D, a d * (progression n d - M d)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ D, |a d * (progression n d - M d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, |a d| * (E * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he d hd) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

/-- Weighted Type I error from prefix estimates for the prime progressions.
For reduced classes the density supplied by Dirichlet GRH is 1 / φ(d). -/
theorem progression_error (n : ℕ) (hn : 2 ≤ n) (D : Finset ℕ)
    (b density : ℕ → ℝ) (E : ℝ) (hb : ∀ d ∈ D, |b d| ≤ 5)
    (hprefix : ∀ d ∈ D, ∀ t ≤ n-1,
      |∑ i ∈ Finset.range t, ((if i % d = n % d then weight i else 0) - density d)| ≤ E) :
    |(∑ d ∈ D, b d * progression n d) -
       (∑ d ∈ D, b d * (density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)))|
       ≤ 5 * (D.card : ℝ) * E * Real.log (n : ℝ) := by
  let M (d : ℕ) := density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)
  have he (d) (hd : d ∈ D) : |progression n d - M d| ≤ E * Real.log (n : ℝ) := by
    have h := reflected_log_of_prefix n hn
      (fun i => (if i % d = n % d then weight i else 0) - density d) E (hprefix d hd)
    simpa only [M, progression, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] using h
  change |(∑ d ∈ D, b d * progression n d) - (∑ d ∈ D, b d * M d)| ≤ _
  calc
    _ = |∑ d ∈ D, b d * (progression n d - M d)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ D, |b d * (progression n d - M d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ D, 5 * (E * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul (hb d hd) (he d hd) (abs_nonneg _) (by norm_num)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Exchange the divisor sum over the complement with prime-progression sums. -/
private theorem divisor_ap_sum {R : Type*} [CommSemiring R] (n : ℕ) (f g : ℕ → R) :
    (∑ p ∈ Finset.range (n-1), f p * ∑ d ∈ (n-p).divisors, g d) =
      ∑ d ∈ Finset.range (n+1), g d *
        ∑ p ∈ (Finset.range (n-1)).filter (fun p => p%d = n%d), f p := by
  classical
  have hs (p : ℕ) (hp : p ∈ Finset.range (n-1)) :
      (n-p).divisors = (Finset.range (n+1)).filter (fun d => p%d = n%d) := by
    have hp' := Finset.mem_range.mp hp
    have hpn : p ≤ n := by omega
    have hpos : 0 < n-p := by omega
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
    change (d ∣ n-p ∧ n-p ≠ 0) ↔ d < n+1 ∧ p ≡ n [MOD d]
    rw [Nat.modEq_iff_dvd' hpn]
    exact ⟨fun h => ⟨by have := Nat.le_of_dvd hpos h.1; omega, h.1⟩,
      fun h => ⟨h.2, hpos.ne'⟩⟩
  calc
    _ = ∑ p ∈ Finset.range (n-1), ∑ d ∈ Finset.range (n+1),
          if p%d = n%d then g d * f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hs p hp, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      split <;> simp [mul_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum, Finset.sum_filter]


open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private noncomputable def omegaPower (z : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else z ^ ArithmeticFunction.cardFactors n
  map_zero' := by simp

private theorem omegaPower_mult (z : ℝ) : (omegaPower z).IsMultiplicative := by
  constructor
  · simp [omegaPower]
  · intro a b _
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp [omegaPower, ha, hb, ArithmeticFunction.cardFactors_mul ha hb, pow_add]

/-- Möbius-inverted divisor coefficients for the generating polynomial. -/
noncomputable def factorCoefficient (z : ℝ) : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ) * omegaPower z

private theorem factorCoefficient_sum (z : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, factorCoefficient z d = z ^ ArithmeticFunction.cardFactors m := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  change ((ζ : ArithmeticFunction ℝ) * ((μ : ArithmeticFunction ℝ) * omegaPower z)) m = _
  rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  simp [omegaPower, hm]

theorem factorCoefficient_prime_pow (z : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    factorCoefficient z (p^(k+1)) = z^k * (z-1) := by
  have hsum (a : ℕ) : ∑ j ∈ Finset.range (a+1), factorCoefficient z (p^j) = z^a := by
    rw [← Nat.sum_divisors_prime_pow (f := fun m => factorCoefficient z m) hp,
      factorCoefficient_sum z (pow_ne_zero _ hp.ne_zero), ArithmeticFunction.cardFactors_apply_prime_pow hp]
  have h := hsum (k+1)
  rw [Finset.sum_range_succ, hsum k, pow_succ z] at h
  rw [mul_sub, mul_one]
  linarith only [h]

theorem factorCoefficient_abs_le_one {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) (d : ℕ) :
    |factorCoefficient z d| ≤ 1 := by
  have hmult : (factorCoefficient z).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast.mul (omegaPower_mult z)
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [hmult.1]
  | prime_pow p k hp hk =>
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [factorCoefficient_prime_pow z hp a, abs_mul, abs_of_nonneg (pow_nonneg hz _),
      abs_of_nonpos (sub_nonpos.mpr hz')]
    exact (mul_le_of_le_one_right (pow_nonneg hz _) (by linarith)).trans (pow_le_one₀ hz hz')
  | coprime a b _ _ hab ha hb =>
    rw [hmult.2 hab, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) ha).trans hb

theorem factorSpectrum_as_progressions (n : ℕ) (z : ℝ) :
    factorSpectrum n z = ∑ d ∈ Finset.range (n+1), factorCoefficient z d * progression n d := by
  let w := fun p : ℕ => weight p * Real.log (n-p : ℕ)
  have hset : (Finset.range (n+1)).filter (fun p => 2 ≤ n-p) = Finset.range (n-1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold factorSpectrum
  rw [hset]
  calc
    _ = ∑ p ∈ Finset.range (n-1), w p * ∑ d ∈ (n-p).divisors, factorCoefficient z d := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_range.mp hp
      rw [factorCoefficient_sum z (by omega : n-p ≠ 0)]
      rfl
    _ = _ := by
      rw [divisor_ap_sum]
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p % d = n % d <;> simp [w,h]

private theorem contrast_as_progressions (n : ℕ) (z : ℝ) :
    4 * factorSpectrum n z - factorSpectrum n (2*z) =
      ∑ d ∈ Finset.range (n+1), (4 * factorCoefficient z d - factorCoefficient (2*z) d)
        * progression n d := by
  rw [factorSpectrum_as_progressions n z, factorSpectrum_as_progressions n (2*z)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]

/-- A certificate that keeps the long-divisor contribution with its sign.
The progression estimates enter only for d in D. -/
theorem correlation_with_signed_tail (n : ℕ) (hn : 2 ≤ n) (z : ℝ)
    (hz : 0 ≤ z) (hz₂ : 2*z ≤ 1) (D : Finset ℕ) (hD : D ⊆ Finset.range (n+1))
    (density : ℕ → ℝ) (E : ℝ)
    (hprefix : ∀ d ∈ D, ∀ t ≤ n-1,
      |∑ i ∈ Finset.range t, ((if i % d = n % d then weight i else 0) - density d)| ≤ E) :
    let b := fun d => 4 * factorCoefficient z d - factorCoefficient (2*z) d
    let M := fun d => density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)
    (∑ d ∈ D, b d * M d) + (∑ d ∈ Finset.range (n+1) \ D, b d * progression n d)
      - 5 * (D.card : ℝ) * E * Real.log (n : ℝ) ≤ 2*z*corr n := by
  dsimp only
  let b := fun d => 4 * factorCoefficient z d - factorCoefficient (2*z) d
  let M := fun d => density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)
  change (∑ d ∈ D, b d * M d) + _ - _ ≤ _
  have hcoef (d) (_ : d ∈ D) : |b d| ≤ 5 := by
    have h₁ := factorCoefficient_abs_le_one hz (by linarith : z ≤ 1) d
    have h₂ := factorCoefficient_abs_le_one (by linarith : 0 ≤ 2*z) hz₂ d
    calc
      _ ≤ |4 * factorCoefficient z d| + |factorCoefficient (2*z) d| := abs_sub _ _
      _ ≤ 5 := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith
  have hE := (abs_le.mp (progression_error n hn D b density E hcoef hprefix)).1
  change -(5 * (D.card : ℝ) * E * Real.log (n : ℝ)) ≤
    (∑ d ∈ D, b d * progression n d) - ∑ d ∈ D, b d * M d at hE
  have hF := (factorSpectrum_bounds n hz hz₂).1
  rw [contrast_as_progressions] at hF
  change (∑ d ∈ Finset.range (n+1), b d * progression n d) ≤ _ at hF
  rw [← Finset.sum_sdiff hD] at hF
  change (∑ d ∈ D, b d * M d) + (∑ d ∈ Finset.range (n+1) \ D, b d * progression n d) - _ ≤ _
  linarith only [hE, hF]

/-- With the GRH progression error C sqrt(n) log(n)^2, summing over
sqrt(n) / log(n)^4 moduli costs at most 5 C n / log(n). -/
theorem grh_short_divisor_budget (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (D : Finset ℕ) (hD : (D.card : ℝ) ≤ Real.sqrt n / (Real.log n)^4) :
    5 * (D.card : ℝ) * (C * Real.sqrt n * (Real.log n)^2) * Real.log n ≤
      5 * C * n / Real.log n := by
  have hl := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : 1 < (n : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have h₁ := (le_div_iff₀ (pow_pos hl 4)).mp hD
  apply (le_div_iff₀ hl).mpr
  calc
    _ = 5*C*Real.sqrt n * ((D.card : ℝ) * (Real.log n)^4) := by ring
    _ ≤ 5*C*Real.sqrt n * Real.sqrt n :=
      mul_le_mul_of_nonneg_left h₁ (by positivity)
    _ = 5*C*n := by rw [mul_assoc (5*C), ← sq, hs]


theorem factorCoefficient_squarefree (z : ℝ) {m : ℕ} (hm : Squarefree m) :
    factorCoefficient z m = (z-1)^m.primeFactors.card := by
  have hmult : (factorCoefficient z).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast.mul (omegaPower_mult z)
  rw [← hmult.prod_primeFactors hm]
  calc
    _ = ∏ _p ∈ m.primeFactors, (z-1) := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa using factorCoefficient_prime_pow z (Nat.prime_of_mem_primeFactors hp) 0
    _ = _ := by simp

theorem squarefree_contrast_abs_lower {z : ℝ} {m : ℕ} (hm : Squarefree m)
    (hz : 0 ≤ 2*z) (hz' : 2*z ≤ 1) (hsmall : z * (m.primeFactors.card : ℝ) ≤ 1/4) :
    2 ≤ |4 * factorCoefficient z m - factorCoefficient (2*z) m| := by
  have h₁ : 3/4 ≤ |factorCoefficient z m| := by
    rw [factorCoefficient_squarefree z hm, abs_pow, abs_of_nonpos (by linarith : z-1 ≤ 0)]
    have h := one_add_mul_le_pow (a := -z) (by linarith) m.primeFactors.card
    rw [show 1 + -z = -(z-1) by ring] at h
    linarith only [h, hsmall]
  have h₂ := factorCoefficient_abs_le_one hz hz' m
  have htri := abs_sub_abs_le_abs_sub (4 * factorCoefficient z m) (factorCoefficient (2*z) m)
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (4 : ℝ))] at htri
  linarith only [h₁, h₂, htri]

/-- The cofactor-one terms already give a lower bound for the absolute
large-divisor sum. This identifies the cancellation lost on taking absolute values. -/
theorem unsigned_tail_ge_cofactor_one (n : ℕ) (T : Finset ℕ) (b : ℕ → ℝ)
    (hT : ∀ d ∈ T, 2 ≤ d ∧ d ≤ n) :
    (∑ d ∈ T, |b d| * (weight (n-d) * Real.log (d : ℝ))) ≤
      ∑ d ∈ T, |b d| * progression n d := by
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨hlo, hhi⟩ := hT d hd
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hcomp : n - (n-d) = d := by omega
  have hres : (n-d)%d = n%d := by
    apply (Nat.modEq_iff_dvd' (by omega : n-d ≤ n)).mpr
    rw [hcomp]
  let term := fun i : ℕ =>
    (if i%d = n%d then weight i else 0) * Real.log ((n-i : ℕ) : ℝ)
  have hpos (i) (hi : i ∈ Finset.range (n-1)) : 0 ≤ term i := by
    have h := Finset.mem_range.mp hi
    apply mul_nonneg
    · split <;> simp [weight_nonneg]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n-i by omega))
  have h := Finset.single_le_sum (f := term) hpos
    (a := n-d) (Finset.mem_range.mpr (by omega : n-d < n-1))
  simpa only [progression,term,hres,ite_true,hcomp] using h

private noncomputable def primeIndicator : ArithmeticFunction ℝ where
  toFun n := if n.Prime then 1 else 0
  map_zero' := by simp [Nat.not_prime_zero]

/-- The Möbius transform of the prime indicator. -/
noncomputable def primeCoefficient : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ) * primeIndicator

private theorem primeCoefficient_sum (m : ℕ) :
    ∑ d ∈ m.divisors, primeCoefficient d = if m.Prime then 1 else 0 := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  change ((ζ : ArithmeticFunction ℝ) * ((μ : ArithmeticFunction ℝ) * primeIndicator)) m = _
  rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  rfl

theorem primeCoefficient_apply (d : ℕ) :
    primeCoefficient d = ∑ p ∈ d.primeFactors, (μ (d / p) : ℝ) := by
  rw [primeCoefficient, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun i j => ((μ : ArithmeticFunction ℝ) i) * primeIndicator j),
    Nat.primeFactors_eq_to_filter_divisors_prime, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime <;> simp [primeIndicator, h]

theorem primeCoefficient_abs_le (d : ℕ) :
    |primeCoefficient d| ≤ (d.primeFactors.card : ℝ) := by
  rw [primeCoefficient_apply]
  calc
    _ ≤ ∑ p ∈ d.primeFactors, |(μ (d / p) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ d.primeFactors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / p))
    _ = _ := by simp

theorem primeCoefficient_abs_le_log (d : ℕ) : |primeCoefficient d| ≤ (Nat.log 2 d : ℝ) := by
  refine (primeCoefficient_abs_le d).trans ?_
  apply Nat.cast_le.mpr
  by_cases hd : d = 0
  · simp [hd]
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ d.primeFactors, p := Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)

/-- The original logarithmic prime-pair correlation as a sum of individual
prime-progression masses. No auxiliary spectral parameter occurs. -/
theorem corr_as_prime_progressions (n : ℕ) :
    corr n = ∑ d ∈ Finset.range (n+1), primeCoefficient d * progression n d := by
  let v := fun p : ℕ => weight p * Real.log (n-p : ℕ)
  have hcut : corr n = ∑ p ∈ Finset.range (n-1), weight p * weight (n-p) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : n-1 ≤ n+1))
    intro p _ hout
    have hp : ¬p < n-1 := fun hp => hout (Finset.mem_range.mpr hp)
    have h : ¬(n-p).Prime := fun h => hp (by have := h.two_le; omega)
    simp [weight,h]
  rw [hcut]
  calc
    _ = ∑ p ∈ Finset.range (n-1), v p * ∑ d ∈ (n-p).divisors, primeCoefficient d := by
      apply Finset.sum_congr rfl
      intro p _
      rw [primeCoefficient_sum]
      by_cases h : (n-p).Prime <;> simp [v,weight,h]
    _ = _ := by
      rw [divisor_ap_sum]
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p % d = n % d <;> simp [v,h]

/-- A GRH prefix error E enters this exact model only through the short
divisors D. The model plus the signed remainder must still be bounded below. -/
theorem prime_progression_remainder (n : ℕ) (hn : 2 ≤ n)
    (D : Finset ℕ) (hD : D ⊆ Finset.range (n+1)) (density : ℕ → ℝ) (E : ℝ)
    (hprefix : ∀ d ∈ D, ∀ t ≤ n-1,
      |∑ i ∈ Finset.range t, ((if i % d = n % d then weight i else 0) - density d)| ≤ E) :
    let M := fun d => density d * ∑ i ∈ Finset.range (n-1), Real.log ((n-i : ℕ) : ℝ)
    |corr n - ((∑ d ∈ D, primeCoefficient d * M d) +
      ∑ d ∈ Finset.range (n+1) \ D, primeCoefficient d * progression n d)| ≤
      (∑ d ∈ D, |primeCoefficient d|) * (E * Real.log (n : ℝ)) := by
  dsimp only
  rw [corr_as_prime_progressions, ← Finset.sum_sdiff hD]
  rw [show ∀ a b c : ℝ, a+b-(c+a)=b-c by intros; ring]
  exact progression_error_weighted n hn D (fun d => primeCoefficient d) density E hprefix

private theorem prime_row_divisors (m p : ℕ) (hm : m ≠ 0) (hp : p.Prime) :
    m.divisors.filter (fun d => d.Coprime (p+m)) = (m / p^m.factorization p).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hpos := (Nat.ordCompl_pos p hm).ne'
  constructor
  · rintro ⟨⟨hd,_⟩,hc⟩
    have hcop := (Nat.coprime_add_iff_left hd).mp hc
    exact ⟨Nat.dvd_ordCompl_of_dvd_not_dvd hd (hp.coprime_iff_not_dvd.mp hcop.symm),hpos⟩
  · rintro ⟨hd,_⟩
    have hdm := hd.trans (Nat.ordCompl_dvd m p)
    have hnot : ¬ p ∣ d := fun h => Nat.not_dvd_ordCompl hp hm (h.trans hd)
    exact ⟨⟨hdm,hm⟩, (Nat.coprime_add_iff_left hdm).mpr (hp.coprime_iff_not_dvd.mpr hnot).symm⟩

private theorem restricted_prime_progressions (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ d ∈ (Finset.range (n+1)).filter P, primeCoefficient d * progression n d) =
      ∑ p ∈ Finset.range (n-1), (weight p * Real.log ((n-p : ℕ) : ℝ)) *
        ∑ d ∈ (n-p).divisors.filter P, primeCoefficient d := by
  let f := fun p : ℕ => weight p * Real.log ((n-p : ℕ) : ℝ)
  let g := fun d : ℕ => if P d then primeCoefficient d else 0
  change _ = ∑ p ∈ Finset.range (n-1), f p * _
  simp only [Finset.sum_filter]
  change _ = ∑ p ∈ Finset.range (n-1), f p * ∑ d ∈ (n-p).divisors, g d
  rw [divisor_ap_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : P d
  · simp only [g, h, ite_true]
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases he : p%d = n%d <;> simp [f,he]
  · simp [g,h]

/-- In one row indexed by a prime p, the complete signed contribution
of moduli with a common factor with n is the difference of two indicators. -/
theorem noncoprime_row (n p : ℕ) (hp : p.Prime) (hpn : p < n) :
    (∑ d ∈ (n-p).divisors.filter (fun d => ¬d.Coprime n), primeCoefficient d) =
      (if (n-p).Prime then (1:ℝ) else 0) -
      (if ((n-p) / p^(n-p).factorization p).Prime then 1 else 0) := by
  have hpart := Finset.sum_filter_add_sum_filter_not (n-p).divisors
    (fun d => d.Coprime n) (fun d => primeCoefficient d)
  have hset := prime_row_divisors (n-p) p (by omega) hp
  rw [show p + (n-p) = n by omega] at hset
  rw [hset, primeCoefficient_sum, primeCoefficient_sum] at hpart
  linarith

private theorem prime_factor_log_sum_le (n : ℕ) :
    (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  rcases n.eq_zero_or_pos with h | h
  · simp [h]
  · have hprod : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hle := Nat.le_of_dvd h (Nat.prod_primeFactors_dvd n)
    have hlog := Real.log_le_log
      (show (0 : ℝ) < ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) by exact_mod_cast hprod)
      (show ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast hle)
    rw [Nat.cast_prod, Real.log_prod _] at hlog
    · exact hlog
    · intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Discarding all non-reduced residue classes from the full signed divisor
expansion changes the actual correlation by at most log(n)^2. -/
theorem noncoprime_progressions_log_sq (n : ℕ) (hn : 1 ≤ n) :
    |∑ d ∈ (Finset.range (n+1)).filter (fun d => ¬d.Coprime n),
      primeCoefficient d * progression n d| ≤ (Real.log n)^2 := by
  classical
  rw [restricted_prime_progressions]
  let row (p : ℕ) := ∑ d ∈ (n-p).divisors.filter (fun d => ¬d.Coprime n), primeCoefficient d
  let mass := fun p : ℕ => weight p * Real.log ((n-p : ℕ) : ℝ)
  change |∑ p ∈ Finset.range (n-1), mass p * row p| ≤ _
  have hLn := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
  have hterm (p : ℕ) (hp : p ∈ Finset.range (n-1)) :
      |mass p * row p| ≤ if p ∈ n.primeFactors then Real.log p * Real.log n else 0 := by
    have hcut := Finset.mem_range.mp hp
    have hpn : p < n := by omega
    have hm : 1 ≤ n-p := by omega
    have hlm := Real.log_nonneg (show (1:ℝ) ≤ (n-p : ℕ) by exact_mod_cast hm)
    have hmass : 0 ≤ mass p := mul_nonneg (weight_nonneg p) hlm
    by_cases hpr : p.Prime
    · have hrow := noncoprime_row n p hpr hpn
      change row p = _ at hrow
      by_cases hdiv : p ∣ n
      · have hmem := Nat.mem_primeFactors.mpr ⟨hpr,hdiv,by omega⟩
        rw [ite_eq_left hmem, abs_mul, abs_of_nonneg hmass]
        have hr : |row p| ≤ 1 := by
          rw [hrow]
          split <;> split <;> norm_num
        have hl := Real.log_le_log (show (0:ℝ) < (n-p : ℕ) by exact_mod_cast (by omega : 0<n-p))
          (show ((n-p : ℕ):ℝ) ≤ n by exact_mod_cast Nat.sub_le n p)
        calc
          _ ≤ mass p * 1 := mul_le_mul_of_nonneg_left hr hmass
          _ = Real.log p * Real.log ((n-p : ℕ):ℝ) := by simp [mass,weight,hpr]
          _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.log_nonneg (by exact_mod_cast hpr.one_le))
      · have hnot : ¬ p ∣ n-p := fun hd => hdiv (by
          simpa only [Nat.sub_add_cancel hpn.le] using dvd_add hd (dvd_refl p))
        have hrem := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd (n-p) hpr).mpr (Or.inr hnot)
        rw [hrem, sub_self] at hrow
        simp [hrow, Nat.mem_primeFactors, hdiv]
    · have hmem : p ∉ n.primeFactors := fun h => hpr (Nat.prime_of_mem_primeFactors h)
      simp [mass,weight,hpr,hmem]
  calc
    _ ≤ ∑ p ∈ Finset.range (n-1), |mass p * row p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.range (n-1), if p ∈ n.primeFactors then Real.log p * Real.log n else 0 :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p * Real.log n := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun p hp => (Finset.mem_filter.mp hp).2
      · exact fun p hp _ => mul_nonneg
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)) hLn
    _ ≤ _ := by
      rw [← Finset.sum_mul, pow_two]
      exact mul_le_mul_of_nonneg_right (prime_factor_log_sum_le n) hLn

theorem reduced_progressions_error (n : ℕ) (hn : 1 ≤ n) :
    |corr n - ∑ d ∈ (Finset.range (n+1)).filter (fun d => d.Coprime n),
      primeCoefficient d * progression n d| ≤ (Real.log n)^2 := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1))
    (fun d => d.Coprime n) (fun d => primeCoefficient d * progression n d)
  rw [corr_as_prime_progressions, ← h, add_sub_cancel_left]
  exact noncoprime_progressions_log_sq n hn

/-- Combine the certified major model and the low-frequency estimates with
a uniform lower bound for the high-high minor term. Each error hypothesis
is written one-sided, as required for a lower bound on the true correlation.
With the certified model take A=1/72. -/
theorem dyadic_floor_of_bulk_margin
    (model major lowLow lowHigh highHigh : ℕ → ℝ) (A b : ℝ) (hgap : b < A)
    (hsplit : ∀ n, corr n = major n + lowLow n + 2*lowHigh n + highHigh n)
    (hmodel : ∀ n : ℕ, 0 < n → Even n → A*(n:ℝ) ≤ model n)
    (herrors : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, Even n →
      model n - e*(n:ℝ) ≤ major n ∧ -(e*(n:ℝ)) ≤ lowLow n ∧ -(e*(n:ℝ)) ≤ lowHigh n)
    (hbulk : ∃ N : ℕ, ∀ n ≥ N, Even n → -(b*(n:ℝ)) ≤ highHigh n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n →
      ((A-b)/2)*(n:ℝ) ≤ corr n := by
  have he : 0 < (A-b)/8 := by linarith
  obtain ⟨N₁,h₁⟩ := herrors _ he
  obtain ⟨N₂,h₂⟩ := hbulk
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro X n hX hXn _ hen
  have hn := hX.trans hXn
  have hn₁ : N₁ ≤ n := ((le_max_left N₁ N₂).trans (le_max_right _ _)).trans hn
  have hn₂ : N₂ ≤ n := ((le_max_right N₁ N₂).trans (le_max_right _ _)).trans hn
  have hpos : 0 < n := (le_max_left _ _).trans hn
  obtain ⟨hM,hL,hH⟩ := h₁ n hn₁ hen
  rw [hsplit]
  linarith only [hM,hL,hH,h₂ n hn₂ hen,hmodel n hpos hen]

/-!
## Using the certified major-arc floor

PR 316 at e4ab24712555ae8c2c926adf19d368a9fb392c35 proves the
major-arc bound for the exact desk arcs, phase, and prime weights. Its
registered theorem has an existential constant. The proof in
`GoldbachMajorArc.major_linear_floor` chooses 1/144. The public
`model_linear_floor` gives n/72 for the model, and
`major_error`, `cutoff_separated`, and `totalArcError_sublinear`
transfer any strictly smaller constant to the actual integral.
PR 158 proves that the major and minor integrals sum to the actual
prime-pair correlation. The desk also certifies minor-bilinear-split,
small-small-saving, and small-bulk-saving. Hence in the theorem above
lowLow and lowHigh can be made arbitrarily small compared with n.
These statements concern the same cutoff k³≤n for the small prime weight.

In particular, the certified 1/144 together with a full signed minor
lower bound -n/288 gives corr(n)≥n/288 at that n. Using the model
directly, a high-high lower bound -b n for any fixed b<1/72 suffices
after paying for all three errors. The full frozen bulk-signed-floor
asks for every b>0. Its one-sided estimate for large even n remains
unproved. The locally checked transfer above has that input as a
hypothesis; it does not add an axiom to the prime-pair theorem.

There is a further analytic consequence of the exact model in PR 316.
Let Q=(⌊log₂(n+2)⌋)² and b=Q/n. Its arithmetic_floor bounds the
real model from below by one third of the continuous kernel mass at
denominator one. The kernel is K(t)=∑_{0≤k≤n} exp(2πikt); orthogonality
on [-1/2,1/2] gives ∫|K|²=n+1. For 0<|t|≤1/2 the geometric sum formula
and sin(π|t|)≥2|t| give |K(t)|≤1/(2|t|). When 0<b≤1/2 the two tails
therefore have total mass ≤ 2∫_b^(1/2) dt/(4t²) = 1/(2b)-1.
Writing E(n) for the PR's totalArcError, for every positive even n
with 2Q²<n this gives
  Re(major(n)) ≥ (n+2−n/(2Q))/3 − E(n).
Since Q→∞ and E(n)/n→0, the inferior limit of Re(major(n))/n along
even n is at least 1/3. The larger constant is a mathematical deduction
here; the interval-energy and tail steps have not been formalized in this
file. If the high-high bound -b n were proved for a fixed b<1/3,
these estimates would suffice for the frozen dyadic floor.

Sources (physical lines in the pinned 5562-line file):
https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L5159-L5161
https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L5514-L5547
https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45427083174
https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45401291478
-/

/-- A finite lower bound for the bad-prime Euler product in the two
retained denominator blocks of the major-arc model. -/
theorem odd_prime_product_lower {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    (9:ℝ)/16 ≤ ∏ p ∈ P, (1-1/((p:ℝ)-1)^2) := by
  let f := fun p : ℕ => 1 - 1 / ((p:ℝ)-1)^2
  have tel (m : ℕ) : (∏ j ∈ Finset.range m, f (3+j)) =
      ((m:ℝ)+2)/(2*((m:ℝ)+1)) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      dsimp [f]
      push_cast
      have h₁ : (m:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (m:ℝ)+2 ≠ 0 := by positivity
      have e : (3:ℝ)+m-1 = (m:ℝ)+2 := by ring
      rw [e]
      field_simp
      ring
  let U := Finset.Ico 3 (P.sup id + 5)
  have hsub : insert 4 P ⊆ U := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · apply Finset.mem_Ico.mpr
      omega
    · have hsup : p ≤ P.sup id := Finset.le_sup (f := id) hp
      have hlarge := (hP p hp).2
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hcmp : (∏ p ∈ U, f p) ≤ ∏ p ∈ insert 4 P, f p := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ hsub
    · intro p hp
      have hp' : 3 ≤ p := (Finset.mem_Ico.mp hp).1
      have hx : (3:ℝ) ≤ p := by exact_mod_cast hp'
      have hs : (1:ℝ) ≤ ((p:ℝ)-1)^2 := by nlinarith [sq_nonneg ((p:ℝ)-2)]
      dsimp [f]
      exact sub_nonneg.mpr ((div_le_one (by linarith : 0 < ((p:ℝ)-1)^2)).mpr hs)
    · intro p _ _
      dsimp [f]
      exact sub_le_self _ (by positivity)
  have hhalf : (1:ℝ)/2 ≤ ∏ p ∈ U, f p := by
    rw [show U = Finset.Ico 3 (P.sup id+5) from rfl, Finset.prod_Ico_eq_prod_range, tel]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have h4 : 4 ∉ P := by
    intro h
    exact (by decide : ¬ Nat.Prime 4) (hP 4 h).1
  rw [Finset.prod_insert h4] at hcmp
  have hf4 : f 4 = 8/9 := by norm_num [f]
  rw [hf4] at hcmp
  change (9:ℝ)/16 ≤ ∏ p ∈ P, f p
  linarith only [hhalf,hcmp]

/-
A sharper use of the same model keeps both positive blocks g=1 and g=2.
For an even target write a squarefree denominator q=g d, where every
prime factor of g divides n and none of the prime factors of d do.
The verified local coefficients are +1/(p-1) for p|n and -1/(p-1)^2
otherwise; all nonsquarefree denominators contribute zero. Set
W(q)=1_{q≤Q} kernelMass(n,Q/(qn)). Regroup the finite powerset of primes
p≤Q used in PR 316, grouping by the chosen subset of primes dividing n.
For each such g the positive block coefficient is ∏_{p|g}1/(p-1).
The remaining signed inner sum is nonnegative: apply signed_powerset_floor
from the pinned source with no good primes, its bad prime set B and
positive integer shift g. In fact that lemma gives at least W(g)/3.
Consequently the full model dominates the sum of the two blocks g=1,2,
both of which have coefficient 1. On even targets n=2^k, these are
exactly all blocks when Q≥2.

Let C₂ = ∏_{p>2} (1-1/(p-1)^2). For g=1 or 2, the block divided by n is
  ∏_{p≤Q, p∤n}(1-1/(p-1)^2) + O(1/sqrt(Q) + 1/n)
uniformly in the even target. Indeed, the periodic energy and its tail
bound above give |W(q)/n-1| ≤ 1/n + sqrt(q/Q), also for q>Q, when W=0.
For any finite set of odd bad primes the sum of the absolute coefficients
weighted by sqrt(d) is at most ∏_{p>2}(1+sqrt(p)/(p-1)^2), which converges
by comparison with ∑_{j≥3} j^(-3/2). Expanding the two finite products
therefore bounds the replacement error uniformly, including terms gd>Q.
Deleting factors from the infinite product defining C₂ only increases it.
For n=2^k the finite product tends to C₂. The PR's o(n) major-model
error now gives the sharp lower limit
  liminf_{even n→∞} Re(major(n))/n = 2 C₂.
There is a rational margin: for a finite set of odd primes p≥3, adjoin
the composite index 4 and compare factors 1-1/(m-1)^2 with the product
over all integers 3≤m≤T. The latter telescopes to T/(2(T-1)), greater
than 1/2; the extra index contributes 8/9. Thus C₂≥9/16. A uniform
signed high-high bound -n would already suffice for corr(n)≥n/16
eventually, after absorbing the proven small terms and the o(n) errors.
This high-high bound remains open. The sharp lower-limit calculation is
an analytic deduction from the upstream model, not an upstream certificate.

Pinned coefficient and grouping identities, in physical source lines:
https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L4899-L4925
https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L5086-L5155
-/


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

private theorem prime_interval_square_le (X : ℕ) (hX : 2 ≤ X) :
    (∑ p ∈ (Finset.Ioc X (2*X)).filter Nat.Prime, Real.log p)^2 ≤
      ∑ n ∈ (Finset.Ioc (2*X) (4*X)).filter Even, corr n := by
  classical
  let S := (Finset.Ioc X (2*X)).filter Nat.Prime
  let B := (Finset.Ioc (2*X) (4*X)).filter Even
  have memS {p : ℕ} (hp : p ∈ S) : X < p ∧ p ≤ 2*X ∧ p.Prime := by
    simpa [S, and_assoc] using hp
  have wsum : ∑ p ∈ S, Real.log p = ∑ p ∈ S, weight p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [weight, (memS hp).2.2]
  change (∑ p ∈ S, Real.log p)^2 ≤ ∑ n ∈ B, corr n
  rw [wsum, pow_two, Finset.sum_mul]
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, weight p * weight q := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ S, ∑ n ∈ B, weight p * weight (n-p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp₁,hp₂,hp₃⟩ := memS hp
      have sub : S.image (p + ·) ⊆ B := by
        intro n hn
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
        obtain ⟨hq₁,hq₂,hq₃⟩ := memS hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
          (hp₃.odd_of_ne_two (by omega)).add_odd (hq₃.odd_of_ne_two (by omega))⟩
      calc
        _ = ∑ n ∈ S.image (p + ·), weight p * weight (n-p) := by
          rw [Finset.sum_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
          simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub
          (fun n _ _ => mul_nonneg (weight_nonneg _) (weight_nonneg _))
    _ = ∑ n ∈ B, ∑ p ∈ S, weight p * weight (n-p) := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn₁ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      apply Finset.sum_le_sum_of_subset_of_nonneg (s := S) (t := Finset.range (n+1))
      · intro p hp
        have := (memS hp).2.1
        exact Finset.mem_range.mpr (by omega)
      · exact fun p _ _ => mul_nonneg (weight_nonneg _) (weight_nonneg _)


private theorem goldbach_corr_cap {n : ℕ} (hn : 1 ≤ n) :
    corr n ≤ (n : ℝ) * Real.log 4 * Real.log n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hcap (m : ℕ) (hm : m ≤ n) : weight m ≤ Real.log n := by
    unfold weight
    split
    next h => exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hm)
    next => exact hlog
  have hweight : (∑ p ∈ Finset.range (n+1), weight p) = Real.log (primorial n : ℝ) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    · simp [Finset.sum_filter, weight]
    · intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  have hprim : Real.log (primorial n : ℝ) ≤ (n : ℝ) * Real.log 4 := by
    have h := Real.log_le_log (show 0 < (primorial n : ℝ) by exact_mod_cast primorial_pos n)
      (show (primorial n : ℝ) ≤ (4 : ℝ)^n by exact_mod_cast primorial_le_four_pow n)
    simpa using h
  calc
    corr n ≤ ∑ p ∈ Finset.range (n+1), weight p * Real.log n :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hcap (n-p) (Nat.sub_le _ _)) (weight_nonneg p)
    _ = Real.log (primorial n : ℝ) * Real.log n := by rw [← Finset.sum_mul, hweight]
    _ ≤ _ := mul_le_mul_of_nonneg_right hprim hlog

open Classical in
private theorem interval_count_core (X : ℕ) (hx : 192^4 ≤ X) :
    let B := (Finset.Ioc (2*X) (4*X)).filter Even
    let G := B.filter (fun n : ℕ => (n:ℝ)/256 ≤ corr n)
    (X:ℝ) ≤ 128 * G.card * Real.log 4 * Real.log (4 * (X:ℝ)) := by
  classical
  let B := (Finset.Ioc (2*X) (4*X)).filter Even
  let G := B.filter (fun n : ℕ => (n:ℝ)/256 ≤ corr n)
  let C := 4*(X:ℝ)*Real.log 4*Real.log (4*(X:ℝ))
  let t := 4*(X:ℝ)/256
  change (X : ℝ) ≤ 128 * (G.card : ℝ) * Real.log 4 * Real.log (4*(X:ℝ))
  have hx2 : 2 ≤ X := (by norm_num : 2 ≤ 192^4).trans hx
  have hxpos : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hfour := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hcard : (B.card : ℝ) ≤ 2*(X:ℝ) := by
    have h := Finset.card_le_card (Finset.filter_subset (s := Finset.Ioc (2*X) (4*X)) Even)
    simp only [Nat.card_Ioc] at h
    exact_mod_cast (show B.card ≤ 2*X by change B.card ≤ _ at h; omega)
  have hpoint (n : ℕ) (hn : n ∈ B) : corr n ≤ (if (n:ℝ)/256 ≤ corr n then C else 0) + t := by
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hn1 : 1 ≤ n := by omega
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hle : (n:ℝ) ≤ 4*(X:ℝ) := by exact_mod_cast hu
    by_cases h : (n:ℝ)/256 ≤ corr n
    · rw [ite_eq_left h]
      refine (goldbach_corr_cap hn1).trans ((le_add_of_nonneg_right ht).trans' ?_)
      dsimp [C]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hle hfour)
        (Real.log_le_log hnpos hle) (Real.log_nonneg (by exact_mod_cast hn1))
        (mul_nonneg (by positivity) hfour)
    · rw [ite_eq_right h, zero_add]
      dsimp [t]
      linarith
  have hup : (∑ n ∈ B, corr n) ≤ (G.card:ℝ)*C + (B.card:ℝ)*t := by
    refine (Finset.sum_le_sum hpoint).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [G]
  have hp := dyadic_prime_mass X hx
  have hsq := mul_self_le_mul_self (show (0:ℝ) ≤ X/4 by positivity) hp
  have hlow := prime_interval_square_le X hx2
  change _ ≤ ∑ n ∈ B, corr n at hlow
  have hcount := mul_le_mul_of_nonneg_right hcard ht
  dsimp only [C,t] at hup hcount
  have hscaled : (X:ℝ)*X ≤ X*(128*(G.card:ℝ)*Real.log 4*Real.log (4*(X:ℝ))) := by
    nlinarith only [hsq, hlow, hup, hcount]
  exact (mul_le_mul_iff_right₀ hxpos).mp hscaled

open Classical in
/-- In every dyadic interval above the threshold, the number of even n for
which corr(n) is at least n/256 is at least (Y-1)/(256 log(4) log(2Y)). -/
theorem dyadic_count_whole (Y : ℕ) (hY : 2*192^4 ≤ Y) :
    (Y : ℝ)-1 ≤ 256 * (((Finset.Ioc Y (2*Y)).filter Even).filter
      (fun n : ℕ => (n : ℝ)/256 ≤ corr n)).card * Real.log 4 * Real.log (2*(Y : ℝ)) := by
  classical
  let X := Y/2
  have hx : 192^4 ≤ X := by dsimp [X]; omega
  have hX1 : 1 ≤ X := by omega
  have hdouble : 2 * X ≤ Y := by dsimp [X]; omega
  have hodd : Y ≤ 2 * X + 1 := by dsimp [X]; omega
  let A := ((Finset.Ioc (2*X) (4*X)).filter Even).filter (fun n : ℕ => (n : ℝ)/256 ≤ corr n)
  let B := ((Finset.Ioc Y (2*Y)).filter Even).filter (fun n : ℕ => (n : ℝ)/256 ≤ corr n)
  have hab : A ⊆ B := by
    intro n hn
    obtain ⟨hnB, hgood⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, he⟩ := Finset.mem_filter.mp hnB
    obtain ⟨hnl, hnu⟩ := Finset.mem_Ioc.mp hnI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ?_, he⟩, hgood⟩
    obtain ⟨k, hk⟩ := he
    omega
  have hc : (A.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hab
  have hs : (X : ℝ) ≤ 128 * A.card * Real.log 4 * Real.log (4*(X : ℝ)) :=
    interval_count_core X hx
  have hL : Real.log (4*(X : ℝ)) ≤ Real.log (2*(Y : ℝ)) := by
    apply Real.log_le_log
    · have : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      positivity
    · exact_mod_cast (show 4*X ≤ 2*Y by omega)
  have hL0 : 0 ≤ Real.log (4*(X : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 4*X by omega))
  have hY' : (Y : ℝ) ≤ 2*(X : ℝ)+1 := by exact_mod_cast hodd
  change (Y : ℝ)-1 ≤ 256 * (B.card : ℝ) * Real.log 4 * Real.log (2*(Y : ℝ))
  calc
    _ ≤ 2*(X : ℝ) := by linarith
    _ ≤ 256 * (A.card : ℝ) * Real.log 4 * Real.log (4*(X : ℝ)) := by linarith
    _ ≤ _ := by gcongr

/-- A linear lower bound for at least one even integer in every sufficiently
large dyadic interval, with an explicit threshold. -/
theorem exists_dyadic_witness (Y : ℕ) (hY : 2 * 192^4 ≤ Y) :
    ∃ n : ℕ, Y < n ∧ n ≤ 2*Y ∧ Even n ∧ (n : ℝ)/256 ≤ corr n := by
  classical
  let S := ((Finset.Ioc Y (2*Y)).filter Even).filter (fun n : ℕ => (n : ℝ)/256 ≤ corr n)
  have hs := dyadic_count_whole Y hY
  change (Y:ℝ)-1 ≤ 256*(S.card:ℝ)*Real.log 4*Real.log (2*(Y:ℝ)) at hs
  by_cases h : S.Nonempty
  · obtain ⟨n,hn⟩ := h
    obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hj,he⟩ := Finset.mem_filter.mp hi
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hj
    exact ⟨n,hl,hu,he,hc⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp h] at hs
    simp at hs
    have hy : (1:ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
    linarith

/-!
## Size of the signed tail (analytic derivation)

The equations above are finite Lean theorems. In the following argument,
ordinary asymptotic estimates are mathematical notes rather than declarations.
Write A(n,d) for `progression n d`, a(d) for `primeCoefficient d`,
R(n) for `corr n`, and T_D(n) = ∑_{D < d ≤ n} a(d) A(n,d).

**The actual block average.** Fix 0 < θ < 1. Use the same D = floor(X^θ)
for every n in X < n ≤ 2X. Then

  ∑_{X < n ≤ 2X, n even} T_D(n) = (3/2)(1 - 1/θ) X² + o(X²).

In particular for θ = 1/2 the signed tail has a *negative* quadratic
block sum. The same conclusion holds for D = floor(sqrt(X)/log(X)^5).
This excludes a uniform estimate T_D(n) = o(n) for that blockwise choice.

Here are details of the coefficient calculation. Let z(s) = ζ(1+s)
and P(s) = ∑_p p^(-1-s). For Re(s)>0 the Dirichlet series of
1_{d odd} a(d)/d equals
  [(1-2^(-1-s)) z(s)]⁻¹ [P(s) - 2^(-1-s)].
The coefficients of P(s)-log z(s) are supported on prime powers p^j
with j ≥ 2 and have a finite absolute moment of order 1/4. Thus the only
term of order 1/log D in the summatory function comes from log z(s)/z(s);
the prefactor (1-2^(-1-s))⁻¹ has coefficient sum 2.

For the sharp cutoff, the coefficients of log z(s)/z(s) sum up to x to
  ∑_{ab ≤ x, b ≥ 2} (μ(a)/a) Λ(b)/(b log b) = 1/log x + O(1/log² x).
To see this, write L=log x and U(t)=∑_{a≤exp(t)} μ(a)/a.
The classical zero-free-region estimate for the Mertens function and
partial summation give |U(t)| ≪ exp(-c sqrt t). Its Laplace transform
is 1/(s ζ(1+s)), so ∫₀^∞ U(t) dt = 1. The part b ≤ sqrt(x) is negligible
by the bound for U. In the remaining part a ≤ sqrt(x); by the prime
number theorem with its classical remainder,
  ∑_{sqrt(x) < b ≤ x/a} Λ(b)/(b log b)
    = log(2(1-log a/L)) + O(L⁻⁴),
uniformly there. Stieltjes summation by parts against U leaves
  ∫₀^(L/2) U(t)/(L-t) dt = 1/L + O(1/L²).
The endpoint value at L/2 is zero in the integration by parts, and the
jump μ(1) is included in U. Convolution with either absolutely convergent
factor above preserves these errors: split its index at sqrt(x) and use
the absolute 1/4 moment on the far side. In particular,
  ∑_{d≤D, d odd} a(d)/d = 2/log D + O(1/log² D).

To average the short divisors, first fix an odd prime p and put m=n-p.
Then m must be odd. For odd d, the odd multiples of d have spacing 2d.
Their sum of log m on (max(1,X-p),2X-p] differs from (1/(2d)) times
the integral of log t on this interval by O(log X), uniformly in p,d;
an empty interval contributes zero. The total error is
O(X D log² X) = o(X²) since ∑_{p≤2X} log p ≪ X and |a(d)| ≤ log₂ d.
The row p=2 contributes O(X log³ X + D log² X). By the prime number
theorem the sum over p of the integrals, weighted by log p, is
(3/2 + o(1)) X² log X: replacing log t by log X costs O(X²), and the
scaled region 1 < p/X + t/X ≤ 2 in the first quadrant has area 3/2.
Thus the short sum averages to (3/(2θ)+o(1))X². The unrestricted true
prime-pair correlation over the even n of the same block sums to
(3/2+o(1))X², by applying the prime number theorem to both variables
on the same region. The omitted odd n require a summand 2 and cost O(X).
Subtracting proves the displayed result.

**A pointwise short-divisor model.** For even n put
  S(n) = 2 ∏_{p>2}(1-1/(p-1)²) ∏_{p|n,p>2}(p-1)/(p-2),
and B = 1+log log(3n). For n ≤ D^C with fixed C, the following estimate
uses the same sharp-cutoff calculation:
  ∑_{d≤D, (d,n)=1} a(d)/φ(d) = S(n)/log D + O_C(B⁴/log² D).
For clarity, write u=p^(-s), F=∏_{p∤n}(1-u/(p-1)), H=z(s)F and
  b_p = [u/(p-1)-u²/(p(p-1))]/[1-u/(p-1)].
Distinguishing the prime in a(d)=(μ*1_prime)(d) gives the series
F ∑_{p∤n} b_p. This is H log z(s)/z(s) + H J/z(s), where
J=∑_{p∤n} b_p-log z(s). H(0)=S(n). At n=2, H and J have absolutely
convergent coefficients with finite 1/4 moment. For p>2 the nonconstant
coefficients of H's local factor are -1/(p^j(p-1)); the coefficients of
b_p for j≥2 are 1/(p(p-1)^j). These identities give the claimed convergence.
For primes p>2 dividing n, multiply H by (1-u/(p-1))⁻¹ and subtract b_p
from J. The extra positive Euler product has mass O(B) by Mertens'
product theorem. Its normalized first and second absolute log moments
are O(B) and O(B²): use ∑_{p|n}(log p)^j/p ≪ B^j (j=1,2), splitting at
(log(3n))², and use ∑_{p|n}log p ≤ log n on the large-prime side.
The same estimates bound the mass and second absolute log moment of J
by O(B) and O(B²), respectively. The second absolute log moment of HJ
is therefore O(B⁴). Split both convolutions at sqrt(D): the far-side
coefficient mass is O(B⁴/log² D), and on the near side expand
1/log(D/m)=1/log D+O(log(m)/log² D) and use the bound for U. This
proves the estimate uniformly. The constant implicit in the error does
not depend on the prime factors of n.

For D=floor(sqrt(n)/log(n)^5), the GRH prime-progression prefix estimate
O(sqrt(n) log² n), the formal theorem `prime_progression_remainder`, and
log(n!) = n log n - n + O(log n) now yield
  R(n) = 2 S(n) n + T_D(n) + o(n).
The ordinary Dirichlet GRH input is used here for the progressions.
For noncoprime classes at most one prime can occur. The prefix cost is
O(n/log n) after summing short divisors with |a(d)| ≤ log₂ d. Also
S(n) ≪ B, which makes the remaining displayed errors o(n) absolutely.
A uniform lower bound T_D(n) ≥ -(2-δ)S(n)n for some fixed δ>0 would
imply the frozen floor. The negative block average does not supply it.

The classical Mertens input is made explicit in
https://arxiv.org/abs/2208.06141 . For independent short-interval
averaged Goldbach estimates see Goldston, equations (4)-(8),
https://doi.org/10.1017/S001708950000937X , and Matomäki–Radziwiłł–Tao,
Theorem 1.3(iv), https://www.math.mcgill.ca/radziwill/correlations.pdf .
-/

/-- The squared coefficient mass of the genuine high-prime sum already
grows like at least Y log(Y)/4 at n=2Y. Parseval turns it into whole-circle
energy. In particular it cannot give a linear upper bound for the minor
coefficient by itself. -/
theorem high_prime_energy_lower (Y : ℕ) (hY : 192^4 ≤ Y) :
    (Y:ℝ)*Real.log Y/4 ≤ ∑ p ∈ (Finset.range (2*Y+1)).filter
      (fun p : ℕ => 2*Y < p^3), (weight p)^2 := by
  let S := (Finset.Ioc Y (2*Y)).filter Nat.Prime
  have hY₂ : 2 ≤ Y := (by norm_num : 2 ≤ 192^4).trans hY
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ Y by exact_mod_cast (by omega : 1 ≤ Y))
  have hsub : S ⊆ (Finset.range (2*Y+1)).filter (fun p : ℕ => 2*Y < p^3) := by
    intro p hp
    obtain ⟨hi,hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hi
    have hpp : 2 < p := by omega
    have hcube : 2*p ≤ p^3 := by
      have hsq := Nat.mul_le_mul_left p (show 2 ≤ p from hpp.le)
      have hmul := Nat.mul_le_mul_left (p*p) (show 1 ≤ p by omega)
      nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  have hm := dyadic_prime_mass Y hY
  calc
    (Y:ℝ)*Real.log Y/4 = ((Y:ℝ)/4) * Real.log Y := by ring
    _ ≤ (∑ p ∈ S, Real.log p) * Real.log Y := mul_le_mul_of_nonneg_right hm hlog
    _ = ∑ p ∈ S, Real.log p * Real.log Y := Finset.sum_mul ..
    _ ≤ ∑ p ∈ S, (weight p)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hi,hprime⟩ := Finset.mem_filter.mp hp
      have hle := (Finset.mem_Ioc.mp hi).1.le
      have hpLog := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hprime.one_le)
      rw [weight, ite_eq_left hprime, pow_two]
      apply mul_le_mul_of_nonneg_left _ hpLog
      exact Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hle)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)

/-!
## Testing a pointwise bound for the high-high minor coefficient

At n=2^k the preceding sharp major-arc calculation gives
  Re HH(n)/n = corr(n)/n - 2 C₂ + o(1).
In particular a uniform bound Re HH(n) ≥ -n implies
liminf_k corr(2^k)/2^k ≥ 2 C₂-1 ≥ 1/8. A theorem counting exceptions
up to X does not establish this inequality on the O(log X) powers of two.
It is a necessary test of the proposed -n route, not a new necessary
constant in the frozen statement, which allows any positive constant.

For the true prime weights, the absolute-value estimate on the minor arcs
loses a logarithm. Write H(t) for the Fourier sum restricted to p³>n.
Parseval and the prime number theorem by partial summation give
  ∫₀¹ |H(t)|² dt = ∑_{p≤n, p³>n} log² p ∼ n log n.
The lemma above gives an elementary finite lower bound on this sum.
In fact the same leading term occurs on the minor arcs alone. On a
major arc about a/q, with q≤Q and (a,q)=1, use the model from PR 316.
By the reverse triangle inequality applied to the two squared sums, the
error for the squared absolute values is at most the PR's pointwise
modelError; summing its integrals costs o(n). For the untruncated prime
weight, each model integral costs at most (n+1) μ(q)²/φ(q)². There are
φ(q) numerators, counting the two endpoints for q=1 jointly. Thus the
major energy is O(n log(2Q)), since
  ∑_{q≤Q} 1/φ(q) ≤ (1+log Q) ∑_{d≥1} μ(d)²/(d φ(d)).
This follows by expanding q/φ(q); the series on the right converges by
its Euler product. Omitting p³≤n costs O(n^(1/3) log² n) in whole-circle
squared norm, giving the same O(n log(2Q)) bound for the high major
energy by the squared triangle inequality. Here Q grows as log² n.
Consequently ∫minor |H(t)² exp(-2πint)| dt ∼ n log n. The sign in
Re HH, essential at the linear scale, is lost in that absolute integral.

A density-one subset tests a different proposed transfer. Fix N_j=4^j
and remove every prime p≥N_j/2 with N_j-p prime, for every j≥1.
The union D is a single fixed set. The upper-bound sieve for the
Goldbach prime pairs at 4^j gives O(N_j/log² N_j) removed primes per
target, since 4^j has no odd prime divisor. A geometric sum gives
#(D∩[1,x])=O(x/log²x): the only contributing j satisfy N_j≤2x.
Thus the retained set has full relative prime density and its prime
sum on each fixed reduced progression keeps the prime number theorem
main term. No square-root remainder for the modified set is asserted.
Every N_j has exactly zero retained representations, even after the
high cutoff, since the larger prime in any such pair was removed.

These sparse deletions change the high-high major integral by o(n)
uniformly. On the grid θ+j/n the desk major arcs contain O(Q²) points,
as there are O(Q²) intervals of total length O(Q²/n). Apply Theorem 1.1
of Ramaré to this 1/n-spaced subset, then integrate over 0≤θ<1/n.
For any prime-supported coefficients u this gives
  ∫major |S_u|² ≪ (log(2Q)/log n) ∑ |u_p|².
For the high deleted weights the coefficient squared sum is O(n);
for the original high weights it is O(n log n). Cauchy-Schwarz then
bounds the change in the signed major by O(n log(2Q)/sqrt(log n))=o(n).
The original high major differs from the all-prime major by o(n) as
well: combine the O(n log(2Q)) major energy with the whole-circle
low energy O(n^(1/3) log² n). Along N_j the modified high-high minor is
therefore -(2C₂+o(1))N_j, strictly below -N_j eventually. This checks
that the estimated major floor, near-full prime density, and ordinary
energy comparisons cannot force the proposed minor bound. The
modified weight is an auxiliary counterexample to that inference;
it is not a counterexample for the actual prime indicator.

Sources: PR 316, definitions modelError and totalArcError, at
https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L4551-L4559 .
Wu, double sieve and Goldbach upper bound, Theorem 1,
https://arxiv.org/pdf/0705.1652 . Ramaré, Notes on restriction theory in
the primes, Theorem 1.1, https://ramare-olivier.github.io/Maths/RestrictionTheory-IJM-06.pdf .
-/

/-- Above the midpoint, a prime divides a shifted factor exactly when the
complementary summand is prime. -/
theorem half_prime_dvd_complement_product {n q : ℕ} (hq : q.Prime)
    (hlo : n/2 < q) (hhi : q ≤ n) :
    q ∣ (∏ p ∈ (Finset.range (n/2+1)).filter Nat.Prime, (n-p)) ↔ (n-q).Prime := by
  rw [hq.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨p,hp,hdiv⟩
    obtain ⟨hpr,hprime⟩ := Finset.mem_filter.mp hp
    have hp' := Finset.mem_range.mp hpr
    obtain ⟨k,hk⟩ := hdiv
    have he : n-p=q := by
      rcases k with _ | k
      · simp at hk
        omega
      · cases k with
        | zero => simpa using hk
        | succ k =>
          have hx : q*2 ≤ n-p := hk ▸ Nat.mul_le_mul_left q (show 2 ≤ k.succ.succ by omega)
          omega
    have ep : n-q=p := by omega
    simpa only [ep] using hprime
  · intro hp
    refine ⟨n-q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩,?_⟩
    rw [Nat.sub_sub_self hhi]

theorem half_prime_gcd_eq_product (n : ℕ) :
    Nat.gcd (∏ q ∈ (Finset.Ioc (n/2) n).filter Nat.Prime, q)
        (∏ p ∈ (Finset.range (n/2+1)).filter Nat.Prime, (n-p)) =
      ∏ q ∈ ((Finset.Ioc (n/2) n).filter Nat.Prime).filter (fun q => (n-q).Prime), q := by
  let U := (Finset.Ioc (n/2) n).filter Nat.Prime
  let B := ∏ p ∈ (Finset.range (n/2+1)).filter Nat.Prime, (n-p)
  let P := ∏ q ∈ U, q
  have hpr : ∀ q ∈ U, Nat.Prime q := fun q hq => (Finset.mem_filter.mp hq).2
  have hfac : P.primeFactors = U := Nat.primeFactors_prod hpr
  have hsq : Squarefree P := by
    have h := Nat.squarefree_prod_primeFactors P
    rwa [hfac] at h
  have hg : Squarefree (P.gcd B) := hsq.squarefree_of_dvd (Nat.gcd_dvd_left P B)
  change P.gcd B = ∏ q ∈ U.filter (fun q => (n-q).Prime), q
  rw [← Nat.prod_primeFactors_of_squarefree hg]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext q
  rw [Nat.mem_primeFactors_of_ne_zero hg.ne_zero, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hq,hqP,hqB⟩
    have hu : q ∈ U := hfac ▸ (Nat.mem_primeFactors_of_ne_zero hsq.ne_zero).mpr ⟨hq,hqP⟩
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1
    exact Finset.mem_filter.mpr ⟨hu,(half_prime_dvd_complement_product hq hi.1 hi.2).mp hqB⟩
  · intro h
    obtain ⟨hu,hprime⟩ := Finset.mem_filter.mp h
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1
    have hq := hpr q hu
    exact ⟨hq, Finset.dvd_prod_of_mem id hu,
      (half_prime_dvd_complement_product hq hi.1 hi.2).mpr hprime⟩

def shiftedPrimeGcd (n : ℕ) : ℕ :=
  Nat.gcd (∏ q ∈ (Finset.Ioc (n/2) n).filter Nat.Prime, q)
    (∏ p ∈ (Finset.range (n/2+1)).filter Nat.Prime, (n-p))

theorem shiftedPrimeGcd_eq (n : ℕ) :
    shiftedPrimeGcd n = ∏ q ∈ (reps n).filter (fun q => n/2 < q), q := by
  rw [shiftedPrimeGcd, half_prime_gcd_eq_product]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext q
  simp only [reps, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hlo,hhi⟩,hq⟩,hp⟩
    exact ⟨⟨by omega,hq,hp⟩,hlo⟩
  · rintro ⟨⟨hhi,hq,hp⟩,hlo⟩
    exact ⟨⟨⟨hlo,by omega⟩,hq⟩,hp⟩

theorem reps_card_by_upper_half (n : ℕ) :
    (reps n).card = 2 * ((reps n).filter (fun p => n/2 < p)).card +
      (if Even n ∧ (n/2).Prime then 1 else 0) := by
  classical
  let T := (reps n).filter (fun p => n/2 < p)
  let A := (reps n).filter (fun p => ¬ n/2 < p)
  let D := A.filter (fun p => 2*p = n)
  let L := A.filter (fun p => ¬ 2*p = n)
  have memR (p : ℕ) : p ∈ reps n ↔ p ≤ n ∧ p.Prime ∧ (n-p).Prime := by
    simp [reps]
  have memL (p : ℕ) : p ∈ L ↔ p ∈ reps n ∧ 2*p < n := by
    simp only [L, A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hle⟩, hne⟩
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨⟨hp, by omega⟩, by omega⟩
  have hflip (p : ℕ) (hp : p ∈ reps n) : n-p ∈ reps n := by
    obtain ⟨hle,hp,hq⟩ := (memR p).mp hp
    exact (memR _).mpr ⟨by omega, hq, (by rwa [show n-(n-p)=p by omega])⟩
  have hLT : L.card = T.card := by
    apply Finset.card_bij (fun p _ => n-p)
    · intro p hp
      obtain ⟨hr, hlt⟩ := (memL p).mp hp
      exact Finset.mem_filter.mpr ⟨hflip _ hr, by omega⟩
    · intro p hp q hq heq
      have hp' := ((memR p).mp ((memL p).mp hp).1).1
      have hq' := ((memR q).mp ((memL q).mp hq).1).1
      change n-p = n-q at heq
      omega
    · intro p hp
      obtain ⟨hr, hgt⟩ := Finset.mem_filter.mp hp
      have hle := ((memR p).mp hr).1
      exact ⟨n-p, (memL _).mpr ⟨hflip _ hr, by omega⟩, by omega⟩
  have memD (p : ℕ) : p ∈ D ↔ (Even n ∧ (n/2).Prime) ∧ p = n/2 := by
    simp only [D, A, Finset.mem_filter, memR]
    constructor
    · rintro ⟨⟨⟨hle, hp, _⟩, _⟩, hfix⟩
      have he : p = n/2 := by omega
      exact ⟨⟨⟨p, by omega⟩, he ▸ hp⟩, he⟩
    · rintro ⟨⟨⟨k,hk⟩, hp⟩, rfl⟩
      have he : n - n/2 = n/2 := by omega
      exact ⟨⟨⟨by omega, hp, he.symm ▸ hp⟩, by omega⟩, by omega⟩
  have hD : D.card = if Even n ∧ (n/2).Prime then 1 else 0 := by
    by_cases h : Even n ∧ (n/2).Prime
    · have he : D = {n/2} := by ext p; simp [memD, h]
      simp [h, he]
    · have he : D = ∅ := by ext p; simp [memD, h]
      simp [h, he]
  have h₁ : T.card + A.card = (reps n).card :=
    Finset.card_filter_add_card_filter_not (s := reps n) (fun p => n/2 < p)
  have h₂ : D.card + L.card = A.card :=
    Finset.card_filter_add_card_filter_not (s := A) (fun p => 2*p = n)
  change (reps n).card = 2*T.card + _
  omega

private theorem repr_log_gcd_bounds (n : ℕ) (hn : 4 ≤ n) :
    2 * Real.log (shiftedPrimeGcd n : ℝ) ≤ (reps n).card * Real.log n ∧
      (reps n).card * Real.log n ≤ 4*Real.log (shiftedPrimeGcd n : ℝ) + Real.log n := by
  classical
  let T := (reps n).filter (fun q => n/2 < q)
  have hc := reps_card_by_upper_half n
  change (reps n).card = 2*T.card + _ at hc
  have hsize : 2*T.card ≤ (reps n).card ∧ (reps n).card ≤ 2*T.card+1 := by
    split at hc <;> omega
  have hL := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
  have hprime (q : ℕ) (hq : q ∈ T) : q.Prime ∧ q ≤ n ∧ n ≤ q^2 := by
    obtain ⟨hr,hh⟩ := Finset.mem_filter.mp hq
    obtain ⟨hi,hp,_⟩ := Finset.mem_filter.mp hr
    have hi' := Finset.mem_range.mp hi
    have hq2 := hp.two_le
    have hs := Nat.mul_le_mul_left q hq2
    have hmid : n ≤ q*2 := by omega
    exact ⟨hp, by omega, by simpa [pow_two] using hmid.trans hs⟩
  have hprod : Real.log (shiftedPrimeGcd n : ℝ) = ∑ q ∈ T, Real.log q := by
    rw [shiftedPrimeGcd_eq, Nat.cast_prod, Real.log_prod _]
    exact fun q hq => by exact_mod_cast (hprime q hq).1.ne_zero
  have hu : (∑ q ∈ T, Real.log q) ≤ (T.card:ℝ)*Real.log n := by
    calc
      _ ≤ ∑ _q ∈ T, Real.log n := by
        apply Finset.sum_le_sum
        intro q hq
        exact Real.log_le_log (by exact_mod_cast (hprime q hq).1.pos)
          (by exact_mod_cast (hprime q hq).2.1)
      _ = _ := by simp
  have hl : (T.card:ℝ)*Real.log n ≤ 2*(∑ q ∈ T, Real.log q) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _q ∈ T, Real.log n := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        have h := Real.log_le_log (show (0:ℝ) < n by exact_mod_cast (by omega : 0 < n))
          (show (n:ℝ) ≤ (q:ℝ)^2 by exact_mod_cast (hprime q hq).2.2)
        simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hc₁ : 2*(T.card:ℝ) ≤ (reps n).card := by exact_mod_cast hsize.1
  have hc₂ : ((reps n).card:ℝ) ≤ 2*(T.card:ℝ)+1 := by exact_mod_cast hsize.2
  rw [hprod]
  constructor <;> nlinarith only [hu,hl,mul_le_mul_of_nonneg_right hc₁ hL,
    mul_le_mul_of_nonneg_right hc₂ hL]

/-- The frozen goal is equivalent to a lower bound on the logarithm of
the gcd of two integer products. The diagonal n=2p is absorbed in the
threshold. Neither side has a conjecture as an extra hypothesis. -/
theorem dyadic_floor_iff_shifted_gcd :
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n) ↔
    ∃ (b : ℝ) (N : ℕ), 0 < b ∧ ∀ n ≥ N, Even n →
      b*(n:ℝ) ≤ Real.log (shiftedPrimeGcd n : ℝ)*Real.log n := by
  rw [dyadic_floor_iff_count]
  constructor
  · rintro ⟨a,M,ha,hcount⟩
    obtain ⟨K,hK⟩ := endpoint_error (a/2) (half_pos ha)
    refine ⟨a/8,max 4 (max M K),by positivity,?_⟩
    intro n hn he
    have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
    have hnM : M ≤ n := ((le_max_left M K).trans (le_max_right _ _)).trans hn
    have hnK : K ≤ n := ((le_max_right M K).trans (le_max_right _ _)).trans hn
    have hL := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    have hdiag := hK n hnK
    have hcoef : (1:ℝ) ≤ ((2*(n.sqrt+1):ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ 2*(n.sqrt+1))
    have hs := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log (n:ℝ)))
    have h := mul_le_mul_of_nonneg_right (repr_log_gcd_bounds n hn4).2 hL
    nlinarith only [hcount n hnM he,h,hdiag,hs]
  · rintro ⟨b,M,hb,hg⟩
    refine ⟨2*b,max 4 M,by positivity,?_⟩
    intro n hn he
    have hn4 := (le_max_left 4 M).trans hn
    have hL := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    have h := mul_le_mul_of_nonneg_right (repr_log_gcd_bounds n hn4).1 hL
    nlinarith only [hg n ((le_max_right _ _).trans hn) he,h]


/-!
For the product B in shiftedPrimeGcd there is also an analytic estimate
for individual n. The argument below is on paper.

Put x=n/2. The prime number theorem gives log B=(1/2+o(1))n.
A prime power d=l^j supplies (log l) times the number of p<=x in the
class n mod d. Classes with l|n contribute O(log² n) in total: their
only possible prime is p=l, and each such p contributes at most log n.
For D=sqrt(x)/log(x)^A, with A sufficiently large, Bombieri–Vinogradov
gives (1/4+o(1))n for the contribution of d<=D. Indeed the sum of
log(l)/phi(l^j) over d<=D is log D+O(1); omitting primes dividing n
costs O(log log n) in that sum. A factor log n in the total progression
error is paid for by taking the logarithmic saving in BV greater than 2.

The contribution of powers with j>=2 and D<l^j<=n is o(n). Use
n/l^j+1 for each occupancy: the weighted reciprocal tail tends to zero
and the contribution of the 1's is O(sqrt(n) log² n). For
D<l<=n^alpha, Brun–Titchmarsh and partial summation give at most
(n+o(n))*log((1/2)/(1-alpha)), with 1/2<alpha<1 fixed.
At alpha=3/5 the mass left is at least
(1/4-log(5/4)-o(1))*n. A complementary integer n-p has at most one
such prime factor, and contributes at most log n. Thus uniformly for
large n, at least n/(40 log n) primes p<=n/2 have n-p divisible by a
prime exceeding n^(3/5).

For alpha=5/8 one can use Iwaniec's prime progression upper bound with
coefficient 8/(6-7t) for t=log(l)/log(x). The log mass left is at least
(1/4-(4/7)*log((5/2)/(6-7*alpha))-o(1))*n, giving n/(270 log n)
such primes p. To pass to the integral, partition the exponent interval
into compact subintervals and then let the mesh and the epsilon in the
progression estimate tend to zero. See the uniform estimate (1.1)-(1.2)
and references in https://arxiv.org/html/2504.12692v1 .
Base estimates: https://doi.org/10.1112/S0025579300005313 and
https://doi.org/10.1112/S0025579300004708 .

If n is even and p is odd, the cofactor (n-p)/l is odd. To contribute
to the gcd it must equal one and l must exceed n/2. The large-factor
count still admits odd cofactors >=3.
-/

/-- A reflected pair of sliding prime sums has positive total mass
as soon as the mean square deviation of one window sum is small. -/
theorem reflected_window_mass_of_variance (N : ℕ) (h : ℝ) (w : ℕ → ℝ)
    (hvar : ∑ t ∈ Finset.range (N+1), (w t - h)^2 ≤ ((N+1:ℕ):ℝ)*h^2/12) :
    ((N+1:ℕ):ℝ)*h^2/2 ≤ ∑ t ∈ Finset.range (N+1), w t * w (N-t) := by
  classical
  let v (t : ℕ) := (w t-h)^2
  let I := Finset.range (N+1)
  have hflip : ∑ t ∈ I, v (N-t) = ∑ t ∈ I, v t := by
    apply Finset.sum_nbij' (fun t => N-t) (fun t => N-t)
    · intro t ht
      have hlt := Finset.mem_range.mp ht
      exact Finset.mem_range.mpr (by omega)
    · intro t ht
      have hlt := Finset.mem_range.mp ht
      exact Finset.mem_range.mpr (by omega)
    · intro t ht
      have hlt := Finset.mem_range.mp ht
      omega
    · intro t ht
      have hlt := Finset.mem_range.mp ht
      omega
    · intro t ht
      rfl
  have hs : ∑ _t ∈ I, 2*h^2 ≤
      ∑ t ∈ I, (3*(w t*w (N-t)) + 3*v t + 3*v (N-t)) := by
    apply Finset.sum_le_sum
    intro t _
    dsimp [v]
    nlinarith only [sq_nonneg (w t-w (N-t)), sq_nonneg (3*(w t+w (N-t))-4*h)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hflip, Finset.sum_const,
    I, Finset.card_range, nsmul_eq_mul] at hs
  change ∑ t ∈ I, v t ≤ _ at hvar
  change _ ≤ ∑ t ∈ I, w t * w (N-t)
  dsimp only [I] at hvar ⊢
  dsimp only [v] at hs hvar
  nlinarith only [hs,hvar]

/-- Expand two reflected sliding windows and group ordered prime pairs
by their sum. A pair contributes at most H times. -/
theorem reflected_window_product_le (N H : ℕ) :
    (∑ t ∈ Finset.range (N+1), (∑ i ∈ Finset.Icc 1 H, weight (t+i)) *
      (∑ j ∈ Finset.Icc 1 H, weight (N-t+j))) ≤
        (H:ℝ) * ∑ m ∈ Finset.Icc (N+2) (N+2*H), corr m := by
  let T := Finset.range (N+1)
  let S := Finset.Icc 1 H
  let U := Finset.Icc (N+2) (N+2*H)
  have hcorr (m : ℕ) : 0 ≤ corr m :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (weight_nonneg _) (weight_nonneg _)
  have hpair (i j : ℕ) : (∑ t ∈ T, weight (t+i)*weight (N-t+j)) ≤ corr (N+i+j) := by
    unfold corr
    apply Finset.sum_le_sum_of_injOn (fun t => t+i)
    · intro a _ b _ e
      dsimp at e
      omega
    · intro x hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      have ht' := Finset.mem_range.mp ht
      exact Finset.mem_range.mpr (by omega)
    · intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [show N+i+j-(t+i)=N-t+j by omega]
    · exact fun _ _ _ => mul_nonneg (weight_nonneg _) (weight_nonneg _)
  have hrow (i : ℕ) (hi : i ∈ S) :
      (∑ j ∈ S, corr (N+i+j)) ≤ ∑ m ∈ U, corr m := by
    apply Finset.sum_le_sum_of_injOn (fun j => N+i+j)
    · intro a _ b _ e
      dsimp at e
      omega
    · intro m hm
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hi₁,hi₂⟩ := Finset.mem_Icc.mp hi
      obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · exact fun _ _ => le_rfl
    · exact fun m _ _ => hcorr m
  change (∑ t ∈ T, (∑ i ∈ S, weight (t+i)) * (∑ j ∈ S, weight (N-t+j))) ≤ _
  calc
    _ = ∑ t ∈ T, ∑ i ∈ S, ∑ j ∈ S, weight (t+i)*weight (N-t+j) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ t ∈ T, weight (t+i)*weight (N-t+j) := by
      rw [Finset.sum_comm (s := T) (t := S)]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, corr (N+i+j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ ≤ ∑ _i ∈ S, ∑ m ∈ U, corr m := Finset.sum_le_sum hrow
    _ = _ := by simp [S,U,Nat.card_Icc,nsmul_eq_mul]

theorem short_interval_mass_of_variance (N H : ℕ) (hH : 0 < H)
    (hvar : ∑ t ∈ Finset.range (N+1),
      ((∑ i ∈ Finset.Icc 1 H, weight (t+i)) - H)^2 ≤ ((N+1:ℕ):ℝ)*H^2/12) :
    ((N+1:ℕ):ℝ)*H/2 ≤ ∑ m ∈ Finset.Icc (N+2) (N+2*H), corr m := by
  have h := (reflected_window_mass_of_variance N (H:ℝ)
    (fun t => ∑ i ∈ Finset.Icc 1 H, weight (t+i)) hvar).trans
    (reflected_window_product_le N H)
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH
  apply le_of_mul_le_mul_left _ hH'
  calc
    _ = ((N+1:ℕ):ℝ)*H^2/2 := by ring
    _ ≤ _ := h

/-- Pass from local first and second moments to the number of indices
where the values exceed a fixed threshold. -/
theorem count_above_threshold_of_moments (S : Finset ℕ) (f : ℕ → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    4*b*(∑ m ∈ S, f m) ≤ 4*b*a*S.card + 4*(∑ m ∈ S, (f m)^2) +
      b^2*((S.filter (fun m => a ≤ f m)).card:ℝ) := by
  classical
  have hpoint (m : ℕ) : 4*b*f m ≤
      4*b*a + 4*(f m)^2 + (if a ≤ f m then b^2 else 0) := by
    by_cases h : a ≤ f m
    · simp only [ite_eq_left h]
      nlinarith only [sq_nonneg (2*f m-b), mul_nonneg hb.le ha]
    · simp only [ite_eq_right h]
      nlinarith only [sq_nonneg (f m), mul_le_mul_of_nonneg_left (le_of_not_ge h) hb.le]
  have hs := Finset.sum_le_sum (s := S) (fun m _ => hpoint m)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_filter] at hs
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm (S.card:ℝ),
    mul_comm (↑(S.filter (fun m => a ≤ f m)).card:ℝ)] using hs

theorem central_count_of_normalized_moments (S : Finset ℕ) (f : ℕ → ℝ) (H : ℕ)
    (hcard : S.card ≤ H) (hfirst : (H:ℝ)/144 ≤ ∑ m ∈ S, f m)
    (hsecond : ∑ m ∈ S, (f m)^2 ≤ 1025*H) :
    (H:ℝ) ≤ 85017600 * ((S.filter (fun m => (1:ℝ)/288 ≤ f m)).card:ℝ) := by
  have hs := count_above_threshold_of_moments S f (1/288) 590400 (by norm_num) (by norm_num)
  have hc : (S.card:ℝ) ≤ H := by exact_mod_cast hcard
  linarith only [hs,hfirst,hsecond,hc]

/-- At unit width the variance hypothesis is already impossible on the
indices t+1 divisible by four. -/
theorem unit_window_variance_obstruction (N : ℕ) (hN : 3 ≤ N) :
    ((N+1:ℕ):ℝ)/12 < ∑ t ∈ Finset.range (N+1), (weight (t+1)-1)^2 := by
  let K := (N+1)/4
  have hsize : N+1 < 12*K := by dsimp [K]; omega
  have hcount : (K:ℝ) ≤ ∑ t ∈ Finset.range (N+1), (weight (t+1)-1)^2 := by
    calc
      _ = ∑ _j ∈ Finset.range K, (1:ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_injOn (fun j => 4*j+3)
        · intro a _ b _ e
          dsimp at e
          omega
        · intro t ht
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
          have hi := Finset.mem_range.mp hj
          dsimp [K] at hi
          exact Finset.mem_range.mpr (by omega)
        · intro j _
          have np : ¬ (4*j+3+1).Prime := by
            intro hp
            have hd : 2 ∣ 4*j+3+1 := ⟨2*j+2, by omega⟩
            have he := (Nat.dvd_prime hp).mp hd
            omega
          simp [weight, np]
        · exact fun t _ _ => sq_nonneg _
  have hcast : ((N+1:ℕ):ℝ) < 12 * (K:ℝ) := by exact_mod_cast hsize
  linarith

/-!
A short-interval consequence for genuine primes (analytic derivation).
The finite lemmas above prove the additive-window and moment steps.
The following proportional-window estimate and sieve bound are invoked
from papers and are not formalized in this file.

Let X be a sufficiently large integer, H=ceil(40000 log² X), delta=H/X
and I=[X/3,2X/3]. Write W(t)=theta((1+delta)t)-theta(t).
Theorem 1 of Cully-Hugill and Dudek under RH gives
  integral_{1..Y} |W(t)-delta*t|² dt < 202 delta Y² log² Y
for Y>=10^8 and 0<delta<=10^(-8). Set Y=2X/3. On I, if W(t)<H/6
then |W(t)-delta*t|>=H/6. By reflection t -> X-t, the measure where
at least one of the two window sums is <H/6 is at most
6464 X log² X/H <= X/6. Therefore integral_I W(t)W(X-t) dt >= XH²/216.
For each contributing ordered pair (p,q), X<p+q<=(1+delta)X.
Its set of t has length at most 2H/3, since p/(1+delta)<=t<p and
p<=(1+delta)*2X/3. For large X both primes lie in [m/4,3m/4] for
m=p+q; in fact they lie between X/3 and (1+delta)*2X/3.
Write R_c(m) for this central, ordered log-weighted representation sum.
It follows that sum_{X<m<=X+H} R_c(m) >= XH/144. All contributing m
are even.

For even m define S(m)=2*C2*prod_{p|m,p>2} (p-1)/(p-2) with the usual
twin-prime constant C2. By Theorem 1.2 of Lichtman, corr(m)<=4m S(m)
for large m, hence R_c(m)<=5X S(m). Put b(p)=((p-1)/(p-2))²-1.
The squarefree divisor expansion and the count <=H/d+1 per divisor
show sum_{even m in (X,X+H]} S(m)² <=
  4*C2²*(H*prod_{p>2}(1+b(p)/p)+prod_{2<p<=2X}(1+b(p))).
The first product is at most exp(9/4)<10 since b(p)<=3/(p-2).
The second, after multiplication by 4*C2², is at most
prod_{p<=2X}(1-1/p)^(-2) <= 4 log²(2X) for large X by Mertens.
Thus the local second moment of R_c is <=1025 X² H.
Apply central_count_of_normalized_moments to f=R_c/X on the even m.
At least H/85017600 even m satisfy R_c(m)>=X/288>=m/300 for large X.
The analytic argument controls a set of m in each short interval.
The frozen quantifier requires each prescribed even integer.

RH input audit: https://math.mit.edu/~drew/grh/ .
Short-window estimate: https://arxiv.org/pdf/2206.00433 .
Goldbach sieve bound: https://arxiv.org/pdf/2309.08522 .
Goldston's short-interval moment method: https://doi.org/10.1017/S001708950000937X .
-/

open Finset in
theorem corr_eq_units_add_diagonal (n : ℕ) (hn : 2 ≤ n) :
    corr n = (∑ t ∈ (range n).filter (fun t => Nat.Coprime t n), weight t * weight (n-t)) +
      (if Even n ∧ (n/2).Prime then (Real.log ((n/2 : ℕ) : ℝ))^2 else 0) := by
  classical
  let w (t : ℕ) := weight t * weight (n-t)
  let S := (range n).filter (fun t => ¬ Nat.Coprime t n)
  have diag {t : ℕ} (ht : t ∈ S) (hw : w t ≠ 0) :
      (Even n ∧ (n/2).Prime) ∧ t = n/2 := by
    obtain ⟨htr, hc⟩ := mem_filter.mp ht
    have hlt := mem_range.mp htr
    by_cases hp : t.Prime
    · by_cases hq : (n-t).Prime
      · have hd := (hp.dvd_iff_not_coprime).mpr hc
        have he := (hq.dvd_iff_eq hp.ne_one).mp (Nat.dvd_sub hd (dvd_refl _))
        have ht' : t = n/2 := by omega
        exact ⟨⟨⟨t, by omega⟩, ht' ▸ hp⟩, ht'⟩
      · simp [w, weight, hq] at hw
    · simp [w, weight, hp] at hw
  have hS : ∑ t ∈ S, w t =
      if Even n ∧ (n/2).Prime then (Real.log ((n/2 : ℕ) : ℝ))^2 else 0 := by
    by_cases h : Even n ∧ (n/2).Prime
    · rw [ite_eq_left h]
      obtain ⟨⟨k, hk⟩, hp⟩ := h
      have hd : n/2 ∣ n := ⟨2, by omega⟩
      have ht : n/2 ∈ S :=
        mem_filter.mpr ⟨mem_range.mpr (by omega), hp.dvd_iff_not_coprime.mp hd⟩
      rw [sum_eq_single_of_mem (n/2) ht (fun t ht hne => by
        by_contra hw
        exact hne (diag ht hw).2)]
      simp [w, weight, hp, show n-n/2=n/2 by omega, pow_two]
    · rw [ite_eq_right h]
      exact sum_eq_zero fun t ht => by
        by_contra hw
        exact h (diag ht hw).1
  calc
    corr n = ∑ t ∈ range n, w t := by simp [corr, sum_range_succ, w, weight]
    _ = (∑ t ∈ (range n).filter (fun t => Nat.Coprime t n), w t) + ∑ t ∈ S, w t :=
      (sum_filter_add_sum_filter_not (range n) (fun t => Nat.Coprime t n) w).symm
    _ = _ := by rw [hS]

private theorem units_reflection_sum (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (∑ u : (ZMod n)ˣ, weight (u : ZMod n).val * weight ((-u : (ZMod n)ˣ) : ZMod n).val) =
      ∑ t ∈ (Finset.range n).filter (fun t => Nat.Coprime t n), weight t * weight (n-t) := by
  classical
  have : Fact (1 < n) := ⟨by omega⟩
  apply Finset.sum_nbij (fun u : (ZMod n)ˣ => (u : ZMod n).val)
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective n hab)
  · intro t ht
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp ht
    refine ⟨ZMod.unitOfCoprime t hc, Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro u _
    have : NeZero (u : ZMod n) := ⟨Units.ne_zero u⟩
    rw [Units.val_neg, ZMod.val_neg_of_ne_zero]

/-- Multiplicative character orthogonality at the target modulus selects
opposite residues. -/
theorem fixed_modulus_unit_reflection (n : ℕ) [NeZero n] (F : (ZMod n)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ n, χ (-1) *
      (∑ a : (ZMod n)ˣ, F a * χ ((a : ZMod n)⁻¹)) *
      (∑ b : (ZMod n)ˣ, F b * χ (b : ZMod n))) =
      (n.totient : ℂ) * ∑ a : (ZMod n)ˣ, F a * F (-a) := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩, rootsOfUnity.isCyclic ..⟩
  let ε := fun χ : DirichletCharacter ℂ n => χ (-1)
  let L := fun (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) => χ ((a : ZMod n)⁻¹)
  let R := fun (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) => χ (a : ZMod n)
  have h (a b : (ZMod n)ˣ) :
      (∑ χ : DirichletCharacter ℂ n, ε χ * L χ a * R χ b) =
        if b = -a then (n.totient : ℂ) else 0 := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * χ (-(b : ZMod n)) := by
        apply Finset.sum_congr rfl
        intro χ _
        dsimp only [ε,L,R]
        rw [show -(b : ZMod n) = (-1)*(b : ZMod n) by ring, map_mul]
        ring
      _ = _ := by
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
        congr 1
        apply propext
        constructor
        · intro h
          apply Units.ext
          change (b : ZMod n) = -(a : ZMod n)
          rw [h,neg_neg]
        · rintro rfl
          simp
  change (∑ χ : DirichletCharacter ℂ n, ε χ * (∑ a, F a * L χ a) * (∑ b, F b * R χ b)) = _
  calc
    _ = ∑ χ : DirichletCharacter ℂ n, ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, (F a*F b)*(ε χ*L χ a*R χ b) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum (f := fun a => F a * L χ a), Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, (F a*F b)*(∑ χ : DirichletCharacter ℂ n, ε χ*L χ a*R χ b) := by
      rw [Finset.sum_comm (s := (Finset.univ : Finset (DirichletCharacter ℂ n)))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm (s := (Finset.univ : Finset (DirichletCharacter ℂ n)))]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [h]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      simp [mul_ite, mul_comm (n.totient : ℂ)]

noncomputable def primeUnitTransform (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ u : (ZMod n)ˣ, (weight (u : ZMod n).val : ℂ) * χ (u : ZMod n)

private theorem primeUnitTransform_inverse (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) :
    (∑ u : (ZMod n)ˣ, (weight (u : ZMod n).val : ℂ) * χ ((u : ZMod n)⁻¹)) =
      star (primeUnitTransform n χ) := by
  rw [primeUnitTransform, star_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hχ : star (χ (u : ZMod n)) = χ ((u : ZMod n)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  rw [star_mul, hχ]
  simp [mul_comm]

private theorem primeUnitTransform_energy (n : ℕ) [NeZero n] :
    (∑ χ : DirichletCharacter ℂ n, χ (-1) * (Complex.normSq (primeUnitTransform n χ) : ℂ)) =
      (n.totient : ℂ) * ∑ u : (ZMod n)ˣ, (weight (u : ZMod n).val : ℂ) *
          (weight ((-u : (ZMod n)ˣ) : ZMod n).val : ℂ) := by
  rw [← fixed_modulus_unit_reflection n (fun u => (weight (u : ZMod n).val : ℂ))]
  apply Finset.sum_congr rfl
  intro χ _
  rw [primeUnitTransform_inverse, mul_assoc]
  exact congrArg (fun x : ℂ => χ (-1)*x)
    (Complex.normSq_eq_conj_mul_self (z := primeUnitTransform n χ))

/-- The signed character energy at modulus n is precisely the original
correlation after removing its possible nonunit diagonal. -/
theorem prime_character_energy_at_target (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (∑ χ : DirichletCharacter ℂ n, χ (-1) * (Complex.normSq (primeUnitTransform n χ) : ℂ)) =
      (n.totient : ℂ) * ((corr n -
        (if Even n ∧ (n/2).Prime then (Real.log ((n/2 : ℕ) : ℝ))^2 else 0) : ℝ) : ℂ) := by
  rw [primeUnitTransform_energy, corr_eq_units_add_diagonal n hn, add_sub_cancel_right,
    ← units_reflection_sum n hn]
  push_cast
  rfl

noncomputable def primeUnitMass (n : ℕ) [NeZero n] : ℝ :=
  ∑ u : (ZMod n)ˣ, weight (u : ZMod n).val

open Classical in
theorem nonprincipal_energy_at_target (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ n)).erase 1,
      χ (-1) * (Complex.normSq (primeUnitTransform n χ) : ℂ)) =
      (n.totient : ℂ) * ((corr n -
        (if Even n ∧ (n/2).Prime then (Real.log ((n/2 : ℕ) : ℝ))^2 else 0) : ℝ) : ℂ) -
        (primeUnitMass n : ℂ)^2 := by
  classical
  have hmass : primeUnitTransform n 1 = (primeUnitMass n : ℂ) := by
    simp [primeUnitTransform, primeUnitMass, MulChar.one_apply_coe]
  let f (χ : DirichletCharacter ℂ n) := χ (-1) * (Complex.normSq (primeUnitTransform n χ) : ℂ)
  have hp : f 1 = (primeUnitMass n : ℂ)^2 := by
    dsimp only [f]
    rw [hmass, MulChar.one_apply (isUnit_one.neg), one_mul, Complex.normSq_eq_conj_mul_self]
    simp [pow_two]
  change (∑ χ ∈ Finset.univ.erase 1, f χ) = _
  apply eq_sub_of_add_eq
  rw [← hp, Finset.sum_erase_add _ _ (Finset.mem_univ _)]
  exact prime_character_energy_at_target n hn

/-!
Consequences of the fixed-modulus identity (analytic arguments on paper).
Write T(n)=sum_{p<n,(p,n)=1} log p and D(n) for the diagonal in
nonprincipal_energy_at_target. The nonprincipal signed energy divided by
phi(n) is E(n)=corr(n)-D(n)-T(n)^2/phi(n). The sign is chi(-1), i.e.
+1 for an even character and -1 for an odd one.

1. No constant C gives E(n)>=-Cn for all sufficiently large even n.
Fix a squarefree even M with 3 not dividing M. In the class n=0 mod M,
n=1 mod 3, the number of ordered pairs of units mod 3M summing to this
class is phi(M). Modulo 3 both units have to be 2, and modulo M they
are u and -u. By the fixed-modulus prime number theorem in each class
and integration over the triangle p+q<=X,
  sum_{n<=X in this class} corr(n) ~ X^2/(8 phi(M)).
The sum of n in the class is asymptotic to X^2/(6M). Thus the weighted
average of corr(n)/n tends to (3/4)*M/phi(M), while the principal term
T(n)^2/(n phi(n)) is at least (1-o(1))*M/phi(M), since T(n)=n+o(n)
by PNT and the primes dividing n cost at most log n. For each fixed
c<1/4 there are arbitrarily large n with E(n)<=-c*(M/phi(M))*n.
Taking fixed products of primes other than 3 makes M/phi(M) unbounded.

2. A positive result on prime multiples. Fix an even M>=2 and let
  S_M=(M/phi(M))*prod_{l prime, l does not divide M}(1-1/(l-1)^2).
For each fixed epsilon>0, all except o(X/log X) of the primes r in
(X,2X] satisfy |corr(Mr)/(Mr)-S_M|<epsilon. In particular for M=2
the limit in prime density is twice the twin-prime constant.

For the first and second moments, use the systems of linear forms
  (r,p,Mr-p),  (r,p,Mr-p,q,Mr-q)
with X<r<=2X and 0<p,q<Mr. Both are pairwise linearly independent
in the sense that no pair is proportional, and the codimensions of
their images are 1 and 2 respectively. Thus Corollary 1.7 of Green
and Tao applies unconditionally. They give the asymptotics for the
von Mangoldt weights. Replacing those weights by prime-only weights
costs o(X^d) for each fixed system in d variables: for each form the
O_M(sqrt(X) log X) higher prime-power values have O_M(X^(d-1))
points per fiber, and each product of weights is O_M(log^5 X).
Normalize by (Mr)^(-k), k=1,2, by subdividing r/X in [1,2] into
fixed subintervals and passing to Riemann sums. The remaining volume
is X in both moments. At a prime l dividing M the local factor is
(l/(l-1))^k. At l not dividing M, the class of r is nonzero and each
free coordinate p (and q) must avoid 0 and Mr mod l, giving
(1-1/(l-1)^2)^k. Thus
  sum_{X<r<=2X, r prime} log(r)*(corr(Mr)/(Mr)-S_M)^2 = o_M(X).
This proves the prime-density assertion. Fixing r before applying
the linear forms theorem makes p and Mr-p affinely dependent.
Source: https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf .

3. Location of the nonprincipal contribution under Dirichlet GRH.
Let f be the primitive conductor of a uniformly random chi mod n.
Write L=log log n, s=1/L (n large). For p^v exactly dividing n put
D_p=v-v_p(f). The D_p are independent. For 1<=j<=v the probability
of D_p>=j is phi(p^(v-j))/phi(p^v)<=2 p^(-j). Consequently
  E[p^(s D_p)] <= 1 + 2(p^s-1)/(p*(1-p^(s-1))).
For p<=log n sum the logs using p^s-1 <= e*s*log p and the Mertens
bound sum_{p<=log n} log(p)/p=O(L). Above log n there are at most
(log n)/L prime divisors and p^(s-1)<=e/log n. The product of the
moments is bounded uniformly. Markov's inequality gives
  Prob(n/f > exp(6L^2)) = O((log n)^(-6)).
For every nonprincipal character GRH gives
|primeUnitTransform n chi|=O(sqrt(n)*log^2 n), uniformly, by the
explicit formula for the inducing primitive character and subtraction
of higher prime powers and prime divisors of n. Thus even the absolute
energy of these low-conductor nonprincipal characters, divided by
phi(n), is O(n/log^2 n). In particular the unbounded negative values
in part 1 persist after deleting that entire subset.

The principal term together with the high-conductor signed energy is
the remaining pointwise lower-bound problem. The AP and moment averages
above retain possible individual exceptional inputs.
-/

section RoughPairs
open Finset

/-- Integers at least two whose least prime factor exceeds z. -/
def roughAt (z t : ℕ) : Prop := 2 ≤ t ∧ z < t.minFac

instance (z t : ℕ) : Decidable (roughAt z t) :=
  inferInstanceAs (Decidable (2 ≤ t ∧ z < t.minFac))

theorem rough_composite_lower {z t : ℕ} (h : roughAt z t) (hc : ¬t.Prime) :
    (z + 1)^2 ≤ t :=
  (Nat.pow_le_pow_left h.2 2).trans (Nat.minFac_sq_le_self (by have := h.1; omega) hc)

theorem rough_pair_prime {n z t : ℕ} (hn : n < 2 * (z+1)^2) (ht : t ≤ n)
    (h₁ : roughAt z t) (h₂ : roughAt z (n-t)) : t.Prime ∨ (n-t).Prime := by
  by_contra! h
  have ha := rough_composite_lower h₁ h.1
  have hb := rough_composite_lower h₂ h.2
  omega

def roughPairs (n z : ℕ) : Finset ℕ :=
  (range (n+1)).filter (fun t => roughAt z t ∧ roughAt z (n-t))

theorem rough_pair_count (n z : ℕ) (hn : n < 2 * (z+1)^2) :
    (roughPairs n z).card =
      (((roughPairs n z).filter Nat.Prime).filter (fun t => (n-t).Prime)).card +
        2 * (((roughPairs n z).filter Nat.Prime).filter (fun t => ¬(n-t).Prime)).card := by
  let S := roughPairs n z
  let A := S.filter Nat.Prime
  let B := S.filter (fun t => ¬t.Prime)
  let C := A.filter (fun t => ¬(n-t).Prime)
  have memS {t : ℕ} : t ∈ S ↔ t ≤ n ∧ roughAt z t ∧ roughAt z (n-t) := by
    simp only [S, roughPairs, Finset.mem_filter, Finset.mem_range_succ_iff]
  have flip {t : ℕ} (ht : t ∈ S) : n-t ∈ S := by
    obtain ⟨hle, h₁, h₂⟩ := memS.mp ht
    exact memS.mpr ⟨Nat.sub_le _ _, h₂, (Nat.sub_sub_self hle).symm ▸ h₁⟩
  have hBC : B.card = C.card := by
    apply Finset.card_bij (fun t _ => n-t)
    · intro t ht
      obtain ⟨hs, hc⟩ := Finset.mem_filter.mp ht
      obtain ⟨hle, h₁, h₂⟩ := memS.mp hs
      have hp := (rough_pair_prime hn hle h₁ h₂).resolve_left hc
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨flip hs, hp⟩, (Nat.sub_sub_self hle).symm ▸ hc⟩
    · intro t ht u hu he
      have ht' := (memS.mp (mem_filter.mp ht).1).1
      have hu' := (memS.mp (mem_filter.mp hu).1).1
      omega
    · intro u hu
      obtain ⟨ha, hc⟩ := mem_filter.mp hu
      obtain ⟨hs, _⟩ := mem_filter.mp ha
      exact ⟨n-u, mem_filter.mpr ⟨flip hs, hc⟩, Nat.sub_sub_self (memS.mp hs).1⟩
  have h₁ : A.card + B.card = S.card := card_filter_add_card_filter_not _
  have h₂ : (A.filter (fun t => (n-t).Prime)).card + C.card = A.card :=
    card_filter_add_card_filter_not _
  change S.card = (A.filter (fun t => (n-t).Prime)).card + 2*C.card
  omega

/-- Scalar inequality for comparing the sum of two linear-sieve lower
coefficients with the actual average count of pairs of rough integers. -/
theorem two_sieve_bounds_le_product {h k b d : ℝ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hb : b ≤ h) (hb' : b ≤ 2*(h-1)) (hd : d ≤ k) (hd' : d ≤ 2*(k-1)) :
    b+d ≤ h*k := by
  by_cases h₂ : h ≤ 2
  · by_cases k₂ : k ≤ 2
    · nlinarith only [hb', hd', mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr k₂)]
    · nlinarith only [hb', hd, mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (le_of_not_ge k₂))]
  · by_cases k₂ : k ≤ 2
    · nlinarith only [hb, hd', mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr (le_of_not_ge h₂))]
    · have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h₂)) (sub_nonneg.mpr hk)
      nlinarith only [hprod, hb, hd, le_of_not_ge k₂]

end RoughPairs

/-!
Pointwise comparison with a square-root sieve. The finite splitting and
the scalar inequality above are kernel-checked. The analytic estimates
in this comment are on paper.

Let z=floor(3 sqrt(n)/4), A=(roughPairs n z).card, and r=(reps n).card.
For all large even n,
  |A-r| << n log log n / log^3 n,  and  corr(n)=A log² n + o(n).
Indeed 2(z+1)^2>n and (z+1)^3>n. Each rough composite up to n is a
product l*b of two primes with z<l<=sqrt(n), l<=b<=n/l. Two such
composites cannot sum to n. The theorem rough_pair_count therefore
leaves only mixed representations p+l*b=n. For l dividing n a prime
p must equal l, giving at most one b per l. For each remaining fixed
prime l, the dimension-two upper-bound sieve for b and n-l*b gives
  << (n/l)/log²(n/l) * prod_{q|n*l,q>2}(q-1)/(q-2).
This estimate is uniform here: each sieving prime q not dividing n*l
forbids two residue classes of b, and those dividing n*l forbid one.
For a squarefree d the total counting error in an interval of length
at most n/l is at most 2^omega(d). Taking level (n/l)^(1/2) and
sieving primes up to (n/l)^(1/100) absorbs these remainders. A prime
value n-l*b below this cutoff costs at most one extra b for each l.
The product above is O(log log n) by Mertens (split at log² n).
The number of available l is O(sqrt(n)/log n), and n/l is comparable
to sqrt(n). Thus the mixed representations contribute
O(n log log n/log³ n). At most 2*pi(z) true ordered prime pairs have
an entry <=z. This proves the unweighted estimate without GRH.

The same two-linear-form sieve gives r << n log log n/log² n.
Discarding entries below n/log^4 n costs O(n/log² n) in weighted mass.
On the remaining pairs the log weights differ from log² n by at most
O(log n log log n), proving the weighted estimate, uniformly in n.
With u(t)=L_z on z-rough t>=2 and zero elsewhere,
L_z=prod_{q<=z}(1-1/q)^(-1)=a log n+O(1), a=exp(gamma)/2, by PNT.
The same splitting gives (w*u)(n)=a*corr(n)+o(n) and
(u*u)(n)=a²*corr(n)+o(n). In particular
  ((w-u)*(w-u))(n)=(1-a)^2*corr(n)+o(n) >= -o(n).
Here * denotes additive convolution. At this cutoff a positive linear
lower bound for the wheel main term would itself imply the frozen goal.

Why two ordinary linear-sieve lower bounds do not supply the missing
inequality. In (X,2X] use fixed exponents 0<1/s,1/t<1 for the two
roughness cutoffs and normalize sums by sum_{X<n<=2X} n/log² n over
all integers. Let H(s)=s*omega_B(s) for Buchstab's function omega_B.
The true average coefficient of rough/rough pairs is H(s)H(t) by the
one-dimensional rough-number asymptotic and Riemann summation over
X<x+y<=2X. The factors describe separate variables inside this summed
domain. Even with hypothetical level of distribution one, the usual
one-sided linear-sieve lower coefficients for the two prime/rough
counts are g(s) and g(t), where g(s)=s*f(s)/exp(gamma). Their common
arithmetic factor averages to one on the all-integer normalization:
the binary singular series vanishes on odds and averages to two on
evens by its absolutely convergent mean Euler product. For smaller
levels the guaranteed coefficients do not increase.
For the standard linear-sieve functions F,f,
  F+f=2 exp(gamma)*omega_B,  F>=f,  sF(s)>=2 exp(gamma).
Consequently g(s)<=H(s) and g(s)<=2(H(s)-1); likewise for t.
The theorem two_sieve_bounds_le_product proves g(s)+g(t)<=H(s)H(t).
Thus inserting these lower estimates into inclusion-exclusion
  prime/prime >= prime/rough + rough/prime - rough/rough
does not yield a positive average margin, even with the exact last
term. The argument concerns those lower estimates at fixed scales.
It gives no upper bound for the actual prime/prime correlation.
See https://doi.org/10.2140/ant.2025.19.1 and
https://www.impan.pl/shop/publication/transaction/download/product/81935 .
-/

section CompositeContributions
open Finset

/-- Reflection shows that the two mixed classes have equal cardinality.
This identity retains the composite-composite term for every cutoff. -/
theorem rough_pair_count_all (n z : ℕ) :
    (((roughPairs n z).filter Nat.Prime).filter (fun t => (n-t).Prime)).card +
        (roughPairs n z).card =
      2 * ((roughPairs n z).filter Nat.Prime).card +
        (((roughPairs n z).filter (fun t => ¬ t.Prime)).filter (fun t => ¬ (n-t).Prime)).card := by
  let S := roughPairs n z
  let P := S.filter Nat.Prime
  let K := S.filter (fun t => ¬ t.Prime)
  let PC := P.filter (fun t => ¬(n-t).Prime)
  let CP := K.filter (fun t => (n-t).Prime)
  have memS {t : ℕ} : t ∈ S ↔ t ≤ n ∧ roughAt z t ∧ roughAt z (n-t) := by
    simp only [S, roughPairs, Finset.mem_filter, Finset.mem_range_succ_iff]
  have flip {t : ℕ} (ht : t ∈ S) : n-t ∈ S := by
    obtain ⟨hle, h₁, h₂⟩ := memS.mp ht
    exact memS.mpr ⟨Nat.sub_le _ _, h₂, (Nat.sub_sub_self hle).symm ▸ h₁⟩
  have hPC : PC.card = CP.card := by
    apply Finset.card_bij (fun t _ => n-t)
    · intro t ht
      obtain ⟨hP, hc⟩ := Finset.mem_filter.mp ht
      obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hP
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨flip hs, hc⟩,
        (Nat.sub_sub_self (memS.mp hs).1).symm ▸ hp⟩
    · intro t ht u hu he
      have getle {v : ℕ} (hv : v ∈ PC) : v ≤ n :=
        (memS.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).1
      have := getle ht
      have := getle hu
      omega
    · intro u hu
      obtain ⟨hK, hp⟩ := Finset.mem_filter.mp hu
      obtain ⟨hs, hc⟩ := Finset.mem_filter.mp hK
      have he := Nat.sub_sub_self (memS.mp hs).1
      exact ⟨n-u, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨flip hs, hp⟩, he.symm ▸ hc⟩, he⟩
  have h₁ : P.card + K.card = S.card := Finset.card_filter_add_card_filter_not _
  have h₂ : (P.filter (fun t => (n-t).Prime)).card + PC.card = P.card :=
    Finset.card_filter_add_card_filter_not _
  have h₃ : CP.card + (K.filter (fun t => ¬ (n-t).Prime)).card = K.card :=
    Finset.card_filter_add_card_filter_not _
  change (P.filter (fun t => (n-t).Prime)).card + S.card =
    2*P.card + (K.filter (fun t => ¬ (n-t).Prime)).card
  omega

theorem rough_pair_count_lower {n z : ℕ} {W : Finset ℕ}
    (hW : W ⊆ (((roughPairs n z).filter (fun t => ¬ t.Prime)).filter (fun t => ¬ (n-t).Prime))) :
    2 * ((roughPairs n z).filter Nat.Prime).card + W.card ≤
      (((roughPairs n z).filter Nat.Prime).filter (fun t => (n-t).Prime)).card +
        (roughPairs n z).card := by
  rw [rough_pair_count_all]
  exact Nat.add_le_add_left (Finset.card_le_card hW) _

def largePrimeFactors (z t : ℕ) : Finset ℕ :=
  t.primeFactors.filter (fun p => z < p)

theorem largePrimeFactors_card_le_seven {n z t : ℕ} (hn : n < (z+1)^8) (ht : t ≤ n) :
    (largePrimeFactors z t).card ≤ 7 := by
  by_cases hzero : t = 0
  · simp [hzero, largePrimeFactors]
  have hpow := Finset.pow_card_le_prod (largePrimeFactors z t) id (z+1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hdvd := Finset.prod_dvd_prod_of_subset (largePrimeFactors z t) t.primeFactors id
    (Finset.filter_subset _ _)
  have hsize := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) (hdvd.trans (Nat.prod_primeFactors_dvd t))
  by_contra! h
  have he := Nat.pow_le_pow_right (Nat.succ_pos z) (show 8 ≤ (largePrimeFactors z t).card by omega)
  exact (not_lt_of_ge (he.trans (hpow.trans (hsize.trans ht)))) hn

theorem largePrimeFactorPairs_card_le {n z t : ℕ} (hn : n < (z+1)^8) (ht : t ≤ n) :
    ((largePrimeFactors z t) ×ˢ (largePrimeFactors z (n-t))).card ≤ 49 := by
  rw [Finset.card_product]
  exact Nat.mul_le_mul (largePrimeFactors_card_le_seven hn ht)
    (largePrimeFactors_card_le_seven hn (Nat.sub_le _ _))

theorem largePrimeFactorPairs_sum_le {n z : ℕ} (hn : n < (z+1)^8)
    (W : Finset ℕ) (hW : ∀ t ∈ W, t ≤ n) :
    ∑ t ∈ W, (largePrimeFactors z t).card * (largePrimeFactors z (n-t)).card ≤ 49*W.card := by
  calc
    _ ≤ ∑ _t ∈ W, 49 := Finset.sum_le_sum (fun t ht => by
      simpa only [Finset.card_product] using largePrimeFactorPairs_card_le hn (hW t ht))
    _ = _ := by simp [Nat.mul_comm]

/-- A lower bound on ordered large-prime divisor witnesses contributes
directly to a lower bound on prime pairs, allowing up to 49 witnesses
for each composite pair. -/
theorem rough_pair_count_with_divisor_witnesses (n z : ℕ) (hn : n < (z+1)^8) :
    let bothComposite := ((roughPairs n z).filter (fun t => ¬ t.Prime)).filter
      (fun t => ¬ (n-t).Prime)
    98 * ((roughPairs n z).filter Nat.Prime).card +
        (∑ t ∈ bothComposite, (largePrimeFactors z t).card * (largePrimeFactors z (n-t)).card) ≤
      49 * ((((roughPairs n z).filter Nat.Prime).filter (fun t => (n-t).Prime)).card +
        (roughPairs n z).card) := by
  intro bothComposite
  have hw : ∀ t ∈ bothComposite, t ≤ n := by
    intro t ht
    obtain ⟨ht, _⟩ := mem_filter.mp ht
    obtain ⟨ht, _⟩ := mem_filter.mp ht
    exact Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp ht).1)
  have h := largePrimeFactorPairs_sum_le hn bothComposite hw
  rw [rough_pair_count_all]
  change _ ≤ 49*(2*((roughPairs n z).filter Nat.Prime).card+bothComposite.card)
  omega

/-- Exact local surviving density for the three primality conditions
in a box of the modular hyperbola. -/
theorem hyperbola_sieve_card (p : ℕ) [Fact p.Prime] (h : ZMod p) :
    ((((univ.erase (0 : ZMod p)) ×ˢ (univ.erase (0 : ZMod p))).filter
      (fun x => x.1*x.2 ≠ h))).card =
        if h = 0 then (p-1)^2 else (p-1)*(p-2) := by
  let T := univ.erase (0 : ZMod p)
  have hT : T.card = p-1 := by
    simp [T, Finset.card_erase_of_mem, ZMod.card]
  have hne {u : ZMod p} (hu : u ∈ T) : u ≠ 0 := (Finset.mem_erase.mp hu).1
  have row (u : ZMod p) (hu : u ∈ T) :
      (T.filter (fun v => u*v ≠ h)).card = if h = 0 then p-1 else p-2 := by
    have hunit : IsUnit u := by
      obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective u
      apply (ZMod.isUnit_iff_coprime a p).mpr
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]
      exact hne hu
    have sol (v : ZMod p) : u*v = h ↔ v = u⁻¹*h := by
      constructor
      · intro he
        rw [← he, ← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul]
      · intro he
        rw [he, ← mul_assoc, ZMod.mul_inv_of_unit _ hunit, one_mul]
    have he : T.filter (fun v => u*v ≠ h) = T.erase (u⁻¹*h) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, sol v]
      exact and_comm
    rw [he]
    by_cases hh : h = 0
    · have hz : (0 : ZMod p) ∉ T := fun hz => hne hz rfl
      simp [hh, Finset.erase_eq_of_notMem hz, hT]
    · have hx : u⁻¹*h ≠ 0 := fun hz => hh (by
        simpa only [hz, mul_zero] using ((sol (u⁻¹*h)).mpr rfl).symm)
      have hmem : u⁻¹*h ∈ T := Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
      simp only [hh, ↓reduceIte, Finset.card_erase_of_mem hmem, hT]
      omega
  change ((T ×ˢ T).filter (fun x => x.1*x.2 ≠ h)).card = _
  rw [Finset.card_filter, Finset.sum_product]
  have hsum := Finset.sum_const_nat (fun u hu => row u hu)
  simp_rw [Finset.card_filter] at hsum
  rw [hsum, hT]
  split <;> simp [*, pow_two]

end CompositeContributions

/-!
Positive composite correction at a fixed target (analytic arguments).
Write A for the number of ordered z-rough pairs, P for the number whose
first entry is prime, C for the number with two composite entries, and
G for pairs with two prime entries. Then G=2P-A+C at all cutoffs.
The identity and factor-witness multiplicity above are Lean theorems.
The analytic estimates below invoke the indicated results on paper.

A pointwise lower bound for part of C. For every large even n and
z=floor(n^(1/8)), there are >> S(n)*n/log² n pairs with both entries
in [n/3,2n/3], both squarefree z-rough composites, and the first entry
a product of exactly two primes. S is the binary singular series.
Take distinct primes a,c coprime to n in [n^(13/100),n^(3/20)].
Set m=ab with prime b in [n/(3a),2n/(3a)] and n-m=cv.
Apply a one-dimensional lower sieve to v with b weighted by log b.
For d composed of primes <=z not dividing n, the condition d|v
selects b=n/a mod cd (division means multiplication by the inverse).
The primes <=z dividing n already do not divide v. The density for
each small prime l not dividing n is 1/(l-1). At D=n^(13/50) one has
log D/log z -> 2.08>2. The linear sieve lower function is positive.
Its main term is >> (n/a)*S(n)/(phi(c)*log n). For fixed a the two
endpoints of the b interval are independent of c. All moduli cd are
<=n^.41, below sqrt(n/a)/log^B n for any fixed B and large n.
Each modulus occurs only once in this summation since c is its only
prime factor above z. The sum of the absolute progression errors is
therefore O_J((n/a)/log^J n) by Bombieri-Vinogradov, including the
two endpoints. Summing over a,c leaves a positive constant from each
prime reciprocal sum, namely log((3/20)/(13/100))+o(1). Removing
divisors of n and a=c changes that by o(1). Divide by log n to remove
the weight. Each ordered pair is counted at most 49 times by
largePrimeFactorPairs_sum_le. Either entry divisible by p^2 for some
p>z costs O(n/z+sqrt(n)) pairs, which may be deleted.
The right cofactor v need not be prime.

A check on the missing term. Suppose every pair in C with at least one
prime divisor in (n^(1/8),n^(1/4)] on either side were counted exactly.
The score 2P-A+C_counted equals G minus the number of uncounted
composite pairs, even granting exact P and A. In X<n<=2X, set
Y=(2X)^(1/4). Semiprimes with both prime factors >Y have count
(log 3+o(1))*tX/log X below tX for each fixed t>0. In fact summing
pi(tX/p)-pi(p)+1 for Y<p<=sqrt(tX) gives that coefficient by PNT:
the integral of 1/(v*(1-v)) from 1/4 to 1/2 is log 3, and the
subtracted pi(p) terms contribute O(X/log² X). Pairs of these
semiprimes are uncounted. Riemann summation over X<x+y<=2X gives for
them coefficient (log 3)^2 on the all-integer scale (3/2)*X²/log² X.
The corresponding true ordered prime-pair coefficient is 1.
The surviving pairs have even sum, apart from negligible endpoints
for the primes. Thus this particular score cannot be positive for
every even n; even perfect knowledge of those medium-factor classes
leaves a deficit. The argument also works with the same fixed
central window on both sides of the comparison.

A pointwise upper bound on the previously uncontrolled double
semiprime term near the square-root cutoff. Count prime a,b,r,s>y
such that ab+rs=n. For fixed y=c*sqrt(n), c>0, all four entries are
of size comparable to sqrt(n). To allow varying cutoffs, take a as
a least entry, place r,s in boxes [ia,(i+1)a), [ja,(j+1)a), i,j>=1.
If a does not divide n, rs=n mod a and b=(n-rs)/a.
At a small prime l<a, the sieve for b,r,s forbids rs=0 or n mod l.
There are 3l-2 forbidden residue pairs when l does not divide n,
and 2l-1 when l divides n. In a single class pair mod squarefree d<a,
write r=dR+r0,s=dT+s0. Modulo a these are translated intervals for
the inverse relation, with target n/d² nonzero. Fourier completion
and Weil's Kloosterman bound give a count
(a-1)/d²+O(sqrt(a)*log² a) in each box and fixed class pair.
Changes from rounding interval endpoints are absorbed in that error.
There are at most d*3^omega(d) bad class pairs. Summing over
d<=a^(1/5) with fixed divisor weights costs O(a^(9/10+o(1))).
The dimension-three upper sieve thus bounds prime survivors per box
by O(a*(n/phi(n))/log³ a). Indeed the local surviving fractions
are (1-1/l)(1-2/l) if l does not divide n, and (1-1/l)^2 otherwise;
the sieve can use z'=a^(1/100), with all prime entries exceeding z'.
There are O((n/a²)*(1+log(n/a²))) boxes. Prime a dividing n forces
a=r or s and contributes O(n/a) points. Summing reciprocal primes
by dyadic shells, the ordered four-prime count is at most
  O( (n/phi(n))*n*(1+log(sqrt(n)/y))²/log^4 y + n*log n/(y*log y) )
for large y<=sqrt(n). This bound concerns exactly two prime factors
per side; for y>n^(1/3) those exhaust all rough composite pairs.

For y=sqrt(n)/log^B n (fixed B>0), the latter count is
o(n/log² n). For the mixed class, fix a prime factor l in (y,sqrt(n)]
of the composite side. Apply the two-linear-form upper sieve to
r,n-l*r and sum n/l over prime l in this band. This gives
O_B(S(n)*n*log log n/log³ n); l|n costs O(log n). Together with
the at most 2*pi(y) lost prime pairs, this extends the pointwise
comparison corr(n)=A(n,floor(y))*log² n+o(n) to these cutoffs.
Here a positive lower bound for A(n,floor(y)) at the requested scale
is still needed.

Sources: Kevin Ford, Sieve Methods (linear sieve and sifting notation),
https://ford126.web.illinois.edu/sieve2023.pdf ; Bombieri's progression
theorem, https://doi.org/10.1112/S0025579300005313 ; Weil's exponential
sum estimate, https://pmc.ncbi.nlm.nih.gov/articles/PMC1079093/ ;
modular hyperbolas in translated boxes, formula (10) of
https://arxiv.org/pdf/1103.2879 .
-/

section RoughDivisorRows
open Finset

/-- A rough composite on the left has a canonical divisor row. The two
entries subjected to the row sieve are its cofactor and the original
right summand. -/
theorem rough_composite_row {n z m : ℕ} (hm : m ∈ roughPairs n z) (hc : ¬ m.Prime) :
    ∃ a b : ℕ, a.Prime ∧ z < a ∧ a^2 ≤ n ∧ m = a*b ∧
        roughAt z b ∧ roughAt z (n-a*b) := by
  obtain ⟨hbound, hleft, hright⟩ := Finset.mem_filter.mp hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hbound)
  have htwo := hleft.1
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  obtain ⟨b, hb⟩ := Nat.minFac_dvd m
  have hb₂ : 2 ≤ b := by
    by_contra! h
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with h | h
    · simp [h] at hb
      omega
    · simp [h] at hb
      exact hc (hb.symm ▸ hp)
  have hdiv : b ∣ m := ⟨m.minFac, by simpa [Nat.mul_comm] using hb⟩
  have hfac := Nat.minFac_le_of_dvd (Nat.minFac_prime (show b ≠ 1 by omega)).two_le
    ((Nat.minFac_dvd b).trans hdiv)
  exact ⟨m.minFac, b, hp, hleft.2,
    (Nat.minFac_sq_le_self (by omega) hc).trans hmn, hb, ⟨hb₂, hleft.2.trans_le hfac⟩,
    hb ▸ hright⟩
/-- Prime first summands whose complementary summand survives the sieve. -/
def primeRoughRows (n z : ℕ) : Finset ℕ :=
  (range (n+1)).filter (fun p => p.Prime ∧ roughAt z (n-p))

/-- Raising the cutoff loses only rows indexed by a prime in the new
interval. Using mere divisibility on each row is sufficient for an
upper bound on the loss. -/
theorem primeRoughRows_cutoff_le (n z y : ℕ) :
    (primeRoughRows n z).card ≤ (primeRoughRows n y).card +
      ∑ a ∈ ((Finset.Ioc z y).filter Nat.Prime),
        ((primeRoughRows n z).filter (fun p => a ∣ n-p)).card := by
  let S := primeRoughRows n z
  let U := S.filter (fun p => y < (n-p).minFac)
  let W := S.filter (fun p => ¬y < (n-p).minFac)
  let I := (Finset.Ioc z y).filter Nat.Prime
  have hU : U ⊆ primeRoughRows n y := by
    intro p hp
    obtain ⟨hs, hlarge⟩ := Finset.mem_filter.mp hp
    obtain ⟨hr, hprime, hrough⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hr, hprime, hrough.1, hlarge⟩
  have hm : (W : Set ℕ).MapsTo (fun p => (n-p).minFac) I := by
    intro p hp
    obtain ⟨hs, hsmall⟩ := Finset.mem_filter.mp hp
    have hrough : roughAt z (n-p) := (Finset.mem_filter.mp hs).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hrough.2, le_of_not_gt hsmall⟩,
      Nat.minFac_prime (by have := hrough.1; omega)⟩
  have hW : W.card ≤ ∑ a ∈ I, (S.filter (fun p => a ∣ n-p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hm]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hw, hfac⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, hfac ▸ Nat.minFac_dvd _⟩
  have hsplit : U.card + W.card = S.card := Finset.card_filter_add_card_filter_not _
  exact hsplit ▸ Nat.add_le_add (Finset.card_le_card hU) hW

/-- Multiplicities are counted. In particular, a cutoff whose fourth
power exceeds the target leaves at most three prime factors. -/
theorem rough_factor_count_lt {n z m k : ℕ} (hm : roughAt z m) (hmn : m ≤ n)
    (hk : n < (z+1)^k) : m.primeFactorsList.length < k := by
  have floorProd (l : List ℕ) (h : ∀ p ∈ l, z+1 ≤ p) : (z+1)^l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.length_cons, pow_succ, List.prod_cons, Nat.mul_comm _ (z+1)]
      exact Nat.mul_le_mul (h a (List.mem_cons_self ..))
        (ih (fun p hp => h p (List.mem_cons_of_mem _ hp)))
  have hprod := floorProd m.primeFactorsList (fun p hp => hm.2.trans_le <|
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hp).two_le
      (Nat.dvd_of_mem_primeFactorsList hp))
  rw [Nat.prod_primeFactorsList (by have := hm.1; omega)] at hprod
  by_contra! hle
  exact (not_lt_of_ge ((Nat.pow_le_pow_right (Nat.succ_pos z) hle).trans (hprod.trans hmn))) hk

end RoughDivisorRows

/-!
A positive prime/rough lower bound beyond the one-quarter cutoff (on paper).
Let C_n be the twin-prime constant times the product of (p-1)/(p-2)
over odd primes dividing the even target n. Put L=log n. For every
sufficiently large even n, at least .05 C_n n/L² primes p have
p>n^.252, n-p>=2, and every prime divisor of n-p greater than n^.252.

In J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime
problem, 2, section 3, take sigma equal to the indicator of {1}.
Write Q=n^(1/2-eta), eta fixed sufficiently small and at most .00001.
Equations (3.4)-(3.7) and Table 2 at s=2 give a baseline of at least
(8*.0232385-o(1)) C_n n/L² with n-p sifted to n^l, l=.25-eta/2.
An arbitrarily small fixed slack can be taken in this inequality.
Primes excluded from the sieve basis divide n; their divisibility into
n-p forces p|n. Removing them and n-p<2 costs O(log n) points.
Changing strict cutoff conventions at a prime endpoint costs one row
of size at most n^(1-l)+1, which is negligible here.

The theorem primeRoughRows_cutoff_le above transfers a bound for the
lost rows to the higher cutoff t=.252. For each prime n^l<a<=n^t,
a not dividing n, write n-p=ar and upper-sieve r through w=n^.1.
The prime p belongs to the class n mod a, and adding d|r gives the
single reduced class n mod ad for (d,n)=1. Sieve density at each small
prime ell not dividing n is 1/(ell-1), and the local surviving product
is (2 exp(-gamma)+o(1))*C_n/log w, uniformly in n. The excluded primes
dividing n above w affect the ratio by 1+O(1/w), since there are at
most ten. The uniform linear dimension upper condition follows by
deleting primes from the product. The level D_a=n^.4999/a gives
s=log(D_a)/log w between 2.47 and 2.51, where F(s)=2 exp(gamma)/s.
The upper sieve weights are bounded by one, supported on squarefree d
with primes below w. Every modulus ad<=n^.4999 determines a uniquely,
as a is its only prime factor above w. The sum of absolute progression
errors over all rows is O_A(n/L^A) by Bombieri-Vinogradov.
PNT and partial summation over a now bound the total loss, in units of
C_n n/L², by 4 times the integral from l to t of du/[u(.4999-u)] + o(1).
For l>=.249995 this is <.129. The baseline minus the loss exceeds .05
after deleting p<=n^.252. Omega(n-p), counting multiplicities, is at
most three because (n^.252)^4>n. The exact finite implication is
rough_factor_count_lt. This still leaves the classes with two or three
factors; the estimate supplies no lower bound for the prime subclass.
Source: https://arxiv.org/pdf/0709.3764 , sections 2-3 and Table 2.

Uniform comparison at higher cutoffs (on paper). Take L=log n and
n^delta<=y<=sqrt(n) with delta>0 fixed. Let A,P,C,G have the meanings
in the preceding section, at z=floor(y). The theorem rough_composite_row
assigns a composite to m=ab with y<a<=sqrt(n) prime, and both b and
n-ab surviving the sieve. At each prime ell<=n^min(.01,delta/2), the
two forms in b forbid two classes when ell does not divide n, one
otherwise. These primes are all smaller than a, including if a|n.
The dimension-two upper sieve on b<=n/a at level (n/a)^(.5) costs
O_delta(C_n n/(a L²)) per row: each squarefree modulus gives total
counting error at most 2^omega(d). Reflection and summation over a
bound A-G by O_delta(C_n n/L² * sum_{y<a<=sqrt(n),a prime} 1/a).
Losing genuine prime pairs with an entry <=y costs at most 2*pi(y).
With y=n^(.5-epsilon) and y>=n^delta, the prime reciprocal sum is
O_delta(epsilon+1/L) by partial summation. Since C_n=O(log log n),
A*L² approximates corr(n) with absolute error o(n) uniformly when
epsilon=o(1/log log n). Freezing prime log weights costs o(n)
as in the earlier square-root comparison.

Using both A and P instead improves the allowable cutoff range.
For y>n^(1/3), every double-composite pair contributes to the
four-prime estimate above. In this range the bound simplifies to
  C*L² << C_n*n*(epsilon+1/L)^2 + n*L^3/(y*log y).
By G=2P-A+C, the signed quantity (2P-A)*L² approximates corr(n)
with absolute error o(n) when epsilon=o(1/sqrt(log log n)).
For example epsilon=(log log n)^(-2/3) gives such a comparison.
A lower bound for this signed quantity for every target is still
needed. The uniform positive lower at the exponent .252 does not
directly reach either of these near-square-root ranges.
-/

section BinaryPacketOrders

/-- Two powers of a unit with the same residue recur at a multiple of
its multiplicative order. -/
theorem packet_order_dvd_of_pow_eq {M : Type*} [Monoid M] {x : M}
    (hx : IsUnit x) {j k : ℕ} (h : x ^ j = x ^ k) :
    orderOf x ∣ k - j := by
  obtain ⟨u, rfl⟩ := hx
  have hu : u ^ j = u ^ k := Units.ext (by simpa using h)
  rw [orderOf_units]
  exact (pow_eq_pow_iff_modEq.mp hu).dvd'

theorem packet_two_order_dvd {d j k : ℕ} (hd : Odd d)
    (h : (2 : ZMod d) ^ j = (2 : ZMod d) ^ k) :
    orderOf (2 : ZMod d) ∣ k - j := by
  apply packet_order_dvd_of_pow_eq _ h
  simpa using (ZMod.isUnit_iff_coprime 2 d).2 hd.coprime_two_left

theorem packet_two_order_dvd_of_add {d n j k : ℕ} (hd : Odd d)
    (hj : d ∣ n + 2 ^ j) (hk : d ∣ n + 2 ^ k) :
    orderOf (2 : ZMod d) ∣ k - j := by
  have hz (i : ℕ) (hi : d ∣ n + 2 ^ i) :
      (n : ZMod d) + 2 ^ i = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff _ _).2 hi
  exact packet_two_order_dvd hd (add_left_cancel ((hz j hj).trans (hz k hk).symm))

end BinaryPacketOrders

/-!
Separating three-factor complements at exponent .252. In Wu's normalization
the triple contamination actually exceeds the preceding lower bound on
average. In X<n<=2X count p+(q1*q2*q3)=n with every qi>n^delta,
counting each p once. Dividing the sum over even n by the corresponding
sum of C_n*n/log² n yields the limit
 (1/3) Integral_{u,v>=delta, u+v<=1-delta} du dv/[u*v*(1-u-v)].
Indeed PNT and partial summation give the single-variable density of
unordered three-prime products with the coefficient 1/6 times that
integral. Repeated factors are negligible; replacing n^delta by the
fixed endpoint cutoffs X^delta and (2X)^delta yields the same limit.
Convolution with primes across the triangular dyadic region gives
the same integral coefficient. The mean of C_n over even n is one
by the Euler product, while the prime products and primes are odd.
This contributes the factor of two in the displayed normalization.
At delta=.252 the coefficient is at least 4.5*(1-3*delta)^2=.267912
by AM-GM. Hence subtracting a uniform upper bound for all triples
from the certified .05 lower coefficient cannot suffice.

Signed contribution on extended rational arcs (analytic proof).
The following applies to the prime weights of PR 316 and to the binary
packet in PR 2327, commit 74a5164cc9df0a6e5c3639fdbbcce5b970d8d8d0,
research/change-sets/fixed-budget-binary-packet.json, lines 53 and 161.
For Q=floor(log_2(n+2))^2, M(Q) consists of reduced a/q, q<=Q,
within distance Q/(qn), on the unit circle. Set L=max(1,floor(log_2(n)/2))
and h_j=2^j, 1<=j<=L. The packet is K(t)=average_j cos(2*pi*h_j*t).
The clipped defect is r=(1-K-tau)_+, tau=1/[2304*(1+log² n)].
S is the sum over p<=n, p^3>n, with weights log p. J on a set is
the real integral of r*S(t)^2*exp(-2*pi*i*n*t).

For every large even n, on M(n^.30) minus M(Q) we get J>=-o(n),
uniformly. We can also adjoin all arcs with q<=P=sqrt(n)/log^10 n
and distance <=sqrt(P/q)/n to M(n^.30), with the same conclusion.
Denote this union by U. On all of U, even the unweighted integral of
S(t)^2*exp(-2*pi*i*n*t) equals n times the full binary singular
series plus o(n). The reference input for the polynomial ranges is
GRH for Dirichlet L-functions; the verification of the GRH source
and this analytic use are separate from the Lean declarations here.
For the standard extended M((log n)^B) with any fixed B>2,
Siegel-Walfisz alone suffices for the signed lower bound.

1. Error of the local model. D_n(beta)=sum_{k=0}^n exp(2*pi*i*k*beta)
has D_n(beta)^2*exp(-2*pi*i*n*beta)=|D_n(beta)|² exactly. The model
on a/q+beta is mu(q)*D_n(beta)/phi(q). Dirichlet GRH and the explicit
formula give a uniform O(sqrt(n)*log²(2nq)) error on untwisted
initial character sums after the principal term is removed. Prime
powers, low primes, and the imprimitive Euler factors fit this bound.
Partial summation adds a factor 1+n|beta|. Expansion in characters,
orthogonality over reduced a, and sum_chi |Gauss(chi)|²=phi(q)^2
give sum_{a reduced}|S-model|² << phi(q)*n*log^4(2nq)*(1+n|beta|)^2.
The contributions from non-unit primes cost at most O(log q) per
residue before squaring. For half-width H(q)/n, H(q)>=1, the integrated
squared error is << log^4(2n)*sum_{q} q H(q)^3. Standard H(q)=n^.30/q
(q<=n^.30) gives O(n^.90 log^4 n). The second width H(q)=sqrt(P/q)
gives O(P² log^4 n). The union is bounded by the sum. Arcs at distinct
fractions are disjoint since sH(q)+qH(s)<=2P*n^.30<n. The squared model
has integral O(n log n), by Parseval and sum_{q<=P} mu(q)^2/phi(q)
<< log(2P). Cauchy-Schwarz therefore costs o(n) on taking the difference
of the squared sums even with multiplier bounded by two. Clipping 1-K
costs O(tau*n log n)=o(n). Freezing K at the center costs o(n) since its
derivative is O(sqrt(n)/L), and H(q)<=n^.30. For polylogarithmic P,
ordinary Siegel-Walfisz on initial sums and partial summation replace GRH.

2. Averaging the shifted Ramanujan sums. For squarefree q write
g=gcd(q,m), b=q/g. Then |c_q(m)|/phi(q)^2=1/[phi(g)*phi(b)^2].
For odd d, the j with d|n ± 2^j form at most one class modulo
ord_d(2) for each sign. The finite recurrence is proved above.
For U_T=product_{k<=T}(2^k-1), all squarefree d of order <=T divide
U_T, so their total weight 1/phi(d) is at most U_T/phi(U_T)
<< log(2T). Dyadic summation over the order proves convergence of
sum_{d odd squarefree}1/[phi(d)*ord_d(2)]. Large d have order at least
log_2(d+1) when d>1. The factor 2 in q can be split off.

For m=n or n ± 2^j in [n/2,2n] put Y=exp((log log n)^2) and
alpha=1/log log n. The portion of sum_{g|rad(m)}1/phi(g) with g>Y
is at most Y^(-alpha)*product_{p|m}(1+p^alpha/(p-1))=o(1).
For p<=log n use Mertens and p^alpha<=exp(1). Larger p contribute
O(1) to the logarithm, using # such divisors <=log(2n)/log log n.
For g<=Y, the extra incomplete period costs at most
L^(-1)*sum_{g<=Y}1/phi(g)=O(log Y/L)=o(1). Since sum_b 1/phi(b)^2
converges, splitting q>T into g>sqrt(T) or b>sqrt(T) proves
 average_{j,sign} sum_{q>T} mu(q)^2 |c_q(n ± 2^j)|/phi(q)^2 = o(1)
for T tending to infinity with n, uniformly. The unrestricted average
is O(1). For the center m=n the analogous absolute tail is o(1) when
T=Y², without averaging, by the same Rankin bound; the b>Y part
is negligible even times n/phi(n), since sum_b sqrt(b)/phi(b)^2
converges on squarefree b. On U the normalized Dirichlet-kernel mass
tends to one with negligible total error for q<=Y². This proves the
assertion for the full unweighted integral on U by the Euler product.

3. The central contribution between the two arc cutoffs. We include
the wings at q<=Q. Set F(v)=(1/n) integral_{|beta|<=v/n}|D_n(beta)|².
For outer half-width H(q)/n let W(q) be its normalized mass minus
the original mass 1_{q<=Q} F(Q/q), taking zero beyond the outer cutoff.
For q<=Q, 0<=W(q)<<q/Q by the Dirichlet-kernel tail bound. On
Q<q<=P_outer, W(q) is nonincreasing and bounded below by F(1), which has a positive absolute lower bound.
 It is bounded above by 2
everywhere. These properties hold both for standard extended arcs and
for the union above. In the shifted sum the q<=sqrt(Q) part is thus
O(Q^(-1/2)) and the rest is o(1) by step 2.

For even n, write w(g)=1/phi(g) for g|rad(n), and B(b)=mu(b)/phi(b)^2
for squarefree b coprime to n. Such b are odd. The central signed sum is
sum_g w(g) sum_b B(b) W(gb). For Q<g<=P_outer its inner sum is at least
kappa*W(g), kappa=2-product_{p>2}(1+1/(p-1)^2)>0, since
the logarithm of the product is <=pi²/24. For g<=Q the possible loss
is O(sqrt(g/Q)) by summing sqrt(b)|B(b)|. For any fixed M>1, the
weighted loss from g<=Q/M is O(M^(-1/2)), by dyadic division and
sum_{x<h<=2x}1/phi(h)<<1. The full loss is uniformly bounded.

To see that the central signed sum has liminf >=0, suppose it is
<=-epsilon along a sequence n. Taking M sufficiently large forces
sum_{Q/M<g<=Q,g|rad n} w(g)>=c(epsilon)>0. Denote this mass by m0.
Write log g as the sum of log p for p|g and then g=p h. Chebyshev on
multiplicative intervals gives
 m0*log(Q/M) <= (n/phi(n))*sup_t sum_{t<p<=Mt} log(p)/(p-1)
              <<_M n/phi(n).
Put R=min(log n,P_outer/Q)/2; as P_outer>=(log n)^B for a fixed B>2,
sum_{p|n,p>R}1/p=O_B(1) by Mertens up to log n and counting beyond it.
Consequently sum_{p|n,p<=R}1/(p-1) tends to infinity on this sequence.
For prime band (2^j,2^(j+1)] remove from the g-window the g already
divisible by a prime in that band. Its cost is O_M(1/j), by factoring
out p and using the universal interval bound for sum 1/phi(h).
Thus for large j the retained mass is at least m0/2. Multiply each
retained g by each p|n in this band. Each image has exactly one
band-prime, so it is counted just once in the band. It lies between
2^j*Q/M and 2^(j+1)*Q. Take 2^j>M and 2^(j+1)<=R; all images belong
to (Q,P_outer]. Separate j into finitely many congruence classes so
the image intervals are disjoint within each class (2^k>2M suffices).
The class with largest prime reciprocal sum gives a total image mass
tending to infinity. Its positive contribution dominates the uniformly
bounded loss, a contradiction. This proves the claimed liminf, and
steps 1 and 2 transfer it to the actual clipped integral on U minus M(Q).

The remaining domain outside U and the actual shifted prime-count
term are still required by the frozen target. In particular this
argument does not give the target from PR 316 alone.
Sources: https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2327 ;
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/316 ;
Dirichlet GRH verification https://math.mit.edu/~drew/grh/ .
-/

/-- A loss of n on the complementary arcs still suffices when the
extended-arc model is at least 5n/4 up to an eventual n/8 error. -/
theorem floor_of_extended_arc_budget (major minor singular : ℕ → ℝ)
    (hsplit : ∀ n, corr n = major n + minor n) (N : ℕ)
    (hmodel : ∀ n ≥ N, Even n → singular n * (n : ℝ) - (n : ℝ)/8 ≤ major n)
    (hseries : ∀ n ≥ N, Even n → (5:ℝ)/4 ≤ singular n)
    (hminor : ∀ n ≥ N, Even n → -(n : ℝ) ≤ minor n) :
    ∃ (c : ℝ) (M : ℕ), 0 < c ∧ ∀ X n : ℕ, M ≤ X → X ≤ n → n < 2*X →
      Even n → c * (n : ℝ) ≤ corr n := by
  refine ⟨1/8, N, by norm_num, ?_⟩
  intro X n hX hXn _ he
  have hn := hX.trans hXn
  have hs := mul_le_mul_of_nonneg_right (hseries n hn he) (Nat.cast_nonneg (α := ℝ) n)
  rw [hsplit]
  linarith [hmodel n hn he, hminor n hn he]

/-!
Standard major arcs up to sqrt(n)/log³ n using the mean-square GRH input.
Take P=floor(sqrt(n)/log³ n) and the usual half-width xi=P/(qn) for
every q<=P. The estimates for W, the center and the shifted sum above
then apply without changing the arc shape. Here is the stronger
mean-square input that justifies this choice of P for true prime weights.

For a nonprincipal Dirichlet character chi modulo q, Ikeda and Suriajaya,
Lemma 2.4, (2.18), bound the integrated square of psi(x+h,chi)-psi(x,chi)
over 0<=x<=n by O(n(h+1)log²(3qn/(h+1))) on Dirichlet GRH,
uniformly for 0<=h<=n and including imprimitive characters. For the
principal character use the classical RH Selberg integral for psi(x+h)-
psi(x)-h, together with the omitted powers of primes dividing q
(the prefix discrepancy is O(log(2q)*log(2n))). Let
 G_chi(beta)=sum_{m=1}^n (Lambda(m)*chi(m)-1_{chi principal})e(m*beta).
Gallagher's elementary Fourier inequality applied with h=1/(2xi)
bounds its integral of |G|² on [-xi,xi] by a constant times h^(-2)
times the integral of squared moving interval sums truncated at n.
The complete intervals cost O(n*h*log^4(2nq)), including the unit
rounding error for the principal term. On the two intervals of x within
h of the ends, the GRH prefix bound O(sqrt(n)*log²(2nq)) suffices.
Therefore the integral is O(n*xi*log^4(2nq)). Character orthogonality
and the Gauss-sum norm as above give integrated squared error for one q
of O(phi(q)*n*xi*log^4 n). The missing nonunit prime powers contribute
at most O(log n*log(2q)) pointwise, and the distinction between summing
the geometric kernel from k=0 or 1 is bounded. These errors fit the bound.
The total square error is O(P² log^4 n). For the mixed model/error term,
apply Cauchy-Schwarz at each q against the model mass <=(n+1)/phi(q).
Its total is O(n log² n*sum_{q<=P}sqrt(P/(qn)))=O(P*sqrt(n)*log² n).
Both estimates are o(n). Removing proper prime powers and primes up to
n^(1/3) from the true sum costs o(n) in the bounded-weight square integral
by full-circle Parseval and Cauchy-Schwarz.

Thus the real unweighted prime square integral on M(P) is
singular_series(n)*n+o(n), uniformly in sufficiently large even n,
and the PR 2327 clipped contribution on M(P) minus M(Q) is >=-o(n).
For freezing K one may use its derivative O(sqrt(n)/L) as in the
preceding argument; the cost O(P*sqrt(n)*log P/L) is still o(n).
Outside M(P), Dirichlet approximation with denominator at most ceil(n/P)
gives a reduced a/q with P<q<=ceil(n/P) and |t-a/q|<=P/(qn).
This leaves a signed integral on a specified denominator range; the
complement has measure 1-O(P²/n). It is not controlled by the major-arc
estimate. The full binary singular series is >=2 times the twin-prime
constant, which is >=4/pi>5/4 by the Wallis product over all even
positive integers. A pointwise lower bound -n on this remaining real
integral would therefore suffice for the frozen floor, allowing an
eventual error n/8 on the major arcs; the transfer above is formal.
For the full prime sum rather than the high sum the same estimates hold
by the same low-prime removal bound.
There is also a check on the size of the remaining error. Parseval gives
total absolute square energy (1+o(1))*n*log n. On M(P) the preceding
mean-square estimate replaces S by the model at cost o(n). Since
F(P/q)=(n+1)/n+O(q/P), the model energy is
n*sum_{q<=P} mu(q)^2/phi(q)+O(n)=(1+o(1))*n*log P. Here the
logarithmic mean has coefficient one by the Euler product, and
sum_{q<=P}q/phi(q)=O(P). Hence the complement retains
(1/2+o(1))*n*log n of absolute square energy. Using that absolute
energy alone loses the order of magnitude needed in the signed budget.
Sources: https://arxiv.org/pdf/2405.04315 , Lemma 2.4;
https://math.mit.edu/~drew/grh/ , independently checked Dirichlet GRH.
-/

/-!
Integral of the prime square over standard enlarged rational arcs.

The finite coefficient, its two elementary Fourier helpers, and the two
integration lemmas below are adapted from TranswarpDrive's Goldbach PR #158,
commit d03fe72a521e7e8e5e06447bc0bae3a1d34465d8, distributed under Apache-2.0.
https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/d03fe72a521e7e8e5e06447bc0bae3a1d34465d8/lean/PEqualNP/Outside/L_goldbach_arc_coefficient_sum.lean

The short exponential antiderivative is adapted from mathlib's
Mathlib.Analysis.SpecialFunctions.Integrals.Basic, integral_exp_mul_complex.
Copyright (c) 2021 Benjamin Davidson. Released under the Apache 2.0 license.
https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean#L242
-/

open MeasureTheory

private theorem packetIntegralExp {a b : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  · ring
  · fun_prop

open MeasureTheory

namespace ExtendedArcCoefficient

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [packetIntegralExp hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

lemma coefficient (w : ℕ → ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
      E (-(n : ℝ) * t)) = ((∑ k ∈ Finset.range (n + 1), w k * w (n - k) : ℝ) : ℂ) := by
  let I := Finset.range (n + 1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ I, term k j t) = (w k : ℂ) * (w (n - k) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hsub : n - k ∈ I := Finset.mem_range.mpr (by omega)
    simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
    rw [Finset.sum_eq_single_of_mem (n - k) hsub]
    · simp [show (k : ℤ) + ((n - k : ℕ) : ℤ) - n = 0 by omega]
    · intro j _ hne
      simp [show (k : ℤ) + j - n ≠ 0 by omega]
  change (∫ t in (0 : ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
    E (-(n : ℝ) * t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  push_cast
  exact Finset.sum_congr rfl hrow

/-- Rational neighborhoods of any prescribed cutoff and radius form a measurable set. -/
theorem measurable_rational_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / (q * n)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) by fun_prop).measurable
        measurable_const
    convert hmeas using 1
    ext t
    exact ⟨fun h => h.2.2.2.2, fun h => ⟨h₁, h₂, h₃, h₄, h⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩

/-- Split any interval-integrable complex coefficient at an arbitrary measurable set. -/
theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume = intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]


end ExtendedArcCoefficient

open ExtendedArcCoefficient

def rationalArcSet (P n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (P : ℝ) / ((q : ℝ) * (n : ℝ))}
noncomputable def primeSquareKernel (n : ℕ) (t : ℝ) : ℂ :=
  (∑ k ∈ Finset.range (n+1), (weight k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t)
noncomputable def primeArcMass (s : Set ℝ) (n : ℕ) : ℝ :=
  (intervalIntegral (s.indicator (primeSquareKernel n)) 0 1 volume).re

theorem corr_eq_primeArcMass (n : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    corr n = primeArcMass s n + primeArcMass sᶜ n := by
  have hc : Continuous (primeSquareKernel n) := by unfold primeSquareKernel E; fun_prop
  have h := (indicator_integral_split hs (hc.intervalIntegrable 0 1)).trans (coefficient weight n)
  exact (congrArg Complex.re h).symm

theorem corr_eq_rationalArcMass (P n : ℕ) :
    corr n = primeArcMass (rationalArcSet P n) n + primeArcMass (rationalArcSet P n)ᶜ n :=
  corr_eq_primeArcMass n _ (measurable_rational_arcs P n)
noncomputable def extendedArcCutoff (n : ℕ) : ℕ :=
  ⌊Real.sqrt (n : ℝ) / (Real.log (n : ℝ)) ^ 3⌋₊

theorem floor_of_primeArcMass_budget (P : ℕ → ℕ) (singular : ℕ → ℝ) (N : ℕ)
    (hmodel : ∀ n ≥ N, Even n → singular n * (n : ℝ) - (n : ℝ)/8 ≤
      primeArcMass (rationalArcSet (P n) n) n)
    (hseries : ∀ n ≥ N, Even n → (5:ℝ)/4 ≤ singular n)
    (hminor : ∀ n ≥ N, Even n → -(n : ℝ) ≤ primeArcMass (rationalArcSet (P n) n)ᶜ n) :
    ∃ (c : ℝ) (M : ℕ), 0 < c ∧ ∀ X n : ℕ, M ≤ X → X ≤ n → n < 2*X →
      Even n → c * (n : ℝ) ≤ corr n :=
  floor_of_extended_arc_budget _ _ singular (fun n => corr_eq_rationalArcMass (P n) n)
    N hmodel hseries hminor

section MoebiusFold
open ArithmeticFunction Finset
open scoped ArithmeticFunction

/-- Truncated logarithmic divisor weight with logarithmic cutoff u. -/
noncomputable def truncatedDivisorLog (k : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, (moebius d : ℝ) * max 0 (u - Real.log d)

theorem truncatedDivisorLog_reflect {k : ℕ} (hs : Squarefree k) (hk : k ≠ 1) (u : ℝ) :
    truncatedDivisorLog k u - (moebius k : ℝ) *
      truncatedDivisorLog k (Real.log k - u) = vonMangoldt k := by
  have hzero : (∑ d ∈ k.divisors, (moebius d : ℝ)) = 0 := by
    rw [← Int.cast_sum, ← coe_mul_zeta_apply, moebius_mul_coe_zeta]
    simp [hk]
  have hflip : (moebius k : ℝ) * truncatedDivisorLog k (Real.log k - u) =
      ∑ d ∈ k.divisors, (moebius d : ℝ) * max 0 (Real.log d - u) := by
    unfold truncatedDivisorLog
    rw [← Nat.sum_div_divisors k (fun d => (moebius d : ℝ) *
      max 0 (Real.log k - u - Real.log d)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hmul : d * (k/d) = k := Nat.mul_div_cancel' hdvd
    have hcop := Nat.coprime_of_squarefree_mul (show Squarefree (d*(k/d)) by rw [hmul]; exact hs)
    have hmu := isMultiplicative_moebius.map_mul_of_coprime hcop
    rw [hmul] at hmu
    have hsq := moebius_sq_eq_one_of_squarefree (hs.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd))
    have hunit : (moebius k : ℝ) * (moebius (k/d) : ℝ) = (moebius d : ℝ) := by
      exact_mod_cast (show moebius k * moebius (k/d) = moebius d by
        rw [hmu, mul_assoc, ← pow_two, hsq, mul_one])
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    have hlog : Real.log (k/d : ℕ) = Real.log k - Real.log d := by
      rw [Nat.cast_div hdvd hd0, Real.log_div (Nat.cast_ne_zero.mpr hs.ne_zero) hd0]
    rw [← mul_assoc, hunit, hlog]
    congr 2
    ring
  rw [hflip]
  unfold truncatedDivisorLog
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ d ∈ k.divisors, ((moebius d : ℝ)*u - (moebius d : ℝ)*Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : Real.log d ≤ u
      · rw [max_eq_right (by linarith : 0 ≤ u - Real.log d),
          max_eq_left (by linarith : Real.log d - u ≤ 0)]
        ring
      · rw [max_eq_left (by linarith : u - Real.log d ≤ 0),
          max_eq_right (by linarith : 0 ≤ Real.log d - u)]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, zero_sub]
      simpa only [ArithmeticFunction.log_apply, neg_neg] using
        congrArg Neg.neg (sum_moebius_mul_log_eq (n := k))

theorem truncatedDivisorLog_at_midpoint {k : ℕ} (hs : Squarefree k) (hk : k ≠ 1) :
    (1 - (moebius k : ℝ)) * truncatedDivisorLog k (Real.log k / 2) = vonMangoldt k := by
  have h := truncatedDivisorLog_reflect hs hk (Real.log k / 2)
  rw [show Real.log k - Real.log k/2 = Real.log k/2 by ring] at h
  linarith only [h]

/-- On a squarefree integer the midpoint expression recovers the prime
log weight, including zero on squarefree composites. -/
theorem weight_eq_midpoint_moebius (k : ℕ) :
    weight k = if Squarefree k then
        (1 - (moebius k : ℝ)) * truncatedDivisorLog k (Real.log k / 2)
      else 0 := by
  by_cases hs : Squarefree k
  · rw [ite_eq_left hs]
    by_cases hone : k = 1
    · subst k
      simp [weight]
    rw [truncatedDivisorLog_at_midpoint hs hone]
    by_cases hp : k.Prime
    · simp [weight, hp, vonMangoldt_apply_prime hp]
    · have hpp : ¬ IsPrimePow k := fun h => hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hs, h⟩)
      simp [weight, hp, vonMangoldt_apply, hpp]
  · have hp : ¬ k.Prime := fun h => hs h.squarefree
    simp [weight, hp, hs]

/-- The original two-prime correlation in terms of midpoint divisor sums.
Only pairs for which both Möbius values are minus one survive. -/
theorem corr_eq_midpoint_moebius (n : ℕ) :
    corr n = 4 * ∑ k ∈ (Finset.range (n+1)).filter
        (fun k => moebius k = -1 ∧ moebius (n-k) = -1),
      truncatedDivisorLog k (Real.log k / 2) *
        truncatedDivisorLog (n-k) (Real.log (n-k) / 2) := by
  classical
  have hw (k : ℕ) : weight k =
      if moebius k = -1 then 2 * truncatedDivisorLog k (Real.log k / 2) else 0 := by
    rw [weight_eq_midpoint_moebius]
    by_cases hs : Squarefree k
    · rw [ite_eq_left hs]
      obtain h | h := (moebius_ne_zero_iff_eq_or.mp (moebius_ne_zero_iff_squarefree.mpr hs))
      · simp [h]
      · simp only [h, ite_true, Int.cast_neg, Int.cast_one]
        ring
    · simp [hs, moebius_eq_zero_of_not_squarefree hs]
  unfold corr
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hw k, hw (n-k)]
  split_ifs <;> simp_all
  ring

end MoebiusFold

theorem odd_prime_product_five_eighths {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    (5 : ℝ) / 8 ≤ ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  let f := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2
  let C : Finset ℕ := {4, 6, 8, 9, 10, 12, 14, 15, 16}
  let U := Finset.Ico 3 (P.sup id + 17)
  have hC : ∀ p ∈ C, 3 ≤ p ∧ p ≤ 16 ∧ ¬ p.Prime := by decide
  have hd : Disjoint C P := Finset.disjoint_left.mpr fun _ hp hq =>
    (hC _ hp).2.2 (hP _ hq).1
  have hu : C ∪ P ⊆ U := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := hC p hp
      exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩
    · have hs : p ≤ P.sup id := Finset.le_sup (f := id) hp
      have h := (hP p hp).2
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hc : (∏ p ∈ U, f p) ≤ ∏ p ∈ C ∪ P, f p := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ hu
    · intro p hp
      have hp' : 3 ≤ p := (Finset.mem_Ico.mp hp).1
      have hx : (3 : ℝ) ≤ p := by exact_mod_cast hp'
      have hs : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith [sq_nonneg ((p : ℝ) - 2)]
      exact sub_nonneg.mpr ((div_le_one (by linarith : 0 < ((p : ℝ)-1)^2)).mpr hs)
    · intro p _ _
      exact sub_le_self _ (by positivity)
  have tel (m : ℕ) : (∏ j ∈ Finset.range m, f (3+j)) =
      ((m : ℝ)+2)/(2*((m : ℝ)+1)) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      dsimp [f]
      push_cast
      have h₁ : (m : ℝ)+1 ≠ 0 := by positivity
      have h₂ : (m : ℝ)+2 ≠ 0 := by positivity
      rw [show (3 : ℝ)+m-1 = (m : ℝ)+2 by ring]
      field_simp
      ring
  have hh : (1 : ℝ)/2 ≤ ∏ p ∈ U, f p := by
    dsimp [U]
    rw [Finset.prod_Ico_eq_prod_range, tel]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  rw [Finset.prod_union hd] at hc
  have hCprod : (∏ p ∈ C, f p) = 131072 / 165165 := by
    norm_num [C, f, Finset.prod_insert]
  rw [hCprod] at hc
  change (5 : ℝ) / 8 ≤ ∏ p ∈ P, f p
  linarith only [hh, hc]

noncomputable def truncatedPrimeSingularSeries (n : ℕ) : ℝ :=
  let primes := (Finset.range (n+1)).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  2 * (∏ p ∈ primes.filter (fun p : ℕ => p ∣ n), (1 + 1 / ((p : ℝ)-1))) *
      ∏ p ∈ primes.filter (fun p : ℕ => ¬ p ∣ n), (1 - 1 / ((p : ℝ)-1)^2)

theorem truncatedPrimeSingularSeries_lower (n : ℕ) :
    (5 : ℝ)/4 ≤ truncatedPrimeSingularSeries n := by
  let primes := (Finset.range (n+1)).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  let good := primes.filter (fun p : ℕ => p ∣ n)
  let bad := primes.filter (fun p : ℕ => ¬ p ∣ n)
  have hp {p : ℕ} (h : p ∈ primes) : p.Prime ∧ 2 < p := (Finset.mem_filter.mp h).2
  have hg : (1 : ℝ) ≤ ∏ p ∈ good, (1 + 1 / ((p : ℝ)-1)) := by
    apply Finset.one_le_prod₀
    intro p h
    have hx : (2 : ℝ) < p := by exact_mod_cast (hp (Finset.mem_filter.mp h).1).2
    exact le_add_of_nonneg_right (one_div_nonneg.mpr (by linarith))
  have hb := odd_prime_product_five_eighths (P := bad) fun p h => hp (Finset.mem_filter.mp h).1
  change (5 : ℝ)/4 ≤ 2 * (∏ p ∈ good, (1 + 1 / ((p : ℝ)-1))) *
    ∏ p ∈ bad, (1 - 1 / ((p : ℝ)-1)^2)
  nlinarith only [hg, hb, mul_nonneg (sub_nonneg.mpr hg) (le_trans (by norm_num) hb)]

theorem floor_of_extendedPrimeArcMass_budget (N : ℕ)
    (hmodel : ∀ n ≥ N, Even n → truncatedPrimeSingularSeries n * (n : ℝ) - (n : ℝ)/8 ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n) n)
    (hminor : ∀ n ≥ N, Even n → -(n : ℝ) ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n)ᶜ n) :
    ∃ (c : ℝ) (M : ℕ), 0 < c ∧ ∀ X n : ℕ, M ≤ X → X ≤ n → n < 2*X →
      Even n → c * (n : ℝ) ≤ corr n :=
  floor_of_primeArcMass_budget extendedArcCutoff truncatedPrimeSingularSeries N hmodel
    (fun n _ _ => truncatedPrimeSingularSeries_lower n) hminor

section MidpointSquareDetector
open ArithmeticFunction

noncomputable def logDivisorTransform (g : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, (moebius d : ℝ) * g (u - Real.log d)

theorem logDivisorTransform_prime_mul (g : ℝ → ℝ) {p k : ℕ}
    (hp : p.Prime) (hc : p.Coprime k) (u : ℝ) :
    logDivisorTransform g (p*k) u =
      logDivisorTransform g k u - logDivisorTransform g k (u - Real.log p) := by
  classical
  have hn : ¬p ∣ k := hp.coprime_iff_not_dvd.mp hc
  have hk : k ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have hu : (p*k).divisors = k.divisors ∪ k.divisors.image (p * ·) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,b,ha,hb,rfl⟩ := Nat.dvd_mul.mp (Nat.dvd_of_mem_divisors hx)
      rcases (Nat.dvd_prime hp).mp ha with rfl | rfl
      · exact Finset.mem_union_left _ (by simpa using Nat.mem_divisors.mpr ⟨hb,hk⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Nat.mem_divisors.mpr ⟨hb,hk⟩,rfl⟩)
    · intro hx
      refine Nat.mem_divisors.mpr ⟨?_, mul_ne_zero hp.ne_zero hk⟩
      rcases Finset.mem_union.mp hx with h | h
      · exact (Nat.dvd_of_mem_divisors h).trans (dvd_mul_left k p)
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
        exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors hb)
  have hd : Disjoint k.divisors (k.divisors.image (p * ·)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    exact hn ((dvd_mul_right p b).trans (Nat.dvd_of_mem_divisors hx))
  unfold logDivisorTransform
  rw [hu, Finset.sum_union hd, Finset.sum_image (fun _ _ _ _ h => (Nat.mul_right_inj hp.ne_zero).mp h),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd'
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (hc.coprime_dvd_right (Nat.dvd_of_mem_divisors hd')).gcd_eq_one,
    ArithmeticFunction.moebius_apply_prime hp, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast (Nat.pos_of_mem_divisors hd').ne')]
  push_cast
  rw [show u - (Real.log p + Real.log d) = u - Real.log p - Real.log d by ring]
  ring

noncomputable def truncatedDivisorLogSq (k : ℕ) (u : ℝ) : ℝ :=
  logDivisorTransform (fun v => (max 0 v)^2) k u

theorem logDivisorTransform_reflect {k : ℕ} (hs : Squarefree k)
    (g : ℝ → ℝ) (u : ℝ) :
    (moebius k : ℝ) * logDivisorTransform g k (Real.log k-u) =
      logDivisorTransform (fun v => g (-v)) k u := by
  unfold logDivisorTransform
  rw [← Nat.sum_div_divisors k (fun d => (moebius d : ℝ) * g (Real.log k-u-Real.log d)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hmul : d * (k/d) = k := Nat.mul_div_cancel' hdvd
  have hcop := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hs : Squarefree (d*(k/d)))
  have hmu := isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hmul] at hmu
  have hsq := moebius_sq_eq_one_of_squarefree (hs.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd))
  have hunit : (moebius k : ℝ) * (moebius (k/d) : ℝ) = (moebius d : ℝ) := by
    exact_mod_cast (show moebius k * moebius (k/d) = moebius d by
      rw [hmu, mul_assoc, ← pow_two, hsq, mul_one])
  have hd0 := Nat.cast_ne_zero (R := ℝ) |>.mpr (Nat.pos_of_mem_divisors hd).ne'
  rw [← mul_assoc, hunit, Nat.cast_div hdvd hd0,
    Real.log_div (Nat.cast_ne_zero.mpr hs.ne_zero) hd0]
  congr 2
  ring

theorem truncatedDivisorLogSq_midpoint {k : ℕ} (hs : Squarefree k) :
    (1+(moebius k : ℝ)) * truncatedDivisorLogSq k (Real.log k/2) =
      logDivisorTransform (fun v => v^2) k (Real.log k/2) := by
  have h := logDivisorTransform_reflect hs (fun v => (max 0 v)^2) (Real.log k/2)
  rw [show Real.log k - Real.log k/2 = Real.log k/2 by ring] at h
  rw [add_mul, one_mul]
  unfold truncatedDivisorLogSq
  rw [h]
  unfold logDivisorTransform
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_add]
  congr 1
  generalize Real.log k/2-Real.log d = v
  change (max 0 v)^2 + (max 0 (-v))^2 = v^2
  by_cases hv : 0 ≤ v
  · rw [max_eq_right hv, max_eq_left (neg_nonpos.mpr hv)]; ring
  · rw [max_eq_left (le_of_not_ge hv), max_eq_right (neg_nonneg.mpr (le_of_not_ge hv))]; ring

theorem quadratic_logDivisorTransform_eq_zero {k a b c : ℕ} (hs : Squarefree k)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : a*b*c ∣ k) (u : ℝ) :
    logDivisorTransform (fun v => v^2) k u = 0 := by
  obtain ⟨m,rfl⟩ := hd
  simp only [Nat.mul_assoc] at hs ⊢
  have h1 := Nat.coprime_of_squarefree_mul hs
  have h2 := Nat.coprime_of_squarefree_mul hs.of_mul_right
  have h3 := Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right
  simp only [logDivisorTransform_prime_mul _ ha h1, logDivisorTransform_prime_mul _ hb h2,
    logDivisorTransform_prime_mul _ hc h3]
  simp only [logDivisorTransform, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun d _ => by ring

theorem midpoint_log_product_eq_zero_of_three_primes {k a b c : ℕ} (hs : Squarefree k)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (da : a ∣ k) (db : b ∣ k) (dc : c ∣ k) :
    truncatedDivisorLog k (Real.log k/2) * truncatedDivisorLogSq k (Real.log k/2) = 0 := by
  have ab := (Nat.coprime_primes ha hb).mpr hab
  have ac := (Nat.coprime_primes ha hc).mpr hac
  have bc := (Nat.coprime_primes hb hc).mpr hbc
  have abc : a*b*c ∣ k := (ac.mul_left bc).mul_dvd_of_dvd_of_dvd
    (ab.mul_dvd_of_dvd_of_dvd da db) dc
  have hn : ¬ k.Prime := by
    intro h
    exact hab (((Nat.dvd_prime h).mp da).resolve_left ha.ne_one |>.trans
      (((Nat.dvd_prime h).mp db).resolve_left hb.ne_one).symm)
  by_cases hmu : (moebius k : ℝ) = 1
  · have e := truncatedDivisorLogSq_midpoint hs
    rw [quadratic_logDivisorTransform_eq_zero hs ha hb hc abc, hmu] at e
    have hz : truncatedDivisorLogSq k (Real.log k/2) = 0 := by linarith
    rw [hz, mul_zero]
  · have e := weight_eq_midpoint_moebius k
    rw [ite_eq_left hs] at e
    simp only [weight, ite_eq_right hn] at e
    have hz := (mul_eq_zero.mp e.symm).resolve_left (sub_ne_zero.mpr (Ne.symm hmu))
    rw [hz, zero_mul]

theorem midpoint_log_product_eq_zero_of_card {k : ℕ} (hs : Squarefree k)
    (hcard : 2 < k.primeFactors.card) :
    truncatedDivisorLog k (Real.log k / 2) * truncatedDivisorLogSq k (Real.log k / 2) = 0 := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hcard
  exact midpoint_log_product_eq_zero_of_three_primes hs
    (Nat.prime_of_mem_primeFactors ha) (Nat.prime_of_mem_primeFactors hb)
    (Nat.prime_of_mem_primeFactors hc) hab hac hbc
    (Nat.dvd_of_mem_primeFactors ha) (Nat.dvd_of_mem_primeFactors hb) (Nat.dvd_of_mem_primeFactors hc)

end MidpointSquareDetector

theorem truncatedDivisorLog_prime_mul {p k : ℕ} (hp : p.Prime) (hc : p.Coprime k) (u : ℝ) :
    truncatedDivisorLog (p*k) u = truncatedDivisorLog k u -
      truncatedDivisorLog k (u - Real.log p) :=
  logDivisorTransform_prime_mul (fun t => max 0 t) hp hc u

private theorem truncatedDivisorLog_prime {p : ℕ} (hp : p.Prime) (u : ℝ) :
    truncatedDivisorLog p u = max 0 u - max 0 (u - Real.log p) := by
  unfold truncatedDivisorLog
  rw [hp.sum_divisors, ArithmeticFunction.moebius_apply_prime hp]
  simp
  ring

private theorem triple_hinge_lower (a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hh : 2*u ≤ a+b+c) :
    0 ≤ max 0 u - max 0 (u-c) - (max 0 (u-b) - max 0 (u-b-c)) -
      (max 0 (u-a) - max 0 (u-a-c) - (max 0 (u-a-b) - max 0 (u-a-b-c))) := by
  grind

theorem truncatedDivisorLog_three_primes_nonneg {a b c : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {u : ℝ}
    (hu : 0 ≤ u) (hh : 2*u ≤ Real.log ((a*b*c : ℕ) : ℝ)) :
    0 ≤ truncatedDivisorLog (a*b*c) u := by
  have hab' := (Nat.coprime_primes ha hb).mpr hab
  have hac' := (Nat.coprime_primes ha hc).mpr hac
  have hbc' := (Nat.coprime_primes hb hc).mpr hbc
  have habc : a.Coprime (b*c) := Nat.Coprime.mul_right hab' hac'
  have la : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha.one_le)
  have lb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb.one_le)
  have lc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc.one_le)
  have eA : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne_zero
  have eB : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne_zero
  have eC : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne_zero
  rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (mul_ne_zero eA eB) eC,
      Real.log_mul eA eB] at hh
  rw [Nat.mul_assoc]
  simp only [truncatedDivisorLog_prime_mul ha habc, truncatedDivisorLog_prime_mul hb hbc',
    truncatedDivisorLog_prime hc]
  exact triple_hinge_lower _ _ _ _ la lb lc hu hh

section MidpointProfiles
open ArithmeticFunction

private theorem logDivisorTransform_at_prime (g : ℝ → ℝ) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    logDivisorTransform g p u = g u - g (u - Real.log p) := by
  unfold logDivisorTransform
  rw [hp.sum_divisors, moebius_apply_prime hp]
  simp
  ring

theorem midpoint_profile_prime {p : ℕ} (hp : p.Prime) :
    truncatedDivisorLog p (Real.log p / 2) = Real.log p / 2 ∧
    truncatedDivisorLogSq p (Real.log p / 2) = (Real.log p / 2)^2 := by
  change logDivisorTransform (fun v => max 0 v) p _ = _ ∧
    logDivisorTransform (fun v => (max 0 v)^2) p _ = _
  have h : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  simp only [logDivisorTransform_at_prime _ hp, max_eq_right (by linarith : 0 ≤ Real.log p / 2),
    max_eq_left (by linarith : Real.log p / 2 - Real.log p ≤ 0), zero_pow (by decide : 2 ≠ 0),
    sub_zero, and_self]

theorem midpoint_profile_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    truncatedDivisorLog (p*q) (Real.log (p*q : ℕ)/2) = Real.log p ∧
    truncatedDivisorLogSq (p*q) (Real.log (p*q : ℕ)/2) = Real.log p * Real.log q := by
  change logDivisorTransform (fun v => max 0 v) (p*q) _ = _ ∧
    logDivisorTransform (fun v => (max 0 v)^2) (p*q) _ = _
  have hcp := (Nat.coprime_primes hp hq).mpr hlt.ne
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hle : Real.log (p : ℝ) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hlt.le)
  let u : ℝ := (Real.log p + Real.log q)/2
  have hu : Real.log (p*q : ℕ)/2 = u := by rw [Nat.cast_mul, Real.log_mul hp0 hq0]
  have h1 : 0 ≤ u := by dsimp [u]; linarith
  have h2 : u - Real.log q ≤ 0 := by dsimp [u]; linarith
  have h3 : 0 ≤ u - Real.log p := by dsimp [u]; linarith
  have h4 : u - Real.log p - Real.log q ≤ 0 := by dsimp [u]; linarith
  rw [hu]
  simp only [logDivisorTransform_prime_mul _ hp hcp, logDivisorTransform_at_prime _ hq,
    max_eq_right h1, max_eq_left h2, max_eq_right h3, max_eq_left h4]
  dsimp [u]
  constructor <;> ring

noncomputable def smoothDivisorWeight (j k : ℕ) : ℝ :=
  if Squarefree k then
    let u := Real.log k / 2
    Real.log k * (truncatedDivisorLog k u / u)^j * (truncatedDivisorLogSq k u / u^2)
  else 0

theorem smoothDivisorWeight_prime (j : ℕ) {p : ℕ} (hp : p.Prime) :
    smoothDivisorWeight j p = Real.log p := by
  have h : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hu : Real.log p / 2 ≠ 0 := by linarith
  simp [smoothDivisorWeight, hp.squarefree, (midpoint_profile_prime hp).1,
    (midpoint_profile_prime hp).2, hu]

theorem smoothDivisorWeight_two_primes (j : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    let u := Real.log (p*q : ℕ) / 2
    let t := Real.log p / u
    smoothDivisorWeight j (p*q) = Real.log (p*q : ℕ) * t^(j+1) * (2-t) := by
  dsimp only
  have hcp := (Nat.coprime_primes hp hq).mpr hlt.ne
  have hs : Squarefree (p*q) := (Nat.squarefree_mul hcp).mpr ⟨hp.squarefree,hq.squarefree⟩
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hpL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  let u : ℝ := Real.log (p*q : ℕ) / 2
  have hsum : 2*u = Real.log p + Real.log q := by
    dsimp [u]; rw [Nat.cast_mul, Real.log_mul hp0 hq0]; ring
  have hu : u ≠ 0 := by linarith
  have hscale : Real.log p * Real.log q / u^2 =
      (Real.log p/u) * (2 - Real.log p/u) := by
    rw [show Real.log (q : ℝ) = 2*u - Real.log p by linarith]
    field_simp
  simp only [smoothDivisorWeight, ite_eq_left hs, (midpoint_profile_two_primes hp hq hlt).1,
    (midpoint_profile_two_primes hp hq hlt).2]
  change Real.log (p*q : ℕ) * (Real.log p/u)^j * (Real.log p*Real.log q/u^2) = _
  rw [hscale, pow_succ]
  ring

theorem smoothDivisorWeight_zero_of_card {j k : ℕ} (hj : 0 < j) (hcard : 2 < k.primeFactors.card) :
    smoothDivisorWeight j k = 0 := by
  unfold smoothDivisorWeight
  split_ifs with hs
  · rcases mul_eq_zero.mp (midpoint_log_product_eq_zero_of_card hs hcard) with hF | hA
    · simp [hF, zero_pow hj.ne']
    · simp [hA]
  · rfl
end MidpointProfiles

/-- Extend the finite series at n to every cutoff Q ≥ n by adjoining the remaining
odd-prime factors. -/
noncomputable def extendedPrimeSingularSeries (n : ℕ) (Q : Set.Ici n) : ℝ :=
  truncatedPrimeSingularSeries n *
    ∏ p ∈ (Finset.Ioc n Q.val).filter (fun p : ℕ => p.Prime ∧ 2 < p),
      (1 - 1 / ((p : ℝ)-1)^2)

@[simp] theorem extendedPrimeSingularSeries_self (n : ℕ) :
    extendedPrimeSingularSeries n ⟨n, by simp⟩ = truncatedPrimeSingularSeries n := by
  simp [extendedPrimeSingularSeries]

private theorem eulerFactor_mem {p : ℕ} (hp : 2 < p) :
    0 ≤ (1 - 1 / ((p : ℝ)-1)^2) ∧ (1 - 1 / ((p : ℝ)-1)^2) ≤ 1 := by
  have h : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hsq : (1 : ℝ) ≤ ((p : ℝ) - 1)^2 := by nlinarith [sq_nonneg ((p : ℝ)-2)]
  exact ⟨sub_nonneg.mpr ((div_le_one (by linarith)).mpr hsq), sub_le_self _ (by positivity)⟩

private theorem allEulerFactors_tail (n Q : ℕ) (hn : 2 ≤ n) (hQ : n ≤ Q) :
    (∏ p ∈ Finset.Ioc n Q, (1 - 1 / ((p : ℝ)-1)^2)) =
    ((n : ℝ)-1) * Q / (n * ((Q : ℝ)-1)) := by
  induction Q, hQ using Nat.le_induction with
  | base =>
    have ha : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hb : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    simp only [Finset.Ioc_self, Finset.prod_empty]
    field_simp
  | succ Q hQ ih =>
    rw [Finset.prod_Ioc_succ_top hQ, ih]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hQ' : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
    have hQ0 : (Q : ℝ) ≠ 0 := by linarith
    simp only [add_sub_cancel_right]
    field_simp [hQ0]
    ring

theorem extendedPrimeSingularSeries_bounds {n : ℕ} (hn : 2 ≤ n) (Q : Set.Ici n) :
    ((n : ℝ)-1)/n * truncatedPrimeSingularSeries n ≤ extendedPrimeSingularSeries n Q ∧
      extendedPrimeSingularSeries n Q ≤ truncatedPrimeSingularSeries n := by
  let U := Finset.Ioc n Q.val
  let P := U.filter (fun p : ℕ => p.Prime ∧ 2 < p)
  let f := fun p : ℕ => 1 - 1 / ((p : ℝ)-1)^2
  have hsub : P ⊆ U := Finset.filter_subset _ _
  have hf {p : ℕ} (hp : p ∈ U) : 0 ≤ f p ∧ f p ≤ 1 :=
    eulerFactor_mem (lt_of_le_of_lt hn (Finset.mem_Ioc.mp hp).1)
  have hcomp : (∏ p ∈ U, f p) ≤ ∏ p ∈ P, f p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub (fun _ h => (hf h).1)
      (fun _ h _ => (hf h).2)
  have hcap : (∏ p ∈ P, f p) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ h => (hf (hsub h)).1) (fun _ h => (hf (hsub h)).2)
  have hlow : ((n : ℝ)-1)/n ≤ ∏ p ∈ U, f p := by
    rw [show (∏ p ∈ U, f p) = _ from allEulerFactors_tail n Q.val hn Q.property]
    have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hQ' : (1 : ℝ) < Q.val := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < n) Q.property)
    field_simp
    nlinarith
  have hs := le_trans (by norm_num : (0 : ℝ) ≤ 5/4) (truncatedPrimeSingularSeries_lower n)
  change _ ≤ truncatedPrimeSingularSeries n * (∏ p ∈ P, f p) ∧ _ ≤ _
  constructor
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hlow.trans hcomp) hs
  · exact (mul_le_mul_of_nonneg_left hcap hs).trans_eq (mul_one _)

theorem truncatedPrimeSingularSeries_upper {n : ℕ} (hn : 2 ≤ n) :
    truncatedPrimeSingularSeries n ≤ 2 * Real.sqrt (n : ℝ) := by
  let primes := (Finset.range (n+1)).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  let G := primes.filter (fun p : ℕ => p ∣ n)
  let B := primes.filter (fun p : ℕ => ¬ p ∣ n)
  let g := fun p : ℕ => 1 + 1 / ((p : ℝ)-1)
  have prime_prop {p : ℕ} (hp : p ∈ primes) : p.Prime ∧ 2 < p := (Finset.mem_filter.mp hp).2
  have hpos {p : ℕ} (hp : p ∈ G) : (3 : ℝ) ≤ p := by
    exact_mod_cast (prime_prop (Finset.mem_filter.mp hp).1).2
  have hg {p : ℕ} (hp : p ∈ G) : 0 ≤ g p := by
    have h := hpos hp
    dsimp [g]
    exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith))
  have hbound {p : ℕ} (hp : p ∈ G) : g p ≤ Real.sqrt (p : ℝ) := by
    have h := hpos hp
    have hd : 1 / ((p : ℝ)-1) ≤ 1/2 := by
      apply (div_le_div_iff₀ (by linarith) (by norm_num)).mpr
      linarith
    calc
      g p ≤ 3/2 := by dsimp [g]; linarith
      _ ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hG : G ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(prime_prop (Finset.mem_filter.mp hp).1).1,
      (Finset.mem_filter.mp hp).2, by omega⟩
  have hdiv : (∏ p ∈ G, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset G n.primeFactors id hG).trans (Nat.prod_primeFactors_dvd n)
  have hnat := Nat.le_of_dvd (by omega : 0 < n) hdiv
  have hGcap : (∏ p ∈ G, g p) ≤ Real.sqrt (n : ℝ) := by
    calc
      _ ≤ ∏ p ∈ G, Real.sqrt (p : ℝ) := Finset.prod_le_prod₀ (fun _ h => hg h) (fun _ h => hbound h)
      _ = Real.sqrt (∏ p ∈ G, (p : ℝ)) := (Real.sqrt_prod G (fun p _ => Nat.cast_nonneg p)).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by
        rw [← Nat.cast_prod]
        exact_mod_cast hnat)
  have hB {p : ℕ} (hp : p ∈ B) := eulerFactor_mem (prime_prop (Finset.mem_filter.mp hp).1).2
  have hBcap := Finset.prod_le_one₀ (s := B) (fun _ h => (hB h).1) (fun _ h => (hB h).2)
  have hGpos : 0 ≤ ∏ p ∈ G, g p := Finset.prod_nonneg (fun _ h => hg h)
  change 2 * (∏ p ∈ G, g p) * (∏ p ∈ B, (1 - 1 / ((p : ℝ)-1)^2)) ≤ _
  exact (mul_le_of_le_one_right (by linarith) hBcap).trans (by linarith)

noncomputable def infinitePrimeSingularSeries (n : ℕ) : ℝ :=
  sInf (Set.range (extendedPrimeSingularSeries n))

theorem infinitePrimeSingularSeries_error {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ truncatedPrimeSingularSeries n - infinitePrimeSingularSeries n ∧
      truncatedPrimeSingularSeries n - infinitePrimeSingularSeries n ≤ 2 / Real.sqrt (n : ℝ) := by
  let s := Set.range (extendedPrimeSingularSeries n)
  have hmem : truncatedPrimeSingularSeries n ∈ s := ⟨⟨n, by simp⟩, extendedPrimeSingularSeries_self n⟩
  have hlow : ((n : ℝ)-1)/n * truncatedPrimeSingularSeries n ∈ lowerBounds s := by
    rintro _ ⟨Q, rfl⟩
    exact (extendedPrimeSingularSeries_bounds hn Q).1
  have hs : s.Nonempty := ⟨_, hmem⟩
  have hu := csInf_le (show BddBelow s from ⟨_, hlow⟩) hmem
  have hl := le_csInf hs hlow
  change 0 ≤ truncatedPrimeSingularSeries n - sInf s ∧ _
  refine ⟨sub_nonneg.mpr hu, ?_⟩
  change truncatedPrimeSingularSeries n - sInf s ≤ _
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr := Real.sqrt_pos_of_pos hn'
  have hcancel : truncatedPrimeSingularSeries n - ((n : ℝ)-1)/n * truncatedPrimeSingularSeries n =
      truncatedPrimeSingularSeries n / n := by field_simp; ring
  calc
    _ ≤ truncatedPrimeSingularSeries n - ((n : ℝ)-1)/n * truncatedPrimeSingularSeries n :=
      sub_le_sub_left hl _
    _ = truncatedPrimeSingularSeries n / n := hcancel
    _ ≤ (2 * Real.sqrt (n : ℝ)) / n :=
      div_le_div_of_nonneg_right (truncatedPrimeSingularSeries_upper hn) hn'.le
    _ = 2 / Real.sqrt (n : ℝ) := by
      field_simp
      nlinarith [Real.sq_sqrt hn'.le]

theorem extendedPrimeSingularSeries_antitone (n : ℕ) :
    Antitone (extendedPrimeSingularSeries n) := by
  intro Q₁ Q₂ hQ
  apply mul_le_mul_of_nonneg_left _ ((by norm_num : (0 : ℝ) ≤ 5/4).trans
    (truncatedPrimeSingularSeries_lower n))
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hQ)
  · intro p hp
    exact (eulerFactor_mem (Finset.mem_filter.mp hp).2.2).1
  · intro p hp _
    exact (eulerFactor_mem (Finset.mem_filter.mp hp).2.2).2

theorem extendedPrimeSingularSeries_tendsto {n : ℕ} (hn : 2 ≤ n) :
    Filter.Tendsto (extendedPrimeSingularSeries n) Filter.atTop
      (nhds (infinitePrimeSingularSeries n)) := by
  apply tendsto_atTop_ciInf (extendedPrimeSingularSeries_antitone n)
  refine ⟨((n : ℝ)-1)/n * truncatedPrimeSingularSeries n, ?_⟩
  rintro _ ⟨Q, rfl⟩
  exact (extendedPrimeSingularSeries_bounds hn Q).1

theorem floor_of_infinitePrimeArcMass_budget (N : ℕ)
    (hmodel : ∀ n ≥ N, Even n → infinitePrimeSingularSeries n * (n : ℝ) - (n : ℝ)/16 ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n) n)
    (hminor : ∀ n ≥ N, Even n → -(n : ℝ) ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n)ᶜ n) :
    ∃ (c : ℝ) (M : ℕ), 0 < c ∧ ∀ X n : ℕ, M ≤ X → X ≤ n → n < 2*X →
      Even n → c * (n : ℝ) ≤ corr n := by
  apply floor_of_extendedPrimeArcMass_budget (max N 1024)
  · intro n hn he
    have hn' : 1024 ≤ n := le_trans (le_max_right _ _) hn
    have hr : (32 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by
      norm_num
      exact_mod_cast hn')
    have htail := (infinitePrimeSingularSeries_error (by omega : 2 ≤ n)).2
    have herr : truncatedPrimeSingularSeries n - infinitePrimeSingularSeries n ≤ 1/16 :=
      htail.trans ((div_le_iff₀ (by linarith)).mpr (by linarith))
    have hm := hmodel n ((le_max_left _ _).trans hn) he
    nlinarith only [hm, mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · exact fun n hn he => hminor n ((le_max_left _ _).trans hn) he

theorem extendedPrimeSingularSeries_lower (n : ℕ) (Q : Set.Ici n) :
    (5 : ℝ)/4 ≤ extendedPrimeSingularSeries n Q := by
  let primes := (Finset.range (n+1)).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  let G := primes.filter (fun p : ℕ => p ∣ n)
  let B := primes.filter (fun p : ℕ => ¬p ∣ n)
  let T := (Finset.Ioc n Q.val).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  let f := fun p : ℕ => 1 - 1 / ((p : ℝ)-1)^2
  have hi {p : ℕ} (h : p ∈ primes) : p.Prime ∧ 2 < p := (Finset.mem_filter.mp h).2
  have hd : Disjoint B T := by
    apply Finset.disjoint_left.mpr
    intro p hb ht
    have hb' : p < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
    have ht' : n < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1).1
    omega
  have hbad : (5 : ℝ)/8 ≤ ∏ p ∈ B ∪ T, f p := by
    apply odd_prime_product_five_eighths
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hi (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).2
  have hg : (1 : ℝ) ≤ ∏ p ∈ G, (1 + 1 / ((p : ℝ)-1)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have h : (2 : ℝ) < p := by exact_mod_cast (hi (Finset.mem_filter.mp hp).1).2
    exact le_add_of_nonneg_right (one_div_nonneg.mpr (by linarith))
  change (5 : ℝ)/4 ≤ 2 * (∏ p ∈ G, (1 + 1 / ((p : ℝ)-1))) *
    (∏ p ∈ B, f p) * (∏ p ∈ T, f p)
  rw [mul_assoc, ← Finset.prod_union hd]
  nlinarith only [hg, hbad, mul_nonneg (sub_nonneg.mpr hg) (le_trans (by norm_num) hbad)]

theorem infinitePrimeSingularSeries_lower (n : ℕ) :
    (5 : ℝ)/4 ≤ infinitePrimeSingularSeries n := by
  apply le_csInf
  · exact ⟨_, ⟨⟨n, by simp⟩, rfl⟩⟩
  · rintro _ ⟨Q, rfl⟩
    exact extendedPrimeSingularSeries_lower n Q

theorem corr_one_eighth_of_infinitePrimeArcMass {n : ℕ}
    (hmodel : infinitePrimeSingularSeries n * (n : ℝ) - (n : ℝ)/8 ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n) n)
    (hminor : -(n : ℝ) ≤ primeArcMass (rationalArcSet (extendedArcCutoff n) n)ᶜ n) :
    (1/8 : ℝ) * (n : ℝ) ≤ corr n := by
  have hs := mul_le_mul_of_nonneg_right (infinitePrimeSingularSeries_lower n) (Nat.cast_nonneg n)
  linarith only [hs, hmodel, hminor, corr_eq_rationalArcMass (extendedArcCutoff n) n]

theorem dyadic_one_eighth_of_infinitePrimeArcMass (N : ℕ)
    (hmodel : ∀ n ≥ N, Even n → infinitePrimeSingularSeries n * (n : ℝ) - (n : ℝ)/8 ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n) n)
    (hminor : ∀ n ≥ N, Even n → -(n : ℝ) ≤
      primeArcMass (rationalArcSet (extendedArcCutoff n) n)ᶜ n) :
    ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (1/8 : ℝ) * (n : ℝ) ≤ corr n := by
  intro X n hX hn _ he
  exact corr_one_eighth_of_infinitePrimeArcMass (hmodel n (hX.trans hn) he)
    (hminor n (hX.trans hn) he)

section SmoothDivisorLimits
open Filter Topology

private theorem squarefree_small_cases {k : ℕ} (hs : Squarefree k)
    (hc : k.primeFactors.card ≤ 2) :
    k = 1 ∨ k.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ k = p*q := by
  have hprod := Nat.prod_primeFactors_of_squarefree hs
  rcases (show k.primeFactors.card = 0 ∨ k.primeFactors.card = 1 ∨
      k.primeFactors.card = 2 by omega) with h | h | h
  · left
    simpa [Finset.card_eq_zero.mp h] using hprod.symm
  · obtain ⟨p,he⟩ := Finset.card_eq_one.mp h
    have hp := Nat.prime_of_mem_primeFactors (show p ∈ k.primeFactors by simp [he])
    have eq : k = p := by simpa [he] using hprod.symm
    exact Or.inr (Or.inl (eq ▸ hp))
  · obtain ⟨p,q,hpq,he⟩ := Finset.card_eq_two.mp h
    have hp := Nat.prime_of_mem_primeFactors (show p ∈ k.primeFactors by simp [he])
    have hq := Nat.prime_of_mem_primeFactors (show q ∈ k.primeFactors by simp [he])
    have eq : k = p*q := by simpa [he,hpq] using hprod.symm
    right; right
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨p,q,hp,hq,hlt,eq⟩
    · exact ⟨q,p,hq,hp,hgt,eq.trans (Nat.mul_comm p q)⟩

private theorem smoothDivisorWeight_geometric (k : ℕ) :
    ∃ A t : ℝ, 0 ≤ A ∧ 0 ≤ t ∧ t < 1 ∧ ∀ j : ℕ, 0 < j →
      smoothDivisorWeight j k = weight k + A*t^j := by
  have flat (h : ∀ j : ℕ, 0 < j → smoothDivisorWeight j k = weight k) :
      ∃ A t : ℝ, 0 ≤ A ∧ 0 ≤ t ∧ t < 1 ∧ ∀ j : ℕ, 0 < j →
        smoothDivisorWeight j k = weight k + A*t^j :=
    ⟨0,0,le_rfl,le_rfl,zero_lt_one,fun j hj => by simpa using h j hj⟩
  by_cases hp : k.Prime
  · exact flat fun j _ => by simp [weight, hp, smoothDivisorWeight_prime j hp]
  have hw : weight k = 0 := by simp [weight,hp]
  by_cases hs : Squarefree k
  · by_cases hc : 2 < k.primeFactors.card
    · exact flat fun _ hj => (smoothDivisorWeight_zero_of_card hj hc).trans hw.symm
    rcases squarefree_small_cases hs (by omega) with rfl | h | ⟨p,q,hp',hq',hlt,rfl⟩
    · exact flat fun _ _ => by simp [smoothDivisorWeight,hw]
    · exact (hp h).elim
    let u := Real.log (p*q : ℕ) / 2
    let t := Real.log p / u
    have hlog : Real.log (p*q : ℕ) = Real.log p + Real.log q := by
      rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp'.ne_zero) (Nat.cast_ne_zero.mpr hq'.ne_zero)]
    have hpL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp'.one_lt)
    have hltL : Real.log (p : ℝ) < Real.log q :=
      Real.log_lt_log (by exact_mod_cast hp'.pos) (by exact_mod_cast hlt)
    have hu : 0 < u := by unfold u; linarith
    have ht : 0 ≤ t := (div_pos hpL hu).le
    have ht1 : t < 1 := by apply (div_lt_one hu).mpr; unfold u; linarith
    refine ⟨Real.log (p*q : ℕ)*t*(2-t),t,?_,ht,ht1,?_⟩
    · exact mul_nonneg (mul_nonneg (by linarith) ht) (by linarith)
    · intro j _
      rw [smoothDivisorWeight_two_primes j hp' hq' hlt, hw]
      change _*t^(j+1)*(2-t) = _
      rw [pow_succ]; ring
  · exact flat fun _ _ => by simp [smoothDivisorWeight,hs,hw]

theorem weight_le_smoothDivisorWeight {j : ℕ} (hj : 0 < j) (k : ℕ) :
    weight k ≤ smoothDivisorWeight j k := by
  obtain ⟨A,t,hA,ht,_,h⟩ := smoothDivisorWeight_geometric k
  rw [h j hj]
  exact le_add_of_nonneg_right (mul_nonneg hA (pow_nonneg ht _))

theorem smoothDivisorWeight_succ_le {j : ℕ} (hj : 0 < j) (k : ℕ) :
    smoothDivisorWeight (j+1) k ≤ smoothDivisorWeight j k := by
  obtain ⟨A,t,hA,ht,ht1,h⟩ := smoothDivisorWeight_geometric k
  rw [h _ (by omega), h j hj, pow_succ]
  gcongr
  exact mul_le_of_le_one_right (pow_nonneg ht j) ht1.le

theorem smoothDivisorWeight_tendsto (k : ℕ) :
    Tendsto (fun j => smoothDivisorWeight j k) atTop (𝓝 (weight k)) := by
  obtain ⟨A,t,_,ht,ht1,h⟩ := smoothDivisorWeight_geometric k
  have hlim := tendsto_const_nhds (x := weight k) |>.add
    ((tendsto_pow_atTop_nhds_zero_of_lt_one ht ht1).const_mul A)
  apply (show Tendsto (fun j : ℕ => weight k + A*t^j) atTop (𝓝 (weight k)) by simpa using hlim).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj
  exact (h j hj).symm

noncomputable def smoothDivisorCorr (j n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), smoothDivisorWeight j k * smoothDivisorWeight j (n-k)

theorem corr_le_smoothDivisorCorr {j : ℕ} (hj : 0 < j) (n : ℕ) :
    corr n ≤ smoothDivisorCorr j n := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul (weight_le_smoothDivisorWeight hj k) (weight_le_smoothDivisorWeight hj _)
    (weight_nonneg _) ((weight_nonneg _).trans (weight_le_smoothDivisorWeight hj _))

theorem smoothDivisorCorr_tendsto (n : ℕ) :
    Tendsto (fun j => smoothDivisorCorr j n) atTop (𝓝 (corr n)) :=
  tendsto_finsetSum _ fun k _ => (smoothDivisorWeight_tendsto k).mul (smoothDivisorWeight_tendsto _)

theorem le_corr_iff_forall_smoothDivisorCorr (n : ℕ) (B : ℝ) :
    B ≤ corr n ↔ ∀ j : ℕ, 0 < j → B ≤ smoothDivisorCorr j n := by
  refine ⟨fun h j hj => h.trans (corr_le_smoothDivisorCorr hj n), fun h => ?_⟩
  exact ge_of_tendsto (smoothDivisorCorr_tendsto n) ((eventually_gt_atTop (0 : ℕ)).mono h)

theorem smoothDivisorCorr_succ_le {j : ℕ} (hj : 0 < j) (n : ℕ) :
    smoothDivisorCorr (j+1) n ≤ smoothDivisorCorr j n := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul (smoothDivisorWeight_succ_le hj k) (smoothDivisorWeight_succ_le hj _)
    ((weight_nonneg _).trans (weight_le_smoothDivisorWeight (by omega) _))
    ((weight_nonneg _).trans (weight_le_smoothDivisorWeight hj _))

theorem dyadic_smoothDivisorCorr_floor_iff :
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n) ↔
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → ∀ j : ℕ, 0 < j → c*(n:ℝ) ≤ smoothDivisorCorr j n) := by
  constructor
  · rintro ⟨c,N,hc,h⟩
    exact ⟨c,N,hc,fun X n hX hXn hn he =>
      (le_corr_iff_forall_smoothDivisorCorr n _).mp (h X n hX hXn hn he)⟩
  · rintro ⟨c,N,hc,h⟩
    exact ⟨c,N,hc,fun X n hX hXn hn he =>
      (le_corr_iff_forall_smoothDivisorCorr n _).mpr (h X n hX hXn hn he)⟩

theorem smoothDivisorWeight_semiprime_unbounded (j : ℕ) (B : ℝ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 < p ∧ p < q ∧ q ≤ 2*p ∧
      B < smoothDivisorWeight j (p*q) - weight (p*q) := by
  let b : ℝ := (1/2 : ℝ)^(j+1)
  have hb : 0 < b := pow_pos (by norm_num) _
  obtain ⟨m,hm⟩ := exists_nat_gt (Real.exp ((|B|+1)/b))
  obtain ⟨p,hpM,hp⟩ := Nat.exists_infinite_primes (max (192^4) m)
  have hm' : m ≤ p := (le_max_right _ _).trans hpM
  have h192 : 192^4 ≤ p := (le_max_left _ _).trans hpM
  have hp2 : 2 < p := by omega
  have hLp : (|B|+1)/b < Real.log (p : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr (hm.trans_le (by exact_mod_cast hm'))
  have hmz := dyadic_prime_mass p h192
  have hne : ((Finset.Ioc p (2*p)).filter Nat.Prime).Nonempty := by
    by_contra! hempty
    rw [hempty, Finset.sum_empty] at hmz
    have hpos : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    linarith
  obtain ⟨q,hq'⟩ := hne
  obtain ⟨hi,hq⟩ := Finset.mem_filter.mp hq'
  obtain ⟨hlt,hqp⟩ := Finset.mem_Ioc.mp hi
  refine ⟨p,q,hp,hq,hp2,hlt,hqp,?_⟩
  have hlog : Real.log (p*q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hltL : Real.log (p : ℝ) < Real.log q :=
    Real.log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast hlt)
  have hqpp : q ≤ p*p := hqp.trans (Nat.mul_le_mul_right p hp.two_le)
  have hqL : Real.log (q : ℝ) ≤ 2*Real.log p := by
    have e := Real.log_le_log (by exact_mod_cast hq.pos : 0 < (q:ℝ))
      (by exact_mod_cast hqpp : (q:ℝ) ≤ (p:ℝ)*p)
    rw [Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hp.ne_zero)] at e
    linarith
  let u := Real.log (p*q : ℕ)/2
  let t := Real.log p/u
  have hu : 0 < u := by unfold u; linarith
  have ht : 1/2 ≤ t := by apply (le_div_iff₀ hu).mpr; unfold u; linarith
  have ht' : t ≤ 1 := by apply (div_le_one hu).mpr; unfold u; linarith
  have hpow : b ≤ t^(j+1) := pow_le_pow_left₀ (by norm_num) ht _
  have hB : B < Real.log (p : ℝ)*b := by
    have h := (div_lt_iff₀ hb).mp hLp
    linarith [le_abs_self B]
  have hlogpos : 0 ≤ Real.log (p*q : ℕ) := by linarith
  rw [smoothDivisorWeight_two_primes j hp hq hlt]
  simp only [weight, ite_eq_right (Nat.not_prime_mul hp.ne_one hq.ne_one), sub_zero]
  change B < Real.log (p*q : ℕ) * t^(j+1) * (2-t)
  calc
    B < Real.log (p : ℝ) * b := hB
    _ ≤ Real.log (p*q : ℕ) * t^(j+1) := mul_le_mul (by linarith) hpow hb.le hlogpos
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hlogpos (hb.le.trans hpow)) (by linarith)

theorem smoothDivisorCorr_even_error_unbounded {j : ℕ} (hj : 0 < j) (B : ℝ) :
    ∃ n : ℕ, Even n ∧ B < smoothDivisorCorr j n - corr n := by
  have hlog : 0 < Real.log (3:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨p,q,hp,hq,hp2,hpq,_,hgap⟩ := smoothDivisorWeight_semiprime_unbounded j (B / Real.log 3)
  let n := p*q + 3
  have ho : Odd (p*q) := (hp.odd_of_ne_two (by omega)).mul (hq.odd_of_ne_two (by omega))
  refine ⟨n,ho.add_odd (by decide : Odd (3:ℕ)),?_⟩
  let D (k : ℕ) := smoothDivisorWeight j k * smoothDivisorWeight j (n-k) -
    weight k * weight (n-k)
  have hD (k : ℕ) : 0 ≤ D k := sub_nonneg.mpr (mul_le_mul
    (weight_le_smoothDivisorWeight hj k) (weight_le_smoothDivisorWeight hj _)
    (weight_nonneg _) ((weight_nonneg _).trans (weight_le_smoothDivisorWeight hj _)))
  have hmem : p*q ∈ Finset.range (n+1) := Finset.mem_range.mpr (by dsimp [n]; omega)
  have hs := Finset.single_le_sum (f := D) (fun k _ => hD k) hmem
  have hthree : n - p*q = 3 := by dsimp [n]; omega
  have hwt : weight 3 = Real.log (3:ℝ) := by norm_num [weight, Nat.prime_three]
  calc
    B < (smoothDivisorWeight j (p*q) - weight (p*q)) * Real.log (3:ℝ) := (div_lt_iff₀ hlog).mp hgap
    _ = D (p*q) := by
      unfold D
      rw [hthree,smoothDivisorWeight_prime j Nat.prime_three,hwt]
      exact sub_mul ..
    _ ≤ ∑ k ∈ Finset.range (n+1), D k := hs
    _ = smoothDivisorCorr j n - corr n := Finset.sum_sub_distrib ..

end SmoothDivisorLimits

section SmoothMomentKernel

/-- Successive weights agree on primes. On a surviving semiprime their ratio
is the smaller factor's logarithm divided by half the total logarithm. -/
noncomputable def smoothDivisorRatio (k : ℕ) : ℝ :=
  smoothDivisorWeight 2 k / smoothDivisorWeight 1 k

private theorem smoothDivisorWeight_shift (j k : ℕ) :
    smoothDivisorWeight (j+1) k = smoothDivisorWeight j k *
      (truncatedDivisorLog k (Real.log k/2) / (Real.log k/2)) := by
  unfold smoothDivisorWeight
  split_ifs <;> (try simp only [pow_succ]) <;> ring

theorem smoothDivisorWeight_as_moment (j k : ℕ) :
    smoothDivisorWeight (j+1) k = smoothDivisorWeight 1 k * (smoothDivisorRatio k)^j := by
  let t := truncatedDivisorLog k (Real.log k/2) / (Real.log k/2)
  have hs (l : ℕ) : smoothDivisorWeight (l+1) k = smoothDivisorWeight l k * t :=
    smoothDivisorWeight_shift l k
  induction j with
  | zero => simp
  | succ j ih =>
    rw [hs (j+1), ih, pow_succ]
    by_cases hz : smoothDivisorWeight 1 k = 0
    · simp [hz]
    · have hr : smoothDivisorRatio k = t := by
        unfold smoothDivisorRatio
        rw [hs 1]
        exact (div_eq_iff hz).mpr (mul_comm _ _)
      rw [hr]
      ring

/-- A finitely supported filter of common moments uses one scalar per pair. -/
theorem smooth_pair_kernel_expansion (n : ℕ) (D : Finset ℕ) (b : ℕ → ℝ) :
    (∑ j ∈ D, b j * ∑ k ∈ Finset.range (n+1),
      smoothDivisorWeight (j+1) k * smoothDivisorWeight (j+1) (n-k)) =
    ∑ k ∈ Finset.range (n+1), smoothDivisorWeight 1 k * smoothDivisorWeight 1 (n-k) *
      ∑ j ∈ D, b j * (smoothDivisorRatio k * smoothDivisorRatio (n-k))^j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [smoothDivisorWeight_as_moment j k, smoothDivisorWeight_as_moment j (n-k), mul_pow]
  ring

theorem smoothDivisorRatio_bounds (k : ℕ) : 0 ≤ smoothDivisorRatio k ∧ smoothDivisorRatio k ≤ 1 := by
  have hw1 := (weight_nonneg k).trans (weight_le_smoothDivisorWeight (j := 1) (by decide) k)
  have hw2 := (weight_nonneg k).trans (weight_le_smoothDivisorWeight (j := 2) (by decide) k)
  unfold smoothDivisorRatio
  constructor
  · exact div_nonneg hw2 hw1
  · by_cases hz : smoothDivisorWeight 1 k = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hw1 (Ne.symm hz))).mpr
        (smoothDivisorWeight_succ_le (j := 1) (by decide) k)

private theorem smoothDivisorRatio_prime {p : ℕ} (hp : p.Prime) :
    smoothDivisorRatio p = 1 := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  simp [smoothDivisorRatio, smoothDivisorWeight_prime _ hp, hlog.ne']

/-- Any polynomial nonnegative on [0,1] and at least one at the endpoint
gives an upper bound on the prime sum, even if its coefficients have signs. -/
theorem corr_le_filtered_smoothDivisorCorr (n : ℕ) (D : Finset ℕ) (b : ℕ → ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ ∑ j ∈ D, b j * x^j)
    (hone : 1 ≤ ∑ j ∈ D, b j) :
    corr n ≤ ∑ j ∈ D, b j * smoothDivisorCorr (j+1) n := by
  unfold smoothDivisorCorr
  rw [smooth_pair_kernel_expansion]
  apply Finset.sum_le_sum
  intro k _
  have h1 := smoothDivisorRatio_bounds k
  have h2 := smoothDivisorRatio_bounds (n-k)
  have hkernel := hpos _ (mul_nonneg h1.1 h2.1) ((mul_le_of_le_one_left h2.1 h1.2).trans h2.2)
  have hpot (l : ℕ) := (weight_nonneg l).trans (weight_le_smoothDivisorWeight (j := 1) (by decide) l)
  have hright := mul_nonneg (mul_nonneg (hpot k) (hpot (n-k))) hkernel
  by_cases hk : k.Prime
  · by_cases hl : (n-k).Prime
    · rw [smoothDivisorRatio_prime hk, smoothDivisorRatio_prime hl] 
      simp only [mul_one, one_pow]
      rw [smoothDivisorWeight_prime 1 hk, smoothDivisorWeight_prime 1 hl]
      simp only [weight, ite_eq_left hk, ite_eq_left hl]
      exact le_mul_of_one_le_right (mul_nonneg (Real.log_nonneg (by exact_mod_cast hk.one_le))
        (Real.log_nonneg (by exact_mod_cast hl.one_le))) hone
    · simpa only [weight, ite_eq_right hl, mul_zero] using hright
  · simpa only [weight, ite_eq_right hk, zero_mul] using hright

end SmoothMomentKernel

/-!
## How much do the semiprimes contribute?

The following uniform estimates are paper calculations. The definitions,
support, exact semiprime profile, monotonicity and fixed-target limit above
are proved in Lean.

Write L = log n, j = ceil((log L)^2) and H_j = smoothDivisorCorr j n.
For all sufficiently large even n the profile gives
  0 <= H_j - corr(n) << n/L^2 + n L^2 (0.61)^j + S(n)n(1/j+1/L).
Here S(n) is the binary singular series. In particular H_j-corr(n)=o(n)
uniformly. The implicit constant is independent of the prime divisors of n.

Indeed V_j(k) lies between zero and log k for k >= 2, because
t^(j+1)(2-t) <= t(2-t) <= 1 for 0 <= t <= 1. The terms with either entry
below n/L^4 contribute O(n/L^2). In the rest, if a surviving semiprime
has a prime factor below n^0.30 then its t is at most 0.61, since its log
is at least L-4 log L. This gives the second error. In all remaining terms
each entry has all prime factors at least n^0.30. A nonprime entry is ab,
where a,b are primes and n^0.30 <= a < b. By symmetry it suffices to
charge such an entry on the left, allowing a factor of two.

Fix a. Sieve the integer variable b <= n/a for the two forms b and n-ab
at primes up to n^0.01. For an odd sieve prime the number of forbidden
classes is two unless it divides n, in which case it is one. The prime a
is larger than the sifting limit. The dimension-two upper sieve bounds the
number of rows by O(S(n)n/(a L^2)), uniformly in a. The interval length
is at least sqrt(n), so a fixed positive power of n is available for the
sieve level with a power saving in the total remainder per row. Both log
weights together cost at most 2 L^2 (2 log a/L)^(j+1) times
(1-4 log L/L)^(-j-1), which is bounded for this j. In the dyadic
shell sqrt(n)/2^(h+1) < a <= sqrt(n)/2^h the prime reciprocal sum is
O(1/L) as long as a >= n^0.30, by Chebyshev's upper bound. The factor
(2 log a/L)^(j+1) is at most exp(-2 h j log(2)/L). The geometric sum
is O(1/j+1/L). Finally S(n) << log log n by the Euler product and
Mertens' estimate, so each error is o(n).

There is also an individual lower bound for H_j. The rough version of
Chen's theorem supplies >> S(n)n/L^2 prime-plus-prime-or-semiprime
representations with both factors on the semiprime side at least n^0.1.
Discard either entry below n^0.9, squares, and primes dividing n at a
cost O(n^0.9+sqrt(n)+log n) in the raw count. On each remaining
semiprime t >= 1/5. Hence H_j >> S(n)n 5^(-j-1) with an absolute
constant. This lower estimate decays with j. Deducing the frozen floor
from the uniform approximation above requires a lower estimate of order
n for the growing j, with a positive constant independent of n.

For Chen's weighted lower bound and its roughness condition see Halberstam,
A proof of Chen's theorem, pp. 281-283,
https://www.numdam.org/article/AST_1975__24-25__281_0.pdf .
For the upper sieve see Green and Tao, Restriction theory of the Selberg
sieve, https://arxiv.org/abs/math/0405581 and Tao, Notes 4, Theorem 30,
https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/ .
-/

open scoped BigOperators
open Finset

private theorem kernel_unit_energy {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (K : A → I → ℂ) (v : I → ℂ) (d : ℝ)
    (hK : ∀ i j, (∑ a, star (K a i) * K a j) = if i = j then (d : ℂ) else 0) :
    (∑ a, ‖∑ i, v i * K a i‖^2) = d * ∑ i, ‖v i‖^2 := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.sq_norm, Complex.ofReal_sum, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  have hex (a : A) : star (∑ i, v i * K a i) * (∑ i, v i * K a i) =
      ∑ i, ∑ j, (star (v i) * v j) * (star (K a i) * K a j) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul]
    ring
  change (∑ a, star (∑ i, v i * K a i) * (∑ i, v i * K a i)) =
    (d : ℂ) * ∑ i, star (v i) * v i
  simp_rw [hex]
  rw [Finset.sum_comm (s := (Finset.univ : Finset A))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := (Finset.univ : Finset A))]
  simp_rw [← Finset.mul_sum, hK]
  simp [mul_ite, mul_comm (d : ℂ)]

private theorem unitSum_eq_zmodSum {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (h : ∀ a, ¬ IsUnit a → F a = 0) :
    (∑ a : (ZMod q)ˣ, F (a : ZMod q)) = ∑ a : ZMod q, F a := by
  classical
  let s := (Finset.univ : Finset (ZMod q)ˣ).map ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩
  have hs : (∑ a ∈ s, F a) = ∑ a : (ZMod q)ˣ, F (a : ZMod q) := Finset.sum_map _ _ _
  rw [← hs]
  apply Finset.sum_subset (Finset.subset_univ s)
  intro a _ ha
  apply h
  rintro ⟨u, rfl⟩
  exact ha (Finset.mem_map.mpr ⟨u, Finset.mem_univ _, rfl⟩)

open Classical in
private theorem unit_character_orthogonality {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    (∑ a : (ZMod q)ˣ, star (χ (a : ZMod q)) * ψ (a : ZMod q)) =
      if χ = ψ then (q.totient : ℂ) else 0 := by
  classical
  let η := χ⁻¹ * ψ
  have hprod (a : ZMod q) : star (χ a) * ψ a = η a := by
    rw [MulChar.star_apply']
    rfl
  simp_rw [hprod]
  rw [unitSum_eq_zmodSum η (fun a ha => η.map_nonunit ha)]
  by_cases he : χ = ψ
  · subst ψ
    simp [η, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · rw [ite_eq_right he]
    apply MulChar.sum_eq_zero_of_ne_one
    intro hh
    apply he
    exact inv_mul_eq_one.mp hh

theorem dirichlet_synthesis_energy (q : ℕ) [NeZero q] (v : DirichletCharacter ℂ q → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, v χ * χ (a : ZMod q)‖^2) =
    (q.totient : ℝ) * ∑ χ, ‖v χ‖^2 := by
  classical
  exact kernel_unit_energy _ _ _ (unit_character_orthogonality (q := q))

theorem dirichlet_analysis_energy (q : ℕ) [NeZero q] (v : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, v u * χ (u : ZMod q)‖^2) =
    (q.totient : ℝ) * ∑ u, ‖v u‖^2 := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩, rootsOfUnity.isCyclic ..⟩
  apply kernel_unit_energy
  intro u w
  have hu (χ : DirichletCharacter ℂ q) : star (χ (u : ZMod q)) = χ ((u : ZMod q)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  simp_rw [hu]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
  congr 1
  exact propext ⟨Units.ext, fun he => congrArg Units.val he⟩

noncomputable def unitGaussCoefficient (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ u : (ZMod q)ˣ, Complex.exp (((2 * Real.pi * ((u : ZMod q).val : ℝ) / q : ℝ) : ℂ) * Complex.I) * χ (u : ZMod q)

theorem dirichletGauss_energy (q : ℕ) [NeZero q] :
    (∑ χ : DirichletCharacter ℂ q, ‖unitGaussCoefficient q χ‖^2) = (q.totient : ℝ)^2 := by
  unfold unitGaussCoefficient
  rw [dirichlet_analysis_energy]
  have he (u : (ZMod q)ˣ) :
      ‖Complex.exp (((2 * Real.pi * ((u : ZMod q).val : ℝ) / q : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  simp_rw [he]
  simp [ZMod.card_units_eq_totient, pow_two]

theorem dirichlet_synthesis_energy_conj (q : ℕ) [NeZero q] (v : DirichletCharacter ℂ q → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, v χ * star (χ (a : ZMod q))‖^2) =
    (q.totient : ℝ) * ∑ χ, ‖v χ‖^2 := by
  classical
  apply kernel_unit_energy
  intro χ ψ
  simp only [star_star]
  have h := unit_character_orthogonality (q := q) ψ χ
  simpa only [mul_comm, eq_comm, Complex.ofReal_natCast] using h

noncomputable def dirichletArcErrorRow (q : ℕ) [NeZero q]
    (T : DirichletCharacter ℂ q → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ χ, (unitGaussCoefficient q χ * T χ / (q.totient : ℂ)) * star (χ (a : ZMod q))

theorem dirichletArcErrorRow_energy (q : ℕ) [NeZero q] (T : DirichletCharacter ℂ q → ℂ) :
    (∑ a, ‖dirichletArcErrorRow q T a‖^2) =
      (∑ χ, ‖unitGaussCoefficient q χ‖^2 * ‖T χ‖^2) / (q.totient : ℝ) := by
  classical
  unfold dirichletArcErrorRow
  rw [dirichlet_synthesis_energy_conj]
  simp_rw [norm_div, norm_mul, div_pow, mul_pow, Complex.norm_natCast]
  rw [← Finset.sum_div]
  have hq : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

open MeasureTheory in
theorem dirichletArcErrorRow_integral_le (q : ℕ) [NeZero q] (T : DirichletCharacter ℂ q → ℝ → ℂ)
    (l r B : ℝ) (hi : ∀ χ, IntervalIntegrable (fun β => ‖T χ β‖^2) volume l r)
    (hB : ∀ χ, (∫ β in l..r, ‖T χ β‖^2) ≤ B) :
    (∫ β in l..r, ∑ a, ‖dirichletArcErrorRow q (fun χ => T χ β) a‖^2) ≤
      (q.totient : ℝ) * B := by
  classical
  simp_rw [dirichletArcErrorRow_energy]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    (fun χ _ => (hi χ).const_mul (‖unitGaussCoefficient q χ‖^2))]
  simp_rw [intervalIntegral.integral_const_mul]
  have hq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ∑ χ, ‖unitGaussCoefficient q χ‖^2 * B :=
      Finset.sum_le_sum fun χ _ => mul_le_mul_of_nonneg_left (hB χ) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, dirichletGauss_energy]; ring

section AdjacentSmoothMoments

noncomputable def smoothMomentGap (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)^2

theorem smoothMomentGap_pos (n : ℕ) : 0 < smoothMomentGap n := by
  unfold smoothMomentGap
  positivity

theorem smoothMomentGap_le_one (n : ℕ) : smoothMomentGap n ≤ 1 := by
  unfold smoothMomentGap
  apply (div_le_one (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

private theorem semiprime_ratio_le {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : p < q) (hbound : p*q ≤ n) :
    Real.log p / (Real.log (p*q : ℕ)/2) ≤ 1 - smoothMomentGap n := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hpL := Real.log_pos (by exact_mod_cast hp.one_lt : 1 < (p:ℝ))
  have hqL := Real.log_pos (by exact_mod_cast hq.one_lt : 1 < (q:ℝ))
  have hsum : Real.log (p*q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne']
  have hdist : 1/(q:ℝ) ≤ Real.log q - Real.log p := by
    have hinc : (1:ℝ)+p ≤ q := by exact_mod_cast (show 1+p ≤ q by omega)
    have hl := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
    rw [Real.log_div hp0.ne' hq0.ne'] at hl
    calc
      1/(q:ℝ) ≤ 1 - (p:ℝ)/q := by
        apply (le_sub_iff_add_le).mpr
        rw [← add_div,div_le_one hq0]
        exact hinc
      _ ≤ _ := by linarith
  have hqk : q ≤ p*q := by simpa using (Nat.mul_le_mul_right q hp.one_le)
  have hqN : (q:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (show q ≤ n+1 by omega)
  have hlN : Real.log (p*q : ℕ) ≤ (n:ℝ)+1 := by
    have hh := Real.log_le_self (Nat.cast_nonneg (α := ℝ) (p*q))
    have hh' : ((p*q : ℕ):ℝ) ≤ n := by exact_mod_cast hbound
    linarith
  have hgapL : smoothMomentGap n * Real.log (p*q : ℕ) ≤ 1/(q:ℝ) := by
    calc
      _ = Real.log (p*q : ℕ) / ((n:ℝ)+1)^2 := by unfold smoothMomentGap; ring
      _ ≤ ((n:ℝ)+1) / ((n:ℝ)+1)^2 := div_le_div_of_nonneg_right hlN (sq_nonneg _)
      _ = 1/((n:ℝ)+1) := by
        have hne : (n:ℝ)+1 ≠ 0 := by positivity
        field_simp
      _ ≤ 1/(q:ℝ) := one_div_le_one_div_of_le hq0 hqN
  apply (div_le_iff₀ (by linarith : 0 < Real.log (p*q : ℕ)/2)).mpr
  nlinarith [hgapL.trans hdist]

def AdmitsSmoothGap (n : ℕ) (δ : ℝ) : Prop :=
  ∀ {p q : ℕ}, p.Prime → q.Prime → p < q → p*q ≤ n →
    Real.log p / (Real.log (p*q : ℕ)/2) ≤ 1-δ

private theorem smoothDivisorWeight_nonprime_contract_with_gap {j k n : ℕ} {δ : ℝ}
    (hg : AdmitsSmoothGap n δ) (hj : 0 < j)
    (hk : k ≤ n) (hp : ¬ k.Prime) :
    smoothDivisorWeight (j+1) k ≤ (1-δ) * smoothDivisorWeight j k := by
  by_cases hs : Squarefree k
  · by_cases hc : 2 < k.primeFactors.card
    · rw [smoothDivisorWeight_zero_of_card (by omega) hc, smoothDivisorWeight_zero_of_card hj hc]
      simp
    rcases squarefree_small_cases hs (by omega) with rfl | h | ⟨p,q,hp',hq',hlt,rfl⟩
    · simp [smoothDivisorWeight]
    · exact (hp h).elim
    let t := Real.log p / (Real.log (p*q : ℕ)/2)
    have hmul : smoothDivisorWeight (j+1) (p*q) = t * smoothDivisorWeight j (p*q) := by
      rw [smoothDivisorWeight_two_primes _ hp' hq' hlt, smoothDivisorWeight_two_primes _ hp' hq' hlt]
      change _*t^((j+1)+1)*(2-t) = t*(_*t^(j+1)*(2-t))
      rw [pow_succ t (j+1)]; ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_right (hg hp' hq' hlt hk)
      ((weight_nonneg _).trans (weight_le_smoothDivisorWeight hj _))
  · simp [smoothDivisorWeight,hs]


theorem smoothDivisorCorr_adjacent_lower_with_gap {n : ℕ} {δ : ℝ} (hd : δ ≤ 1)
    (hg : AdmitsSmoothGap n δ) {j : ℕ} (hj : 0 < j) :
    smoothDivisorCorr (j+1) n - (1-δ) * smoothDivisorCorr j n ≤
      δ * corr n := by
  let r := 1 - δ
  have hr : 0 ≤ r := sub_nonneg.mpr hd
  have nonprime {a b : ℕ} (ha : a ≤ n) (hpa : ¬ a.Prime) :
      smoothDivisorWeight (j+1) a * smoothDivisorWeight (j+1) b -
        r * (smoothDivisorWeight j a * smoothDivisorWeight j b) ≤
        δ * (weight a * weight b) := by
    have hz : weight a = 0 := by simp [weight,hpa]
    rw [hz,zero_mul,mul_zero,sub_nonpos]
    calc
      _ ≤ (r * smoothDivisorWeight j a) * smoothDivisorWeight j b :=
        mul_le_mul (smoothDivisorWeight_nonprime_contract_with_gap hg hj ha hpa) (smoothDivisorWeight_succ_le hj b)
          ((weight_nonneg _).trans (weight_le_smoothDivisorWeight (by omega) _))
          (mul_nonneg hr ((weight_nonneg _).trans (weight_le_smoothDivisorWeight hj _)))
      _ = _ := mul_assoc .. 
  unfold smoothDivisorCorr corr
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  by_cases ha : k.Prime
  · by_cases hb : (n-k).Prime
    · rw [smoothDivisorWeight_prime _ ha, smoothDivisorWeight_prime _ ha,
        smoothDivisorWeight_prime _ hb, smoothDivisorWeight_prime _ hb]
      simp only [weight, ite_eq_left ha, ite_eq_left hb]
      exact le_of_eq (by ring)
    · simpa only [mul_comm (smoothDivisorWeight (j+1) (n-k)), mul_comm (smoothDivisorWeight j (n-k)),
          mul_comm (weight (n-k))] using
        (nonprime (b := k) (Nat.sub_le n k) hb)
  · exact nonprime hk' ha

theorem smoothDivisorCorr_adjacent_lower (n : ℕ) {j : ℕ} (hj : 0 < j) :
    smoothDivisorCorr (j+1) n - (1-smoothMomentGap n) * smoothDivisorCorr j n ≤
      smoothMomentGap n * corr n :=
  smoothDivisorCorr_adjacent_lower_with_gap (smoothMomentGap_le_one n)
    (fun hp hq h hk => semiprime_ratio_le hp hq h hk) hj

theorem smoothDivisorCorr_two_moment_certificate (n : ℕ) {j : ℕ} (hj : 0 < j) (B : ℝ)
    (h : smoothMomentGap n * B ≤ smoothDivisorCorr (j+1) n -
      (1-smoothMomentGap n) * smoothDivisorCorr j n) : B ≤ corr n :=
  (le_of_mul_le_mul_left (h.trans (smoothDivisorCorr_adjacent_lower n hj)) (smoothMomentGap_pos n))


noncomputable def smoothTwoMomentLower (j n : ℕ) : ℝ :=
  (smoothDivisorCorr (j+1) n - (1-smoothMomentGap n) * smoothDivisorCorr j n) / smoothMomentGap n

theorem smoothTwoMomentLower_le_corr (n : ℕ) {j : ℕ} (hj : 0 < j) :
    smoothTwoMomentLower j n ≤ corr n := by
  apply (div_le_iff₀ (smoothMomentGap_pos n)).mpr
  simpa only [mul_comm (corr n)] using smoothDivisorCorr_adjacent_lower n hj

theorem smoothTwoMomentLower_tendsto (n : ℕ) :
    Filter.Tendsto (fun j => smoothTwoMomentLower j n) Filter.atTop (nhds (corr n)) := by
  have h := smoothDivisorCorr_tendsto n
  have hsucc := h.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim := (hsucc.sub (h.const_mul (1-smoothMomentGap n))).div_const (smoothMomentGap n)
  have hz : smoothMomentGap n ≠ 0 := (smoothMomentGap_pos n).ne'
  have he : (corr n - (1-smoothMomentGap n)*corr n)/smoothMomentGap n = corr n := by
    apply (div_eq_iff hz).mpr
    ring
  rw [he] at hlim
  exact hlim

theorem lt_corr_iff_exists_two_moment_lower (n : ℕ) (B : ℝ) :
    B < corr n ↔ ∃ j : ℕ, 0 < j ∧ B < smoothTwoMomentLower j n := by
  refine ⟨fun h => ?_, fun ⟨j,hj,h⟩ => h.trans_le (smoothTwoMomentLower_le_corr n hj)⟩
  have hprev := (smoothTwoMomentLower_tendsto n).eventually (lt_mem_nhds h)
  exact (Filter.eventually_gt_atTop (0 : ℕ) |>.and hprev).exists

end AdjacentSmoothMoments
section FixedSmoothMomentRate

theorem smoothDivisorWeight_le_nat {j : ℕ} (hj : 0 < j) (k : ℕ) :
    smoothDivisorWeight j k ≤ (k : ℝ) := by
  by_cases hs : Squarefree k
  · by_cases hc : 2 < k.primeFactors.card
    · rw [smoothDivisorWeight_zero_of_card hj hc]
      exact Nat.cast_nonneg _
    rcases squarefree_small_cases hs (by omega) with rfl | hp | ⟨p,q,hp,hq,hlt,rfl⟩
    · simp [smoothDivisorWeight]
    · rw [smoothDivisorWeight_prime j hp]
      exact Real.log_le_self (Nat.cast_nonneg _)
    let K : ℝ := Real.log (p*q : ℕ)
    let t : ℝ := Real.log p/(K/2)
    have hK : K = Real.log p + Real.log q := by
      unfold K
      rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
    have hpL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hpqL : Real.log (p : ℝ) ≤ Real.log q :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hlt.le)
    have hu : 0 < K/2 := by linarith
    have ht : 0 ≤ t := (div_pos hpL hu).le
    have ht1 : t ≤ 1 := (div_le_one hu).mpr (by linarith)
    have hf : t^(j+1)*(2-t) ≤ 1 := by
      rw [pow_succ,mul_assoc]
      have hq' : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
      exact (mul_le_mul (pow_le_one₀ ht ht1) hq' (mul_nonneg ht (by linarith)) zero_le_one).trans_eq
        (one_mul 1)
    rw [smoothDivisorWeight_two_primes j hp hq hlt]
    change K*t^(j+1)*(2-t) ≤ _
    rw [mul_assoc]
    exact (mul_le_of_le_one_right (by linarith : 0 ≤ K) hf).trans
      (Real.log_le_self (Nat.cast_nonneg _))
  · simp [smoothDivisorWeight,hs]

theorem smoothDivisorCorr_initial_cap (n : ℕ) : smoothDivisorCorr 1 n ≤ ((n : ℝ)+1)^3 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ((n : ℝ)+1) * ((n : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro k hk
      have h₁ : (k : ℝ) ≤ (n:ℝ)+1 := by
        exact_mod_cast (Finset.mem_range.mp hk).le
      have h₂ : ((n-k : ℕ):ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (show n-k ≤ n+1 by omega)
      exact mul_le_mul ((smoothDivisorWeight_le_nat (by decide : 0 < 1) k).trans h₁)
        ((smoothDivisorWeight_le_nat (by decide : 0 < 1) (n-k)).trans h₂)
        ((weight_nonneg _).trans (weight_le_smoothDivisorWeight (by decide : 0 < 1) _)) (by positivity)
    _ = _ := by simp; ring

theorem smoothDivisorCorr_geometric_with_gap {n : ℕ} {δ : ℝ} (hd : δ ≤ 1)
    (hg : AdmitsSmoothGap n δ) (j : ℕ) :
    smoothDivisorCorr (j+1) n - corr n ≤
      (1-δ)^j * (smoothDivisorCorr 1 n - corr n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := smoothDivisorCorr_adjacent_lower_with_gap hd hg (show 0 < j+1 by omega)
    calc
      smoothDivisorCorr (j+1+1) n - corr n ≤
          (1-δ) * (smoothDivisorCorr (j+1) n - corr n) := by linarith only [h]
      _ ≤ (1-δ) * ((1-δ)^j * (smoothDivisorCorr 1 n - corr n)) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hd)
      _ = _ := by rw [pow_succ]; ring

theorem smoothDivisorCorr_geometric_error (n j : ℕ) :
    smoothDivisorCorr (j+1) n - corr n ≤
      (1-smoothMomentGap n)^j * (smoothDivisorCorr 1 n - corr n) :=
  smoothDivisorCorr_geometric_with_gap (smoothMomentGap_le_one n)
    (fun hp hq h hk => semiprime_ratio_le hp hq h hk) j

theorem smoothMoment_power_decay (n j : ℕ) :
    (1-smoothMomentGap n)^j ≤ 1/(1+(j:ℝ)*smoothMomentGap n) := by
  let d := smoothMomentGap n
  have hd : 0 ≤ d := (smoothMomentGap_pos n).le
  have hr : 0 ≤ 1-d := sub_nonneg.mpr (smoothMomentGap_le_one n)
  have h (i : ℕ) : (1-d)^i * (1+(i:ℝ)*d) ≤ 1 := by
    induction i with
    | zero => simp
    | succ i hi =>
      have he : (1-d)*(1+((i:ℝ)+1)*d) ≤ 1+(i:ℝ)*d := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (sq_nonneg d),sq_nonneg d]
      rw [Nat.cast_succ, pow_succ, mul_assoc]
      exact (mul_le_mul_of_nonneg_left he (pow_nonneg hr _)).trans hi
  apply (le_div_iff₀ (by positivity : 0 < 1+(j:ℝ)*d)).mpr
  exact h j

theorem smoothDivisorCorr_uniform_error (n : ℕ) :
    smoothDivisorCorr ((n+1)^6+1) n - 1/((n:ℝ)+1) ≤ corr n ∧
    corr n ≤ smoothDivisorCorr ((n+1)^6+1) n := by
  let x := (n:ℝ)+1
  let J := (n+1)^6
  have hx : 0 < x := by unfold x; positivity
  have hJ : (J:ℝ) = x^6 := by unfold J x; push_cast; rfl
  have hg : (J:ℝ) * smoothMomentGap n = x^4 := by
    rw [hJ]
    change x^6 * (1/x^2) = x^4
    rw [show x^6 = x^4*x^2 by ring, mul_assoc, mul_one_div_cancel (pow_ne_zero _ hx.ne'), mul_one]
  have hR : 0 ≤ corr n := Finset.sum_nonneg fun k _ => mul_nonneg (weight_nonneg k) (weight_nonneg _)
  have he0 : 0 ≤ smoothDivisorCorr 1 n - corr n :=
    sub_nonneg.mpr (corr_le_smoothDivisorCorr (by decide) n)
  have hcap : smoothDivisorCorr 1 n - corr n ≤ x^3 :=
    (sub_le_self _ hR).trans (smoothDivisorCorr_initial_cap n)
  have he : smoothDivisorCorr (J+1) n - corr n ≤ 1/x := calc
    _ ≤ (1-smoothMomentGap n)^J * (smoothDivisorCorr 1 n - corr n) :=
      smoothDivisorCorr_geometric_error n J
    _ ≤ (1/(1+(J:ℝ)*smoothMomentGap n)) * x^3 :=
      mul_le_mul (smoothMoment_power_decay n J) hcap he0 (by have := smoothMomentGap_pos n; positivity)
    _ ≤ 1/x := by
      rw [hg,mul_comm,← div_eq_mul_one_div]
      apply (div_le_div_iff₀ (by positivity) hx).mpr
      nlinarith
  exact ⟨by change smoothDivisorCorr (J+1) n - 1/x ≤ corr n; linarith only [he],
    corr_le_smoothDivisorCorr (by omega) n⟩

end FixedSmoothMomentRate

section SharpSmoothMomentRate

noncomputable def sharpSmoothGap (n : ℕ) : ℝ :=
  1 / ((Real.sqrt (n:ℝ)+1) * Real.log ((n:ℝ)+1))

theorem sharpSmoothGap_pos {n : ℕ} (hn : 0 < n) : 0 < sharpSmoothGap n := by
  have h : 1 < (n:ℝ)+1 := by exact_mod_cast (show 1 < n+1 by omega)
  unfold sharpSmoothGap
  exact one_div_pos.mpr (mul_pos (by positivity) (Real.log_pos h))

theorem sharpSmoothGap_le_one {n : ℕ} (hn : 0 < n) : sharpSmoothGap n ≤ 1 := by
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by simpa using hN)
  have hx : 0 < (n:ℝ)+1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hi : ((n:ℝ)+1)⁻¹ ≤ 1/2 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hL : 1/2 ≤ Real.log ((n:ℝ)+1) := by linarith
  have hD : 1 ≤ (Real.sqrt (n:ℝ)+1) * Real.log ((n:ℝ)+1) := by
    have he := mul_le_mul (by linarith : (2:ℝ) ≤ Real.sqrt (n:ℝ)+1) hL
      (by norm_num) (by positivity)
    linarith
  exact (div_le_one (by linarith : 0 < (Real.sqrt (n:ℝ)+1) * Real.log ((n:ℝ)+1))).mpr hD

theorem sharpSmoothGap_admissible (n : ℕ) : AdmitsSmoothGap n (sharpSmoothGap n) := by
  intro p q hp hq hpq hk
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hp1 : 0 < (p:ℝ)+1 := by positivity
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hsum : Real.log (p*q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne']
  have hLp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hLq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlt : (p:ℝ)+1 ≤ q := by exact_mod_cast hpq
  have hlogstep : 1/((p:ℝ)+1) ≤ Real.log q - Real.log p := by
    have h := Real.log_le_sub_one_of_pos (div_pos hp0 hp1)
    rw [Real.log_div hp0.ne' hp1.ne'] at h
    have hl := Real.log_le_log hp1 hlt
    have he : 1/((p:ℝ)+1) = 1-(p:ℝ)/((p:ℝ)+1) := by field_simp; ring
    linarith
  have hsqrt : (p:ℝ) ≤ Real.sqrt (n:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show p^2 ≤ n by rw [sq]; exact (Nat.mul_le_mul_left p hpq.le).trans hk)
  have hn : 0 < n := (Nat.mul_pos hp.pos hq.pos).trans_le hk
  have Lpos : 0 < Real.log ((n:ℝ)+1) := Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))
  have hL := Real.log_le_log (by exact_mod_cast Nat.mul_pos hp.pos hq.pos : 0 < ((p*q:ℕ):ℝ))
    (by exact_mod_cast (show p*q ≤ n+1 by omega) : ((p*q:ℕ):ℝ) ≤ (n:ℝ)+1)
  have hgap : sharpSmoothGap n * Real.log (p*q : ℕ) ≤ Real.log q - Real.log p := calc
    _ ≤ sharpSmoothGap n * Real.log ((n:ℝ)+1) :=
      mul_le_mul_of_nonneg_left hL (sharpSmoothGap_pos hn).le
    _ = 1/(Real.sqrt (n:ℝ)+1) := by
      unfold sharpSmoothGap
      have : 0 < Real.sqrt (n:ℝ)+1 := by positivity
      field_simp
    _ ≤ 1/((p:ℝ)+1) := one_div_le_one_div_of_le hp1 (by linarith)
    _ ≤ _ := hlogstep
  apply (div_le_iff₀ (by linarith : 0 < Real.log (p*q : ℕ)/2)).mpr
  nlinarith only [hgap,hsum]

theorem smoothDivisorCorr_sharp_geometric_error {n : ℕ} (hn : 0 < n) (j : ℕ) :
    smoothDivisorCorr (j+1) n - corr n ≤
      (1-sharpSmoothGap n)^j * (smoothDivisorCorr 1 n - corr n) :=
  smoothDivisorCorr_geometric_with_gap (sharpSmoothGap_le_one hn) (sharpSmoothGap_admissible n) j

noncomputable def sharpSmoothMomentIndex (n : ℕ) : ℕ :=
  ⌈4*(Real.sqrt (n:ℝ)+1)*(Real.log ((n:ℝ)+1))^2⌉₊

theorem smoothDivisorCorr_sharp_uniform_error (n : ℕ) :
    smoothDivisorCorr (sharpSmoothMomentIndex n + 1) n - 1/((n:ℝ)+1) ≤ corr n ∧
      corr n ≤ smoothDivisorCorr (sharpSmoothMomentIndex n + 1) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [sharpSmoothMomentIndex,smoothDivisorCorr,corr,weight,smoothDivisorWeight]
  let x := (n:ℝ)+1
  let L := Real.log x
  let y := Real.sqrt (n:ℝ)+1
  let d := sharpSmoothGap n
  let J := sharpSmoothMomentIndex n
  have hx : 0 < x := by unfold x; positivity
  have hL : 0 < L := Real.log_pos (by unfold x; exact_mod_cast (show 1 < n+1 by omega))
  have hy : 0 < y := by unfold y; positivity
  have hd : 0 < d := sharpSmoothGap_pos hn
  have hscale : 4*y*L^2*d = 4*L := by
    change 4*y*L^2*(1/(y*L)) = 4*L
    field_simp
  have hJd : 4*L ≤ (J:ℝ)*d := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil (4*y*L^2)) hd.le
  have hpow : (1-d)^J ≤ 1/x^4 := calc
    _ ≤ (Real.exp (-d))^J := pow_le_pow_left₀ (sub_nonneg.mpr (sharpSmoothGap_le_one hn))
      (by linarith only [Real.add_one_le_exp (-d)]) _
    _ = Real.exp (-(J:ℝ)*d) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(4*L)) := Real.exp_le_exp.mpr (by linarith only [hJd])
    _ = 1/x^4 := by
      rw [Real.exp_neg,show 4*L = ((4:ℕ):ℝ)*L by norm_num,Real.exp_nat_mul,Real.exp_log hx]
      simp only [one_div]
  have hR : 0 ≤ corr n := Finset.sum_nonneg fun k _ => mul_nonneg (weight_nonneg k) (weight_nonneg _)
  have he0 : 0 ≤ smoothDivisorCorr 1 n - corr n := sub_nonneg.mpr (corr_le_smoothDivisorCorr (by decide) n)
  have hcap : smoothDivisorCorr 1 n - corr n ≤ x^3 :=
    (sub_le_self _ hR).trans (smoothDivisorCorr_initial_cap n)
  have he : smoothDivisorCorr (J+1) n - corr n ≤ 1/x := calc
    _ ≤ (1-d)^J * (smoothDivisorCorr 1 n - corr n) := smoothDivisorCorr_sharp_geometric_error hn J
    _ ≤ (1/x^4)*x^3 := mul_le_mul hpow hcap he0 (by positivity)
    _ = 1/x := by field_simp
  exact ⟨by change smoothDivisorCorr (J+1) n - 1/x ≤ corr n; linarith only [he],
    corr_le_smoothDivisorCorr (by omega) n⟩

end SharpSmoothMomentRate

section FiniteLowerKernel

private theorem smoothDivisorRatio_nonprime {k n : ℕ} {δ : ℝ} (hh : δ ≤ 1) (hg : AdmitsSmoothGap n δ) (hk : k ≤ n) (hn : ¬ k.Prime) :
    smoothDivisorRatio k ≤ 1 - δ := by
  have hpos := (weight_nonneg k).trans (weight_le_smoothDivisorWeight (j := 1) (by decide) k)
  by_cases hz : smoothDivisorWeight 1 k = 0
  · simp only [smoothDivisorRatio, hz, div_zero]
    exact sub_nonneg.mpr hh
  · exact (div_le_iff₀ (lt_of_le_of_ne hpos (Ne.symm hz))).mpr
      (smoothDivisorWeight_nonprime_contract_with_gap (j := 1) hg (by decide) hk hn)

/-- A polynomial nonpositive on the entire nonprime spectrum and at most
one at the prime endpoint gives a finite lower certificate at a target. -/
theorem filtered_smoothDivisorCorr_le_corr (n : ℕ) {δ : ℝ} (hh : δ ≤ 1) (hg : AdmitsSmoothGap n δ) (D : Finset ℕ) (b : ℕ → ℝ)
    (hnon : ∀ x : ℝ, 0 ≤ x → x ≤ 1 - δ → ∑ j ∈ D, b j * x^j ≤ 0)
    (hone : ∑ j ∈ D, b j ≤ 1) :
    ∑ j ∈ D, b j * smoothDivisorCorr (j+1) n ≤ corr n := by
  unfold smoothDivisorCorr
  rw [smooth_pair_kernel_expansion]
  apply Finset.sum_le_sum
  intro k hk
  have h1 := smoothDivisorRatio_bounds k
  have h2 := smoothDivisorRatio_bounds (n-k)
  have hpot (l : ℕ) := (weight_nonneg l).trans (weight_le_smoothDivisorWeight (j := 1) (by decide) l)
  have hnon' (hprod : smoothDivisorRatio k * smoothDivisorRatio (n-k) ≤ 1 - δ) :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hpot k) (hpot (n-k)))
      (hnon _ (mul_nonneg h1.1 h2.1) hprod)
  by_cases hp : k.Prime
  · by_cases hq : (n-k).Prime
    · rw [smoothDivisorRatio_prime hp, smoothDivisorRatio_prime hq]
      simp only [mul_one, one_pow, weight, ite_eq_left hp, ite_eq_left hq,
        smoothDivisorWeight_prime 1 hp, smoothDivisorWeight_prime 1 hq]
      exact mul_le_of_le_one_right
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))
          (Real.log_nonneg (by exact_mod_cast hq.one_le))) hone
    · simp only [weight, ite_eq_right hq, mul_zero]
      exact hnon' ((mul_le_of_le_one_left h2.1 h1.2).trans
        (smoothDivisorRatio_nonprime hh hg (Nat.sub_le n k) hq))
  · simp only [weight, ite_eq_right hp, zero_mul]
    have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
    exact hnon' ((mul_le_of_le_one_right h1.1 h2.2).trans (smoothDivisorRatio_nonprime hh hg hkn hp))

end FiniteLowerKernel

section ChebyshevMomentBounds
open Polynomial

noncomputable def smoothPolynomialMoment (n : ℕ) (f : Polynomial ℝ) : ℝ :=
  ∑ j ∈ f.support, f.coeff j * smoothDivisorCorr (j+1) n

private theorem eval_from_support (f : Polynomial ℝ) (x : ℝ) :
    (∑ j ∈ f.support, f.coeff j * x^j) = f.eval x :=
  f.eval_eq_sum.symm

private theorem polyMoment_upper (n : ℕ) (f : Polynomial ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ f.eval x) (h1 : 1 ≤ f.eval 1) :
    corr n ≤ smoothPolynomialMoment n f := by
  apply corr_le_filtered_smoothDivisorCorr
  · intro x hx hx'
    rw [eval_from_support]
    exact h x hx hx'
  · simpa only [← eval_from_support, one_pow, mul_one] using h1

private theorem polyMoment_lower (n : ℕ) {δ : ℝ} (hh : δ ≤ 1) (hg : AdmitsSmoothGap n δ) (f : Polynomial ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1-δ → f.eval x ≤ 0) (h1 : f.eval 1 ≤ 1) :
    smoothPolynomialMoment n f ≤ corr n := by
  apply filtered_smoothDivisorCorr_le_corr n hh hg
  · intro x hx hx'
    rw [eval_from_support]
    exact h x hx hx'
  · simpa only [← eval_from_support, one_pow, mul_one] using h1

/-- Map the nonprime interval [0,r] to [-1,1]. -/
noncomputable def scaledChebyshev (r : ℝ) (d : ℤ) : Polynomial ℝ :=
  (Chebyshev.T ℝ d).comp (C (2/r)*X-1)

private theorem scaledChebyshev_eval (r x : ℝ) (d : ℤ) :
    (scaledChebyshev r d).eval x = (Chebyshev.T ℝ d).eval ((2/r)*x-1) := by
  simp [scaledChebyshev]

noncomputable def lowerChebyshevFilter (r : ℝ) (d : ℤ) : Polynomial ℝ :=
  let f := scaledChebyshev r d
  C (1 / (f.eval 1 ^ 2 - 1)) * (f^2 - 1)

noncomputable def upperChebyshevFilter (r : ℝ) (d : ℤ) : Polynomial ℝ :=
  let f := scaledChebyshev r d
  C (1 / f.eval 1 ^ 2) * f^2

theorem chebyshev_smooth_moment_bracket (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {δ : ℝ} (hh : δ ≤ 1) (hg : AdmitsSmoothGap n δ) (hgap : 1-δ ≤ r) {d : ℤ} (hd : d ≠ 0) :
    smoothPolynomialMoment n (lowerChebyshevFilter r d) ≤ corr n ∧
      corr n ≤ smoothPolynomialMoment n (upperChebyshevFilter r d) := by
  have ht : 1 < 2/r-1 := by
    have hdiv : 2 < 2/r := (lt_div_iff₀ hr).mpr (by linarith)
    linarith
  have hB : 1 < (scaledChebyshev r d).eval 1 := by
    simpa only [scaledChebyshev_eval, mul_one] using Chebyshev.one_lt_eval_T_real hd ht
  have hBsq : 0 < ((scaledChebyshev r d).eval 1)^2-1 := by nlinarith [sq_nonneg ((scaledChebyshev r d).eval 1-1)]
  constructor
  · apply polyMoment_lower n hh hg
    · intro x hx hx'
      have hscaled : (2/r)*x = (2*x)/r := by ring
      have hxlo : 0 ≤ (2/r)*x := mul_nonneg (by positivity) hx
      have hxhi : (2/r)*x ≤ 2 := by
        rw [hscaled, div_le_iff₀ hr]
        linarith [hx'.trans hgap]
      have habs : |(2/r)*x-1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hT := (abs_le.mp (Chebyshev.abs_eval_T_real_le_one d habs))
      have hX : ((scaledChebyshev r d).eval x)^2 ≤ 1 := by
        rw [scaledChebyshev_eval]
        nlinarith [mul_nonneg (by linarith only [hT.1] : 0 ≤ (Chebyshev.T ℝ d).eval ((2/r)*x-1)+1)
          (by linarith only [hT.2] : 0 ≤ 1-(Chebyshev.T ℝ d).eval ((2/r)*x-1))]
      simp only [lowerChebyshevFilter, eval_mul, eval_C, eval_sub, eval_pow, eval_one]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_nonneg.mpr hBsq.le) (sub_nonpos.mpr hX)
    · simp [lowerChebyshevFilter, hBsq.ne']
  · apply polyMoment_upper
    · intro x _ _
      simp only [upperChebyshevFilter, eval_mul, eval_C, eval_pow]
      positivity
    · have hn : (scaledChebyshev r d).eval 1 ≠ 0 := by linarith
      simp [upperChebyshevFilter, hn]

theorem corr_between_chebyshev_moments (n : ℕ) (hn : 0 < n) {d : ℕ} (hd : 0 < d) :
    let r := 1 - sharpSmoothGap n/2
    smoothPolynomialMoment n (lowerChebyshevFilter r d) ≤ corr n ∧
      corr n ≤ smoothPolynomialMoment n (upperChebyshevFilter r d) := by
  dsimp only
  have hpos := sharpSmoothGap_pos hn
  have hu := sharpSmoothGap_le_one hn
  apply chebyshev_smooth_moment_bracket n (by linarith) (by linarith) hu (sharpSmoothGap_admissible n) (by linarith)
  exact_mod_cast hd.ne'

private theorem smoothPolynomialMoment_eval (n : ℕ) (f : Polynomial ℝ) :
    smoothPolynomialMoment n f =
      ∑ k ∈ Finset.range (n+1), smoothDivisorWeight 1 k * smoothDivisorWeight 1 (n-k) *
        f.eval (smoothDivisorRatio k * smoothDivisorRatio (n-k)) := by
  unfold smoothPolynomialMoment smoothDivisorCorr
  rw [smooth_pair_kernel_expansion]
  simp only [eval_from_support]

/-- The difference of the two finite certificates has an explicit upper
bound in terms of the value of the polynomial at the prime endpoint. -/
theorem chebyshev_smooth_moment_width (n : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {d : ℤ} (hd : d ≠ 0) :
    smoothPolynomialMoment n (upperChebyshevFilter r d) -
        smoothPolynomialMoment n (lowerChebyshevFilter r d) ≤
      smoothDivisorCorr 1 n / (((scaledChebyshev r d).eval 1)^2 - 1) := by
  let B := (scaledChebyshev r d).eval 1
  have ht : 1 < 2/r-1 := by
    have hdiv : 2 < 2/r := (lt_div_iff₀ hr).mpr (by linarith)
    linarith
  have hB : 1 < B := by
    simpa only [B, scaledChebyshev_eval, mul_one] using Chebyshev.one_lt_eval_T_real hd ht
  have hBs : 0 < B^2-1 := by nlinarith [sq_nonneg (B-1)]
  have hB0 : B ≠ 0 := by linarith
  rw [smoothPolynomialMoment_eval, smoothPolynomialMoment_eval, ← Finset.sum_sub_distrib]
  unfold smoothDivisorCorr
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k _
  let w := smoothDivisorWeight 1 k * smoothDivisorWeight 1 (n-k)
  let x := smoothDivisorRatio k * smoothDivisorRatio (n-k)
  let z := (scaledChebyshev r d).eval x
  have hpot (l : ℕ) := (weight_nonneg l).trans (weight_le_smoothDivisorWeight (j := 1) (by decide) l)
  have hw : 0 ≤ w := mul_nonneg (hpot k) (hpot (n-k))
  simp only [lowerChebyshevFilter, upperChebyshevFilter, eval_mul, eval_C, eval_pow, eval_sub, eval_one]
  change w * (1/B^2 * z^2) - w * (1/(B^2-1) * (z^2-1)) ≤ w / (B^2-1)
  have hident : (w * (1/B^2 * z^2) - w * (1/(B^2-1) * (z^2-1))) * (B^2-1)
      = w - w*z^2/B^2 := by
    field_simp [hBs.ne', hB0]
    ring
  apply (le_div_iff₀ hBs).mpr
  rw [hident]
  exact sub_le_self _ (div_nonneg (mul_nonneg hw (sq_nonneg _)) (sq_nonneg _))

end ChebyshevMomentBounds


/-!
## Uniformity in n and a bound from finitely many moments

For each fixed j >= 1 the unnormalised unboundedness proved in Lean above
also holds after division by n, by the following argument on paper.
Choose any fixed even W, and let X tend to infinity before W is increased.
Write s=j+1. Take primes
  X^(1/2-1/(8s)) <= a <= X^(1/2-1/(16s)),
and choose a prime b so that m=ab lies in [0.55X,0.60X]. Eventually
b>a, so the pair is counted once. The ordinary prime number theorem,
uniformly for this fixed ratio of endpoints as X/a tends to infinity,
gives >> X/(a log X) choices of b. Partial summation gives a prime
reciprocal sum >> 1/s over the displayed range, with absolute implied
constant and an X threshold allowed to depend on j. Here
t=2 log a / log m >= 1-1/(4s), so Bernoulli's inequality gives
t^s >= 3/4. Thus each semiprime has weight >> log X. For each m,
the prime number theorem in the fixed reduced class -m modulo W gives
weighted mass >> X/phi(W) from primes p in [0.55X,0.60X].
All pairs contribute to H_j(p+m)-corr(p+m) as genuine mixed terms.
There are O(X/W) possible sums. At some even n divisible by W in
[1.10X,1.20X] we obtain
  (H_j(n)-corr(n))/n >> W/(phi(W)(j+1)).
Taking arbitrarily large fixed primorials W proves the asserted infinite
limsup for each fixed j. This quantifier order coexists with the o(n)
estimate above for j=ceil((log log n)^2).

There are also lower filters with a finite degree choice for each n.
For n>=4 the nonprime ratios on a nonzero term are separated from one
by at least delta=1/((sqrt(n)+1)log n). Indeed if k=ab<=n with
a<b prime, log(b/a)>=log(1+1/a)>=1/(a+1), a<=sqrt(n).
A product of two ratios with a nonprime entry is likewise at most
rho=1-delta. Pairs of primes have ratio one. For the Chebyshev
polynomial T_d put
  Q(x)=(T_d(2x/rho-1)/T_d(2/rho-1))^2,  eps=1/T_d(2/rho-1)^2.
On [0,rho] we have 0<=Q<=eps, and Q(1)=1. Consequently Q is an
upper filter and (Q-eps)/(1-eps) a lower filter for the prime mass
when d>=1. Each is an explicit signed linear combination of H_1
through H_(2d+1) by smooth_pair_kernel_expansion. From
  arcosh((1+delta)/(1-delta))=2 artanh(sqrt(delta))>=2 sqrt(delta)
one gets eps <= 4 exp(-4d sqrt(delta)). Since H_1(n) <= (n+1)log^2 n,
taking d >= 3 log(n+1)/sqrt(delta) makes the error of either filter
less than 1/n for n>=4. The displayed degree choice is a paper calculation. Lean proves the
square-root spectral gap with log(n+1) in the denominator, the
polynomial brackets, and their width in terms of the endpoint value B.
The elementary gap 1/(n+1)^2 also suffices for the two-moment test. A lower estimate of order n for any of these
finite certificates over all sufficiently large even n remains to be proved.
-/

open scoped BigOperators
open Finset ExtendedArcCoefficient

private theorem arc_dual_delta {q : ℕ} [NeZero q] (u b : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, star (χ (u : ZMod q)) * χ (b : ZMod q)) =
      if u = b then (q.totient : ℂ) else 0 := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩, rootsOfUnity.isCyclic ..⟩
  have hu (χ : DirichletCharacter ℂ q) : star (χ (u : ZMod q)) = χ ((u : ZMod q)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  simp_rw [hu]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
  congr 1
  exact propext ⟨Units.ext, fun he => congrArg Units.val he⟩

private theorem arc_gauss_inversion (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, unitGaussCoefficient q χ * star (χ (u : ZMod q))) =
      (q.totient : ℂ) * E (((u : ZMod q).val : ℝ) / q) := by
  classical
  unfold unitGaussCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h (b : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
      Complex.exp (((2 * Real.pi * ((b : ZMod q).val : ℝ) / q : ℝ) : ℂ) * Complex.I) *
        χ (b : ZMod q) * star (χ (u : ZMod q)) =
        E (((b : ZMod q).val : ℝ) / q) * (star (χ (u : ZMod q)) * χ (b : ZMod q)) := by
    simp only [E, mul_div_assoc]
    ring
  simp_rw [h, ← Finset.mul_sum, arc_dual_delta]
  simp [mul_comm]

private theorem arc_E_nat (d : ℕ) : E (d : ℝ) = 1 := by
  unfold E
  push_cast
  convert Complex.exp_nat_mul_two_pi_mul_I d using 2; ring

private theorem arc_E_mod_div (d q : ℕ) [NeZero q] :
    E (((d % q : ℕ) : ℝ) / q) = E ((d : ℝ) / q) := by
  have hnum : (d : ℝ) = ((d % q : ℕ) : ℝ) + (q : ℝ) * ((d / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div d q).symm
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have he : (d : ℝ) / q = ((d % q : ℕ) : ℝ) / q + ((d / q : ℕ) : ℝ) := by
    field_simp
    linarith [hnum, mul_comm (q : ℝ) ((d / q : ℕ) : ℝ)]
  rw [he, phase_add, arc_E_nat, mul_one]

private theorem arc_Gauss_single (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (k : ℕ) :
    dirichletArcErrorRow q (fun χ => star (χ (k : ZMod q))) a =
      if k.Coprime q then E ((k : ℝ) * ((a : ZMod q).val : ℝ) / q) else 0 := by
  classical
  by_cases h : k.Coprime q
  · rw [ite_eq_left h]
    let v := (ZMod.unitOfCoprime k h)
    have hv : (v : ZMod q) = (k : ZMod q) := ZMod.coe_unitOfCoprime _ _
    have hnz : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    have hs (χ : DirichletCharacter ℂ q) :
        (unitGaussCoefficient q χ * star (χ (k : ZMod q)) / (q.totient : ℂ)) *
          star (χ (a : ZMod q)) =
        (unitGaussCoefficient q χ * star (χ ((a * v : (ZMod q)ˣ) : ZMod q))) / (q.totient : ℂ) := by
      simp [Units.val_mul, map_mul, hv, star_mul]; ring
    unfold dirichletArcErrorRow
    simp_rw [hs]
    rw [← Finset.sum_div, arc_gauss_inversion, mul_div_cancel_left₀ _ hnz]
    have heq : ((a * v : (ZMod q)ˣ) : ZMod q) = ((((a : ZMod q).val * k : ℕ) : ZMod q)) := by
      push_cast
      simp [hv]
    rw [heq, ZMod.val_natCast, arc_E_mod_div]
    push_cast
    rw [mul_comm]
  · rw [ite_eq_right h]
    have hn : ¬ IsUnit (k : ZMod q) := fun hu => h ((ZMod.isUnit_iff_coprime k q).mp hu)
    simp [dirichletArcErrorRow, fun χ : DirichletCharacter ℂ q => χ.map_nonunit hn]

noncomputable def weightedArcCharacterSum (q : ℕ) [NeZero q] (s : Finset ℕ) (w : ℕ → ℂ)
    (β : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ s, (w k * E ((k : ℝ) * β)) * star (χ (k : ZMod q))

theorem dirichletArcErrorRow_weighted (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (s : Finset ℕ)
    (w : ℕ → ℂ) (β : ℝ) :
    dirichletArcErrorRow q (weightedArcCharacterSum q s w β) a =
    ∑ k ∈ s.filter (fun k => k.Coprime q), w k * E ((k : ℝ) * (β + ((a : ZMod q).val : ℝ) / q)) := by
  classical
  have hlin (χ : DirichletCharacter ℂ q) :
      (unitGaussCoefficient q χ * weightedArcCharacterSum q s w β χ / (q.totient : ℂ)) * star (χ (a : ZMod q)) =
      ∑ k ∈ s, (w k * E ((k : ℝ) * β)) *
        ((unitGaussCoefficient q χ * star (χ (k : ZMod q)) / (q.totient : ℂ)) * star (χ (a : ZMod q))) := by
    simp only [weightedArcCharacterSum, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold dirichletArcErrorRow
  simp_rw [hlin]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ k ∈ s, w k * E ((k : ℝ) * β) * dirichletArcErrorRow q (fun χ => star (χ (k : ZMod q))) a) = _
  simp_rw [arc_Gauss_single]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [mul_add, phase_add, ← mul_div_assoc, mul_assoc]

open Classical in
noncomputable def centeredPrimeArcTransform (q : ℕ) [NeZero q] (n : ℕ) (β : ℝ)
    (M : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  weightedArcCharacterSum q (Finset.range (n+1)) (fun k => (weight k : ℂ)) β χ -
    (if χ = 1 then M else 0)

open Classical in
theorem dirichletArcErrorRow_sub_principal (q : ℕ) [NeZero q] (a : (ZMod q)ˣ)
    (T : DirichletCharacter ℂ q → ℂ) (M : ℂ) :
    dirichletArcErrorRow q (fun χ => T χ - (if χ = 1 then M else 0)) a =
      dirichletArcErrorRow q T a - unitGaussCoefficient q 1 * M / (q.totient : ℂ) := by
  classical
  unfold dirichletArcErrorRow
  simp only [mul_sub, sub_div, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
  · simp [MulChar.one_apply_coe]
  · intro b _ hb
    simp [hb]
  · simp

theorem primeArc_nonunit_remainder_bound (q : ℕ) [NeZero q] (n : ℕ) (t : ℝ) :
    ‖∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ k.Coprime q),
      (weight k : ℂ) * E ((k : ℝ) * t)‖ ≤ Real.log (q : ℝ) := by
  classical
  let s := (Finset.range (n+1)).filter (fun k => ¬ k.Coprime q)
  have hs : s.filter Nat.Prime ⊆ q.primeFactors := by
    intro p hp
    obtain ⟨hm, hprime⟩ := Finset.mem_filter.mp hp
    have hnc := (Finset.mem_filter.mp hm).2
    exact Nat.mem_primeFactors.mpr ⟨hprime, hprime.dvd_iff_not_coprime.mpr hnc, NeZero.ne q⟩
  have hn (k : ℕ) : ‖(weight k : ℂ) * E ((k : ℝ) * t)‖ = weight k := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg _)]
    have he : ‖E ((k : ℝ) * t)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [he, mul_one]
  calc
    _ ≤ ∑ k ∈ s, ‖(weight k : ℂ) * E ((k : ℝ) * t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ s.filter Nat.Prime, Real.log (k : ℝ) := by
      simp_rw [hn]
      simp only [Finset.sum_filter, weight]
    _ ≤ ∑ k ∈ q.primeFactors, Real.log (k : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
    _ ≤ Real.log (q : ℝ) := prime_factor_log_sum_le q

theorem primeArc_centered_remainder (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (n : ℕ) (β : ℝ) (M : ℂ) :
    ‖(∑ k ∈ Finset.range (n+1), (weight k : ℂ) * E ((k : ℝ) * (β + ((a : ZMod q).val : ℝ) / q))) -
      unitGaussCoefficient q 1 * M / (q.totient : ℂ) -
      dirichletArcErrorRow q (centeredPrimeArcTransform q n β M) a‖ ≤ Real.log (q : ℝ) := by
  classical
  unfold centeredPrimeArcTransform
  rw [dirichletArcErrorRow_sub_principal, dirichletArcErrorRow_weighted]
  let f := fun k : ℕ => (weight k : ℂ) * E ((k : ℝ) * (β + ((a : ZMod q).val : ℝ) / q))
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1)) (fun k => k.Coprime q) f
  rw [show (∑ k ∈ Finset.range (n+1), f k) =
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime q), f k) +
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ k.Coprime q), f k) from hs.symm]
  convert primeArc_nonunit_remainder_bound q n (β + ((a : ZMod q).val : ℝ) / q) using 2
  dsimp only [f]
  abel

noncomputable def primeArcModelDiscrepancy (q : ℕ) [NeZero q] (a : (ZMod q)ˣ)
    (n : ℕ) (β : ℝ) (M : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n+1), (weight k : ℂ) * E ((k : ℝ) * (β + ((a : ZMod q).val : ℝ) / q))) -
    unitGaussCoefficient q 1 * M / (q.totient : ℂ)

private theorem arc_norm_sq_le_of_residual {v d : ℂ} {L : ℝ} (h : ‖v - d‖ ≤ L) :
    ‖v‖^2 ≤ 2 * ‖d‖^2 + 2 * L^2 := by
  have hb : ‖v‖ ≤ L + ‖d‖ :=
    calc
      ‖v‖ = ‖(v - d) + d‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - d‖ + ‖d‖ := norm_add_le _ _
      _ ≤ L + ‖d‖ := add_le_add h le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg v) ((norm_nonneg v).trans hb)).mpr hb
  nlinarith only [hs, sq_nonneg (L - ‖d‖)]

theorem primeArcModelDiscrepancy_energy_le (q : ℕ) [NeZero q] (n : ℕ) (β : ℝ) (M : ℂ) :
    (∑ a, ‖primeArcModelDiscrepancy q a n β M‖^2) ≤
      2 * ((∑ χ, ‖unitGaussCoefficient q χ‖^2 * ‖centeredPrimeArcTransform q n β M χ‖^2) / (q.totient : ℝ)) +
      (q.totient : ℝ) * (2 * (Real.log q)^2) := by
  classical
  let D := dirichletArcErrorRow q (centeredPrimeArcTransform q n β M)
  let F := fun a => primeArcModelDiscrepancy q a n β M
  have hrow (a : (ZMod q)ˣ) : ‖F a‖^2 ≤ 2 * ‖D a‖^2 + 2 * (Real.log q)^2 :=
    arc_norm_sq_le_of_residual (v := F a) (d := D a) (primeArc_centered_remainder q a n β M)
  calc
    _ ≤ ∑ a, (2 * ‖D a‖^2 + 2 * (Real.log q)^2) := Finset.sum_le_sum fun a _ => hrow a
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [D, dirichletArcErrorRow_energy, ZMod.card_units_eq_totient, nsmul_eq_mul]

open MeasureTheory
namespace ModThreeMinor

/-- The primitive real character modulo three, including its value at multiples of three. -/
def character (p : ℕ) : ℂ :=
  if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1

/-- Prime logarithms with the sole prime dividing the conductor omitted. -/
noncomputable def primeWeight (p : ℕ) : ℂ :=
  if p.Prime ∧ p ≠ 3 then (Real.log p : ℂ) else 0

@[simp] theorem primeWeight_three : primeWeight 3 = 0 := by simp [primeWeight]
@[simp] theorem primeWeight_two : primeWeight 2 = (Real.log 2 : ℂ) := by
  simp [primeWeight, Nat.prime_two]
@[simp] theorem character_three : character 3 = 0 := by norm_num [character]
@[simp] theorem character_two : character 2 = -1 := by norm_num [character]

noncomputable def mode (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((((k : ℝ) * t : ℝ) : ℂ) * (2 * Real.pi * Complex.I))

private theorem mode_shift (k : ℤ) (t u : ℝ) :
    mode k (t + u) = mode k t * mode k u := by
  unfold mode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem mode_period (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  rw [mode_shift]
  simp [mode, Complex.exp_int_mul_two_pi_mul_I]

private theorem third_mode_ne {k : ℤ} (hk : ¬ 3 ∣ k) : mode k (1/3) ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp h
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hR : (k : ℝ) * (1/3) = (z : ℝ) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_intCast] using mul_right_cancel₀ hC hz
  apply hk
  refine ⟨z, ?_⟩
  exact_mod_cast (show (k : ℝ) = 3 * (z : ℝ) by linarith)

noncomputable def coefficient (s : Set ℝ) (k : ℤ) : ℂ :=
  ∫ t in (0:ℝ)..1, s.indicator (mode k) t

/-- A one-third-periodic domain annihilates every other integral Fourier mode. -/
theorem coefficient_zero (s : Set ℝ) (hs : ∀ t, t + 1/3 ∈ s ↔ t ∈ s)
    (k : ℤ) (hk : ¬ 3 ∣ k) : coefficient s k = 0 := by
  classical
  let g := s.indicator (mode k)
  have hper3 : Function.Periodic (fun t : ℝ => t ∈ s) (1/3) := by
    intro t
    exact propext (hs t)
  have hper1 : Function.Periodic (fun t : ℝ => t ∈ s) 1 := by
    simpa using hper3.nsmul 3
  have hG : Function.Periodic g 1 := by
    intro t
    have hm : t+1 ∈ s ↔ t ∈ s := Iff.of_eq (hper1 t)
    simp [g, Set.indicator_apply, hm, mode_period k t]
  have hstep (t : ℝ) : g (t + 1/3) = mode k (1/3) * g t := by
    by_cases ht : t ∈ s
    · simp only [g, Set.indicator_of_mem ht, Set.indicator_of_mem ((hs t).mpr ht), mode_shift]
      exact mul_comm _ _
    · simp only [g, Set.indicator_of_notMem ht, Set.indicator_of_notMem (mt (hs t).mp ht), mul_zero]
  have hI : (∫ t in (0:ℝ)..1, g (t + 1/3)) = coefficient s k := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [coefficient, g, add_comm] using (hG.intervalIntegral_add_eq (1/3) 0)
  simp_rw [hstep] at hI
  rw [intervalIntegral.integral_const_mul] at hI
  change mode k (1/3) * coefficient s k = coefficient s k at hI
  exact (mul_eq_zero.mp (show (mode k (1/3) - 1) * coefficient s k = 0 by
    rw [sub_mul, hI, one_mul, sub_self])).resolve_left (sub_ne_zero.mpr (third_mode_ne hk))

def sign (n : ℕ) : ℂ := if n % 3 = 0 then -1 else 1

private theorem prime_mod_ne_zero {p : ℕ} (h : p.Prime ∧ p ≠ 3) : p % 3 ≠ 0 := by
  intro he
  rcases h.1.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero he) with h1 | h3
  · omega
  · exact h.2 h3.symm

private theorem resonant_pair (n p q : ℕ) (h : (3 : ℤ) ∣ (p : ℤ) + q - n) :
    (character p * primeWeight p) * (character q * primeWeight q) =
      sign n * (primeWeight p * primeWeight q) := by
  by_cases hp : p.Prime ∧ p ≠ 3
  · by_cases hq : q.Prime ∧ q ≠ 3
    · have hp' := prime_mod_ne_zero hp
      have hq' := prime_mod_ne_zero hq
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h1 | h1 <;>
        rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h2 | h2
      all_goals
        have h0 : n % 3 = (p % 3 + q % 3) % 3 := by omega
        simp [character, sign, h0, h1, h2]
    · simp [primeWeight, hq]
  · simp [primeWeight, hp]

/-- The exponential sum with the sign convention exp(2πikt). -/
noncomputable def series (n : ℕ) (w : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (n+1), w p * mode p t

noncomputable def arcIntegral (s : Set ℝ) (n : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, s.indicator (fun x => series n w x ^ 2 * mode (-(n:ℤ)) x) t

set_option maxHeartbeats 1200000 in
private theorem expansion (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ) (w : ℕ → ℂ) :
    arcIntegral s n w = ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (n+1),
      (w p * w q) * coefficient s ((p : ℤ) + q - n) := by
  classical
  let T := fun (p q : ℕ) (t : ℝ) => w p * w q * s.indicator (mode ((p:ℤ)+q-n)) t
  have hI (p q : ℕ) : IntervalIntegrable (T p q) volume 0 1 := by
    have hc : Continuous (mode ((p:ℤ)+q-n)) := by unfold mode; fun_prop
    have hi := hc.intervalIntegrable («μ» := volume) 0 1
    have hcut : IntervalIntegrable (s.indicator (mode ((p:ℤ)+q-n))) volume 0 1 :=
      ⟨hi.1.indicator hs, hi.2.indicator hs⟩
    exact hcut.const_mul _
  have hmul (p q : ℕ) (t : ℝ) :
      mode p t * mode q t * mode (-(n:ℤ)) t = mode ((p:ℤ)+q-n) t := by
    unfold mode
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he (t : ℝ) : s.indicator (fun x => series n w x ^ 2 * mode (-(n:ℤ)) x) t =
      ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (n+1), T p q t := by
    by_cases ht : t ∈ s
    · simp only [Set.indicator_of_mem ht, series, sq, Finset.sum_mul, Finset.mul_sum, T]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← hmul]
      ring
    · simp [ht, T]
  unfold arcIntegral
  simp_rw [he]
  have hRow (p : ℕ) : IntervalIntegrable (fun t => ∑ q ∈ Finset.range (n+1), T p q t) volume 0 1 := by
    have Hfun : (fun t => ∑ q ∈ Finset.range (n+1), T p q t) = ∑ q ∈ Finset.range (n+1), T p q := by
      funext t
      rw [Finset.sum_apply]
    rw [Hfun]
    exact IntervalIntegrable.sum _ (fun q _ => hI p q)
  rw [intervalIntegral.integral_finsetSum (fun p _ => hRow p)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [intervalIntegral.integral_finsetSum (fun q _ => hI p q)]
  simp [T, coefficient, intervalIntegral.integral_const_mul]

/-- On any measurable one-third-periodic region, the twisted true prime square
is exactly the ordinary prime square times its residue-dependent sign. -/
theorem quadratic_arc_integral (s : Set ℝ) (hs : MeasurableSet s)
    (hper : ∀ t, t + 1/3 ∈ s ↔ t ∈ s) (n : ℕ) :
    arcIntegral s n (fun p => character p * primeWeight p) =
      sign n * arcIntegral s n primeWeight := by
  rw [expansion s hs, expansion s hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : (3:ℤ) ∣ (p:ℤ)+q-n
  · rw [resonant_pair n p q h, mul_assoc]
  · simp [coefficient_zero s hper _ h]

/-- The intersection of a circle region and its two one-third translates. -/
def core (s : Set ℝ) : Set ℝ :=
  {t | t ∈ s ∧ t + 1/3 ∈ s ∧ t + 2/3 ∈ s}

theorem core_measurable {s : Set ℝ} (hs : MeasurableSet s) : MeasurableSet (core s) :=
  hs.inter ((hs.preimage (measurable_id.add_const (1/3 : ℝ))).inter
    (hs.preimage (measurable_id.add_const (2/3 : ℝ))))

theorem core_periodic {s : Set ℝ} (h : ∀ t, t + 1 ∈ s ↔ t ∈ s) :
    ∀ t, t + 1/3 ∈ core s ↔ t ∈ core s := by
  intro t
  change (_ ∈ s ∧ _ ∈ s ∧ _ ∈ s) ↔ (_ ∈ s ∧ _ ∈ s ∧ _ ∈ s)
  rw [show t + 1/3 + 1/3 = t+2/3 by ring, show t + 1/3 + 2/3 = t+1 by ring, h t]
  tauto

/-- The missing measure is represented by the real deficit indicator on a period. -/
noncomputable def missing (s : Set ℝ) : ℝ → ℝ := sᶜ.indicator (fun _ => (1 : ℝ))

private theorem missing_integrable {s : Set ℝ} (hs : MeasurableSet s) (a b : ℝ) :
    IntervalIntegrable (missing s) volume a b := by
  have hi : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  exact ⟨hi.1.indicator hs.compl, hi.2.indicator hs.compl⟩

/-- A near-full starting region stays near-full, with at most three times its deficit. -/
theorem core_missing_le {s : Set ℝ} (hs : MeasurableSet s) (hp : ∀ t, t + 1 ∈ s ↔ t ∈ s) :
    (∫ t in (0:ℝ)..1, missing (core s) t) ≤ 3 * (∫ t in (0:ℝ)..1, missing s t) := by
  classical
  let f := missing s
  have hF : Function.Periodic f 1 := by
    intro t
    simp [f, missing, Set.indicator_apply, hp t]
  have hmove (d : ℝ) : (∫ t in (0:ℝ)..1, f (t+d)) = ∫ t in (0:ℝ)..1, f t := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [add_comm] using (hF.intervalIntegral_add_eq d 0)
  have hI (d : ℝ) : IntervalIntegrable (fun t => f (t+d)) volume 0 1 := by
    have h := (missing_integrable hs (0+d) (1+d)).comp_add_right d
    simpa [f] using h
  have hbound (t : ℝ) : missing (core s) t ≤ f t + f (t+1/3) + f (t+2/3) := by
    by_cases h0 : t ∈ s <;> by_cases h1 : t + 1/3 ∈ s <;> by_cases h2 : t + 2/3 ∈ s <;>
      simp only [f, missing, Set.indicator_apply, Set.mem_compl_iff, core, Set.mem_ofPred_eq,
        h0, h1, h2, and_false, and_true, not_false_eq_true, not_true_eq_false, ite_true, ite_false] <;> norm_num
  calc
    _ ≤ ∫ t in (0:ℝ)..1, f t + f (t+1/3) + f (t+2/3) :=
      intervalIntegral.integral_mono (by norm_num) (missing_integrable (core_measurable hs) _ _)
        (((missing_integrable hs _ _).add (hI _)).add (hI _)) hbound
    _ = _ := by
      rw [intervalIntegral.integral_add ((missing_integrable hs _ _).add (hI _)) (hI _),
        intervalIntegral.integral_add (missing_integrable hs _ _) (hI _), hmove, hmove]
      ring

/-- On one period the deficit is exactly the Lebesgue measure of the omitted set. -/
theorem missing_integral {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ t in (0:ℝ)..1, missing s t) = (volume (sᶜ ∩ Set.Ioo (0:ℝ) 1)).toReal := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo, missing, integral_indicator_const _ hs.compl,
    measureReal_def, Measure.restrict_apply hs.compl]
  simp

theorem quadratic_minor_core {s : Set ℝ} (hs : MeasurableSet s)
    (hp : ∀ t, t + 1 ∈ s ↔ t ∈ s) (n : ℕ) :
    arcIntegral (core s) n (fun p => character p * primeWeight p) =
      sign n * arcIntegral (core s) n primeWeight :=
  quadratic_arc_integral _ (core_measurable hs) (core_periodic hp) n

/-- The same signed identity holds with any additional prime coefficient, including
a sharp lower cutoff in the high-prime exponential sum. -/
theorem quadratic_weighted_core {s : Set ℝ} (hs : MeasurableSet s)
    (hp : ∀ t, t + 1 ∈ s ↔ t ∈ s) (n : ℕ) (v : ℕ → ℂ) :
    arcIntegral (core s) n (fun p => v p * (character p * primeWeight p)) =
      sign n * arcIntegral (core s) n (fun p => v p * primeWeight p) := by
  rw [expansion _ (core_measurable hs), expansion _ (core_measurable hs), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : (3:ℤ) ∣ (p:ℤ)+q-n
  · rw [show v p * (character p * primeWeight p) * (v q * (character q * primeWeight q)) =
        (v p * v q) * ((character p * primeWeight p) * (character q * primeWeight q)) by ring,
      resonant_pair n p q h]
    ring
  · simp [coefficient_zero (core s) (core_periodic hp) _ h]

/-- Periodize the complement of desk arcs supplied on [0,1), then take the
intersection of the three translates. The endpoints have zero Lebesgue measure. -/
noncomputable def minorCore (major : Set ℝ) : Set ℝ := core ((Int.fract : ℝ → ℝ) ⁻¹' majorᶜ)

theorem quadratic_minor_arc {major : Set ℝ} (hmajor : MeasurableSet major) (n : ℕ) (v : ℕ → ℂ) :
    arcIntegral (minorCore major) n (fun p => v p * (character p * primeWeight p)) =
      sign n * arcIntegral (minorCore major) n (fun p => v p * primeWeight p) := by
  apply quadratic_weighted_core (hmajor.compl.preimage measurable_fract)
  intro t
  simp only [Set.mem_preimage, Int.fract_add_one]

theorem minorCore_subset_outside {major : Set ℝ} {t : ℝ} (ht : t ∈ Set.Ico 0 1)
    (h : t ∈ minorCore major) : t ∉ major := by
  have h' : Int.fract t ∉ major := h.1
  rwa [Int.fract_eq_self.mpr ht] at h'

/-- The actual Lebesgue measure lost on a period is at most three times
the measure of the original desk major arcs in that period. -/
theorem minorCore_missing_measure {major : Set ℝ} (hm : MeasurableSet major) :
    (volume ((minorCore major)ᶜ ∩ Set.Ioo 0 1)).toReal ≤
      3 * (volume (major ∩ Set.Ioo 0 1)).toReal := by
  let s := (Int.fract : ℝ → ℝ) ⁻¹' majorᶜ
  have hs : MeasurableSet s := hm.compl.preimage measurable_fract
  have hp (t : ℝ) : t + 1 ∈ s ↔ t ∈ s := by simp [s, Int.fract_add_one]
  have h := core_missing_le hs hp
  rw [missing_integral (core_measurable hs), missing_integral hs] at h
  have he : sᶜ ∩ Set.Ioo 0 1 = major ∩ Set.Ioo 0 1 := by
    ext t
    by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
    · simp [s, ht, Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩]
    · simp [ht]
  rw [he] at h
  exact h

private theorem two_unit : IsUnit (2 : ZMod 3) :=
  ⟨⟨2, 2, by decide, by decide⟩, rfl⟩

/-- The packaged nonprincipal Dirichlet character inducing the coefficient above. -/
noncomputable def dirichlet : DirichletCharacter ℂ 3 where
  toFun a := character a.val
  map_one' := by rfl
  map_mul' := by
    intro a b
    have h (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by decide +revert
    have h₁ : (1 : ZMod 3).val = 1 := rfl
    have h₂ : (2 : ZMod 3).val = 2 := rfl
    have h₄ : (4 : ZMod 3).val = 1 := rfl
    rcases h a with rfl | rfl | rfl <;> rcases h b with rfl | rfl | rfl <;>
      norm_num [character, h₁, h₂, h₄]
  map_nonunit' := by
    intro a ha
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by decide +revert) with rfl | rfl | rfl
    · rfl
    · exact (ha isUnit_one).elim
    · exact (ha two_unit).elim

theorem dirichlet_eval (p : ℕ) : dirichlet p = character p := by
  change character ((p : ZMod 3).val) = _
  simp [character, ZMod.val_natCast]

theorem dirichlet_ne_one : dirichlet ≠ 1 := by
  intro h
  have he := congrArg (fun f : DirichletCharacter ℂ 3 => f (2 : ZMod 3)) h
  change dirichlet (2 : ZMod 3) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at he
  rw [MulChar.one_apply two_unit] at he
  have h₂ : dirichlet (2 : ZMod 3) = -1 := rfl
  rw [h₂] at he
  norm_num at he

/-- Formulation with a mathlib Dirichlet character instead of its residue formula. -/
theorem nonprincipal_minor_arc {major : Set ℝ} (hm : MeasurableSet major) (n : ℕ) (v : ℕ → ℂ) :
    arcIntegral (minorCore major) n (fun p => v p * (dirichlet p * primeWeight p)) =
      sign n * arcIntegral (minorCore major) n (fun p => v p * primeWeight p) := by
  simp_rw [dirichlet_eval]
  exact quadratic_minor_arc hm n v

end ModThreeMinor

section AggregateSemiprimeTail

private theorem semiprime_row_step (P x : ℝ) (hP : 0 < P) (hx : 0 < x)
    (a : ℕ) (ha : 0 < a) :
    (P/(x+1))^(a+1) ≤ (P/(a:ℝ))*((P/x)^a-(P/(x+1))^a) := by
  have hx1 : 0 < x+1 := by linarith
  have ha' : 0 < (a:ℝ) := by exact_mod_cast ha
  have haux : -(2:ℝ) ≤ 1/x := le_trans (by norm_num : -(2:ℝ) ≤ 0) (by positivity)
  have hbern := one_add_mul_le_pow haux a
  have hrat : (a:ℝ)/(x+1) ≤ ((x+1)/x)^a - 1 := by
    have hfirst : (a:ℝ)/(x+1) ≤ a/x :=
      div_le_div_of_nonneg_left ha'.le hx (by linarith)
    rw [show (x+1)/x = 1+1/x by field_simp] 
    linarith [show (a:ℝ)*(1/x) = a/x by ring]
  have hs := mul_le_mul_of_nonneg_left hrat (pow_nonneg (div_pos hP hx1).le a)
  rw [mul_sub, mul_one, ← mul_pow, show P/(x+1)*((x+1)/x) = P/x by field_simp] at hs
  calc
    (P/(x+1))^(a+1) = (P/(a:ℝ))*((P/(x+1))^a * ((a:ℝ)/(x+1))) := by
      rw [pow_succ]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (div_pos hP ha').le

private theorem semiprime_row_bound {p a : ℕ} (hp : 0 < p) (ha : 0 < a) (N : ℕ) :
    (∑ q ∈ Finset.Ioc p N, ((p:ℝ)/q)^(a+1)) ≤ (p:ℝ)/a := by
  by_cases hN : p ≤ N
  · have step (M : ℕ) (hM : p ≤ M) :
        (∑ q ∈ Finset.Ioc p M, ((p:ℝ)/q)^(a+1)) ≤
          (p:ℝ)/a*(1-((p:ℝ)/M)^a) := by
      induction M, hM using Nat.le_induction with
      | base => simp [Nat.ne_of_gt hp]
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM, Nat.cast_succ]
        have ht := semiprime_row_step p M (by exact_mod_cast hp) (by exact_mod_cast hp.trans_le hM) a ha
        linarith only [ih,ht]
    refine (step N hN).trans ?_
    exact mul_le_of_le_one_right (by positivity) (by have := pow_nonneg (by positivity : 0 ≤ (p:ℝ)/N) a; linarith)
  · simp [Finset.Ioc_eq_empty_of_le (le_of_not_ge hN), div_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg a)]

private theorem semiprime_power_tail {p q n a j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : p < q) (hk : p*q ≤ n) (hj : ((a+1:ℕ):ℝ) * Real.log n ≤ j) :
    smoothDivisorWeight j (p*q) ≤ Real.log n * ((p:ℝ)/q)^(a+1) := by
  let K := Real.log (p*q : ℕ)
  let D := Real.log (q:ℝ) - Real.log p
  let t := Real.log p / (K/2)
  have hK : K = Real.log p + Real.log q := by
    unfold K
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have Lp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hD : 0 < D := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast hlt))
  have hK0 : 0 < K := by unfold D at hD; linarith
  have hKn : K ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.mul_pos hp.pos hq.pos) (by exact_mod_cast hk)
  have ht : 0 ≤ t := by unfold t; positivity
  have hex : (1-t)*K = D := by
    change (1 - Real.log (p:ℝ)/(K/2))*K = Real.log q-Real.log p
    field_simp
    linarith
  have hr : ((a+1 : ℕ):ℝ) ≤ (j:ℝ)/K := (le_div_iff₀ hK0).mpr
    ((mul_le_mul_of_nonneg_left hKn (Nat.cast_nonneg _)).trans hj)
  have hmul : ((a+1 : ℕ):ℝ)*D ≤ (j:ℝ)*(1-t) := by
    have he := mul_le_mul_of_nonneg_right hr hD.le
    calc
      _ ≤ (j:ℝ)/K*D := he
      _ = _ := by rw [← hex]; field_simp
  have htPow : t^j ≤ ((p:ℝ)/q)^(a+1) := calc
    _ ≤ (Real.exp (t-1))^j := pow_le_pow_left₀ ht (by linarith only [Real.add_one_le_exp (t-1)]) j
    _ = Real.exp ((j:ℝ)*(t-1)) := (Real.exp_nat_mul ..).symm
    _ ≤ Real.exp (((a+1:ℕ):ℝ)*(-D)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_nat_mul,show -D = Real.log p-Real.log q by unfold D; ring,Real.exp_sub,
        Real.exp_log (by exact_mod_cast hp.pos),Real.exp_log (by exact_mod_cast hq.pos)]
  rw [smoothDivisorWeight_two_primes j hp hq hlt]
  change K*t^(j+1)*(2-t) ≤ _
  calc
    _ = K*t^j*(t*(2-t)) := by ring
    _ ≤ K*t^j := mul_le_of_le_one_right (mul_nonneg hK0.le (pow_nonneg ht _)) (by nlinarith [sq_nonneg (t-1)])
    _ ≤ _ := mul_le_mul hKn htPow (pow_nonneg ht _) (hK0.le.trans hKn)

private theorem smooth_excess_cases {j : ℕ} (hj : 0 < j) (k : ℕ) :
    smoothDivisorWeight j k = weight k ∨ ∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ k = p*q := by
  by_cases hp : k.Prime
  · exact Or.inl (by simp [smoothDivisorWeight_prime j hp, weight,hp])
  by_cases hs : Squarefree k
  · by_cases hc : 2 < k.primeFactors.card
    · exact Or.inl (by simp [smoothDivisorWeight_zero_of_card hj hc,weight,hp])
    rcases squarefree_small_cases hs (by omega) with rfl | h | h
    · exact Or.inl (by simp [smoothDivisorWeight,weight])
    · exact (hp h).elim
    · exact Or.inr h
  · exact Or.inl (by simp [smoothDivisorWeight,hs,weight,hp])

private theorem weight_le_log_range {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    weight k ≤ Real.log n := by
  by_cases hp : k.Prime
  · simpa [weight,hp] using Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
  · simpa [weight,hp] using Real.log_nonneg (by exact_mod_cast hn)

private theorem smooth_in_range_le_log {a j n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n)
    (hj0 : 0 < j) (hj : ((a+1:ℕ):ℝ) * Real.log n ≤ j) : smoothDivisorWeight j k ≤ Real.log n := by
  rcases smooth_excess_cases hj0 k with he | ⟨p,q,hp,hq,hlt,rfl⟩
  · rw [he]; exact weight_le_log_range hn hk
  · refine (semiprime_power_tail hp hq hlt hk hj).trans ?_
    exact mul_le_of_le_one_right (Real.log_nonneg (by exact_mod_cast hn))
      (pow_le_one₀ (by positivity) ((div_le_one (by exact_mod_cast hq.pos)).mpr (by exact_mod_cast hlt.le)))

theorem aggregate_smooth_excess {a j n : ℕ} (hn : 1 ≤ n) (ha : 0 < a) (hj0 : 0 < j)
    (hj : ((a+1:ℕ):ℝ) * Real.log n ≤ j) :
    (∑ k ∈ Finset.range (n+1), (smoothDivisorWeight j k - weight k)) ≤ (n:ℝ)*Real.log n/a := by
  classical
  let L := Real.log (n:ℝ)
  let P := Finset.Icc 1 n.sqrt
  let S := Finset.range (n+1)
  let G (p q : ℕ) := L * ((p:ℝ)/q)^(a+1)
  let B (p q k : ℕ) := if k = p*q then G p q else 0
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
  have hG (p q : ℕ) : 0 ≤ G p q := mul_nonneg hL (pow_nonneg (by positivity) _)
  have hB (p q k : ℕ) : 0 ≤ B p q k := by unfold B; split_ifs <;> simp [hG]
  have outer (k : ℕ) (hkS : k ∈ S) : smoothDivisorWeight j k - weight k ≤
      ∑ p ∈ P, ∑ q ∈ Finset.Ioc p n, B p q k := by
    rcases smooth_excess_cases hj0 k with hf | ⟨p,q,hp,hq,hlt,rfl⟩
    · rw [hf,sub_self]
      exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => hB p q k
    · have hk : p*q ≤ n := by simpa [S] using Finset.mem_range.mp hkS
      have hP : p ∈ P := Finset.mem_Icc.mpr ⟨hp.one_le,Nat.le_sqrt.mpr ((Nat.mul_le_mul_left p hlt.le).trans hk)⟩
      have hQ : q ∈ Finset.Ioc p n := Finset.mem_Ioc.mpr ⟨hlt,(by
        have := Nat.mul_le_mul_right q hp.one_le
        simpa using this.trans hk)⟩
      have hbq := Finset.single_le_sum (f := fun q' => B p q' (p*q)) (fun q' _ => hB p q' _) hQ
      have hbp := Finset.single_le_sum (f := fun p' => ∑ q' ∈ Finset.Ioc p' n, B p' q' (p*q))
        (fun p' _ => Finset.sum_nonneg (fun q' _ => hB p' q' _)) hP
      have hval : B p q (p*q) = G p q := by simp [B]
      exact ((sub_le_self _ (weight_nonneg _)).trans (semiprime_power_tail hp hq hlt hk hj)).trans
        (show G p q ≤ _ by rw [← hval]; exact hbq.trans hbp)
  have hcell (p q : ℕ) : ∑ k ∈ S, B p q k ≤ G p q := by
    unfold B
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp [hG]
  calc
    _ ≤ ∑ k ∈ S, ∑ p ∈ P, ∑ q ∈ Finset.Ioc p n, B p q k := Finset.sum_le_sum outer
    _ = ∑ p ∈ P, ∑ q ∈ Finset.Ioc p n, ∑ k ∈ S, B p q k := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ Finset.Ioc p n, G p q :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hcell p q
    _ ≤ ∑ p ∈ P, L * ((n.sqrt:ℝ)/a) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp0,hpr⟩ := Finset.mem_Icc.mp hp
      unfold G
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left ((semiprime_row_bound hp0 ha n).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hpr) (Nat.cast_nonneg _))) hL
    _ = ((n.sqrt:ℝ)^2)*L/a := by simp [P]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sqrt_le' n) hL)
      (Nat.cast_nonneg _)

theorem smoothDivisorCorr_aggregate_error {a j n : ℕ} (hn : 1 ≤ n) (ha : 0 < a) (hj0 : 0 < j)
    (hj : ((a+1:ℕ):ℝ)*Real.log n ≤ j) :
    smoothDivisorCorr j n - corr n ≤ 2*(n:ℝ)*(Real.log n)^2/a := by
  let L := Real.log (n:ℝ)
  let E (k : ℕ) := smoothDivisorWeight j k - weight k
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
  have hE (k : ℕ) : 0 ≤ E k := sub_nonneg.mpr (weight_le_smoothDivisorWeight hj0 k)
  have hpoint (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      smoothDivisorWeight j k*smoothDivisorWeight j (n-k)-weight k*weight (n-k) ≤ L*(E k+E (n-k)) := by
    have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
    have he := mul_le_mul_of_nonneg_left (smooth_in_range_le_log hn (Nat.sub_le n k) hj0 hj) (hE k)
    have he' := mul_le_mul_of_nonneg_right (weight_le_log_range hn hk') (hE (n-k))
    change _ ≤ L*(E k+E (n-k))
    calc
      _ = E k * smoothDivisorWeight j (n-k) + weight k * E (n-k) := by unfold E; ring
      _ ≤ E k*L+L*E (n-k) := add_le_add he he'
      _ = _ := by ring
  calc
    _ = ∑ k ∈ Finset.range (n+1), (smoothDivisorWeight j k*smoothDivisorWeight j (n-k)-weight k*weight (n-k)) :=
      (Finset.sum_sub_distrib ..).symm
    _ ≤ ∑ k ∈ Finset.range (n+1), L*(E k+E (n-k)) := Finset.sum_le_sum hpoint
    _ = (2*L)* ∑ k ∈ Finset.range (n+1), E k := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_flip E]; ring
    _ ≤ (2*L)*((n:ℝ)*L/a) := mul_le_mul_of_nonneg_left (aggregate_smooth_excess hn ha hj0 hj) (by positivity)
    _ = _ := by unfold L; ring

noncomputable def polylogSmoothIndex (n : ℕ) : ℕ := ⌈(Real.log n)^4⌉₊

theorem polylog_smooth_error {n : ℕ} (hL : 2 ≤ Real.log n) :
    smoothDivisorCorr (polylogSmoothIndex n) n - corr n ≤ 8*(n:ℝ)/Real.log n := by
  let L := Real.log (n:ℝ)
  let a : ℕ := ⌊L^3/2⌋₊
  have hL' : 2 ≤ L := hL
  have hcube : 8 ≤ L^3 := by
    calc (8:ℝ) = (2:ℝ)^3 := by norm_num
         _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL' 3
  have hfloor : (a:ℝ) ≤ L^3/2 := Nat.floor_le (by linarith)
  have hceil : L^3/2 < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have ha : 0 < a := by by_contra! he; have := Nat.eq_zero_of_le_zero he; rw [this] at hceil; norm_num at hceil; linarith
  have hsize : L^3/4 ≤ (a:ℝ) := by linarith
  have hh : ((a+1:ℕ):ℝ)*L ≤ (polylogSmoothIndex n : ℝ) := calc
    _ ≤ L^3*L := mul_le_mul_of_nonneg_right (by push_cast; linarith) (by linarith)
    _ = L^4 := by ring
    _ ≤ _ := Nat.le_ceil _
  have hn : 1 ≤ n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    rw [hn0] at hL
    norm_num at hL
  have hj0 : 0 < polylogSmoothIndex n := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
  have he := smoothDivisorCorr_aggregate_error hn ha hj0 hh
  refine he.trans ?_
  apply (div_le_div_iff₀ (by exact_mod_cast ha) (by linarith : 0 < L)).mpr
  have hint := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg (α := ℝ) n)
  change 2*(n:ℝ)*L^2*L ≤ 8*(n:ℝ)*a
  nlinarith only [hint]

theorem polylog_smooth_relative_error_tendsto :
    Filter.Tendsto (fun n : ℕ => (smoothDivisorCorr (polylogSmoothIndex n) n - corr n) / (n:ℝ))
      Filter.atTop (nhds 0) := by
  have hL : Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdec : Filter.Tendsto (fun n : ℕ => (8:ℝ) / Real.log n) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hL
  apply squeeze_zero' ?_ ?_ hdec
  · filter_upwards [hL.eventually_ge_atTop 2] with n hn
    have hj : 0 < polylogSmoothIndex n := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
    exact div_nonneg (sub_nonneg.mpr (corr_le_smoothDivisorCorr hj n)) (Nat.cast_nonneg _)
  · filter_upwards [hL.eventually_ge_atTop 2, Filter.eventually_gt_atTop (0:ℕ)] with n hn hn0
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn0
    exact (div_le_div_of_nonneg_right (polylog_smooth_error hn) hn'.le).trans_eq (by field_simp)
end AggregateSemiprimeTail

/-- A positive floor on the single polylogarithmic sequence of moments is
equivalent to the frozen dyadic floor for the genuine prime correlation. -/
theorem dyadic_floor_iff_polylog_smooth :
    (∃ (c : ℝ) (M : ℕ), 0 < c ∧ ∀ X n : ℕ, M ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n) ↔
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Even n →
      c*(n:ℝ) ≤ smoothDivisorCorr (polylogSmoothIndex n) n) := by
  constructor
  · rintro ⟨c,M,hc,h⟩
    refine ⟨c,max M 2,hc,by omega,?_⟩
    intro n hn he
    have hn2 : 1 < n := by omega
    have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hj : 0 < polylogSmoothIndex n := Nat.ceil_pos.mpr (pow_pos hlog 4)
    exact (h n n (by omega) le_rfl (by omega) he).trans (corr_le_smoothDivisorCorr hj n)
  · rintro ⟨c,N,hc,hN,h⟩
    have hsmall := polylog_smooth_relative_error_tendsto.eventually
      (gt_mem_nhds (half_pos hc))
    obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hsmall
    refine ⟨c/2,max N K,half_pos hc,?_⟩
    intro X n hX hnX _ he
    have hn : 0 < n := by omega
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have herr := (div_lt_iff₀ hn').mp (hK n (by omega))
    linarith only [herr,h n (by omega) he]

/-- The nonprincipal quadratic character on the translation-invariant
part of the actual extended minor arcs. The prime 3 is omitted. -/
theorem quadratic_extended_minor_core (n : ℕ) :
    let U := ModThreeMinor.minorCore (rationalArcSet (extendedArcCutoff n) n)
    ModThreeMinor.arcIntegral U n (fun p => ModThreeMinor.dirichlet p * ModThreeMinor.primeWeight p) =
      ModThreeMinor.sign n * ModThreeMinor.arcIntegral U n ModThreeMinor.primeWeight := by
  simpa only [one_mul] using ModThreeMinor.nonprincipal_minor_arc
    (major := rationalArcSet (extendedArcCutoff n) n) (measurable_rational_arcs _ _) n (fun _ => 1)

/-- Testing a single explicit finite order at each target suffices for the
original linear floor. The reciprocal error is paid by halving the constant. -/
theorem dyadic_floor_iff_sharp_smooth_moment :
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ corr n) ↔
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n ≥ N, Even n →
      c*(n:ℝ) ≤ smoothDivisorCorr (sharpSmoothMomentIndex n+1) n) := by
  constructor
  · rintro ⟨c,N,hc,h⟩
    refine ⟨c,max N 1,hc,?_⟩
    intro n hn he
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    exact (h n n ((le_max_left N 1).trans hn) le_rfl (by omega) he).trans
      (smoothDivisorCorr_sharp_uniform_error n).2
  · rintro ⟨c,N,hc,h⟩
    obtain ⟨K,hK⟩ := exists_nat_gt (2/c)
    refine ⟨c/2,max N K,half_pos hc,?_⟩
    intro X n hX hXn _ he
    have hn := hX.trans hXn
    have hk : K ≤ n := (le_max_right N K).trans hn
    have hb := (div_lt_iff₀ hc).mp (hK.trans_le (by exact_mod_cast hk : (K:ℝ) ≤ n))
    have hrec : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hup := (smoothDivisorCorr_sharp_uniform_error n).1
    have hlo := h n ((le_max_left N K).trans hn) he
    nlinarith only [hb,hrec,hup,hlo]
/-!
## Individual lower bounds in a prescribed congruence class nearby

This paper argument concerns the actual prime logarithmic correlation.
For large n, W >= 1 and a prescribed residue n mod W, write phi=phi(W)
and K=#{r mod W : r and n-r are units}. Assume K>0. Put L=log(3Wn).
Under Dirichlet GRH, for an absolute sufficiently large C, whenever
C phi^2 L^2/K <= H <= n/6 there exists an even m in (n,n+2H] with
m congruent to n modulo W and corr(m) >> n K W/phi^2.

Let I=[n/3,2n/3] and let A_r(t) be the prime log mass in (t,t+H]
in class r. Character Parseval and the short-interval mean-square
estimate for Dirichlet characters give
  V = sum_r int_I |A_r(t)-H/phi|^2 dt << nH L^2.
The sum is over units. The principal term uses the usual RH Selberg
integral. The nonprincipal estimate is Lemma 2.4(2.18) of Ikeda and
Suriajaya, https://arxiv.org/pdf/2405.04315 . Passing from von Mangoldt
to prime weights costs O(nH) in variance per character: the total mass
of proper prime powers up to 2n is O(sqrt(n)), its window integral is
O(H sqrt(n)), and the window mass is bounded by its total mass.
Omitting primes dividing W from the principal character costs at most
H(log W)^2 in integrated square.

Put a=H/phi. Reflection t -> n-t preserves I and the map r -> n-r
permutes the K matched classes. By Cauchy-Schwarz,
  sum_matched_r int_I A_r(t)A_(n-r)(n-t) dt
    >= K |I| a^2 - 2a sqrt(K |I| V) - V >= K |I| a^2/2.
Each pair contributes on a set of t of length at most H. Its sum m is
even, lies in (n,n+2H], and is congruent to n modulo W. There are at
most 1+2H/W possible m. The lower threshold on H implies H>=W:
K<=phi and W/phi<=omega(W)+1<=1+log_2 W by ordering the prime
divisors. Division gives the asserted coefficient lower bound.

For example, for W dividing n one has K=phi, so some m has
corr(m) >> (W/phi)n in a window of length O(phi log^2(3Wn)).
This supplies genuinely large coefficients in the prescribed class.
In fact a positive proportion of the candidate lattice points are good.
For B=KW/phi^2 its local factors are p/(p-1) at p|gcd(n,W) and
1-1/(p-1)^2 at the remaining p|W. Thus B<=n/phi(n). When W is odd
the parity restriction loses at most a factor two. A two-prime upper
sieve gives corr(m) << n B F(m) for even m in the class, where
F(m)=prod_{p|m,p not dividing W,p>2}(1+1/(p-2)). For odd m the
central sum vanishes. With T of order H/W, we have sum F(m)^2 << T.
Indeed primes above y=(log n)^2 contribute a bounded factor, since
there are at most log(2n)/log y of them. For smaller primes expand
g(p)=(1+1/(p-2))^2-1. Each squarefree divisor d of these primes
is coprime to W and divides at most T/d+1 candidates. Hence the
sum is O(T prod(1+g(p)/p)+prod_{p<=y,p>2}(1+g(p))) =
O(T+(log y)^2) by Mertens, and T >> log^2(3Wn)/B >> (log y)^2.
Cauchy-Schwarz applied to the large summands now yields >>T even m
in the prescribed class with central correlation >> B n.
One can approximate the full singular factor uniformly while retaining
a subpower window. Take y=log n/log log n, W=prod_{p<=y}p. Then
W=n^o(1), and the omitted prime factors p|n contribute a reciprocal
sum o(1): sum_{y<p<=log n}1/p=o(1) by Mertens, while those p>log n
have total at most 1/log log n. The remaining omitted Euler factors have
logarithmic sum O(1/y). Consequently B=(1+o(1))S(n) and H may be n^o(1).
This argument still leaves many candidates and does not isolate n.
-/

section FiniteCoreArcBands
open MeasureTheory

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

private theorem coreArcBand_union (n R : ℕ) {A B C : ℕ} (h₁ : A ≤ B) (h₂ : B ≤ C) :
    coreArcBand n R A C = coreArcBand n R A B ∪ coreArcBand n R B C := by
  ext t
  constructor
  · rintro ⟨q,a,hq,hC,ha,hc,hw⟩
    by_cases hqB : q ≤ B
    · exact Or.inl ⟨q,a,hq,hqB,ha,hc,hw⟩
    · exact Or.inr ⟨q,a,by omega,hC,ha,hc,hw⟩
  · rintro (⟨q,a,hq,hB,ha,hc,hw⟩ | ⟨q,a,hq,hC,ha,hc,hw⟩)
    · exact ⟨q,a,hq,hB.trans h₂,ha,hc,hw⟩
    · exact ⟨q,a,lt_of_le_of_lt h₁ hq,hC,ha,hc,hw⟩

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

noncomputable def coreArcIntegral (n R A B : ℕ) (F : ℝ → ℂ) : ℂ :=
  intervalIntegral ((coreArcBand n R A B).indicator F) 0 1 volume

private theorem coreArcIntegral_split {n R A B C : ℕ} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (hs : 2*R*C < n) {F : ℝ → ℂ} (hF : Continuous F) :
    coreArcIntegral n R A C F = coreArcIntegral n R A B F + coreArcIntegral n R B C F := by
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable _ _
  have hI (X Y : ℕ) : IntervalIntegrable ((coreArcBand n R X Y).indicator F) volume 0 1 :=
    ⟨hi.1.indicator (measurable_coreArcBand ..),hi.2.indicator (measurable_coreArcBand ..)⟩
  unfold coreArcIntegral
  rw [coreArcBand_union n R h₁ h₂,← intervalIntegral.integral_add (hI A B) (hI B C)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g 0 1 volume)
  funext t
  by_cases ha : t ∈ coreArcBand n R A B
  · have hb := Set.disjoint_left.mp (coreArcBand_disjoint h₂ hs) ha
    simp [ha,hb]
  · by_cases hb : t ∈ coreArcBand n R B C <;> simp [ha,hb]

theorem coreArcIntegral_three {n R A B C D : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (hs : 2*R*D < n) {F : ℝ → ℂ} (hF : Continuous F) :
    coreArcIntegral n R A D F = coreArcIntegral n R A B F +
      coreArcIntegral n R B C F + coreArcIntegral n R C D F := by
  have hs' := lt_of_le_of_lt (Nat.mul_le_mul_left (2*R) hCD) hs
  rw [coreArcIntegral_split (hAB.trans hBC) hCD hs hF,coreArcIntegral_split hAB hBC hs' hF]

private theorem coreBandModel_split (g : ℕ → ℂ) {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    ∑ q ∈ Finset.Ioc A C, g q = ∑ q ∈ Finset.Ioc A B, g q + ∑ q ∈ Finset.Ioc B C, g q := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hAB hBC,Finset.sum_union]
  exact Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_Ioc.mp hy).1.not_ge (Finset.mem_Ioc.mp hx).2

theorem coreBandModel_three (g : ℕ → ℂ) {A B C D : ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D) :
    ∑ q ∈ Finset.Ioc A D, g q = ∑ q ∈ Finset.Ioc A B, g q +
      ∑ q ∈ Finset.Ioc B C, g q + ∑ q ∈ Finset.Ioc C D, g q := by
  rw [coreBandModel_split g (hAB.trans hBC) hCD,coreBandModel_split g hAB hBC]

theorem coreArcBand_setDiff {n R A D : ℕ} (hAD : A ≤ D) (hs : 2*R*D < n) :
    coreArcBand n R 0 D \ coreArcBand n R 0 A = coreArcBand n R A D := by
  rw [coreArcBand_union n R (Nat.zero_le A) hAD]
  ext t
  have hd := Set.disjoint_left.mp (coreArcBand_disjoint (A := 0) hAD hs)
  by_cases h : t ∈ coreArcBand n R 0 A
  · have hb := hd h
    simp [h,hb]
  · simp [h]

end FiniteCoreArcBands
section FrozenCoreCutoffs
open Filter

theorem eventually_core_cutoffs :
    ∀ᶠ n : ℕ in atTop,
      let Q := (Nat.log 2 (n+2))^2
      let B := ⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊
      let C := ⌊(n:ℝ)^(1/10:ℝ)⌋₊
      let D := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      Q ≤ B ∧ B ≤ C ∧ C ≤ D ∧ 2*Q*D < n := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 12000, eventually_ge_atTop (27:ℕ)] with n hL hn
  let L := Real.log (n:ℝ)
  let m := Nat.log 2 (n+2)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have Lge : 12000 ≤ L := hL
  have h2 : 1/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2:ℝ))
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
  have hQ : (((m^2:ℕ):ℝ)) ≤ Real.exp (Real.sqrt L) := by
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hm 2
    have he := Real.pow_div_factorial_le_exp (Real.sqrt L) (Real.sqrt_nonneg L) 6
    rw [show (Real.sqrt L)^6 = ((Real.sqrt L)^2)^3 by ring,
      Real.sq_sqrt (by linarith : 0≤L)] at he
    norm_num [Nat.factorial] at he
    push_cast
    nlinarith only [hpow,he,mul_nonneg (sq_nonneg L) (sub_nonneg.mpr Lge)]
  have hB : Real.exp (Real.sqrt L) ≤ (n:ℝ)^(1/10:ℝ) := by
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    change Real.sqrt L ≤ L*(1/10:ℝ)
    nlinarith only [Real.sq_sqrt (by linarith : 0≤L),sq_nonneg (Real.sqrt L-10),Lge]
  have hC : (n:ℝ)^(1/10:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) (by norm_num)
  let D := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hDn : ((n:ℝ)^(1/3:ℝ))^3 = (n:ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have hD3 : 3 ≤ D := by
    apply Nat.le_floor
    have hn' : (27:ℝ) ≤ n := by exact_mod_cast hn
    simpa using (show (3:ℝ) ≤ (n:ℝ)^(1/3:ℝ) by
      by_contra! hnot
      have hlt := pow_lt_pow_left₀ hnot (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by decide : 3≠0)
      rw [hDn] at hlt
      norm_num at hlt
      linarith)
  have hDn' : D^3 ≤ n := by
    have hD : (D:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hD 3
    rw [hDn] at hpow
    exact_mod_cast hpow
  have hQB := Nat.le_floor hQ
  have hBC := Nat.floor_mono hB
  have hCD := Nat.floor_mono hC
  have hQD : m^2 ≤ D := hQB.trans (hBC.trans hCD)
  exact ⟨hQB,hBC,hCD,by
    change 2*m^2*D < n
    have e := Nat.mul_le_mul_right D hQD
    have e' := Nat.mul_le_mul_right (D*D) hD3
    have hpos : 0 < D*D := Nat.mul_pos (by omega) (by omega)
    nlinarith only [e,e',hDn',hpos]⟩

end FrozenCoreCutoffs
section RegisteredMediumCore
open MeasureTheory Filter

abbrev medDeskQ (n : ℕ) := (Nat.log 2 (n+2))^2
noncomputable abbrev medDeskB (n : ℕ) := ⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊
noncomputable abbrev medDeskC (n : ℕ) := ⌊(n:ℝ)^(1/10:ℝ)⌋₊
noncomputable abbrev medDeskD (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

noncomputable def medDeskSignal (n : ℕ) (t : ℝ) : ℂ :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
  (S n w t)^2*E (-(n:ℝ)*t)

noncomputable def medDeskModelTerm (n q : ℕ) : ℂ :=
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
  let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β)
  ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume

noncomputable abbrev medDeskBand (n a b : ℕ) :=
  coreArcIntegral n (medDeskQ n) a b (medDeskSignal n)

noncomputable abbrev medDeskModel (n a b : ℕ) :=
  ∑ q ∈ Finset.Ioc a b, medDeskModelTerm n q

noncomputable def medDeskCore (n : ℕ) : ℂ :=
  intervalIntegral ((coreArcBand n (medDeskQ n) 0 (medDeskD n) \
    coreArcBand n (medDeskQ n) 0 (medDeskQ n)).indicator (medDeskSignal n)) 0 1 volume

abbrev medDeskModelFloor : Prop :=
  ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n ≥ N, Even n → -(e*(n:ℝ)) ≤ (medDeskModel n (medDeskQ n) (medDeskD n)).re

abbrev medDeskError (A B : ℕ → ℕ) : Prop :=
  ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n ≥ N, Even n →
    ‖medDeskBand n (A n) (B n) - medDeskModel n (A n) (B n)‖ ≤ e*(n:ℝ)

theorem medDeskCore_floor_of_four
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD) :
    ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n ≥ N, Even n → -(e*(n:ℝ)) ≤ (medDeskCore n).re := by
  intro e he
  have he4 : 0 < e/4 := by positivity
  obtain ⟨N₀,h₀⟩ := hm _ he4
  obtain ⟨N₁,h₁⟩ := h₁ _ he4
  obtain ⟨N₂,h₂⟩ := h₂ _ he4
  obtain ⟨N₃,h₃⟩ := h₃ _ he4
  obtain ⟨K,hcut⟩ := Filter.eventually_atTop.mp eventually_core_cutoffs
  refine ⟨max K (max N₀ (max N₁ (max N₂ N₃))),?_⟩
  intro n hn heven
  obtain ⟨hab,hbc,hcd,hs⟩ := hcut n (by omega)
  have hF : Continuous (medDeskSignal n) := by unfold medDeskSignal; fun_prop
  have hid : medDeskCore n = medDeskBand n (medDeskQ n) (medDeskB n) +
      medDeskBand n (medDeskB n) (medDeskC n) + medDeskBand n (medDeskC n) (medDeskD n) := by
    unfold medDeskCore
    rw [coreArcBand_setDiff (hab.trans (hbc.trans hcd)) hs]
    exact coreArcIntegral_three hab hbc hcd hs hF
  have hmm := h₀ n (by omega) heven
  have hmId := coreBandModel_three (medDeskModelTerm n) hab hbc hcd
  change medDeskModel n (medDeskQ n) (medDeskD n) = _ at hmId
  rw [hmId] at hmm
  have err {z w : ℂ} (h : ‖z-w‖ ≤ e/4*n) : w.re-e/4*n ≤ z.re := by
    have ha := Complex.abs_re_le_norm (z-w)
    have hb := neg_le_abs (z-w).re
    rw [Complex.sub_re] at ha hb
    linarith
  have hlow₁ := err (h₁ n (by omega) heven)
  have hlow₂ := err (h₂ n (by omega) heven)
  have hlow₃ := err (h₃ n (by omega) heven)
  rw [hid]
  change -((e/4)*(n:ℝ)) ≤ (medDeskModel n (medDeskQ n) (medDeskB n) +
    medDeskModel n (medDeskB n) (medDeskC n) + medDeskModel n (medDeskC n) (medDeskD n)).re at hmm
  simp only [Complex.add_re] at hmm ⊢
  linarith only [hmm,hlow₁,hlow₂,hlow₃]

end RegisteredMediumCore

theorem primeArcMass_partition {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hsub : A ⊆ B) (n : ℕ) :
    primeArcMass B n = primeArcMass A n + primeArcMass (B \ A) n := by
  have hc : Continuous (primeSquareKernel n) := by unfold primeSquareKernel E; fun_prop
  have hf := hc.intervalIntegrable («μ» := volume) 0 1
  have hi {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator (primeSquareKernel n)) volume 0 1 :=
    ⟨hf.1.indicator hs, hf.2.indicator hs⟩
  have split : intervalIntegral (B.indicator (primeSquareKernel n)) 0 1 volume =
      intervalIntegral (A.indicator (primeSquareKernel n)) 0 1 volume +
      intervalIntegral ((B \ A).indicator (primeSquareKernel n)) 0 1 volume := by
    rw [← intervalIntegral.integral_add (hi hA) (hi (hB.diff hA))]
    apply congrArg (fun f : ℝ → ℂ => intervalIntegral f 0 1 volume)
    funext t
    by_cases ha : t ∈ A
    · simp [ha, hsub ha]
    · by_cases hb : t ∈ B <;> simp [ha,hb]
  exact congrArg Complex.re split

/-- With the constants from PR 316 and the narrow middle-band lower
bound, a deficit n/288 on the rest of the circle still suffices. -/
theorem corr_one_576_of_narrow_arc_budget {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hsub : A ⊆ B) (n : ℕ)
    (hmajor : (n:ℝ)/144 ≤ primeArcMass A n)
    (hcore : -(n:ℝ)/576 ≤ primeArcMass (B \ A) n)
    (hrest : -(n:ℝ)/288 ≤ primeArcMass Bᶜ n) :
    (n:ℝ)/576 ≤ corr n := by
  rw [corr_eq_primeArcMass n B hB, primeArcMass_partition hA hB hsub n]
  linarith

theorem dyadic_floor_from_narrow_core_budget
    (hm : medDeskModelFloor) (h₁ : medDeskError medDeskQ medDeskB)
    (h₂ : medDeskError medDeskB medDeskC) (h₃ : medDeskError medDeskC medDeskD)
    (major : ∃ N : ℕ, ∀ n ≥ N, Even n →
      (n:ℝ)/144 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(n:ℝ)/288 ≤ primeArcMass (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ n) :
    ∃ N : ℕ, ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → (n:ℝ)/576 ≤ corr n := by
  obtain ⟨N₁,hcore⟩ := medDeskCore_floor_of_four hm h₁ h₂ h₃ (1/576) (by norm_num)
  obtain ⟨N₂,hmaj⟩ := major
  obtain ⟨N₃,hrest⟩ := rest
  obtain ⟨N₄,hcuts⟩ := Filter.eventually_atTop.mp eventually_core_cutoffs
  refine ⟨max (max N₁ N₂) (max N₃ N₄),?_⟩
  intro X n hX hXn _ he
  have hc := hcore n (by omega) he
  change -(1/576*(n:ℝ)) ≤ primeArcMass
    (coreArcBand n (medDeskQ n) 0 (medDeskD n) \ coreArcBand n (medDeskQ n) 0 (medDeskQ n)) n at hc
  have hD : medDeskQ n ≤ medDeskD n := by
    obtain ⟨a,b,c,_⟩ := hcuts n (by omega)
    exact a.trans (b.trans c)
  have hn : coreArcBand n (medDeskQ n) 0 (medDeskQ n) ⊆
      coreArcBand n (medDeskQ n) 0 (medDeskD n) := by
    rintro t ⟨q,a,hp,hu,ha,hcop,hw⟩
    exact ⟨q,a,hp,hu.trans hD,ha,hcop,hw⟩
  exact corr_one_576_of_narrow_arc_budget (measurable_coreArcBand ..) (measurable_coreArcBand ..)
    hn n (hmaj n (by omega) he) (by linarith only [hc]) (hrest n (by omega) he)

/-!
## Applying the production frontier statements (25 November 2026)

The authoritative real-prime/modeled-band error estimates cover the
successive denominators from Q=(Nat.log 2 (n+2))^2 to exp(sqrt(log n)),
to n^(1/10), and to B=n^(1/3), with natural-number floor cutoffs.
Each arc has half-width Q/(q n). The model real part for the union has
the lower bound -epsilon n. The four budgets, each used with epsilon/4,
therefore give the real prime narrow middle core the same eventual
lower bound. The separate low- and medium-modulus outer wings, and the
deep minor arcs, lie beyond that narrow core. In particular PR 316's
n/144 on the original major arcs leaves the margin in
corr_one_576_of_narrow_arc_budget if the remaining complement contributes
at least -n/288. The three true/model comparisons and the model bound
have authoritative runs 45632569579, 45632663848, 45631371513, and
45636877921, respectively. See
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2458 .

For the frozen GRH medium-zones statement, the earlier centered Euler
sum argument yields a further paper estimate. In its notation the wide
arcs have q<=B and numerator H=256 B Q. They are disjoint for distinct
reduced centers because 2 B H<n eventually. The copies at 0 and 1
combine at q=1. The excess between these wide arcs and the original
desk major arcs is exactly the union of the core and its outer wings.
For each q the character short-interval estimate and Gallagher step
above give total integrated square error O(phi(q) (H/q) log^4 n);
summing costs O(B H log^4 n). Since the model energy is O(n log n),
the error in the signed square is O(n^(5/6) log^(7/2) n)=o(n).
Model replacement for true prime weights uses the proper prime power
removal and the omitted nonunit primes as in the earlier argument.

At the center n the model weights are
  W(q)=F(H/q)-1_{q<=Q}F(Q/q)   (q<=B).
They lie between zero and Cq/Q for q<=Q. On Q<q<=B they are
nonincreasing and bounded below by F(1). Thus the earlier proof by
splitting a squarefree denominator into the part dividing n and the
part coprime to n applies with P_outer=B. There is a shorter proof of the last liminf step. Put A=n/phi(n),
y=log n and w(g)=1/phi(g) on divisors of rad(n). The total possible
loss for g<=Q is O(A Q^(-1/4)+A/log Q). For g<=sqrt(Q) this follows
at once from the earlier bound O(sqrt(g/Q)) per unit of weight.
For g>sqrt(Q) multiply that bound by log g=sum_{p|g}log p and
sum first over p in g=p h. The sum over p<=Q/h of
(log p)/(p-1) sqrt(p h/Q) is O(1) by Chebyshev and partial summation.
The outer weights sum to at most A. In particular the loss is always
O(1), and tends to zero on sequences with A=o(log Q).
On a sequence with A>=delta log Q for fixed delta>0, the sum of
1/p over missing primes p<=y is bounded in terms of delta by Mertens;
the prime divisors above y have total reciprocal mass O(1/log y).
Choose fixed a>0 small enough that the primes in (y^a,y] dividing n
carry total weight sum 1/(p-1)>=1. For fixed integer s>2/a the
products d of s distinct such primes have total weight >=1/(2s!)
eventually: ordered selections with repeated primes have negligible
weight, since the maximum single weight tends to zero and total
weight is bounded in terms of a. Then Q<d<=y^s. All products g0 of
primes p|n up to y^a satisfy g0<=exp(O(y^a)) and their total weight
is >>_a A. The distinct g0 d lie in (Q,B], where the coprime-b sum
has a positive lower bound per unit of weight. This positive mass tends
to infinity and pays the bounded loss. The two cases prove the stated
liminf uniformly in even n. This gives the GRH paper lower bound for the combined core
and wings. An authority-checked Lean proof of that inference and the
pointwise lower bound for the deep region remain outstanding.

PR 2468 proves the B4-by-B4 Type-II deep coefficient. Its conclusion
bounds the norm of an integral with the n-th phase. It does not
give an absolute-square energy bound permitting Cauchy-Schwarz
against an arbitrary second factor. The proof uses the small divisor
complement in the Vaughan weight to reduce to two interval sums of
step <=n^(19/48) and treats shared rational poles by Ramanujan sums.
The central B3-by-B3 estimate is one of the other nine cells at the
time of this check.
https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45639721952
-/


end GoldbachPartial
