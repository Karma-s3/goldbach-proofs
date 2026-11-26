import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace GoldbachPartial

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

theorem divisor_count_fourth_le_two_pow_256 (n : ℕ) : n.divisors.card^4 ≤ 2^256*n :=
  (divisor_count_fourth_le n).trans (Nat.mul_le_mul_right n
    (Nat.pow_le_pow_right (by decide) (by decide : 48 ≤ 256)))

end GoldbachPartial
