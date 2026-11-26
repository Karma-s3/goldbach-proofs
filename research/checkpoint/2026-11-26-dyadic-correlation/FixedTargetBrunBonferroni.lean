import FixedTargetBrunProgressions
import VerifiedFiniteBonferroni

namespace GoldbachPartial
open Finset
open scoped Classical

noncomputable def fixedTargetBrunSurvivorMass (n z : ℕ) : ℝ :=
  ∑ k ∈ (Ioc (n/4) (n/2)).filter (fun k => ∀ p : ℕ, p.Prime → p≤z → ¬p∣n-k), weight k

noncomputable def fixedTargetBrunPrimeSurvivors (n z : ℕ) : Finset ℕ :=
  (Ioc (n/4) (n/2)).filter (fun k => k.Prime ∧ ∀ p : ℕ, p.Prime → p≤z → ¬p∣n-k)

theorem fixedTarget_prime_subset_product_dvd (t : Finset ℕ) (ht : ∀ p∈t,p.Prime) (m : ℕ) :
    (∏ p∈t,p) ∣ m ↔ ∀ p∈t,p∣m := by
  refine ⟨fun hd p hp => (Finset.dvd_prod_of_mem id hp).trans hd,?_⟩
  intro hh
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hpt ih =>
    have hp := ht p (mem_insert_self ..)
    have hother (l : ℕ) (hl : l∈t) := ht l (mem_insert_of_mem hl)
    have hc : p.Coprime (∏ l∈t,l) :=
      Nat.coprime_prod_right_iff.mpr fun l hl =>
        (Nat.coprime_primes hp (hother l hl)).mpr (by rintro rfl; exact hpt hl)
    rw [prod_insert hpt]
    exact hc.mul_dvd_of_dvd_of_dvd (hh p (mem_insert_self ..))
      (ih hother (fun l hl => hh l (mem_insert_of_mem hl)))

theorem fixedTarget_Brun_bonferroni (n z K : ℕ) (hK : Odd K) (hz : z≤n/4) :
    (∑ t ∈ (fixedTargetBrunPrimes n z).powerset.filter (fun t => t.card≤K),
      (-1:ℝ)^t.card * fixedTargetDivisorRow n (∏ p∈t,p)) ≤ fixedTargetBrunSurvivorMass n z := by
  let I := Ioc (n/4) (n/2)
  let B := fixedTargetBrunPrimes n z
  let T := B.powerset.filter (fun t : Finset ℕ => t.card≤K)
  have hu (k : ℕ) (_hk : k∈I) : 0≤weight k := by
    unfold weight
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  have hb := weightedBonferroni_odd I B weight hu (fun k p => p∣n-k) hK
  have hrow (t : Finset ℕ) (ht : t∈T) :
      fixedTargetDivisorRow n (∏ p∈t,p) = ∑ k ∈ I.filter (fun k=>∀p∈t,p∣n-k),weight k := by
    have htB := mem_powerset.mp (mem_filter.mp ht).1
    have hp (p : ℕ) (h : p∈t) := (mem_filter.mp (htB h)).2.1
    unfold fixedTargetDivisorRow
    rw [sum_filter]
    apply sum_congr rfl
    intro k _
    exact if_congr (fixedTarget_prime_subset_product_dvd t hp (n-k)) rfl rfl
  calc
    _ = ∑ t∈T, (-1:ℝ)^t.card*(∑ k ∈ I.filter (fun k=>∀p∈t,p∣n-k),weight k) :=
      sum_congr rfl fun t ht => congrArg _ (hrow t ht)
    _ ≤ ∑ k ∈ I.filter (fun k => ∀ p∈B, ¬p∣n-k), weight k := by
      convert hb using 1
      · apply sum_congr (by ext t; simp only [T,mem_filter]) 
        intro t _
        congr 1
        apply sum_congr (by ext k; simp only [mem_filter]) 
        intro k _
        rfl
      · apply sum_congr (by ext k; simp only [mem_filter]) 
        intro k _
        rfl
    _ = fixedTargetBrunSurvivorMass n z := by
      unfold fixedTargetBrunSurvivorMass
      rw [sum_filter,sum_filter]
      apply sum_congr rfl
      intro k hk
      by_cases hk' : k.Prime
      · refine if_congr ⟨?_,?_⟩ rfl rfl
        · intro avoid p hpr hpz
          by_cases hpn : p∣n
          · exact fixedTarget_common_prime_excluded hz hpr hpz hpn hk' hk
          · exact avoid p (mem_filter.mpr ⟨mem_range_succ_iff.mpr hpz,hpr,hpn⟩)
        · intro avoid p hp
          obtain ⟨hl,hpr,_⟩ := mem_filter.mp hp
          exact avoid p hpr (mem_range_succ_iff.mp hl)
      · simp [weight,hk']

theorem fixedTarget_Brun_mass_eq_prime_sum (n z : ℕ) :
    fixedTargetBrunSurvivorMass n z = ∑ k∈fixedTargetBrunPrimeSurvivors n z,Real.log k := by
  unfold fixedTargetBrunSurvivorMass fixedTargetBrunPrimeSurvivors
  rw [sum_filter,sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hp : k.Prime
  · by_cases hr : ∀ p : ℕ, p.Prime → p≤z → ¬p∣n-k
    · rw [ite_eq_left hr,ite_eq_left ⟨hp,hr⟩,weight,ite_eq_left hp]
    · rw [ite_eq_right hr,ite_eq_right (fun h=>hr h.2)]
  · by_cases hr : ∀ p : ℕ, p.Prime → p≤z → ¬p∣n-k
    · rw [ite_eq_left hr,ite_eq_right (fun h=>hp h.1),weight,ite_eq_right hp]
    · rw [ite_eq_right hr,ite_eq_right (fun h=>hr h.2)]

theorem fixedTarget_Brun_count_of_mass (n z : ℕ) (hn : 2≤n) :
    fixedTargetBrunSurvivorMass n z/Real.log n ≤ (fixedTargetBrunPrimeSurvivors n z).card := by
  have hL : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  apply (div_le_iff₀ hL).mpr
  rw [fixedTarget_Brun_mass_eq_prime_sum]
  calc
    _ ≤ ∑ _k∈fixedTargetBrunPrimeSurvivors n z,Real.log n := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hi,hk',_⟩ := mem_filter.mp hk
      exact Real.log_le_log (by exact_mod_cast hk'.pos)
        (by exact_mod_cast (show k≤n by have := (mem_Ioc.mp hi).2;omega))
    _ = _ := by simp

theorem fixedTarget_Brun_prime_of_positive {n z : ℕ} (h : 0<fixedTargetBrunSurvivorMass n z) :
    ∃ k ∈ Ioc (n/4) (n/2), k.Prime ∧ ∀ p : ℕ,p.Prime → p≤z → ¬p∣n-k := by
  have hne : (fixedTargetBrunPrimeSurvivors n z).Nonempty := by
    by_contra nh
    rw [fixedTarget_Brun_mass_eq_prime_sum,not_nonempty_iff_eq_empty.mp nh,sum_empty] at h
    exact lt_irrefl _ h
  obtain ⟨k,hk⟩ := hne
  exact ⟨k,(mem_filter.mp hk).1,(mem_filter.mp hk).2⟩

end GoldbachPartial