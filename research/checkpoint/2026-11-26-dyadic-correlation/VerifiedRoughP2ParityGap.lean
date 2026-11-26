import VerifiedGenuineGoldbachCubicExceptions
import VerifiedMiddleFactorCount

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

/-- The same roughness convention as a sieve that removes primes below z. -/
def reflectedRoughP2 (m z : ℕ) : Prop :=
  2≤m ∧ ArithmeticFunction.cardFactors m≤2 ∧ ∀ r : ℕ, r.Prime → r∣m → z≤r

noncomputable def reflectedP2Set (n z : ℕ) : Finset ℕ :=
  (range (n+1)).filter (fun p => p.Prime ∧ reflectedRoughP2 (n-p) z)

noncomputable def reflectedP2LogMass (n z : ℕ) : ℝ :=
  ∑p∈reflectedP2Set n z, Real.log p*Real.log (n-p:ℕ)

noncomputable def reflectedP2ParityMass (n z : ℕ) : ℝ :=
  ∑p∈reflectedP2Set n z, ((-1:ℝ)^ArithmeticFunction.cardFactors (n-p))*(Real.log p*Real.log (n-p:ℕ))

theorem reflectedP2_parity_exact (n z : ℕ) :
    reflectedP2LogMass n z-reflectedP2ParityMass n z =
      2*∑p∈range (n+1), if z≤n-p then weight p*weight (n-p) else 0 := by
  unfold reflectedP2LogMass reflectedP2ParityMass
  rw [←sum_sub_distrib,mul_sum]
  unfold reflectedP2Set
  rw [sum_filter]
  apply sum_congr rfl
  intro p _
  let m := n-p
  change (if p.Prime ∧ reflectedRoughP2 m z then
    Real.log p*Real.log m-(-1:ℝ)^ArithmeticFunction.cardFactors m*(Real.log p*Real.log m) else 0) =
      2*(if z≤m then weight p*weight m else 0)
  by_cases hpp : p.Prime
  · by_cases hq : m.Prime
    · have hiff : reflectedRoughP2 m z ↔ z≤m := by
        constructor
        · intro h
          exact h.2.2 m hq (dvd_refl _)
        · intro hz
          refine ⟨hq.two_le,(ArithmeticFunction.cardFactors_apply_prime hq).le.trans (by decide),?_⟩
          intro r hr hd
          simpa only [(Nat.prime_dvd_prime_iff_eq hr hq).mp hd] using hz
      by_cases hz : z≤m
      · simp only [hpp,hiff,hz,and_self,ite_true,ArithmeticFunction.cardFactors_apply_prime hq,pow_one,
          weight,hq,ite_true]
        ring
      · simp [hpp,hiff,hz]
    · by_cases hS : reflectedRoughP2 m z
      · have hpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (show 1<m from hS.1)
        have hone : ArithmeticFunction.cardFactors m≠1 := fun h => hq (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
        have hh := hS.2.1
        have he : ArithmeticFunction.cardFactors m=2 := by omega
        simp [hpp,hS,he,weight,hq]
      · simp [hpp,hS,weight,hq]
  · simp [hpp,weight]

private theorem pairWeight_nonneg (k : ℕ) : 0≤weight k := by
  unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl

private theorem pairWeight_le_log {k n : ℕ} (hk : k≤n) : weight k≤Real.log n := by
  unfold weight
  split_ifs with hp
  · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
  · exact Real.log_natCast_nonneg _

/-- All discarded prime pairs have a complementary prime below z, so their
whole contribution is bounded by z log² n for each target individually. -/
theorem reflectedP2_parity_cutoff (n z : ℕ) :
    let D := reflectedP2LogMass n z-reflectedP2ParityMass n z
    D ≤ 2*corr n ∧ 2*corr n ≤ D+2*z*(Real.log n)^2 := by
  rw [reflectedP2_parity_exact]
  let I := range (n+1)
  let W := fun p : ℕ => weight p*weight (n-p)
  let G := I.filter (fun p => z≤n-p)
  let T := I.filter (fun p => ¬z≤n-p)
  have hgood : (∑p∈I,if z≤n-p then W p else 0)=∑p∈G,W p := (sum_filter ..).symm
  change 2*(∑p∈I,if z≤n-p then W p else 0) ≤ 2*(∑p∈I,W p) ∧
    2*(∑p∈I,W p) ≤ 2*(∑p∈I,if z≤n-p then W p else 0)+2*z*(Real.log n)^2
  rw [hgood]
  have hsplit : (∑p∈G,W p)+(∑p∈T,W p)=∑p∈I,W p := sum_filter_add_sum_filter_not .. 
  have hT0 : 0≤∑p∈T,W p := sum_nonneg (fun p _=>mul_nonneg (pairWeight_nonneg _) (pairWeight_nonneg _))
  have hpn {p : ℕ} (hp : p∈T) : p≤n := mem_range_succ_iff.mp (mem_filter.mp hp).1
  have hTcard : T.card≤z := by
    calc T.card ≤ (range z).card := card_le_card_of_injOn (fun p=>n-p)
          (fun p hp => mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2))
          (by intro p hp q hq h;dsimp at h;have := hpn hp;have := hpn hq;omega)
         _ = _ := card_range z
  have hval : (∑p∈T,W p)≤(z:ℝ)*(Real.log n)^2 := by
    calc _ ≤ ∑_p∈T,(Real.log n)^2 := by
              apply sum_le_sum
              intro p hp
              rw [sq]
              exact mul_le_mul (pairWeight_le_log (hpn hp)) (pairWeight_le_log (Nat.sub_le n p))
                (pairWeight_nonneg _) (Real.log_natCast_nonneg _)
         _ = (T.card:ℝ)*(Real.log n)^2 := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hTcard) (sq_nonneg _)
  constructor <;> linarith only [hsplit,hT0,hval]

theorem reflectedP2_cutoff_small (z : ℕ→ℕ)
    (hz : ∀ᶠ n : ℕ in atTop,(z n:ℝ)≤Real.sqrt n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, 2*(z n:ℝ)*(Real.log n)^2 ≤ ε*n := by
  have ht : Tendsto (fun n:ℕ => (Real.log n)^2/Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hz,ht.eventually_le_const (show 0<ε/2 by linarith),eventually_ge_atTop (1:ℕ)] with n hn he h1
  have hr : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast h1)
  have hh := (div_le_iff₀ hr).mp he
  have hsq := Real.mul_self_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hh' := mul_le_mul_of_nonneg_left hh hr.le
  nlinarith only [hh',mul_le_mul_of_nonneg_right hn (sq_nonneg (Real.log (n:ℝ))),
    congrArg (ε*·) hsq]

/-- For any cutoff at most √n, the signed mass on the rough at-most-two-factor
set has a linear deficit exactly when the frozen dyadic prime correlation does. -/
theorem dyadic_floor_iff_roughP2_parity_gap (z : ℕ→ℕ)
    (hz : ∀ᶠ n : ℕ in atTop,(z n:ℝ)≤Real.sqrt n) :
    (∃ (c:ℝ) (N:ℕ),0<c ∧ ∀ X n:ℕ,N≤X → X≤n → n<2*X → Even n → c*n≤corr n) ↔
    (∃ d:ℝ,0<d ∧ ∀ᶠ n:ℕ in atTop,Even n →
      d*n ≤ reflectedP2LogMass n (z n)-reflectedP2ParityMass n (z n)) := by
  constructor
  · rintro ⟨c,N,hc,h⟩
    refine ⟨c,hc,?_⟩
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),reflectedP2_cutoff_small z hz c hc] with n hn hp he
    intro hev
    have hh := h n n hn le_rfl (by omega) hev
    have hm := (reflectedP2_parity_cutoff n (z n)).2
    linarith only [hh,hm,he]
  · rintro ⟨d,hd,h⟩
    obtain ⟨T,hT⟩ := eventually_atTop.mp h
    refine ⟨d/2,T,by linarith,?_⟩
    intro X n hX hn _ he
    have hh := hT n (hX.trans hn) he
    have hm := (reflectedP2_parity_cutoff n (z n)).1
    linarith only [hh,hm]

theorem roughP2_parity_dyadic_exception_cubic (z : ℕ→ℕ)
    (hz : ∀ᶠ n : ℕ in atTop,(z n:ℝ)≤Real.sqrt n) :
    ∃ K:ℝ,0<K ∧ ∀ᶠ X:ℕ in atTop,
      ((((Ico X (2*X)).filter Even).filter (fun n =>
        reflectedP2LogMass n (z n)-reflectedP2ParityMass n (z n)<(n:ℝ)/36)).card:ℝ)
          ≤ K*X/(Real.log X)^3 := by
  obtain ⟨K,hK,hbound⟩ := genuine_goldbach_dyadic_exception_cubic
  obtain ⟨T,hT⟩ := eventually_atTop.mp (reflectedP2_cutoff_small z hz (1/36) (by norm_num))
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop T] with X hh hX
  apply le_trans _ hh
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hi,hgap⟩ := mem_filter.mp hn
  apply mem_filter.mpr ⟨hi,?_⟩
  have hcost := hT n (hX.trans (mem_Ico.mp (mem_filter.mp hi).1).1)
  have hm := (reflectedP2_parity_cutoff n (z n)).2
  linarith only [hgap,hcost,hm]

end GoldbachPartial