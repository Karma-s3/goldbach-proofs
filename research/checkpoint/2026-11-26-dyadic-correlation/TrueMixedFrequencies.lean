import MixedMobiusGRHReduction
import GcdDilationFamily
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

noncomputable def nonresonantCoefficient (n D q k : ℕ) : ℝ :=
  ∑ d ∈ ((Ioc D n).filter (fun d => ¬q∣d)).filter (fun d => d∣k),crtLambdaCoefficient d

theorem nonresonantWave_at_frequencies (n D q : ℕ) (t : ℝ) :
    nonresonantMobiusWave n D q t=∑ k∈Icc 1 n,(nonresonantCoefficient n D q k:ℂ)*E ((k:ℝ)*t) := by
  unfold nonresonantMobiusWave nonresonantCoefficient
  rw [smallDivisorWave_coefficients]
  simp only [Complex.ofReal_sum]

theorem nonresonantCoefficient_bound {k : ℕ} (hk : 0<k) (n D q : ℕ) :
    |nonresonantCoefficient n D q k|≤(k.divisors.card:ℝ)*Real.log n := by
  let I := ((Ioc D n).filter (fun d => ¬q∣d)).filter (fun d => d∣k)
  have hs : I⊆k.divisors := fun d hd => Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2,hk.ne'⟩
  apply (abs_sum_le_sum_abs ..).trans
  change (∑ d∈I,|crtLambdaCoefficient d|)≤_
  calc
    _ ≤ ∑ _d∈I,Real.log n := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hd).1).1
      rw [crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg d)]
      have hmu : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
      exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hmu).trans
        (Real.log_le_log (by exact_mod_cast (show 0<d by omega)) (by exact_mod_cast hu))
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hs) (Real.log_natCast_nonneg _)

noncomputable def trueMixedFrequencyRow (n D q k : ℕ) (ρ : ℝ) : ℂ :=
  ∑ a∈(range q).filter (fun a=>a.Coprime q),∫ β in -ρ..ρ,
    let t := β+(a:ℝ)/q
    2*(nonresonantCoefficient n D q k:ℂ)*E ((k:ℝ)*t)*
      resonantMobiusWave n D n q t*E (-(n:ℝ)*t)

theorem trueMixedFrequencyRow_exact (n D q k : ℕ) (hq : 0<q) (hk : k≤n) (ρ : ℝ) :
    trueMixedFrequencyRow n D q k ρ =
      (2*(nonresonantCoefficient n D q k:ℂ)*(dyadicRamanujanDivisor (n-k) q:ℂ))*
      (∫ β in -ρ..ρ,resonantMobiusWave n D n q β*E (-((n-k:ℕ):ℝ)*β)) := by
  let U := (range q).filter (fun a=>a.Coprime q)
  let T := resonantMobiusWave n D n q
  let b := (nonresonantCoefficient n D q k:ℂ)
  have h (a : ℕ) (β : ℝ) :
      2*b*E ((k:ℝ)*(β+(a:ℝ)/q))*T (β+(a:ℝ)/q)*E (-(n:ℝ)*(β+(a:ℝ)/q)) =
        E (-(((n-k:ℕ):ℝ)*a/q)) * ((2*b)*(T β*E (-((n-k:ℕ):ℝ)*β))) := by
    rw [show T (β+(a:ℝ)/q) = T β from resonantMobiusWave_at_center hq n D n a β]
    rw [show 2*b*E ((k:ℝ)*(β+(a:ℝ)/q))*T β*E (-(n:ℝ)*(β+(a:ℝ)/q)) =
      (2*b*T β)*(E ((k:ℝ)*(β+(a:ℝ)/q))*E (-(n:ℝ)*(β+(a:ℝ)/q))) by ring,←phase_add]
    rw [show (k:ℝ)*(β+(a:ℝ)/q) + -(n:ℝ)*(β+(a:ℝ)/q) =
      -(((n-k:ℕ):ℝ)*a/q) + -((n-k:ℕ):ℝ)*β by rw [Nat.cast_sub hk];ring,phase_add]
    ring
  change (∑ a∈U,∫ β in -ρ..ρ,2*b*E ((k:ℝ)*(β+(a:ℝ)/q))*T (β+(a:ℝ)/q)*E (-(n:ℝ)*(β+(a:ℝ)/q)))=_
  simp_rw [h,intervalIntegral.integral_const_mul]
  rw [←sum_mul]
  change (∑ a∈(range q).filter (fun a=>a.Coprime q),E (-(((n-k:ℕ):ℝ)*a/q)))*_=_
  rw [actualRamanujan_neg_eq_divisor (n-k) q hq]
  change _=2*b*_*(∫ β in -ρ..ρ,T β*E (-((n-k:ℕ):ℝ)*β))
  ring

noncomputable def trueMixedFrequencyBand (n D R Q : ℕ) (I : Finset ℕ) : ℂ :=
  ∑ k∈I, ∑ j∈Ico R Q,trueMixedFrequencyRow n D (j+1) k (naturalTubeRadius (3*Q) (j+1))

noncomputable def nonresonantSquareMass (n D R Q : ℕ) : ℂ :=
  ∑ j∈Ico R Q,∑ a∈(range (j+1)).filter (fun a=>a.Coprime (j+1)),
    ∫ β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),
      let t := β+(a:ℝ)/((j+1:ℕ):ℝ)
      (nonresonantMobiusWave n D (j+1) t)^2*E (-(n:ℝ)*t)

theorem trueMixedFrequencyBand_complete (n D R Q : ℕ) :
    nonresonantMobiusRemainderMass n D R Q =
      nonresonantSquareMass n D R Q + trueMixedFrequencyBand n D R Q (Icc 1 n) := by
  unfold nonresonantMobiusRemainderMass nonresonantSquareMass trueMixedFrequencyBand
  rw [sum_comm (s:=Icc 1 n),←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold trueMixedFrequencyRow
  rw [sum_comm (s:=Icc 1 n),←sum_add_distrib]
  apply sum_congr rfl
  intro a _
  let q := j+1
  let ρ := naturalTubeRadius (3*Q) q
  let t := fun β:ℝ => β+(a:ℝ)/(q:ℝ)
  let T := resonantMobiusWave n D n q
  let N := nonresonantMobiusWave n D q
  let g := fun k β => 2*(nonresonantCoefficient n D q k:ℂ)*E ((k:ℝ)*t β)*T (t β)*E (-(n:ℝ)*t β)
  let F := fun β => (N (t β))^2*E (-(n:ℝ)*t β)
  have hF : Continuous F := by unfold F N t nonresonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hc (k : ℕ) : Continuous (g k) := by unfold g t T resonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hsum : Continuous (fun β => ∑ k∈Icc 1 n,g k β) := continuous_finsetSum (Icc 1 n) (fun k _ => hc k)
  change _=(∫ β in -ρ..ρ,F β)+∑ k∈Icc 1 n,∫ β in -ρ..ρ,g k β
  rw [←intervalIntegral.integral_finsetSum (fun k _ => (hc k).intervalIntegrable _ _),
    ←intervalIntegral.integral_add (hF.intervalIntegrable _ _) (hsum.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro β _
  change (N (t β)^2+2*N (t β)*T (t β))*E (-(n:ℝ)*t β)=F β+∑ k∈Icc 1 n,g k β
  dsimp only [F,g]
  rw [add_mul]
  congr 1
  rw [show N (t β)=_ from nonresonantWave_at_frequencies n D q (t β),mul_sum,sum_mul,sum_mul]
  simp only [mul_assoc]


private theorem mixed_one_row_bound {n k : ℕ} (hk0 : 0<k) (hk : k≤n) (D R Q : ℕ) {B : ℝ}
    (hT : ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤B)
    {j : ℕ} (hj : j∈Ico R Q) :
    ‖trueMixedFrequencyRow n D (j+1) k (naturalTubeRadius (3*Q) (j+1))‖ ≤
      (4/(3*(Q:ℝ))*(k.divisors.card:ℝ)*Real.log n*B)*
        (|(dyadicRamanujanDivisor (n-k) (j+1):ℝ)|/((j+1:ℕ):ℝ)) := by
  let q := j+1
  let ρ := naturalTubeRadius (3*Q) q
  have hq : 0<q := Nat.succ_pos _
  have hρ : 0≤ρ := by dsimp [ρ,naturalTubeRadius];positivity
  have hi : ‖∫ β in -ρ..ρ,resonantMobiusWave n D n q β*E (-((n-k:ℕ):ℝ)*β)‖ ≤ B*(2*ρ) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=B) (fun t _ => ?_)).trans_eq
    · rw [sub_neg_eq_add,abs_of_nonneg (add_nonneg hρ hρ)];ring
    · rw [norm_mul,show ‖E (-((n-k:ℕ):ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
      exact hT j hj t
  have hcast : ‖(dyadicRamanujanDivisor (n-k) q:ℂ)‖=|(dyadicRamanujanDivisor (n-k) q:ℝ)| := by norm_cast
  rw [trueMixedFrequencyRow_exact n D q k hq hk,norm_mul,norm_mul,norm_mul,hcast,
    Complex.norm_real,Real.norm_eq_abs]
  norm_num only [Complex.norm_ofNat]
  apply (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (nonresonantCoefficient_bound hk0 n D q) (by norm_num : (0:ℝ)≤2)) (abs_nonneg _))
      hi (norm_nonneg _) (by positivity)).trans_eq
  change _=4/(3*(Q:ℝ))*(k.divisors.card:ℝ)*Real.log n*B*(|(dyadicRamanujanDivisor (n-k) q:ℝ)|/(q:ℝ))
  dsimp only [ρ,naturalTubeRadius]
  push_cast
  ring

theorem trueMixedFrequencyBand_nonzero_bound {n : ℕ} (D R Q : ℕ) (I : Finset ℕ)
    (hI : ∀ k∈I,0<k ∧ k<n) {B : ℝ} (hB : 0≤B)
    (hT : ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤B) :
    ‖trueMixedFrequencyBand n D R Q I‖ ≤ (4/(3*(Q:ℝ))*Real.log n*B*(1+Real.log Q))*
      ∑ k∈I,(k.divisors.card:ℝ)*((n-k).divisors.card:ℝ) := by
  unfold trueMixedFrequencyBand
  rw [mul_sum]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro k hk
  obtain ⟨hk0,hkn⟩ := hI k hk
  let C := 4/(3*(Q:ℝ))*(k.divisors.card:ℝ)*Real.log n*B
  have hC : 0≤C := by dsimp only [C]; positivity
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ j∈Ico R Q,C*(|(dyadicRamanujanDivisor (n-k) (j+1):ℝ)|/((j+1:ℕ):ℝ)) :=
      sum_le_sum fun j hj => mixed_one_row_bound hk0 hkn.le D R Q hT hj
    _ = _ := (mul_sum ..).symm
    _ ≤ C*((1+Real.log Q)*((n-k).divisors.card:ℝ)) := mul_le_mul_of_nonneg_left
      (resonantRamanujan_harmonic (n-k) R Q (by omega)) hC
    _ = _ := by dsimp only [C];ring

theorem trueMixedFrequencyBand_zero_bound {n : ℕ} (hn : 0<n) (D R Q : ℕ)
    {B : ℝ} (hB : 0≤B)
    (hT : ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤B) :
    ‖trueMixedFrequencyBand n D R Q {n}‖≤(4/(3*(Q:ℝ))*(n.divisors.card:ℝ)*Real.log n*B)*(Q:ℝ) := by
  let C := 4/(3*(Q:ℝ))*(n.divisors.card:ℝ)*Real.log n*B
  have hC : 0≤C := by dsimp only [C]; positivity
  simp only [trueMixedFrequencyBand,sum_singleton]
  apply (norm_sum_le ..).trans
  have hrow (j : ℕ) (hj : j∈Ico R Q) :
      ‖trueMixedFrequencyRow n D (j+1) n (naturalTubeRadius (3*Q) (j+1))‖ ≤ C := by
    apply (mixed_one_row_bound hn le_rfl D R Q hT hj).trans
    rw [Nat.sub_self]
    have hz := unit_exp_ramanujan_eq_divisor 0 (j+1)
    simp [E,ZMod.card_units_eq_totient] at hz
    have h0 : dyadicRamanujanDivisor 0 (j+1) = ((j+1).totient:ℤ) := by exact_mod_cast hz.symm
    rw [h0,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _)]
    apply mul_le_of_le_one_right hC
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.totient_le _)
  apply (sum_le_sum hrow).trans
  change (∑ _j∈Ico R Q,C)≤C*(Q:ℝ)
  rw [sum_const,nsmul_eq_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_right (by rw [Nat.card_Ico];exact_mod_cast Nat.sub_le Q R) hC

end GoldbachPartial