import NonresonantSquareShortModes
import GoldbachCRTRemainder

namespace GoldbachPartial
open Finset Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable def truncatedLambdaDivisors (D k : ℕ) : ℝ :=
  ∑ d∈k.divisors.filter (fun d => d≤D),crtLambdaCoefficient d

theorem unrestrictedLargeCoefficient (n D k : ℕ) (hk : 0<k) (hkn : k≤n) :
    nonresonantCoefficient n D 0 k = Λ k - truncatedLambdaDivisors D k := by
  have hi : ((Ioc D n).filter (fun d => ¬0∣d)).filter (fun d => d∣k) =
      k.divisors.filter (fun d => ¬d≤D) := by
    ext d
    simp only [mem_filter,mem_Ioc,Nat.mem_divisors,Nat.zero_dvd]
    constructor
    · rintro ⟨⟨⟨hd,_⟩,_⟩,hdk⟩
      exact ⟨⟨hdk,hk.ne'⟩,by omega⟩
    · rintro ⟨⟨hdk,_⟩,hd⟩
      exact ⟨⟨⟨by omega,(Nat.le_of_dvd hk hdk).trans hkn⟩,by omega⟩,hdk⟩
  have hsum : (∑ d∈k.divisors,crtLambdaCoefficient d)=Λ k := by
    have h := ArithmeticFunction.sum_moebius_mul_log_eq (n:=k)
    simp only [ArithmeticFunction.log_apply] at h
    simp only [crtLambdaCoefficient,neg_mul,sum_neg_distrib,h,neg_neg]
  unfold nonresonantCoefficient truncatedLambdaDivisors
  rw [hi,←hsum]
  have hs := sum_filter_add_sum_filter_not k.divisors (fun d => d≤D) crtLambdaCoefficient
  linarith only [hs]

theorem nonresonantSquare_zero_eq_sum (n D q : ℕ) :
    nonresonantSquareModeCoefficient n D q 0 =
      ∑ k∈Ioo 0 n,nonresonantCoefficient n D q k*nonresonantCoefficient n D q (n-k) := by
  symm
  change _ = ∑ u∈(Icc 1 n ×ˢ Icc 1 n).filter (fun u => farPairFrequency n u.1 u.2=0),
    nonresonantCoefficient n D q u.1 * nonresonantCoefficient n D q u.2
  apply sum_bij (fun k _ => (k,n-k))
  · intro k hk
    obtain ⟨h0,hn⟩ := mem_Ioo.mp hk
    apply mem_filter.mpr
    constructor
    · exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,mem_Icc.mpr ⟨by omega,by omega⟩⟩
    · change (k:ℤ)+((n-k:ℕ):ℤ)-n=0
      omega
  · intro k _ j _ he
    exact congrArg Prod.fst he
  · rintro ⟨k,l⟩ he
    obtain ⟨hb,hf⟩ := mem_filter.mp he
    obtain ⟨hk,hl⟩ := mem_product.mp hb
    obtain ⟨hk₁,hkn⟩ := mem_Icc.mp hk
    obtain ⟨hl₁,hln⟩ := mem_Icc.mp hl
    change (k:ℤ)+l-n=0 at hf
    refine ⟨k,mem_Ioo.mpr ⟨by omega,by omega⟩,Prod.ext rfl ?_⟩
    change n-k=l
    omega
  · intro _ _
    rfl

/-- The two corrections contain, respectively, only small divisors, and one
von Mangoldt factor paired with a sum over small divisors. -/
noncomputable def smallDivisorZeroCorrection (n D : ℕ) : ℝ :=
  (∑ k∈Ioo 0 n,truncatedLambdaDivisors D k*truncatedLambdaDivisors D (n-k)) -
    2*∑ k∈Ioo 0 n,Λ k*truncatedLambdaDivisors D (n-k)

theorem largeDivisor_zero_decomposition (n D : ℕ) :
    nonresonantSquareModeCoefficient n D 0 0 =
      crtLambdaConvolution n + smallDivisorZeroCorrection n D := by
  let s := truncatedLambdaDivisors D
  have href : (∑ k∈Ioo 0 n,s k * Λ (n-k))=∑ k∈Ioo 0 n,Λ k*s (n-k) := by
    apply sum_bij (fun k _ => n-k)
    · intro k hk
      have h := mem_Ioo.mp hk
      exact mem_Ioo.mpr ⟨by omega,by omega⟩
    · intro k hk j hj he
      have h₁ := mem_Ioo.mp hk
      have h₂ := mem_Ioo.mp hj
      omega
    · intro k hk
      have h := mem_Ioo.mp hk
      exact ⟨n-k,mem_Ioo.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro k hk
      have h := mem_Ioo.mp hk
      rw [show n-(n-k)=k by omega,mul_comm]
  rw [nonresonantSquare_zero_eq_sum]
  have hid : (∑ k∈Ioo 0 n, nonresonantCoefficient n D 0 k * nonresonantCoefficient n D 0 (n-k)) =
      ∑ k∈Ioo 0 n, (Λ k*Λ (n-k) + s k*s (n-k) - Λ k*s (n-k) - s k*Λ (n-k)) := by
    apply sum_congr rfl
    intro k hk
    obtain ⟨h0,hn⟩ := mem_Ioo.mp hk
    rw [unrestrictedLargeCoefficient n D k h0 hn.le,
      unrestrictedLargeCoefficient n D (n-k) (by omega) (Nat.sub_le ..)]
    dsimp only [s];ring
  rw [hid,sum_sub_distrib,sum_sub_distrib,sum_add_distrib,href]
  unfold crtLambdaConvolution smallDivisorZeroCorrection
  dsimp only [s]
  ring

theorem largeDivisor_zero_sub_corr_error {n : ℕ} (hn : 1≤n) (D : ℕ) :
    |nonresonantSquareModeCoefficient n D 0 0 -
      (corr n + smallDivisorZeroCorrection n D)| ≤ 4*Real.sqrt n*(Real.log n)^2 := by
  rw [largeDivisor_zero_decomposition,add_sub_add_right_eq_sub,
    abs_of_nonneg (crtLambdaConvolution_prime_error hn).1]
  exact (crtLambdaConvolution_prime_error hn).2

end GoldbachPartial