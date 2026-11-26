import VerifiedVaughanCharacterIdentity
import VerifiedVaughanTypeI
import DivisorSquareMean
import Mathlib.NumberTheory.Chebyshev

namespace GoldbachPartial
open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

private theorem vaughan_lambda_sum (N : ℕ) :
    (∑j∈Icc 1 N,Λ j) ≤ (Real.log 4+4)*N := by
  apply le_trans _ (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) N))
  rw [Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
  exact sum_le_sum_of_subset_of_nonneg (fun j hj => mem_Icc.mpr ⟨Nat.zero_le _,(mem_Icc.mp hj).2⟩)
    (fun _ _ _=>ArithmeticFunction.vonMangoldt_nonneg)

private theorem vaughan_lambda_initial_nonneg (V j : ℕ) : 0≤vaughanInitial V Λ j := by
  change 0 ≤ (if j≤V then Λ j else 0)
  split_ifs <;> first | exact ArithmeticFunction.vonMangoldt_nonneg | exact le_rfl

theorem vaughan_lambda_initial_l1 (N V : ℕ) :
    (∑j∈Icc 1 N,vaughanInitial V Λ j)≤(Real.log 4+4)*V := by
  apply le_trans _ (vaughan_lambda_sum V)
  change (∑j∈Icc 1 N,if j≤V then Λ j else 0)≤_
  rw [←sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (fun j hj=>mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hj).1).1,(mem_filter.mp hj).2⟩)
    (fun _ _ _=>ArithmeticFunction.vonMangoldt_nonneg)

theorem vaughan_mu_initial_l1 (N U : ℕ) :
    (∑ m∈Icc 1 N,|vaughanInitial U (μ : ArithmeticFunction ℝ) m|) ≤ U := by
  calc
    _ ≤ ∑m∈Icc 1 N,if m≤U then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro m _
      change |if m≤U then (μ m:ℝ) else 0|≤_
      by_cases hm : m≤U
      · rw [ite_eq_left hm,ite_eq_left hm]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=m))
      · rw [ite_eq_right hm,ite_eq_right hm,abs_zero]
    _ ≤ _ := by
      rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
      have hs : (Icc 1 N).filter (fun m=>m≤U) ⊆ Icc 1 U := fun m hm=>
        mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hm).1).1,(mem_filter.mp hm).2⟩
      exact_mod_cast (card_le_card hs).trans (by simp : (Icc 1 U).card≤U)

theorem vaughan_short_character_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N V : ℕ) :
    ‖vaughanCharacterSum χ N (vaughanInitial V Λ)‖≤(Real.log 4+4)*V := by
  apply (norm_sum_le ..).trans (le_trans ?_ (vaughan_lambda_initial_l1 N V))
  apply sum_le_sum
  intro m _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (vaughan_lambda_initial_nonneg V m)]
  exact mul_le_of_le_one_right (vaughan_lambda_initial_nonneg V m) (χ.norm_le_one _)

theorem vaughan_typeI_log_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (N U : ℕ) :
    ‖vaughanCharacterBilinear χ N (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log‖ ≤
      (2*((q:ℝ)+1)*Real.log (N+1:ℕ))*U := by
  apply (typeI_log_bound hχ N (Icc 1 N) (fun m => ((vaughanInitial U (μ : ArithmeticFunction ℝ) m):ℂ))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.norm_real,Real.norm_eq_abs] using vaughan_mu_initial_l1 N U

theorem vaughan_typeI_coefficient_l1 (N U V : ℕ) :
    (∑m∈Icc 1 N,|vaughanTypeICoefficient U V m|) ≤ (U:ℝ)*((Real.log 4+4)*V) := by
  let a := fun m => |vaughanInitial U (μ : ArithmeticFunction ℝ) m|
  let b := fun j => vaughanInitial V Λ j
  have hbox (m : ℕ) : (∑j∈Icc 1 (N/m),b j) ≤ (Real.log 4+4)*V := vaughan_lambda_initial_l1 .. 
  calc
    _ ≤ ∑m∈Icc 1 N,∑ x∈m.divisorsAntidiagonal,a x.1*b x.2 := by
      apply sum_le_sum
      intro m _
      rw [vaughanTypeICoefficient,ArithmeticFunction.mul_apply]
      apply (abs_sum_le_sum_abs ..).trans_eq
      apply sum_congr rfl
      intro x _
      rw [abs_mul,abs_of_nonneg (vaughan_lambda_initial_nonneg V _)]
    _ = ∑m∈Icc 1 N,a m*∑j∈Icc 1 (N/m),b j := by rw [vaughan_finite_hyperbola];simp only [mul_sum]
    _ ≤ ∑m∈Icc 1 N,a m*((Real.log 4+4)*V) :=
      sum_le_sum (fun m _=>mul_le_mul_of_nonneg_left (hbox m) (abs_nonneg _))
    _ ≤ _ := by
      rw [←sum_mul]
      exact mul_le_mul_of_nonneg_right (vaughan_mu_initial_l1 N U) (by positivity)

theorem vaughan_typeI_zeta_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (N U V : ℕ) :
    ‖vaughanCharacterBilinear χ N (vaughanTypeICoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      ((q:ℝ)+1)*((U:ℝ)*((Real.log 4+4)*V)) := by
  unfold vaughanCharacterBilinear
  apply (norm_sum_le ..).trans
  rw [mul_comm ((q:ℝ)+1)]
  apply le_trans _ (mul_le_mul_of_nonneg_right (vaughan_typeI_coefficient_l1 N U V) (by positivity))
  rw [sum_mul]
  apply sum_le_sum
  intro m _
  have hinner :
      (∑ j∈Icc 1 (N/m),(((ζ : ArithmeticFunction ℝ) j):ℂ)*χ (j:ZMod q)) =
      ∑ j∈Icc 1 (N/m),χ (j:ZMod q) := by
    apply sum_congr rfl
    intro j hj
    rw [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne (by have := (mem_Icc.mp hj).1;omega)]
    simp
  rw [hinner,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul _ (OAI.LargePrimeGaps.char_sum_Icc_norm_le hχ _) (norm_nonneg _) (abs_nonneg _)
  exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)

theorem vaughan_typeII_left_square_le (U Y : ℕ) (S : Finset ℕ) (hS : S⊆Icc 1 Y) :
    (∑m∈S,(vaughanTypeIICoefficient U m)^2) ≤ (Y:ℝ)*(1+Real.log Y)^3 := by
  apply le_trans _ (divisor_square_mean_bound Y)
  apply (sum_le_sum (fun m (_ : m∈S) => ?_)).trans (sum_le_sum_of_subset_of_nonneg hS (fun i _ _=>sq_nonneg (i.divisors.card:ℝ)))
  rw [←sq_abs (vaughanTypeIICoefficient U m)]
  exact pow_le_pow_left₀ (abs_nonneg _) (vaughanTypeIICoefficient_abs_le U m) _

theorem vaughan_typeII_right_square_le (V Y : ℕ) (S : Finset ℕ) (hS : S⊆Icc 1 Y) :
    (∑j∈S,(vaughanTail V Λ j)^2) ≤ ((Real.log 4+4)*(Y:ℝ))*Real.log Y := by
  rw [mul_comm ((Real.log 4+4)*(Y:ℝ))]
  apply le_trans _ (mul_le_mul_of_nonneg_left (vaughan_lambda_sum Y) (Real.log_natCast_nonneg _))
  rw [mul_sum]
  apply (sum_le_sum (fun j (hj : j∈S) => ?_)).trans (sum_le_sum_of_subset_of_nonneg hS (fun j _ _=>
    mul_nonneg (Real.log_natCast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg))
  rw [vaughanTail_apply]
  by_cases hV : V<j
  · rw [ite_eq_left hV,pow_two]
    have hi := mem_Icc.mp (hS hj)
    have hl : Real.log j ≤ Real.log Y := Real.log_le_log (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
    exact mul_le_mul_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log.trans hl) ArithmeticFunction.vonMangoldt_nonneg
  · rw [ite_eq_right hV,zero_pow (by decide : 2≠0)]
    exact mul_nonneg (Real.log_natCast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

/-- All terms other than the genuine Type II bilinear form are bounded for each
nonprincipal character, without summing over a family of conductors. -/
theorem vaughan_character_minus_typeII_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (N U V : ℕ) :
    ‖vaughanCharacterSum χ N Λ - vaughanCharacterBilinear χ N (vaughanTypeIICoefficient U)
      (vaughanTail V Λ)‖ ≤ (Real.log 4+4)*V + (2*((q:ℝ)+1)*Real.log (N+1:ℕ))*U +
        ((q:ℝ)+1)*((U:ℝ)*((Real.log 4+4)*V)) := by
  rw [vaughan_character_sum_identity χ N U V,add_sub_cancel_right]
  exact (norm_sub_le ..).trans (add_le_add
    ((norm_add_le ..).trans (add_le_add (vaughan_short_character_bound χ N V)
      (vaughan_typeI_log_character_bound hχ N U))) (vaughan_typeI_zeta_character_bound hχ N U V))

theorem vaughan_typeII_rectangle_squares (U V M L : ℕ) (S T : Finset ℕ)
    (hS : S⊆Icc 1 M) (hT : T⊆Icc 1 L) :
    (∑m∈S, (vaughanTypeIICoefficient U m)^2)*(∑j∈T, (vaughanTail V Λ j)^2) ≤
      ((M:ℝ)*(1+Real.log M)^3)*(((Real.log 4+4)*(L:ℝ))*Real.log L) := by
  exact mul_le_mul (vaughan_typeII_left_square_le U M S hS) (vaughan_typeII_right_square_le V L T hT)
    (sum_nonneg fun _ _=>sq_nonneg _) (by positivity)

end GoldbachPartial