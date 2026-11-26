import FejerDilationGram
import DyadicFejerDefinitions

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

noncomputable def fejerGramMultiplicity (M:ℕ) (h:ℤ) : ℕ :=
  (((range M) ×ˢ (range M)).filter (fun p => (p.1:ℤ)-p.2=h)).card

noncomputable def fejerTriangleCoefficient (M : ℕ) (h : ℤ) : ℂ :=
  (fejerGramMultiplicity M h:ℂ)/(M:ℂ)

theorem fejerGramMultiplicity_le (M:ℕ) (h:ℤ) : fejerGramMultiplicity M h ≤ M := by
  unfold fejerGramMultiplicity
  apply le_trans _ (card_range M).le
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (mem_product.mp (mem_filter.mp hp).1).1
  · intro p hp r hr hpr
    have hp' := (mem_filter.mp hp).2
    have hr' := (mem_filter.mp hr).2
    exact Prod.ext hpr (by omega)

theorem fejerTriangleCoefficient_norm_le (M:ℕ) (h:ℤ) : ‖fejerTriangleCoefficient M h‖ ≤ 1 := by
  by_cases hM:M=0
  · simp [hM,fejerTriangleCoefficient]
  have hpos : (0:ℝ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [fejerTriangleCoefficient,norm_div,Complex.norm_natCast,Complex.norm_natCast,div_le_one hpos]
  exact_mod_cast fejerGramMultiplicity_le M h

private theorem dilation_fejer_conj (t:ℝ): (starRingEnd ℂ) (E t)=E (-t) := by
  unfold E
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

theorem fejerWave_fourier (M K:ℕ) (hM:0<M) (hMK:M≤K+1) (x:ℝ) :
    (fejerWave M x:ℂ) = fejerGramPolynomial K (fejerTriangleCoefficient M) x := by
  let S := (range M) ×ˢ (range M)
  let f (p:ℕ×ℕ) : ℤ := (p.1:ℤ)-p.2
  have hmem (p:ℕ×ℕ) (hp:p∈S) : f p∈fejerGramModes K := by
    have ha := mem_range.mp (mem_product.mp hp).1
    have hb := mem_range.mp (mem_product.mp hp).2
    apply mem_Icc.mpr
    dsimp only [f]; omega
  have hexp : ((‖dirichletGeometricKernel (M-1) x‖^2:ℝ):ℂ) =
      ∑ p ∈ S, E (((f p):ℝ)*x) := by
    rw [Complex.ofReal_pow,←Complex.mul_conj']
    unfold dirichletGeometricKernel
    rw [Nat.sub_add_cancel hM,map_sum,Finset.sum_mul,Finset.sum_product]
    apply sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro b _
    dsimp only [f]
    rw [dilation_fejer_conj,←phase_add]
    congr 1
    push_cast
    ring
  have hsplit := Finset.sum_fiberwise_of_maps_to (t:=fejerGramModes K) hmem (fun p => E (((f p):ℝ)*x))
  dsimp only [fejerWave,fejerGramPolynomial]
  rw [Complex.ofReal_div,hexp,Complex.ofReal_natCast,←hsplit,Finset.sum_div]
  apply sum_congr rfl
  intro h _
  have hsum : (∑ p ∈ S.filter (fun p => f p=h), E (((f p):ℝ)*x)) =
      (fejerGramMultiplicity M h:ℂ)*E ((h:ℝ)*x) := by
    calc
      _ = ∑ _p ∈ S.filter (fun p => f p=h), E ((h:ℝ)*x) :=
        sum_congr rfl fun p hp => by rw [(mem_filter.mp hp).2]
      _ = _ := by simp [fejerGramMultiplicity,S,f,nsmul_eq_mul]
  rw [hsum]
  unfold fejerTriangleCoefficient
  ring

noncomputable def dyadicFejerFourierCoefficient (Q:ℕ) (h:ℤ):ℂ :=
  ∑ j ∈ range (Nat.log 2 Q+1), fejerTriangleCoefficient (2^j) h

theorem dyadicFejerFourierCoefficient_bound (Q:ℕ) (h:ℤ) :
    ‖dyadicFejerFourierCoefficient Q h‖ ≤ ((Nat.log 2 Q+1:ℕ):ℝ) := by
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _j ∈ range (Nat.log 2 Q+1), (1:ℝ) := sum_le_sum fun j _ => fejerTriangleCoefficient_norm_le .. 
    _ = _ := by simp

theorem dyadicFejerEnvelope_fourier (Q:ℕ) (x:ℝ) :
    (dyadicFejerEnvelope Q x:ℂ) = fejerGramPolynomial Q (dyadicFejerFourierCoefficient Q) x := by
  have hexp (j:ℕ) (hj:j∈range (Nat.log 2 Q+1)) :
      (fejerWave (2^j) x:ℂ) = fejerGramPolynomial Q (fejerTriangleCoefficient (2^j)) x := by
    apply fejerWave_fourier _ _ (by positivity)
    by_cases hQ:Q=0
    · subst Q
      simp at hj
      simp [hj]
    · have hj' : j≤Nat.log 2 Q := Nat.le_of_lt_succ (mem_range.mp hj)
      exact (Nat.pow_le_pow_right (by decide : 0<2) hj').trans ((Nat.pow_log_le_self 2 hQ).trans (Nat.le_succ _))
  unfold dyadicFejerEnvelope
  push_cast
  rw [sum_congr rfl hexp]
  unfold fejerGramPolynomial dyadicFejerFourierCoefficient
  rw [sum_comm]
  exact sum_congr rfl fun h _ => (sum_mul ..).symm

end GoldbachPartial