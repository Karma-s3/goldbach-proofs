import VerifiedConductorMean
import VerifiedVaughanNumericBounds

namespace GoldbachPartial
open Finset OAI.LargePrimeGaps
open scoped Classical ArithmeticFunction.vonMangoldt

noncomputable def primitiveConductorMass (u : ℕ) (D : Finset ℕ) : ℝ :=
  ∑ q ∈ D, (1/(q.totient:ℝ)) *
    ∑ χ ∈ sievePrimitiveCharacters q, ‖primeCharacterError (u:ℝ) χ‖

noncomputable def vaughanTypeIIConductorMass (u U V : ℕ) (D : Finset ℕ) : ℝ :=
  ∑ q ∈ D, (1/(q.totient:ℝ)) * ∑ χ ∈ sievePrimitiveCharacters q,
    ‖vaughanCharacterBilinear χ u (vaughanTypeIICoefficient U) (vaughanTail V Λ)‖

noncomputable def vaughanShortBound (u Q U V : ℕ) : ℝ :=
  (Real.log 4+4)*V + (2*((Q:ℝ)+1)*Real.log (u+1:ℕ))*U + ((Q:ℝ)+1)*((U:ℝ)*((Real.log 4+4)*V))

theorem primeError_eq_vaughan {q : ℕ} {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (u : ℕ) :
    primeCharacterError (u:ℝ) χ = vaughanCharacterSum χ u Λ := by
  simp only [primeCharacterError,ite_eq_right hne,sub_zero,primeCharacterPrefix,Nat.floor_natCast,
    vaughanCharacterSum,← Icc_succ_left_eq_Ioc]
  exact sum_congr rfl fun _ _ => mul_comm _ _

private theorem typeI_conductor_comparison (u Q U V : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Ioc 1 Q) :
    primitiveConductorMass u D ≤ (Q:ℝ)*vaughanShortBound u Q U V + vaughanTypeIIConductorMass u U V D := by
  let F (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    ‖vaughanCharacterBilinear χ u (vaughanTypeIICoefficient U) (vaughanTail V Λ)‖
  let W := vaughanShortBound u Q U V
  have hW : 0 ≤ W := by dsimp [W,vaughanShortBound]; positivity
  have hrow (q : ℕ) (hq : q∈D) : (1/(q.totient:ℝ)) *
      (∑ χ ∈ sievePrimitiveCharacters q, ‖primeCharacterError (u:ℝ) χ‖) ≤
      W + (1/(q.totient:ℝ))*(∑ χ ∈ sievePrimitiveCharacters q,F q χ) := by
    have hq' := mem_Ioc.mp (hD hq)
    let : NeZero q := ⟨by omega⟩
    have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (show 0<q by omega)
    have hr (χ : DirichletCharacter ℂ q) (hχ : χ ∈ sievePrimitiveCharacters q) :
        ‖primeCharacterError (u:ℝ) χ‖ ≤ W + F q χ := by
      have hne : χ ≠ 1 := by
        rintro rfl
        have he := (mem_filter.mp hχ).2
        change (1:DirichletCharacter ℂ q).conductor = q at he
        rw [DirichletCharacter.conductor_one] at he
        omega
      rw [primeError_eq_vaughan hne]
      have htri := norm_add_le (vaughanCharacterSum χ u Λ -
        vaughanCharacterBilinear χ u (vaughanTypeIICoefficient U) (vaughanTail V Λ))
          (vaughanCharacterBilinear χ u (vaughanTypeIICoefficient U) (vaughanTail V Λ))
      rw [sub_add_cancel] at htri
      refine htri.trans (add_le_add ((vaughan_character_minus_typeII_bound hne u U V).trans ?_) le_rfl)
      dsimp only [W,vaughanShortBound]
      gcongr <;> exact_mod_cast hq'.2
    have hcard : ((sievePrimitiveCharacters q).card:ℝ) ≤ q.totient := by
      exact_mod_cast (card_le_card (subset_univ (sievePrimitiveCharacters q))).trans_eq
        (by simpa only [card_univ,Nat.card_eq_fintype_card] using
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
    have hsum := sum_le_sum hr
    rw [sum_add_distrib,sum_const,nsmul_eq_mul] at hsum
    have h := mul_le_mul_of_nonneg_left (hsum.trans
      (add_le_add (mul_le_mul_of_nonneg_right hcard hW) le_rfl)) (one_div_nonneg.mpr hφ.le)
    rwa [mul_add,← mul_assoc,one_div_mul_cancel hφ.ne',one_mul] at h
  have h := sum_le_sum hrow
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at h
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ hW) le_rfl)
  have hd' := card_le_card hD
  rw [Nat.card_Ioc] at hd'
  exact_mod_cast hd'.trans (Nat.sub_le ..)

theorem high_conductor_dyadic_cover (u Q H U V : ℕ) (hH : 1 ≤ H) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ P : ℕ, 0 < P → P ≤ Q → H < 2*P → ∀ D : Finset ℕ, D ⊆ Ioc H Q →
      (∀ q ∈ D, P < q ∧ q ≤ 2*P) → vaughanTypeIIConductorMass u U V D ≤ B) :
    vaughanTypeIIConductorMass u U V (Ioc H Q) ≤ ((Nat.log 2 Q:ℝ)+1)*B := by
  let I := Ioc H Q
  let k (q : ℕ) := Nat.log 2 (q-1)
  let J := range (Nat.log 2 Q+1)
  have hm : ∀ q ∈ I, k q ∈ J := by
    intro q hq
    exact mem_range_succ_iff.mpr (Nat.log_mono_right ((Nat.sub_le q 1).trans (mem_Ioc.mp hq).2))
  unfold vaughanTypeIIConductorMass
  rw [←sum_fiberwise_of_maps_to hm]
  have hr (i : ℕ) (_hi : i∈J) :
      vaughanTypeIIConductorMass u U V (I.filter fun q => k q = i) ≤ B := by
    let D := I.filter fun q => k q = i
    by_cases hne : D.Nonempty
    · have hf (q : ℕ) (hq : q∈D) : 2^i < q ∧ q ≤ 2*2^i := by
        obtain ⟨hm',hk⟩ := mem_filter.mp hq
        have hs := (mem_Ioc.mp hm').1
        have h0 : q-1 ≠ 0 := by omega
        have hl := Nat.pow_log_le_self 2 h0
        have hh := Nat.lt_pow_succ_log_self (b:=2) (by decide) (q-1)
        change Nat.log 2 (q-1) = i at hk
        rw [hk] at hl
        rw [hk,pow_succ] at hh
        omega
      obtain ⟨q,hq⟩ := hne
      have hh := hf q hq
      have hqI := mem_Ioc.mp (mem_filter.mp hq).1
      exact hblock (2^i) (by positivity) (by omega) (by omega) D (filter_subset ..) hf
    · rw [show I.filter (fun q => k q=i) = ∅ from not_nonempty_iff_eq_empty.mp hne]
      simpa only [vaughanTypeIIConductorMass,sum_empty] using hB
  have h := sum_le_sum hr
  rw [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at h
  exact h

theorem prime_prefix_mean_of_typeII_blocks (u Q H U V : ℕ) (hu : 1 ≤ u) (hH : 1 ≤ H)
    {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ P : ℕ, 0 < P → P ≤ Q → H < 2*P → ∀ D : Finset ℕ, D ⊆ Ioc H Q →
      (∀ q ∈ D, P < q ∧ q ≤ 2*P) → vaughanTypeIIConductorMass u U V D ≤ B) :
    (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError u q) ≤
      (4*(1+Real.log Q)) *
        (primitiveConductorMass u (Icc 1 H) + (Q:ℝ)*vaughanShortBound u Q U V +
          ((Nat.log 2 Q:ℝ)+1)*B) +
      (Q:ℝ)*((Nat.log 2 u:ℝ)*Real.log Q+2*Real.sqrt u*Real.log u) := by
  have hsplit : primitiveConductorMass u (Icc 1 Q) ≤
      primitiveConductorMass u (Icc 1 H)+primitiveConductorMass u (Ioc H Q) := by
    let I := Icc 1 Q
    let F (q : ℕ) := (1/(q.totient:ℝ))*∑ χ ∈ sievePrimitiveCharacters q, ‖primeCharacterError (u:ℝ) χ‖
    have hp := sum_filter_add_sum_filter_not I (fun q => q≤H) F
    have hf (q : ℕ) : 0 ≤ F q := mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _)
    change (∑ q ∈ I, F q) ≤ (∑ q ∈ Icc 1 H, F q) + ∑ q ∈ Ioc H Q, F q
    rw [←hp]
    apply add_le_add <;> apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hf q)
    · intro q hq
      obtain ⟨hq,h⟩ := mem_filter.mp hq
      exact mem_Icc.mpr ⟨(mem_Icc.mp hq).1,h⟩
    · intro q hq
      obtain ⟨hq,h⟩ := mem_filter.mp hq
      exact mem_Ioc.mpr ⟨lt_of_not_ge h,(mem_Icc.mp hq).2⟩
  have hcomp := typeI_conductor_comparison u Q U V (Ioc H Q) (fun q hq =>
    mem_Ioc.mpr ⟨hH.trans_lt (mem_Ioc.mp hq).1,(mem_Ioc.mp hq).2⟩)
  have hcov := high_conductor_dyadic_cover u Q H U V hH hB hblock
  apply (prime_prefix_mean_le_primitive u Q hu).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change primitiveConductorMass u (Icc 1 Q) ≤ _
  linarith only [hsplit,hcomp,hcov]

end GoldbachPartial