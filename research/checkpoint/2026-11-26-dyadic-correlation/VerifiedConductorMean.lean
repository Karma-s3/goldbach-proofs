import VerifiedBrunDistributionBudget
import VerifiedPrimitiveSieveTransfer
import ResonantModelEnergy

namespace GoldbachPartial
open Finset OAI.LargePrimeGaps
open scoped Classical

private theorem primitive_conductor_row {q : ℕ} (hq : 0 < q)
    (F : (d : ℕ) → DirichletCharacter ℂ d → ℝ) (hF : ∀ d χ, 0 ≤ F d χ) :
    (∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter) ≤
      ∑ d ∈ q.divisors, ∑ ψ ∈ sievePrimitiveCharacters d, F d ψ := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let lift (p : (r : ℕ) × DirichletCharacter ℂ r) : DirichletCharacter ℂ q :=
    if h : p.1 ∣ q then p.2.changeLevel h else 1
  let idx (χ : DirichletCharacter ℂ q) : (d : ℕ) × DirichletCharacter ℂ d :=
    ⟨χ.conductor, χ.primitiveCharacter⟩
  have hinv (χ : DirichletCharacter ℂ q) : lift (idx χ) = χ := by
    dsimp only [idx,lift]
    rw [dite_eq_left χ.conductor_dvd_level, DirichletCharacter.changeLevel_primitiveCharacter]
  rw [sum_sigma']
  apply sum_le_sum_of_injOn idx
  · intro χ _ ψ _ h
    rw [← hinv χ, ← hinv ψ, h]
  · intro p hp
    obtain ⟨χ, _, rfl⟩ := mem_image.mp hp
    exact mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq.ne'⟩,
      mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩⟩
  · intro χ _
    exact le_rfl
  · intro p _ _
    exact hF p.1 p.2

private theorem totient_divisor_average (Q : ℕ) (W : ℕ → ℝ) (hW : ∀ r, 0 ≤ W r) :
    (∑ q ∈ Icc 1 Q, (1/(q.totient:ℝ)) * ∑ r ∈ q.divisors, W r) ≤
      (4*(1+Real.log Q)) * ∑ r ∈ Icc 1 Q, (1/(r.totient:ℝ))*W r := by
  let I := Icc 1 Q
  let H := I.sigma Nat.divisors
  let f (p : (q : ℕ) × ℕ) : ℕ × ℕ := (p.2, p.1/p.2)
  have facts (p : (q : ℕ) × ℕ) (hp : p∈H) :
      0 < p.1 ∧ p.1 ≤ Q ∧ 0 < p.2 ∧ p.2 ∣ p.1 := by
    obtain ⟨h1,h2⟩ := mem_sigma.mp hp
    exact ⟨(mem_Icc.mp h1).1,(mem_Icc.mp h1).2,Nat.pos_of_mem_divisors h2,
      (Nat.mem_divisors.mp h2).1⟩
  have hpair : (∑ p ∈ H, (1/(p.1.totient:ℝ))*W p.2) ≤
      ∑ z ∈ I ×ˢ I, (1/(z.2.totient:ℝ))*((1/(z.1.totient:ℝ))*W z.1) := by
    apply sum_le_sum_of_injOn f
    · intro p hp v hv he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      change p.2=v.2 at h1
      change p.1/p.2=v.1/v.2 at h2
      have hk : p.1 = v.1 := by
        rw [← Nat.div_mul_cancel (facts p hp).2.2.2, h2,h1,
          Nat.div_mul_cancel (facts v hv).2.2.2]
      obtain ⟨p,r⟩ := p
      obtain ⟨v,s⟩ := v
      change p=v at hk
      change r=s at h1
      cases hk; cases h1; rfl
    · intro z hz
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
      obtain ⟨hpos,hQ,hr,hd⟩ := facts p hp
      have hrq := Nat.le_of_dvd hpos hd
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hr,hrq.trans hQ⟩,
        mem_Icc.mpr ⟨Nat.div_pos hrq hr,(Nat.div_le_self _ _).trans hQ⟩⟩
    · intro p hp
      obtain ⟨hpos,_,hr,hd⟩ := facts p hp
      have hb := Nat.totient_super_multiplicative (p.1/p.2) p.2
      rw [Nat.div_mul_cancel hd] at hb
      have hl : (0:ℝ)<(p.1/p.2).totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hpos hd) hr)
      have hr' : (0:ℝ)<p.2.totient := by exact_mod_cast Nat.totient_pos.mpr hr
      have hc := one_div_le_one_div_of_le (mul_pos hl hr') (show
        ((p.1/p.2).totient:ℝ)*p.2.totient ≤ p.1.totient by exact_mod_cast hb)
      dsimp only [f]
      calc _ ≤ (1/(((p.1/p.2).totient:ℝ)*p.2.totient))*W p.2 :=
            mul_le_mul_of_nonneg_right hc (hW _)
           _ = _ := by ring
    · intro z _ _
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hW _))
  have hT := modelTotientReciprocal_sum 0 Q
  rw [Finset.sum_Ico_add' (fun k : ℕ => 1/(k.totient:ℝ)) 0 Q (c:=1)] at hT
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc] at hT
  change (∑ q ∈ I, _) ≤ _
  simp_rw [mul_sum]
  rw [sum_sigma']
  apply hpair.trans
  rw [sum_product]
  simp_rw [← sum_mul]
  rw [← mul_sum, ← mul_sum]
  exact mul_le_mul_of_nonneg_right hT (sum_nonneg fun r _ => mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) r.totient)) (hW r))

theorem primitive_conductor_average (Q : ℕ) (F : (d : ℕ) → DirichletCharacter ℂ d → ℝ)
    (hF : ∀ d χ, 0 ≤ F d χ) :
    (∑ q ∈ Icc 1 Q, (1/(q.totient:ℝ)) * ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter) ≤
      (4*(1+Real.log Q)) * ∑ d ∈ Icc 1 Q, (1/(d.totient:ℝ)) *
        ∑ ψ ∈ sievePrimitiveCharacters d, F d ψ := by
  refine le_trans (sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left
    (primitive_conductor_row (mem_Icc.mp hq).1 F hF) (by positivity))) ?_
  exact totient_divisor_average Q _ (fun r => sum_nonneg fun χ _ => hF r χ)

private theorem conductor_class_error_row (u q : ℕ) (hu : 1 ≤ u) (hq : 0 < q) :
    brunPrimePrefixMaxError u q ≤
      (1/(q.totient:ℝ)) * ∑ χ : DirichletCharacter ℂ q,
        ‖primeCharacterError (u:ℝ) χ.primitiveCharacter‖ +
      ((Nat.log 2 u:ℝ)*Real.log q + 2*Real.sqrt u*Real.log u) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hw := sum_le_sum (s:=univ) (fun (χ : DirichletCharacter ℂ q) _ =>
    primeCharacterError_le_primitive (u:ℝ) hq χ)
  simp only [Nat.floor_natCast, sum_add_distrib, sum_const, card_univ, hcard,nsmul_eq_mul] at hw
  have hP := (GoldbachMajorArc.prime_power_correction u q)
  unfold brunPrimePrefixMaxError
  apply sup'_le
  intro a _
  split_ifs with ha
  · have hc := endpointClassError_le_character_sum (u:ℝ) hq ha.1 ha.2
    rw [Nat.floor_natCast] at hc
    have hr := (hP a).trans (Chebyshev.psi_sub_theta_le (by exact_mod_cast hu : (1:ℝ)≤u))
    refine (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt u q a) _).trans
      ((add_le_add hr hc).trans ?_)
    have hs := div_le_div_of_nonneg_right hw hφ.le
    rw [add_div, mul_div_cancel_left₀ _ hφ.ne'] at hs
    simp only [div_eq_mul_inv,one_mul] at hs ⊢
    linarith only [hs]
  · exact add_nonneg (mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _))
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
       (mul_nonneg (by positivity) (Real.log_natCast_nonneg _)))

/-- The maximum over reduced residue classes, summed over all positive moduli.
The character sum is only over primitive characters at their own conductor. -/
theorem prime_prefix_mean_le_primitive (u Q : ℕ) (hu : 1 ≤ u) :
    (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError u q) ≤
      (4*(1+Real.log Q)) * (∑ d ∈ Icc 1 Q, (1/(d.totient:ℝ)) *
        ∑ ψ ∈ sievePrimitiveCharacters d, ‖primeCharacterError (u:ℝ) ψ‖) +
      (Q:ℝ)*((Nat.log 2 u:ℝ)*Real.log Q+2*Real.sqrt u*Real.log u) := by
  have hr := sum_le_sum (s:=Icc 1 Q) (fun q hq => conductor_class_error_row u q hu (mem_Icc.mp hq).1)
  rw [sum_add_distrib] at hr
  apply hr.trans
  apply add_le_add (primitive_conductor_average Q (fun _ χ => ‖primeCharacterError (u:ℝ) χ‖)
    (fun _ χ => norm_nonneg _))
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, ((Nat.log 2 u:ℝ)*Real.log Q + 2*Real.sqrt u*Real.log u) := by
      apply sum_le_sum
      intro q hq
      have hlog := Real.log_le_log (by exact_mod_cast (mem_Icc.mp hq).1 : (0:ℝ)<q)
        (by exact_mod_cast (mem_Icc.mp hq).2 : (q:ℝ)≤Q)
      exact add_le_add (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) le_rfl
    _ = _ := by simp [Nat.card_Icc, nsmul_eq_mul, mul_add]

/-- Polylogarithmic conductors, including the principal character at conductor one.
The exponent A in the conclusion can be chosen before the cutoff exponent B. -/
theorem primitive_small_conductor_mean (A B : ℕ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℕ in Filter.atTop, ∀ H : ℕ, (H:ℝ) ≤ (Real.log u)^B →
      (∑ d ∈ Icc 1 H, (1/(d.totient:ℝ)) *
        ∑ ψ ∈ sievePrimitiveCharacters d, ‖primeCharacterError (u:ℝ) ψ‖) ≤ C*u/(Real.log u)^A := by
  let k := A+B+1
  have hk : (0:ℝ)<k := by dsimp [k]; positivity
  obtain ⟨C,hC,u₀,_,hSW⟩ := siegelWalfisz (k:ℝ) (B:ℝ) hk (by exact_mod_cast hB)
  refine ⟨C,hC,?_⟩
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [ht, Filter.eventually_ge_atTop ⌈u₀⌉₊] with u hu h₀
  intro H hH
  let L := Real.log u
  change 1 ≤ L at hu
  have hL : 0<L := by linarith
  have h₀' := (Nat.le_ceil u₀).trans (by exact_mod_cast h₀ : (⌈u₀⌉₊:ℝ)≤u)
  have hr (d : ℕ) (hd : d ∈ Icc 1 H) :
      (1/(d.totient:ℝ))*(∑ ψ ∈ sievePrimitiveCharacters d, ‖primeCharacterError (u:ℝ) ψ‖)
        ≤ C*u/L^k := by
    have hpos := (mem_Icc.mp hd).1
    let : NeZero d := ⟨Nat.ne_of_gt hpos⟩
    have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hpos
    have hcard : (sievePrimitiveCharacters d).card ≤ d.totient := by
      refine (card_le_card (subset_univ _)).trans_eq ?_
      simpa only [card_univ, Nat.card_eq_fintype_card] using
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
    have hdL := (show (d:ℝ)≤H by exact_mod_cast (mem_Icc.mp hd).2).trans hH
    have hψ (ψ : DirichletCharacter ℂ d) (hψ : ψ ∈ sievePrimitiveCharacters d) :
        ‖primeCharacterError (u:ℝ) ψ‖ ≤ C*u/L^k := by
      have h := hSW u h₀' d hpos (by simpa only [Real.rpow_natCast] using hdL) ψ (mem_filter.mp hψ).2
      change _ ≤ C*u*L^(-(k:ℝ)) at h
      simpa only [Real.rpow_neg hL.le,Real.rpow_natCast,div_eq_mul_inv] using h
    have hsum := sum_le_sum hψ
    rw [sum_const,nsmul_eq_mul] at hsum
    have hnum : (0:ℝ) ≤ C*u/L^k := by positivity
    have hh := hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard :
      ((sievePrimitiveCharacters d).card:ℝ) ≤ d.totient) hnum)
    rw [one_div_mul_eq_div,div_le_iff₀ hφ]
    linarith only [hh]
  have h := sum_le_sum hr
  rw [sum_const, Nat.card_Icc,nsmul_eq_mul,Nat.add_sub_cancel] at h
  refine h.trans ((mul_le_mul_of_nonneg_right hH (by positivity)).trans ?_)
  change L^B*(C*u/L^k) ≤ C*u/L^A
  rw [show k=A+B+1 by rfl, pow_succ,pow_add]
  field_simp
  nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) u) (sub_nonneg.mpr hu)]

end GoldbachPartial