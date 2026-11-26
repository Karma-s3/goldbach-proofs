import VerifiedActualVaughanConductor
import VerifiedVaughanParameterBudget

namespace GoldbachPartial
open Finset Filter
open scoped Topology

def VaughanHighMeanEstimate : Prop :=
  ∃ C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ X Q H P : ℕ,
    2≤X → 1≤Q → Q≤X → 1≤H → 0<P → P≤Q → H<2*P →
    ∀ D : Finset ℕ, D⊆Ioc H Q → (∀q∈D,P<q ∧ q≤2*P) →
      vaughanTypeIIConductorMass X H H D ≤ C*(1+Real.log X)^b *
        ((X:ℝ)/H+(X:ℝ)/Real.sqrt H+Q*Real.sqrt X)

private theorem quarter_natlog (n : ℕ) : (Nat.log 2 n:ℝ) ≤ 2*Real.log n := by
  have h := Real.natLog_le_logb n 2
  have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at ht
  simp only [Real.logb,Nat.cast_ofNat] at h
  apply h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg (Real.log_natCast_nonneg n) (show 0≤2*Real.log 2-1 by linarith)]

private theorem quarter_short_bound (X Q H : ℕ) (hX : 1≤X) (hQ : 1≤Q) (hH : 1≤H) :
    (Q:ℝ)*vaughanShortBound X Q H H ≤ 32*(1+Real.log X)*((Q:ℝ)^2*(H:ℝ)^2) := by
  let L := 1+Real.log X
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg X]
  have hQ' : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hH' : (1:ℝ)≤H := by exact_mod_cast hH
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have hlog : Real.log (X+1:ℕ) ≤ L := by
    have hc : (((X+1:ℕ):ℝ)) ≤ 2*X := by exact_mod_cast (show X+1≤2*X by omega)
    have h := Real.log_le_log (by positivity) hc
    rw [Real.log_mul (by norm_num) hx.ne'] at h
    dsimp [L];linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hk : Real.log 4 + 4 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hq : (Q:ℝ)+1 ≤ 2*Q := by linarith
  have hH2 : (H:ℝ) ≤ (H:ℝ)^2 := le_self_pow₀ hH' (by decide)
  let Y := (Q:ℝ)*L*(H:ℝ)^2
  have h0 : (H:ℝ) ≤ Y := by
    calc _ ≤ 1*1*(H:ℝ)^2 := by simpa using hH2
         _ ≤ _ := by dsimp only [Y]; gcongr
  have h1 : 2*((Q:ℝ)+1)*Real.log (X+1:ℕ)*H ≤ 4*Y := by
    calc _ ≤ 2*(2*(Q:ℝ))*L*(H:ℝ)^2 := by gcongr
         _ = _ := by dsimp only [Y]; ring
  have h2 : ((Q:ℝ)+1)*((H:ℝ)*((Real.log 4+4)*H)) ≤ 16*Y := by
    calc _ ≤ (2*(Q:ℝ))*((H:ℝ)*(8*H))*1 := by rw [mul_one]; gcongr
         _ ≤ (2*(Q:ℝ))*((H:ℝ)*(8*H))*L := by gcongr
         _ = _ := by dsimp only [Y];ring
  have h3 := (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (α:=ℝ) H)).trans
    (mul_le_mul_of_nonneg_left h0 (by norm_num : (0:ℝ)≤8))
  have hs : vaughanShortBound X Q H H ≤ 32*Y := by
    dsimp only [vaughanShortBound]
    linarith only [h1,h2,h3,show 0≤Y by dsimp [Y];positivity]
  exact (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans_eq (by dsimp [Y,L];ring)

private theorem quarter_mean_envelope (hh : VaughanHighMeanEstimate)
    : ∃ C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ X Q H : ℕ, 2≤X → 1≤Q → Q≤X → 1≤H →
    let L := 1+Real.log X
    let S := (Q:ℝ)^2*(H:ℝ)^2+(X:ℝ)/Real.sqrt H+(X:ℝ)/H+(Q:ℝ)*Real.sqrt X
    (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError X q) ≤
      4*L*primitiveConductorMass X (Icc 1 H) + C*L^b*S := by
  obtain ⟨C,hC,b,hblocks⟩ := hh
  refine ⟨132+12*C,by positivity,b+2,?_⟩
  intro X Q H hX hQ hQX hH L S
  have hL : 1≤L := by dsimp [L];linarith [Real.log_natCast_nonneg X]
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hS : 0≤S := by dsimp [S];positivity
  have hlogQ : Real.log Q ≤ Real.log X := Real.log_le_log (by exact_mod_cast hQ) (by exact_mod_cast hQX)
  have hQn : (Nat.log 2 Q:ℝ)+1 ≤ 3*L := by dsimp [L];linarith [quarter_natlog Q,Real.log_natCast_nonneg X]
  have hXn : (Nat.log 2 X:ℝ) ≤ 2*L := by dsimp [L];linarith [quarter_natlog X]
  have hlx : Real.log X ≤ L := by dsimp [L];linarith
  have hr1 : 1 ≤ Real.sqrt (X:ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  let T := (X:ℝ)/H + (X:ℝ)/Real.sqrt H + Q*Real.sqrt X
  have ht : 0≤T := by dsimp [T];positivity
  have htS : T≤S := by dsimp [S,T];linarith only [show (0:ℝ)≤(Q:ℝ)^2*(H:ℝ)^2 by positivity]
  have hQS : (Q:ℝ)*Real.sqrt X ≤ S := by dsimp [S]; exact le_add_of_nonneg_left (by positivity)
  have hfS : (Q:ℝ)^2*(H:ℝ)^2 ≤ S := by
    dsimp [S]
    linarith only [show 0≤(X:ℝ)/Real.sqrt H by positivity,show 0≤(X:ℝ)/H by positivity,
      show 0≤(Q:ℝ)*Real.sqrt X by positivity]
  have hsub := prime_prefix_mean_of_typeII_blocks X Q H H H (by omega) hH
    (B:=C*L^b*T) (by positivity) (fun P hp hpQ hb D hd hD => hblocks X Q H P hX hQ hQX hH hp hpQ hb D hd hD)
  let E := primitiveConductorMass X (Icc 1 H)
  have hE : 0≤E := sum_nonneg fun q _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _)
  have hshort := (quarter_short_bound X Q H (by omega) hQ hH).trans (mul_le_mul_of_nonneg_left hfS (by positivity))
  have hdya := mul_le_mul hQn (mul_le_mul_of_nonneg_left htS (by positivity : 0≤C*L^b))
    (by positivity : 0≤C*L^b*T) (by positivity : 0≤3*L)
  have hlogS : (Nat.log 2 X:ℝ)*Real.log Q ≤ 2*L^2*Real.sqrt X := by
    calc _ ≤ (2*L)*L := mul_le_mul hXn (hlogQ.trans hlx) (Real.log_natCast_nonneg _) (by positivity)
         _ ≤ (2*L)*L*Real.sqrt X := le_mul_of_one_le_right (by positivity) hr1
         _ = _ := by ring
  have hlogS' : 2*Real.sqrt X*Real.log X ≤ 2*L^2*Real.sqrt X := by
    calc _ ≤ 2*Real.sqrt X*L^2 := mul_le_mul_of_nonneg_left (hlx.trans (le_self_pow₀ hL (by decide))) (by positivity)
         _ = _ := by ring
  have hext : (Q:ℝ)*((Nat.log 2 X:ℝ)*Real.log Q+2*Real.sqrt X*Real.log X) ≤ 4*L^2*S := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hlogS hlogS') (Nat.cast_nonneg (α:=ℝ) Q)
    have h' := mul_le_mul_of_nonneg_left hQS (show 0≤4*L^2 by positivity)
    linarith only [h,h']
  have hcost : 4*(1+Real.log Q) ≤ 4*L := by dsimp [L]; linarith only [hlogQ]
  change _ ≤ 32*L*S at hshort
  have hshort0 : 0≤vaughanShortBound X Q H H := by dsimp [vaughanShortBound]; positivity
  have hinter := add_le_add (add_le_add (le_refl E) hshort) hdya
  have hmain := mul_le_mul hcost hinter (by positivity) (by positivity : 0≤4*L)
  have hLS := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (show 2≤b+2 by omega)) hS
  refine hsub.trans ?_
  rw [pow_add] at hLS ⊢
  dsimp only [E] at hmain
  linear_combination hmain + hext + 132*hLS

/-- Fixed endpoint, maximum over the reduced residue classes, and every modulus
up to a fourth root. Both displayed exponents refer to actual finite sums. -/
theorem quarter_prime_distribution_of_high_mean (hh : VaughanHighMeanEstimate) (A : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ, Q^4 ≤ X →
      (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError X q) ≤ C*X/(Real.log X)^A := by
  obtain ⟨c,hc,b,hm⟩ := quarter_mean_envelope hh
  let K := vaughanParameterExponent A b
  have hk : 0<K := by dsimp [K,vaughanParameterExponent];omega
  obtain ⟨C,hC,hsmall⟩ := primitive_small_conductor_mean (A+1) K hk
  refine ⟨8*C+1,by positivity,?_⟩
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (2:ℕ), ht, hsmall,
    vaughan_quarter_level_parameter_budget A b c hc.le, vaughan_parameter_floor_bounds A b] with X hX ht hs hp hf
  let T := Real.log X
  let L := 1+T
  let H := vaughanParameterCutoff A b X
  change 1≤T at ht
  have hT : 0<T := zero_lt_one.trans_le ht
  obtain ⟨hH,_,hcut,_,_⟩ := hf
  have hS := hs H hcut
  change primitiveConductorMass X (Icc 1 H) ≤ C*X/T^(A+1) at hS
  intro Q hQ
  rcases Nat.eq_zero_or_pos Q with rfl | hQp
  · simp only [Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),sum_empty]
    positivity
  have hQX : Q≤X := (Nat.le_self_pow (by decide : 4≠0) Q).trans hQ
  have hb := hm X Q H hX hQp hQX hH
  have hp' := hp Q hQ
  have hS0 : 0≤primitiveConductorMass X (Icc 1 H) :=
    sum_nonneg fun q _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _)
  have hsmall' : 4*L*primitiveConductorMass X (Icc 1 H) ≤ (8*C)*X/T^A := by
    calc
      _ ≤ (8*T)*(C*X/T^(A+1)) := mul_le_mul (by dsimp [L]; linarith) hS hS0 (by positivity)
      _ = _ := by rw [pow_succ]; field_simp
  have hp'' : (X:ℝ)/L^A ≤ (X:ℝ)/T^A :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hT _)
      (pow_le_pow_left₀ hT.le (by dsimp [L]; linarith) _)
  change _ ≤ (8*C+1)*X/T^A
  refine hb.trans ((add_le_add hsmall' (hp'.trans hp'')).trans_eq ?_)
  ring

/-- A quarter-level mean estimate for the genuine logarithmic prime weights at a fixed endpoint. -/
theorem prime_progressions_quarter_level (A : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ, Q^4 ≤ X →
      (∑ q ∈ Icc 1 Q, brunPrimePrefixMaxError X q) ≤ C*X/(Real.log X)^A :=
  quarter_prime_distribution_of_high_mean vaughan_actual_conductor_bound A

end GoldbachPartial