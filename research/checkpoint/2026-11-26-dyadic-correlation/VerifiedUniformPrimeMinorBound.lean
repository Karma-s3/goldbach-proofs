import VerifiedMinorArcDyadicAssembly
import VerifiedFixedMinorTypeIINumeric
import VerifiedFixedUniformDirichlet
import VerifiedUniformPrimeMajorFloor

namespace GoldbachPartial
open Finset Filter ExtendedArcCoefficient
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

set_option maxRecDepth 4096 in
/-- All size conditions used outside the second-type dyadic cells. -/
theorem uniformPrime_minor_parameters :
    ∀ᶠ X : ℕ in atTop, let L:=Real.log X
      let U:=uniformPrimeDenominator 24 X
      let Q:=uniformPrimeDenominator 64 X
      0<X ∧ 2≤L ∧ 0<U ∧ 0<Q ∧ Q≤X ∧ 2*(U*U)≤Q ∧
      (U:ℝ)*L ≤ X ∧ (U:ℝ)^2*L^2≤Q ∧
      L^2≤Real.sqrt X ∧ Real.log (X+1:ℕ)≤2*L ∧ ((Nat.log 2 X+1:ℕ):ℝ)≤3*L := by
  have ht:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he:=(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (64:ℝ) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [ht.eventually_ge_atTop 2,he,eventually_ge_atTop (1:ℕ)] with X hL hx hX
  let L:=Real.log X
  let U:=uniformPrimeDenominator 24 X
  let Q:=uniformPrimeDenominator 64 X
  change 2≤L at hL
  have hLX : L^64≤Real.sqrt (X:ℝ) := by
    simpa only [L,Function.comp_def,←Real.sqrt_eq_rpow,show (64:ℝ)=(64:ℕ) by norm_num,Real.rpow_natCast] using hx
  have h1 : 1≤L := by linarith
  have hw (i j:ℕ) (h:i≤j) : L^i≤L^j := pow_le_pow_right₀ h1 h
  have hW (j:ℕ) : 1≤L^j := by simpa only [pow_zero] using hw 0 j (Nat.zero_le _)
  have hU : (U:ℝ)≤L^24 := Nat.floor_le (by positivity)
  have hQ : (Q:ℝ)≤L^64 := Nat.floor_le (by positivity)
  have hUpos : 0<U := Nat.le_floor (by simpa using hW 24)
  have hQpos : 0<Q := Nat.le_floor (by simpa using hW 64)
  have hf : L^64 < (Q:ℝ)+1 := Nat.lt_floor_add_one (L^64)
  have hQr : (1:ℝ)≤Q := by exact_mod_cast hQpos
  have hlo : L^64≤2*(Q:ℝ) := by linarith
  have h4 : 2≤L^14 := hL.trans (by simpa using hw 1 14 (by decide))
  have hmid : (U:ℝ)^2*L^2≤Q := by
    calc
      _ ≤ (L^24)^2*L^2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg U) hU 2) (sq_nonneg _)
      _ = L^50 := by ring
      _ ≤ Q := by
        have hh : L^50*2 ≤ L^64 := by
          rw [show (64:ℕ)=50+14 by decide,pow_add]
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
        linarith only [hh,hlo]
  have hd : 2*(U*U)≤Q := by
    have hr : 2≤L^2 := hL.trans (by simpa using hw 1 2 (by decide))
    have hh := (mul_le_mul_of_nonneg_left hr (sq_nonneg (U:ℝ))).trans hmid
    exact_mod_cast (show 2*((U:ℝ)*U)≤Q by linarith only [hh])
  have hs1 : 1≤Real.sqrt (X:ℝ) := by simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤X by exact_mod_cast hX)
  have hsX : Real.sqrt (X:ℝ)≤X := by
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) X),
      mul_nonneg (Real.sqrt_nonneg (X:ℝ)) (sub_nonneg.mpr hs1)]
  have huX : (U:ℝ)*L≤X := by
    calc _ ≤ L^24*L := mul_le_mul_of_nonneg_right hU (by linarith)
         _ = L^25 := by ring
         _ ≤ _ := ((hw 25 64 (by decide)).trans hLX).trans hsX
  have hlog : Real.log (X+1:ℕ)≤2*L := by
    have hx1 : (0:ℝ)<X := by exact_mod_cast hX
    have hh : ((X+1:ℕ):ℝ)≤2*(X:ℝ) := by
      push_cast
      have hh' : (1:ℝ)≤X := by exact_mod_cast hX
      linarith only [hh']
    apply (Real.log_le_log (by positivity) hh).trans
    rw [Real.log_mul (by norm_num) hx1.ne']
    change Real.log 2+L≤2*L
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),hL]
  have hlg : ((Nat.log 2 X+1:ℕ):ℝ)≤3*L := by
    have hb:=Real.natLog_le_logb X 2
    have h2:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h2
    simp only [Nat.cast_ofNat,Real.logb] at hb
    have hdiv : L/Real.log 2≤2*L := (div_le_iff₀ (by linarith : (0:ℝ)<Real.log 2)).mpr (by
      nlinarith only [mul_nonneg (by linarith : 0≤L) (show 0≤Real.log 2-1/2 by linarith)])
    push_cast
    change (Nat.log 2 X:ℝ)+1≤3*L
    linarith only [hb.trans hdiv,hL]
  exact ⟨hX,hL,hUpos,hQpos,by exact_mod_cast hQ.trans (hLX.trans hsX),hd,huX,hmid,
    (hw 2 64 (by decide)).trans hLX,hlog,hlg⟩


set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem centralPrimeWave_uniform_minor64 :
    ∀ᶠ X : ℕ in atTop, ∀ α∈uniformPrimeMinor 64 X,
      ‖centralPrimeWave X α‖ ≤ 100000*(X:ℝ)/Real.log X := by
  filter_upwards [uniformPrime_minor_parameters,vaughan_fixed_typeII_numeric] with X hp hnumeric
  let L := Real.log X
  let U := uniformPrimeDenominator 24 X
  let Q := uniformPrimeDenominator 64 X
  let W := (X:ℝ)/L
  obtain ⟨hX,hL,hU,hQ,hQX,hUV,hUx,hUVQ,hsqrt,hlog,hk⟩ := hp
  change 2≤L at hL
  change (U:ℝ)*L≤X at hUx
  change (U:ℝ)^2*L^2≤Q at hUVQ
  change L^2≤Real.sqrt (X:ℝ) at hsqrt
  change Real.log (X+1:ℕ)≤2*L at hlog
  change ((Nat.log 2 X+1:ℕ):ℝ)≤3*L at hk
  have hLp : 0<L := by linarith
  have h1 : 1≤L := by linarith
  have hW : 0≤W := div_nonneg (Nat.cast_nonneg X) hLp.le
  have hU1 : (1:ℝ)≤U := by exact_mod_cast hU
  have hUU : (U:ℝ)≤(U:ℝ)^2 := by nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) U) (sub_nonneg.mpr hU1)]
  have hcp : (U:ℝ)≤W := (le_div_iff₀ hLp).mpr hUx
  have hnum : Real.log 4+4≤8 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hnum0 : 0≤Real.log 4+4 := by positivity
  intro α hα
  obtain ⟨a,q,hqQ,hqX,_,_,hc,_,ha⟩ := fixedUniform_dirichlet_cover_div hQ hQX
    (show (Q:ℝ)/X≤uniformPrimeWidth 64 X by
      dsimp only [uniformPrimeWidth];change _ ≤ 2*(Q:ℝ)/X;gcongr;linarith [Nat.cast_nonneg (α:=ℝ) Q])
    hα.1 hα.2
  have hq : 0<q := hQ.trans hqQ
  have hqUV : 2*(U*U)≤q := hUV.trans hqQ.le
  have hqU : 2*U≤q := (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right U hU)).trans hqUV
  have he : (q:ℝ)*(U:ℝ)^2*L^2≤X := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hUVQ (Nat.cast_nonneg _)).trans
      (by exact_mod_cast (Nat.le_div_iff_mul_le hQ).mp hqX)
  have hqw : (q:ℝ)*(U:ℝ)^2*L≤W := (le_div_iff₀ hLp).mpr (by nlinarith only [he])
  have hqwu : (q:ℝ)*(U:ℝ)*L≤W :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUU (Nat.cast_nonneg _)) hLp.le).trans hqw
  have hqws : (q:ℝ)*(U:ℝ)^2≤W :=
    (le_mul_of_one_le_right (by positivity) h1).trans hqw
  have hshort : ‖vaughanAdditiveSum X (vaughanInitial U Λ) α‖≤8*W :=
    (vaughan_additive_initial_bound X U α).trans (mul_le_mul hnum hcp (Nat.cast_nonneg _) (by norm_num))
  have hfirst : ‖vaughanAdditiveBilinear X (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log α‖≤8*W := by
    apply (vaughan_additive_log_small X U q a hqU hc ha).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤4*(q:ℝ))) (Nat.cast_nonneg (α:=ℝ) U)
    nlinarith only [hh,hqwu]
  have hsecond : ‖vaughanAdditiveBilinear X (vaughanTypeICoefficient U U) (ζ : ArithmeticFunction ℝ) α‖≤16*W := by
    apply (vaughan_additive_zeta_small X U U q a hqUV hc ha).trans
    have hh := mul_le_mul hnum hqws (show 0≤(q:ℝ)*(U:ℝ)^2 by positivity) (by norm_num : (0:ℝ)≤8)
    nlinarith only [hh]
  have htype : ‖vaughanAdditiveBilinear X (vaughanTypeIICoefficient U) (vaughanTail U Λ) α‖≤90000*W := by
    apply (vaughan_additive_typeII_of_block_cap X U U hX α (10000*(X:ℝ)/L^4) (by positivity)
      (fun M N hM hN hMX hNX hu hv hMN=>(vaughanMinorArcTypeIIBlock_sq X U U M N q a hM hN hMX hNX hq hc ha).trans
        (hnumeric q M N hqQ hqX hM hN hu hv hMN))).trans
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2) (by positivity : 0≤10000*(X:ℝ)/L^4)).trans
    calc
      (3*L)^2*(10000*(X:ℝ)/L^4) = 90000*W/L := by dsimp only [W];field_simp;ring
      _ ≤ 90000*W := (div_le_self (by positivity) h1)
  have hpow : ‖centralPrimeWave X α-vaughanAdditiveSum X Λ α‖≤2*W := by
    apply (centralPrimeWave_additiveLambda_error X α).trans
    have hs := (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt (Nat.cast_nonneg (α:=ℝ) X))
    have hh : Real.sqrt (X:ℝ)*L≤W := (le_div_iff₀ hLp).mpr (by nlinarith only [hs])
    change 2*Real.sqrt (X:ℝ)*L≤2*W
    linarith only [hh]
  have hΛ : ‖vaughanAdditiveSum X Λ α‖≤90032*W := by
    rw [vaughan_additive_identity X U U]
    apply (norm_add_le ..).trans
    have hh := norm_sub_le (vaughanAdditiveSum X (vaughanInitial U Λ) α+
      vaughanAdditiveBilinear X (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log α) (vaughanAdditiveBilinear X (vaughanTypeICoefficient U U) (ζ : ArithmeticFunction ℝ) α)
    have hh' := norm_add_le (vaughanAdditiveSum X (vaughanInitial U Λ) α)
      (vaughanAdditiveBilinear X (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log α)
    linarith only [hh,hh',hshort,hfirst,hsecond,htype]
  apply (norm_le_norm_sub_add _ (vaughanAdditiveSum X Λ α)).trans
  rw [show 100000*(X:ℝ)/Real.log X=100000*W by dsimp only [W,L];ring]
  linarith only [hpow,hΛ,hW]

end GoldbachPartial