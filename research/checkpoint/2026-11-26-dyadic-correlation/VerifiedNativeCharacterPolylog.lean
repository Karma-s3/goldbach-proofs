import VerifiedNativeCharacterConductor
import VerifiedPolylogPrimeClass

namespace GoldbachPartial
open Finset Filter OAI.LargePrimeGaps
open scoped Classical Topology ArithmeticFunction.vonMangoldt

private theorem native_mangoldt_error {q:ℕ} (n:ℕ) (χ:DirichletCharacter ℂ q):
    mangoldtCharacterPrefix q n χ - (if χ=1 then (n:ℂ) else 0) = primeCharacterError (n:ℝ) χ := by
  simp only [mangoldtCharacterPrefix,primeCharacterError,primeCharacterPrefix,Nat.floor_natCast,Complex.ofReal_natCast]
  congr 1
  have hset:Ioc 0 n=(range (n+1)).erase 0:=by
    ext k;simp only [mem_Ioc,mem_erase,mem_range];omega
  rw [hset]
  rw [sum_erase_eq_sub (mem_range.mpr (Nat.zero_lt_succ n))]
  simp [mul_comm]

private theorem native_prefix_endpoint {n:ℕ} [NeZero n] (hn:2≤n) (χ:DirichletCharacter ℂ n)(hχ:χ≠1) :
    star (primeUnitTransform n χ)= centeredPrimeArcTransform n n 0 ((n:ℂ)+1) χ := by
  rw [primeUnitTransform_prefix hn χ hχ]
  have hzero:¬IsUnit (n:ZMod n):=by
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_self];omega
  simp only [centeredPrimeArcTransform,ite_eq_right hχ,sub_zero,weightedArcCharacterSum,
    Nat.sub_add_cancel (by omega:1≤n),sum_range_succ,χ.map_nonunit hzero,star_zero,mul_zero,add_zero]

theorem native_prime_transform_le_primitive {n:ℕ} [NeZero n] (hn:2≤n) (χ:DirichletCharacter ℂ n)(hχ:χ≠1) :
    ‖primeUnitTransform n χ‖ ≤ ‖primeCharacterError (n:ℝ) (χ⁻¹).primitiveCharacter‖+
      (Nat.log 2 n:ℝ)*Real.log n+2*Real.sqrt n*Real.log n+1 := by
  have h:=centeredPrimeArcTransform_le_psi_error n n χ
  rw [←native_prefix_endpoint hn χ hχ,norm_star,native_mangoldt_error] at h
  have hp:=primeCharacterError_le_primitive (n:ℝ) (show 0<n by omega) (χ⁻¹)
  rw [Nat.floor_natCast] at hp
  have hc:=Chebyshev.psi_sub_theta_le (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega))
  linarith only [h,hp,hc]

theorem native_low_conductor_transform (A B:ℕ):
    ∃ M:ℝ,0<M ∧ ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (χ:DirichletCharacter ℂ n),χ≠1 →
      (χ.conductor:ℝ)≤(Real.log n)^B → ‖primeUnitTransform n χ‖≤M*n/(Real.log n)^A := by
  obtain ⟨M,hM,x₀,_,hSW⟩:=siegelWalfisz ((A+1:ℕ):ℝ) ((B+1:ℕ):ℝ) (by positivity) (by positivity)
  refine ⟨M+5,by positivity,?_⟩
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((A+2:ℕ):ℝ) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [htlog,hpow,eventually_ge_atTop (max 2 ⌈x₀⌉₊)] with u hlog hpow hu
  intro _ χ hχ hdL
  let L := Real.log u
  have hx : x₀≤(u:ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right 2 ⌈x₀⌉₊).trans hu)
  have huR : (1:ℝ)≤u := by exact_mod_cast (show 1≤u by omega)
  change 1≤L at hlog
  have hL : 0<L := by linarith
  have hbig : L^(A+2) ≤ Real.sqrt u := by simpa only [L,Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow] using hpow
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) u)
  have hnext := (pow_le_pow_right₀ hlog (by omega : A+1≤A+2)).trans hbig
  have hroot : Real.sqrt u≤(u:ℝ) := by
    have h1 : 1≤Real.sqrt (u:ℝ) := by simpa using Real.sqrt_le_sqrt huR
    nlinarith only [hr,mul_nonneg (zero_le_one.trans h1) (sub_nonneg.mpr h1)]
  have hnat : (Nat.log 2 u:ℝ)≤2*L := by
    have h := Real.natLog_le_logb u 2
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    simp only [Nat.cast_ofNat,Real.logb] at h
    apply h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr _)
    nlinarith only [mul_nonneg hL.le (show 0≤2*Real.log 2-1 by linarith)]
  have hu2:2≤u:=(le_max_left ..).trans hu
  have hqi:((χ⁻¹).conductor:ℝ)≤L^(B+1):=by
    rw [DirichletCharacter.conductor_inv];exact hdL.trans (pow_le_pow_right₀ hlog (by omega))
  have hs:=hSW u hx (χ⁻¹).conductor (Nat.pos_of_ne_zero (χ⁻¹).conductor_ne_zero)
    (by simpa only [Real.rpow_natCast] using hqi) (χ⁻¹).primitiveCharacter (χ⁻¹).primitiveCharacter_isPrimitive
  change _≤M*(u:ℝ)*L^(-((A+1:ℕ):ℝ)) at hs
  rw [Real.rpow_neg hL.le,Real.rpow_natCast,←div_eq_mul_inv] at hs
  have hsw:‖primeCharacterError (u:ℝ) (χ⁻¹).primitiveCharacter‖ ≤ M*(u:ℝ)/L^A :=
    hs.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hL _) (pow_le_pow_right₀ hlog (by omega)))
  have hAP:=native_prime_transform_le_primitive hu2 χ hχ
  have hx1 : (Nat.log 2 u:ℝ)*Real.log u ≤ 2*(u:ℝ)/L^A := by
    apply (mul_le_mul_of_nonneg_right hnat (Real.log_natCast_nonneg _)).trans
    apply (le_div_iff₀ (pow_pos hL A)).mpr
    calc
      _ = 2*L^(A+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbig.trans hroot) (by norm_num)
  have hx2 : 2*Real.sqrt u*L ≤ 2*(u:ℝ)/L^A := by
    apply (le_div_iff₀ (pow_pos hL A)).mpr
    calc
      _ = 2*Real.sqrt u*L^(A+1) := by rw [pow_succ]; ring
      _ ≤ 2*Real.sqrt u*Real.sqrt u := mul_le_mul_of_nonneg_left hnext (by positivity)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  have hone:1≤(u:ℝ)/L^A := by
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    rw [one_mul]
    exact (pow_le_pow_right₀ hlog (by omega : A≤A+2)).trans (hbig.trans hroot)
  change _≤(M+5)*(u:ℝ)/L^A
  calc _ ≤ ‖primeCharacterError (u:ℝ) (χ⁻¹).primitiveCharacter‖ + (Nat.log 2 u:ℝ)*Real.log u+2*Real.sqrt u*L+1 := hAP
       _ ≤ M*u/L^A+2*u/L^A+2*u/L^A+u/L^A:=add_le_add (add_le_add (add_le_add hsw hx1) hx2) hone
       _ = _ := by ring

open private primitive_conductor_row from VerifiedConductorMean
open private modelHarmonic_bound from ResonantModelEnergy

theorem native_small_conductor_card {n D:ℕ} [NeZero n] (S:Finset (DirichletCharacter ℂ n))
    (hs:∀χ∈S,χ.conductor≤D) : (S.card:ℝ) ≤ (D:ℝ)^2 := by
  classical
  let F (d:ℕ) (_:DirichletCharacter ℂ d) : ℝ := if d≤D then 1 else 0
  have hF d (χ:DirichletCharacter ℂ d) : 0≤F d χ := by dsimp [F];split <;> norm_num
  have h := primitive_conductor_row (Nat.pos_of_ne_zero (NeZero.ne n)) F hF
  have hmain : (S.card:ℝ) ≤ ∑χ:DirichletCharacter ℂ n,F χ.conductor χ.primitiveCharacter := by
    calc _ = ∑_χ∈S,(1:ℝ) := by simp
         _ = ∑χ∈S,F χ.conductor χ.primitiveCharacter := sum_congr rfl (fun χ hχ=>(ite_eq_left (hs χ hχ)).symm)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun χ _ _=>hF χ.conductor χ.primitiveCharacter)
  apply (hmain.trans h).trans
  calc _ ≤ ∑d∈n.divisors,if d≤D then (D:ℝ) else 0 := by
         apply sum_le_sum;intro d hd
         let _ : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
         by_cases hl:d≤D
         · simp only [F,ite_eq_left hl,sum_const,nsmul_eq_mul,mul_one]
           apply Nat.cast_le.mpr
           apply (card_le_univ _).trans
           rw [←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
           exact (Nat.totient_le _).trans hl
         · simp [F,hl]
       _ ≤ ∑_d∈Icc 1 D,(D:ℝ) := by
         rw [←sum_filter]
         exact sum_le_sum_of_subset_of_nonneg (fun d hd=>mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩) (fun _ _ _=>Nat.cast_nonneg _)
       _ = _ :=by simp [sq]

theorem native_low_conductor_unconditional_saving (A B:ℕ) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (S:Finset (DirichletCharacter ℂ n)), 1∉S →
      (∀χ∈S,(χ.conductor:ℝ)≤(Real.log n)^B) →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖/(n.totient:ℝ) ≤ C*n/(Real.log n)^A := by
  let k:=A+B+1
  obtain ⟨M,hM,hpre⟩:=native_low_conductor_transform k B
  refine ⟨4*M^2,by positivity,?_⟩
  have ht:=(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hpre,ht,eventually_ge_atTop (2:ℕ)] with n hh hL hn
  intro _ S hs hS
  let L:=Real.log n
  have hL1:1≤L:=hL
  have hpos:0<L:=by linarith
  have hφ:0<(n.totient:ℝ):=by exact_mod_cast Nat.totient_pos.mpr (show 0<n by omega)
  have hratio:(n:ℝ)/n.totient≤4*L:=by
    apply (model_totient_ratio_le_divisor_reciprocals n (by omega)).trans
    have hsum:(∑d∈n.divisors,(d:ℝ)⁻¹)≤1+L:=by
      apply le_trans _ (modelHarmonic_bound n)
      exact sum_le_sum_of_subset_of_nonneg (fun d hd=>mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hd).1⟩) (fun d _ _=>by positivity)
    linarith only [hsum,hL1]
  have hcard:(S.card:ℝ)≤(L^B)^2 :=(native_small_conductor_card (D:=⌊L^B⌋₊) S (fun χ hχ=>Nat.le_floor (hS χ hχ))).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (pow_nonneg hpos.le _)) _)
  have hb:‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖≤(S.card:ℝ)*(M*n/L^k)^2:=by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑_χ∈S,(M*n/L^k)^2 := by
           apply sum_le_sum;intro χ hχ
           rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq]
           apply (mul_le_of_le_one_left (sq_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
           exact pow_le_pow_left₀ (norm_nonneg _) (hh _ χ (fun he=> hs (he ▸ hχ)) (hS χ hχ)) _
         _ = _ :=by simp
  calc _ ≤ (L^B)^2*(M*n/L^k)^2/(n.totient:ℝ) :=
          div_le_div_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))) hφ.le
       _ = ((L^B)^2*M^2*n/((L^k)^2))*((n:ℝ)/n.totient) :=by ring
       _ ≤ ((L^B)^2*M^2*n/((L^k)^2))*(4*L) := mul_le_mul_of_nonneg_left hratio (by positivity)
       _ = (4*M^2*n)/L^A*(1/L^(A+1)) :=by
         dsimp only [k]
         rw [pow_succ,pow_add,pow_succ]
         field_simp;ring
       _ ≤ _ :=mul_le_of_le_one_right (by positivity) ((div_le_one (pow_pos hpos _)).mpr (one_le_pow₀ hL1))

end GoldbachPartial
