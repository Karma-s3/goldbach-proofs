import LargeDivisorPrimeMass
import DyadicFejerDomination
import DyadicFejerFamilyEnergy

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private theorem shiftRowSum (D : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 D,f d)=∑ j ∈ range D,f (j+1) := by
  symm
  apply sum_bij (fun j _ => j+1)
  · intro j hj; exact mem_Icc.mpr ⟨by omega,mem_range.mp hj⟩
  · intro i _ j _ h; omega
  · intro d hd; obtain ⟨hl,hu⟩ := mem_Icc.mp hd; exact ⟨d-1,mem_range.mpr (by omega),by omega⟩
  · intro _ _; rfl

private theorem absMobiusCoefficient_le {d n : ℕ} (hd : 0<d) (hdn : d≤n) :
    ‖(crtLambdaCoefficient d:ℂ)‖≤Real.log n := by
  rw [Complex.norm_real,Real.norm_eq_abs,crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg d)]
  have hm : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hm).trans
    (Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdn))

theorem mobius_energy_le_envelope_family {D n R Q : ℕ}
    (hR : 0<R) (hQ : 0<Q) (hDR : D≤R) (hDn : D≤n) :
    (∫ t in naturalTubeUnion R Q (3*Q),‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2) ≤
      (48*Real.log n)^2*(∫ t in (0:ℝ)..1,(∑ j ∈ range D,dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t))^2) := by
  let U := naturalTubeUnion R Q (3*Q)
  let A := smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ))
  let G := fun t : ℝ => ∑ j ∈ range D,dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t)
  have hA : Continuous A := by unfold A smallDivisorWave positiveDivisorRow E; fun_prop
  have hG : Continuous G := by unfold G dyadicFejerEnvelope fejerWave dirichletGeometricKernel E; fun_prop
  have hi : U⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  have hm : MeasurableSet U := naturalTubeUnion_measurable ..
  have hpot (t : ℝ) (ht : t∈U) : ‖A t‖≤(48*Real.log n)*G t := by
    apply (norm_sum_le _ _).trans
    change _≤(48*Real.log n)*∑ j ∈ range D,_
    rw [←shiftRowSum D (fun d => dyadicFejerEnvelope Q ((d:ℝ)*t)),mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hd0,hdD⟩ := mem_Icc.mp hd
    rw [norm_mul,positiveDivisorRow_eq hd0 (hdD.trans hDn),norm_mul,
      show ‖E ((d:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
    have hb := naturalTube_geometricKernel_le_fejer_envelope hd0 (hdD.trans hDR) ht (n/d-1)
    exact (mul_le_mul (absMobiusCoefficient_le hd0 (hdD.trans hDn)) hb (norm_nonneg _) (Real.log_natCast_nonneg n)).trans_eq (by ring)
  have hp (t : ℝ) (ht : t∈U) : ‖A t‖^2≤(48*Real.log n)^2*(G t)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpot t ht) 2
  have hAint : IntegrableOn (fun t => ‖A t‖^2) U := (hA.norm.pow 2).integrableOn_Icc.mono_set hi
  have hGint : IntegrableOn (fun t => (G t)^2) (Set.Icc 0 1) := (hG.pow 2).integrableOn_Icc
  have hu := setIntegral_mono_on hAint ((hGint.mono_set hi).const_mul ((48*Real.log n)^2)) hm hp
  rw [integral_const_mul] at hu
  have hg := setIntegral_mono_set hGint (Eventually.of_forall fun _ => sq_nonneg _) hi.eventuallySubset
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hg
  exact hu.trans (mul_le_mul_of_nonneg_left hg (sq_nonneg _))

/-- Removal of the full small-divisor block, in terms of its actual local energy. -/
theorem mobius_kernel_transfer_of_energy {n D : ℕ} {V : Set ℝ} (hi : V⊆Set.Icc 0 1)
    (hDn : D≤n) {M s : ℝ} (hs : 0<s)
    (hM : (∫ t in V,‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2)≤M) :
    ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,largeMobiusKernel n D t)‖ ≤
      s*(((n:ℝ)+1)*(Real.log n)^2)+(1+s⁻¹)*(2*M+4*Real.sqrt n*(Real.log n)^2) := by
  let S := smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ))
  let P := properPrimePowerWave n
  let B := fun t => S t-P t
  have hS : Continuous S := by unfold S smallDivisorWave positiveDivisorRow E; fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E; fun_prop
  have hB : Continuous B := hS.sub hP
  have he := truePrime_centering_young n hi B hB hs
  have hsame : centeredTruePrimeKernel n B = largeMobiusKernel n D := by
    ext1 t
    unfold centeredTruePrimeKernel largeMobiusKernel
    congr 2
    have hh := primeWave_largeDivisor_decomposition hDn t
    change centralPrimeWave n t - B t = _
    change centralPrimeWave n t = _ + B t at hh
    rw [hh,add_sub_cancel_right]
  rw [hsame] at he
  apply he.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hI {f:ℝ→ℝ} (hf:Continuous f) : IntegrableOn f V := hf.integrableOn_Icc.mono_set hi
  have h (t : ℝ) : ‖B t‖^2≤2*‖S t‖^2+2*‖P t‖^2 := by
    have h' := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (S t) (P t)) 2
    dsimp only [B]
    nlinarith only [h',sq_nonneg (‖S t‖-‖P t‖)]
  apply (integral_mono (hI (hB.norm.pow 2)) (hI ((continuous_const.mul (hS.norm.pow 2)).add
    (continuous_const.mul (hP.norm.pow 2)))) h).trans
  change (∫ t in V,2*‖S t‖^2+2*‖P t‖^2)≤_
  rw [integral_add (f:=fun t => 2*‖S t‖^2) (g:=fun t => 2*‖P t‖^2)
    (hI (continuous_const.mul (hS.norm.pow 2))) (hI (continuous_const.mul (hP.norm.pow 2))),
    integral_const_mul,integral_const_mul]
  change (∫ t in V,‖S t‖^2)≤M at hM
  have hp := properPrimePowerWave_energy n hi
  change (∫ t in V,‖P t‖^2)≤_ at hp
  linarith only [hM,hp]

noncomputable def nearSqrtMobiusCutoff (n : ℕ) : ℕ := ⌊Real.sqrt n/(1+Real.log n)^11⌋₊

private theorem logTwo_scale {n Q : ℕ} (hQ : 0<Q) (hQn : Q≤n) :
    ((Nat.log 2 Q+1:ℕ):ℝ) ≤ 4*(1+Real.log n) := by
  let m := Nat.log 2 Q
  have hp : (2:ℝ)^m≤(Q:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hQ.ne'
  have h := Real.log_le_log (by positivity : 0<(2:ℝ)^m) (hp.trans (show (Q:ℝ)≤(n:ℝ) by exact_mod_cast hQn))
  rw [Real.log_pow] at h
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h₂
  have hm := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α:=ℝ) m)
  change ((m+1:ℕ):ℝ)≤_
  push_cast
  nlinarith only [hm,h,Real.log_natCast_nonneg n]

private theorem mobius_envelope_bound {n D R Q : ℕ} (hR : 0<R) (hQ : 0<Q) (hDR : D≤R)
    (hDQ : D≤Q) (hQn : Q≤n)
    (hfam : (∫ t in (0:ℝ)..1,(∑ j∈range D,dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t))^2) ≤
      ((Nat.log 2 Q+1:ℕ):ℝ)^2*((D:ℝ)^2+4*(Q:ℝ)*D*(1+Real.log D))) :
    (∫ t in naturalTubeUnion R Q (3*Q),‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2) ≤
      184320*((Q:ℝ)*D)*(1+Real.log n)^5 := by
  let L := 1+Real.log (n:ℝ)
  have hL : 1≤L := by dsimp only [L];linarith [Real.log_natCast_nonneg n]
  have hdq : (D:ℝ)≤Q := by exact_mod_cast hDQ
  have hlog : Real.log n≤L := by dsimp only [L];linarith
  have hlogD : 1+Real.log D≤L := by
    rcases Nat.eq_zero_or_pos D with rfl|hd
    · simpa using hL
    · exact add_le_add_right (Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hDQ.trans hQn)) _
  have hl2 : ((Nat.log 2 Q+1:ℕ):ℝ) ≤4*L := logTwo_scale hQ hQn
  have hs : (D:ℝ)^2≤((Q:ℝ)*D)*L := by
    rw [sq (D:ℝ)]
    calc
      _ ≤ (Q:ℝ)*D := mul_le_mul_of_nonneg_right hdq (Nat.cast_nonneg _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
  have hB : (D:ℝ)^2+4*(Q:ℝ)*D*(1+Real.log D) ≤5*((Q:ℝ)*D)*L := by
    have hh : 4*(Q:ℝ)*D*(1+Real.log D) ≤ 4*(Q:ℝ)*D*L := by gcongr
    linarith only [hs,hh]
  apply (mobius_energy_le_envelope_family hR hQ hDR (hDQ.trans hQn)).trans
  apply (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans
  change _≤184320*((Q:ℝ)*D)*L^5
  calc
    _ ≤ (48*L)^2*((4*L)^2*(5*((Q:ℝ)*D)*L)) := by gcongr
    _ = _ := by ring

/-- A uniform pointwise approximation by the large divisors d>sqrt(n)/(1+log n)^11. -/
theorem nearSqrtMobiusKernel_high_error :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (nearSqrtMobiusCutoff n) t)‖ ≤
        737290*(n:ℝ)/(1+Real.log n)^2 := by
  let t := fun n : ℕ => (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht2 hl1
  let L := 1+Real.log (n:ℝ)
  let D := nearSqrtMobiusCutoff n
  let Q := naturalTubeScale n
  let R := terminalPrimeArcCutoff n
  let V := highNaturalPrimeTubes n
  let T := t n
  have hT2 : 2≤T := ht2
  have hT : 0<T := by linarith
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL1 : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hlog : Real.log n≤L := by dsimp [L]; linarith
  have h16 : T^16=Real.sqrt n := by
    dsimp only [T,t]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤(n:ℝ)),Real.sqrt_eq_rpow];norm_num
  have hL2T : L≤2*T := by
    change Real.log n/T<1 at hl1
    dsimp only [L]
    linarith [(div_lt_iff₀ hT).mp hl1]
  have hL8 : L^8 ≤ Real.sqrt n := calc
    _ ≤ (2*T)^8 := pow_le_pow_left₀ hL.le hL2T _
    _ ≤ (T*T)^8 := by gcongr
    _ = T^16 := by ring
    _ = _ := h16
  have hD : (D:ℝ)≤Real.sqrt n/L^11 := Nat.floor_le (by positivity)
  have hDR : D≤R := by
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity : 0<L^5)
      (pow_le_pow_right₀ hL1 (by decide : 5≤11))
  have hDQ : D≤Q := Nat.floor_mono (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1))
  have hQ0 : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hQ : (Q:ℝ)≤Real.sqrt n := Nat.floor_le (by positivity)
  have hQn : Q≤n := Nat.floor_le_of_le (by rw [Real.sqrt_eq_rpow];simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ)≤1))
  have hR : 0<R := hg.1.trans_le hg.2.1
  have hV : V⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  have hen := mobius_envelope_bound hR hQ0 hDR hDQ hQn (dyadicFejerEnvelope_family_energy Q D)
  have hsmall : (∫ u in V,‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) u‖^2) ≤
      184320*(n:ℝ)/L^6 := by
    apply hen.trans
    change 184320*((Q:ℝ)*D)*L^5≤_
    calc
      _ ≤ 184320*(Real.sqrt n*(Real.sqrt n/L^11))*L^5 := by gcongr
      _ = _ := by
        rw [←mul_div_assoc,Real.mul_self_sqrt (by positivity)]
        field_simp
  have hlow := mobius_kernel_transfer_of_energy hV (hDQ.trans hQn) (s:=(L^4)⁻¹) (by positivity) hsmall
  apply hlow.trans
  change _≤737290*(n:ℝ)/L^2
  rw [inv_inv]
  have hproper : 4*Real.sqrt n*(Real.log n)^2 ≤ 4*(n:ℝ)/L^6 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (4*Real.sqrt n*L^2)*L^6 := by gcongr
      _ = 4*Real.sqrt n*L^8 := by ring
      _ ≤ 4*Real.sqrt n*Real.sqrt n := by gcongr
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  have hX : (n:ℝ)+1≤2*(n:ℝ) := by linarith
  have h4one := one_le_pow₀ hL1 (n:=4)
  calc
    _ ≤ (L^4)⁻¹*((2*(n:ℝ))*L^2)+(2*L^4)*(2*(184320*(n:ℝ)/L^6)+4*(n:ℝ)/L^6) := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul (by linarith only [h4one]) (add_le_add le_rfl hproper) (by positivity) (by positivity)
    _ = _ := by field_simp; ring

noncomputable def nearSqrtMobiusArcMass (n : ℕ) : ℝ :=
  primeArcMass (highNaturalPrimeTubes n)ᶜ n +
    (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (nearSqrtMobiusCutoff n) t).re

theorem nearSqrtMobiusArcMass_error :
    ∀ᶠ n : ℕ in atTop, |nearSqrtMobiusArcMass n-corr n| ≤ 737290*(n:ℝ)/(1+Real.log n)^2 := by
  filter_upwards [nearSqrtMobiusKernel_high_error,highNaturalPrimeTubes_geometry] with n h hg
  let V := highNaturalPrimeTubes n
  have hm : MeasurableSet V := naturalTubeUnion_measurable ..
  have hs := corr_eq_primeArcMass n V hm
  rw [primeArcMass_eq_setIntegral_re_of_subset_Icc n hm hg.1] at hs
  let z := (∫ t in V,primeSquareKernel n t) - (∫ t in V,largeMobiusKernel n (nearSqrtMobiusCutoff n) t)
  have hh : |z.re|≤737290*(n:ℝ)/(1+Real.log n)^2 := (Complex.abs_re_le_norm _).trans h
  have he : nearSqrtMobiusArcMass n-corr n= -z.re := by
    unfold nearSqrtMobiusArcMass
    dsimp only [z,Complex.sub_re]
    change corr n=(∫ t in V,primeSquareKernel n t).re + primeArcMass Vᶜ n at hs
    change primeArcMass Vᶜ n + _ - corr n = _
    linarith only [hs]
  simpa only [he,abs_neg] using hh

theorem nearSqrtMobiusArcMass_close {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |nearSqrtMobiusArcMass n-corr n|≤ε*(n:ℝ) := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (737290/ε)
  filter_upwards [nearSqrtMobiusArcMass_error,hl] with n h hn
  change 737290/ε≤Real.log (n:ℝ) at hn
  have hL : 1≤1+Real.log n := by linarith [Real.log_natCast_nonneg n]
  apply h.trans
  rw [div_le_iff₀ (by positivity : 0<(1+Real.log (n:ℝ))^2)]
  have hsq : Real.log n≤(1+Real.log n)^2 := by nlinarith [Real.log_natCast_nonneg n,sq_nonneg (Real.log n)]
  have hh := (div_le_iff₀ hε).mp (hn.trans hsq)
  linarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) n)]

/-- The exact frozen dyadic floor is equivalent to positivity after all divisor rows up to
sqrt(n)/(1+log n)^11 are removed on the large-denominator arcs. -/
theorem dyadic_floor_iff_nearSqrtMobiusArcMass :
    (∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p))) ↔
    (∃ d : ℝ, 0<d ∧ ∀ᶠ n : ℕ in atTop, Even n → d*(n:ℝ)≤nearSqrtMobiusArcMass n) := by
  constructor
  · rintro ⟨c,N,hc,hfloor⟩
    refine ⟨c/2,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),
      nearSqrtMobiusArcMass_close (ε:=c/2) (by positivity)] with n hn hn1 he
    intro hev
    have h : c*(n:ℝ)≤corr n := hfloor n n hn le_rfl (by omega) hev
    linarith only [h,(abs_le.mp he).1]
  · rintro ⟨d,hd,hrest⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hrest.and (nearSqrtMobiusArcMass_close (ε:=d/2) (by positivity)))
    refine ⟨d/2,N,by positivity,?_⟩
    intro X n hX hXn _ hev
    change _≤corr n
    obtain ⟨hm,he⟩ := hN n (hX.trans hXn)
    linarith only [hm hev,(abs_le.mp he).2]

end GoldbachPartial