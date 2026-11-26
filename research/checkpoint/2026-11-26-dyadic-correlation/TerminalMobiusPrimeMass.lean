import NearSqrtMobiusPrimeMass
import SharpFejerFamilyEnergy
import TruePrimeCenteringChebyshev

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private theorem fullRange_kernel_transfer_of_energy {n D : ℕ} {V : Set ℝ} (hi : V⊆Set.Icc 0 1)
    (hDn : D≤n) {M s : ℝ} (hs : 0<s)
    (hM : (∫ t in V,‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2)≤M) :
    ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,largeMobiusKernel n D t)‖ ≤
      s*(Real.log 4*(n:ℝ)*Real.log n)+(1+s⁻¹)*(2*M+4*Real.sqrt n*(Real.log n)^2) := by
  let S := smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ))
  let P := properPrimePowerWave n
  let B := fun t => S t-P t
  have hS : Continuous S := by unfold S smallDivisorWave positiveDivisorRow E; fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E; fun_prop
  have hB : Continuous B := hS.sub hP
  have he := truePrime_centering_young_chebyshev n hi B hB hs
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


theorem fullRange_mobius_energy {n R Q : ℕ} (hR : 0<R) (hQ : 0<Q)
    (hRQ : R≤Q) (hQn : Q≤n) (hQroot : (Q:ℝ)≤Real.sqrt n)
    (hRroot : (R:ℝ)≤Real.sqrt n/(1+Real.log n)^5) :
    (∫ t in naturalTubeUnion R Q (3*Q),‖smallDivisorWave n (Icc 1 R) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2) ≤
      368640*(n:ℝ)/(1+Real.log n)^2 := by
  let L := 1+Real.log n
  have hL1 : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith only [hL1]
  have hlog : Real.log n≤L := by dsimp [L];linarith
  have hlogR : 1+Real.log R≤L := add_le_add_right
    (Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRQ.trans hQn)) _
  have hlogs := logTwo_scale hQ hQn
  change ((Nat.log 2 Q+1:ℕ):ℝ) ≤ 4*L at hlogs
  change (R:ℝ)≤Real.sqrt n/L^5 at hRroot
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hfirst : (48*Real.log n)^2 * (2*((Nat.log 2 Q+1:ℕ):ℝ)^2*(R:ℝ)^2) ≤ 73728*(n:ℝ)/L^2 := calc
    _ ≤ (48*L)^2*(2*(4*L)^2*(Real.sqrt n/L^5)^2) := by gcongr
    _ = 73728*(n:ℝ)/L^6 := by rw [div_pow,hroot]; field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hL1 (by decide : 2≤6))
  have hsecond : (48*Real.log n)^2 * (128*(Q:ℝ)*R*(1+Real.log R)) ≤ 294912*(n:ℝ)/L^2 := calc
    _ ≤ (48*L)^2*(128*(Real.sqrt n)*(Real.sqrt n/L^5)*L) := by gcongr
    _ = _ := by field_simp; nlinarith only [hroot]
  apply (mobius_energy_le_envelope_family hR hQ le_rfl (hRQ.trans hQn)).trans
  apply (mul_le_mul_of_nonneg_left (dyadicFejerEnvelope_family_energy_sharp Q R hQ hR)
    (sq_nonneg (48*Real.log (n:ℝ)))).trans
  rw [mul_add]
  change _≤368640*(n:ℝ)/L^2
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- On the high-denominator Farey arcs, all Möbius rows up to the lower Farey cutoff
can be removed at sublinear signed-square cost, uniformly in the target n. -/
theorem fullRange_largeMobius_high_error :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (terminalPrimeArcCutoff n) t)‖ ≤
        1500000*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  let t := fun n : ℕ => (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht2 hl1
  let L := 1+Real.log (n:ℝ)
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
  have hL4 : L^4≤Real.sqrt n := (pow_le_pow_right₀ hL1 (by decide : 4≤8)).trans hL8
  have hRQ : R≤Q := Nat.floor_mono (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1))
  have hQ0 : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hQ : (Q:ℝ)≤Real.sqrt n := Nat.floor_le (by positivity)
  have hQn : Q≤n := Nat.floor_le_of_le (by rw [Real.sqrt_eq_rpow];simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ)≤1))
  have hR : 0<R := hg.1.trans_le hg.2.1
  have hRroot : (R:ℝ)≤Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hV : V⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  have hen := fullRange_mobius_energy hR hQ0 hRQ hQn hQ hRroot
  have hs : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs1 : 1≤Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hlow := fullRange_kernel_transfer_of_energy hV (hRQ.trans hQn)
    (s:=(L*Real.sqrt L)⁻¹) (by positivity) hen
  apply hlow.trans
  change _≤1500000*(n:ℝ)/Real.sqrt L
  rw [inv_inv]
  have hproper : 4*Real.sqrt n*(Real.log n)^2 ≤ 4*(n:ℝ)/L^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (4*Real.sqrt n*L^2)*L^2 := by gcongr
      _ = 4*Real.sqrt n*L^4 := by ring
      _ ≤ 4*Real.sqrt n*Real.sqrt n := by gcongr
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  have hlog4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hU1 := one_le_mul_of_one_le_of_one_le hL1 hs1
  change _ + (1+L*Real.sqrt L)*(2*(368640*(n:ℝ)/L^2)+_)≤_
  calc
    _ ≤ (L*Real.sqrt L)⁻¹*(4*(n:ℝ)*L)+(2*(L*Real.sqrt L))*(2*(368640*(n:ℝ)/L^2)+4*(n:ℝ)/L^2) := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul (by linarith only [hU1]) (add_le_add le_rfl hproper) (by positivity) (by positivity)
    _ = 1474572*(n:ℝ)/Real.sqrt L := by
      have hss := Real.sq_sqrt hL.le
      field_simp
      nlinarith only [hss]
    _ ≤ _ := by gcongr; norm_num

noncomputable def terminalMobiusArcMass (n : ℕ) : ℝ :=
  primeArcMass (highNaturalPrimeTubes n)ᶜ n +
    (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (terminalPrimeArcCutoff n) t).re

theorem terminalMobiusArcMass_error :
    ∀ᶠ n : ℕ in atTop, |terminalMobiusArcMass n-corr n| ≤ 1500000*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  filter_upwards [fullRange_largeMobius_high_error,highNaturalPrimeTubes_geometry] with n h hg
  let V := highNaturalPrimeTubes n
  have hm : MeasurableSet V := naturalTubeUnion_measurable ..
  have hs := corr_eq_primeArcMass n V hm
  rw [primeArcMass_eq_setIntegral_re_of_subset_Icc n hm hg.1] at hs
  let z := (∫ t in V,primeSquareKernel n t) - (∫ t in V,largeMobiusKernel n (terminalPrimeArcCutoff n) t)
  have hh : |z.re|≤1500000*(n:ℝ)/Real.sqrt (1+Real.log n) := (Complex.abs_re_le_norm _).trans h
  have he : terminalMobiusArcMass n-corr n= -z.re := by
    unfold terminalMobiusArcMass
    dsimp only [z,Complex.sub_re]
    change corr n=(∫ t in V,primeSquareKernel n t).re + primeArcMass Vᶜ n at hs
    change primeArcMass Vᶜ n + _ - corr n = _
    linarith only [hs]
  simpa only [he,abs_neg] using hh

theorem terminalMobiusArcMass_close {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |terminalMobiusArcMass n-corr n|≤ε*(n:ℝ) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop
        ((1500000/ε)^2)
  filter_upwards [terminalMobiusArcMass_error,hlog] with n h hl
  change (1500000/ε)^2≤Real.log (n:ℝ) at hl
  have hL : (0:ℝ)<1+Real.log n := by linarith [Real.log_natCast_nonneg n]
  have hS : 1500000/ε≤Real.sqrt (1+Real.log (n:ℝ)) :=
    Real.le_sqrt_of_sq_le (by linarith only [hl])
  apply h.trans
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hL)]
  have h' := (div_le_iff₀ hε).mp hS
  linarith only [mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg (α:=ℝ) n)]

/-- The exact frozen dyadic floor is equivalent to positivity after all divisor rows up to
sqrt(n)/(1+log n)^5 are removed on the large-denominator arcs. -/
theorem dyadic_floor_iff_terminalMobiusArcMass :
    (∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p))) ↔
    (∃ d : ℝ, 0<d ∧ ∀ᶠ n : ℕ in atTop, Even n → d*(n:ℝ)≤terminalMobiusArcMass n) := by
  constructor
  · rintro ⟨c,N,hc,hfloor⟩
    refine ⟨c/2,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),
      terminalMobiusArcMass_close (ε:=c/2) (by positivity)] with n hn hn1 he
    intro hev
    have h : c*(n:ℝ)≤corr n := hfloor n n hn le_rfl (by omega) hev
    linarith only [h,(abs_le.mp he).1]
  · rintro ⟨d,hd,hrest⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hrest.and (terminalMobiusArcMass_close (ε:=d/2) (by positivity)))
    refine ⟨d/2,N,by positivity,?_⟩
    intro X n hX hXn _ hev
    change _≤corr n
    obtain ⟨hm,he⟩ := hN n (hX.trans hXn)
    linarith only [hm hev,(abs_le.mp he).2]

end GoldbachPartial