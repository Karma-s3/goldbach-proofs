import TerminalMobiusPrimeMass

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

/-- The square of the von Mangoldt wave after subtracting a finite divisor sum. -/
noncomputable def weightedMangoldtKernel (n D : ℕ) (a : ℕ→ℂ) : ℝ→ℂ :=
  centeredTruePrimeKernel n (fun t => smallDivisorWave n (Icc 1 D) a t - properPrimePowerWave n t)

private theorem shiftRowSum (D : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 D,f d)=∑ j ∈ range D,f (j+1) := by
  symm
  apply sum_bij (fun j _ => j+1)
  · intro j hj; exact mem_Icc.mpr ⟨by omega,mem_range.mp hj⟩
  · intro i _ j _ h; omega
  · intro d hd; obtain ⟨hl,hu⟩ := mem_Icc.mp hd; exact ⟨d-1,mem_range.mpr (by omega),by omega⟩
  · intro _ _; rfl

private theorem weighted_energy_envelope {D n R Q : ℕ} (a : ℕ → ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ d∈Icc 1 D, ‖a d‖≤C)
    (hR : 0<R) (hQ : 0<Q) (hDR : D≤R) (hDn : D≤n) :
    (∫ t in naturalTubeUnion R Q (3*Q),‖smallDivisorWave n (Icc 1 D) a t‖^2) ≤
      (48*C)^2*(∫ t in (0:ℝ)..1,(∑ j ∈ range D,dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t))^2) := by
  let U := naturalTubeUnion R Q (3*Q)
  let A := smallDivisorWave n (Icc 1 D) a
  let G := fun t : ℝ => ∑ j ∈ range D,dyadicFejerEnvelope Q (((j+1:ℕ):ℝ)*t)
  have hA : Continuous A := by unfold A smallDivisorWave positiveDivisorRow E; fun_prop
  have hG : Continuous G := by unfold G dyadicFejerEnvelope fejerWave dirichletGeometricKernel E; fun_prop
  have hi : U⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  have hm : MeasurableSet U := naturalTubeUnion_measurable ..
  have hpot (t : ℝ) (ht : t∈U) : ‖A t‖≤(48*C)*G t := by
    apply (norm_sum_le _ _).trans
    change _≤(48*C)*∑ j ∈ range D,_
    rw [←shiftRowSum D (fun d => dyadicFejerEnvelope Q ((d:ℝ)*t)),mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hd0,hdD⟩ := mem_Icc.mp hd
    rw [norm_mul,positiveDivisorRow_eq hd0 (hdD.trans hDn),norm_mul,
      show ‖E ((d:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
    have hb := naturalTube_geometricKernel_le_fejer_envelope hd0 (hdD.trans hDR) ht (n/d-1)
    exact (mul_le_mul (ha d hd) hb (norm_nonneg _) hC).trans_eq (by ring)
  have hp (t : ℝ) (ht : t∈U) : ‖A t‖^2≤(48*C)^2*(G t)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpot t ht) 2
  have hAint : IntegrableOn (fun t => ‖A t‖^2) U := (hA.norm.pow 2).integrableOn_Icc.mono_set hi
  have hGint : IntegrableOn (fun t => (G t)^2) (Set.Icc 0 1) := (hG.pow 2).integrableOn_Icc
  have hu := setIntegral_mono_on hAint ((hGint.mono_set hi).const_mul ((48*C)^2)) hm hp
  rw [integral_const_mul] at hu
  have hg := setIntegral_mono_set hGint (Eventually.of_forall fun _ => sq_nonneg _) hi.eventuallySubset
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hg
  exact hu.trans (mul_le_mul_of_nonneg_left hg (sq_nonneg _))

private theorem weighted_kernel_transfer {n D : ℕ} (a : ℕ→ℂ) {V : Set ℝ} (hi : V⊆Set.Icc 0 1)
    {M s : ℝ} (hs : 0<s)
    (hM : (∫ t in V,‖smallDivisorWave n (Icc 1 D) a t‖^2)≤M) :
    ‖(∫ t in V,primeSquareKernel n t)-(∫ t in V,weightedMangoldtKernel n D a t)‖ ≤
      s*(Real.log 4*(n:ℝ)*Real.log n)+(1+s⁻¹)*(2*M+4*Real.sqrt n*(Real.log n)^2) := by
  let S := smallDivisorWave n (Icc 1 D) a
  let P := properPrimePowerWave n
  let B := fun t => S t-P t
  have hS : Continuous S := by unfold S smallDivisorWave positiveDivisorRow E; fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E; fun_prop
  have hB : Continuous B := hS.sub hP
  have he := truePrime_centering_young_chebyshev n hi B hB hs
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


theorem weighted_terminal_tube_energy {n R Q : ℕ} (a : ℕ→ℂ)
    (ha : ∀d∈Icc 1 R, ‖a d‖≤8*(1+Real.log n)) (hR : 0<R) (hQ : 0<Q)
    (hRQ : R≤Q) (hQn : Q≤n) (hQroot : (Q:ℝ)≤Real.sqrt n)
    (hRroot : (R:ℝ)≤Real.sqrt n/(1+Real.log n)^5) :
    (∫ t in naturalTubeUnion R Q (3*Q),‖smallDivisorWave n (Icc 1 R) a t‖^2) ≤
      23592960*(n:ℝ)/(1+Real.log n)^2 := by
  let L := 1+Real.log n
  have hL1 : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith only [hL1]
  have hlogR : 1+Real.log R≤L := add_le_add_right
    (Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRQ.trans hQn)) _
  have hlogs := logTwo_scale hQ hQn
  change ((Nat.log 2 Q+1:ℕ):ℝ) ≤ 4*L at hlogs
  change (R:ℝ)≤Real.sqrt n/L^5 at hRroot
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hfirst : (48*(8*L))^2 * (2*((Nat.log 2 Q+1:ℕ):ℝ)^2*(R:ℝ)^2) ≤ 4718592*(n:ℝ)/L^2 := calc
    _ ≤ (48*(8*L))^2*(2*(4*L)^2*(Real.sqrt n/L^5)^2) := by gcongr
    _ = 4718592*(n:ℝ)/L^6 := by rw [div_pow,hroot]; field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hL1 (by decide : 2≤6))
  have hsecond : (48*(8*L))^2 * (128*(Q:ℝ)*R*(1+Real.log R)) ≤ 18874368*(n:ℝ)/L^2 := calc
    _ ≤ (48*(8*L))^2*(128*(Real.sqrt n)*(Real.sqrt n/L^5)*L) := by gcongr
    _ = _ := by field_simp; nlinarith only [hroot]
  apply (weighted_energy_envelope a (by positivity : 0≤8*L) ha hR hQ le_rfl (hRQ.trans hQn)).trans
  apply (mul_le_mul_of_nonneg_left (dyadicFejerEnvelope_family_energy_sharp Q R hQ hR)
    (sq_nonneg (48*(8*L)))).trans
  rw [mul_add]
  change _≤23592960*(n:ℝ)/L^2
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

theorem weighted_terminal_kernel_error :
    ∀ᶠ n : ℕ in atTop,∀ a : ℕ→ℂ, (∀d∈Icc 1 (terminalPrimeArcCutoff n), ‖a d‖≤8*(1+Real.log n)) →
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-(∫ t in highNaturalPrimeTubes n,
        weightedMangoldtKernel n (terminalPrimeArcCutoff n) a t)‖ ≤ 95000000*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  let t := fun n : ℕ => (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht2 hl1
  intro a ha
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
  have hen := weighted_terminal_tube_energy a ha hR hQ0 hRQ hQn hQ hRroot
  have hs : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs1 : 1≤Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hlow := weighted_kernel_transfer a hV
    (s:=(L*Real.sqrt L)⁻¹) (by positivity) hen
  apply hlow.trans
  change _≤95000000*(n:ℝ)/Real.sqrt L
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
  change _ + (1+L*Real.sqrt L)*(2*(23592960*(n:ℝ)/L^2)+_)≤_
  calc
    _ ≤ (L*Real.sqrt L)⁻¹*(4*(n:ℝ)*L)+(2*(L*Real.sqrt L))*(2*(23592960*(n:ℝ)/L^2)+4*(n:ℝ)/L^2) := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul (by linarith only [hU1]) (add_le_add le_rfl hproper) (by positivity) (by positivity)
    _ = 94371852*(n:ℝ)/Real.sqrt L := by
      have hss := Real.sq_sqrt hL.le
      field_simp
      nlinarith only [hss]
    _ ≤ _ := by gcongr; norm_num

end GoldbachPartial