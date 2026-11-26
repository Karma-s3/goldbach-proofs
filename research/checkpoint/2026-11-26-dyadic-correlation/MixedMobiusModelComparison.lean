import MixedMobiusGRHReduction
import CenteredDistantPrimeMass

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private theorem waveDiffEnergy {V : Set ℝ} (hi : V⊆Set.Icc 0 1) {F G:ℝ→ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    (∫ t in V,‖F t-G t‖^2) ≤
      2*(∫ t in V,‖F t‖^2)+2*(∫ t in V,‖G t‖^2) := by
  have hI {f : ℝ → ℝ} (h : Continuous f) : IntegrableOn f V := h.integrableOn_Icc.mono_set hi
  have h (t : ℝ) : ‖F t-G t‖^2≤2*‖F t‖^2+2*‖G t‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F t) (G t)) 2
    nlinarith only [hh,sq_nonneg (‖F t‖-‖G t‖)]
  apply (integral_mono (hI ((hF.sub hG).norm.pow 2)) (hI ((continuous_const.mul (hF.norm.pow 2)).add
    (continuous_const.mul (hG.norm.pow 2)))) h).trans_eq
  change (∫ t in V,2*‖F t‖^2+2*‖G t‖^2)=_
  rw [integral_add (f:=fun t => 2*‖F t‖^2) (g:=fun t => 2*‖G t‖^2)
    (hI (continuous_const.mul (hF.norm.pow 2))) (hI (continuous_const.mul (hG.norm.pow 2))),
    integral_const_mul,integral_const_mul]

noncomputable abbrev terminalLargeWave (n : ℕ) :=
  smallDivisorWave n (Ioc (terminalPrimeArcCutoff n) n) (fun d => (crtLambdaCoefficient d:ℂ))

theorem terminalLargeWave_high_L2 :
    ∀ᶠ n : ℕ in atTop,(∫ t in highNaturalPrimeTubes n,‖terminalLargeWave n t‖^2) ≤
      1500000*(n:ℝ)*(1+Real.log n)^2 := by
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ)] with n hg hn
  let V := highNaturalPrimeTubes n
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let L := 1+Real.log (n:ℝ)
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL1 : 1≤L := by dsimp [L];linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hlog : Real.log n≤L := by dsimp [L];linarith
  have hRQ : R≤Q := Nat.floor_mono (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1))
  have hQ0 : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hQ : (Q:ℝ)≤Real.sqrt n := Nat.floor_le (by positivity)
  have hroot : Real.sqrt n≤(n:ℝ) := by
    rw [Real.sqrt_eq_rpow];simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ)≤1)
  have hQn : Q≤n := by exact_mod_cast hQ.trans hroot
  have hR : 0<R := hg.1.trans_le hg.2.1
  have hRroot : (R:ℝ)≤Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hi : V⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  let S := centralPrimeWave n
  let A := smallDivisorWave n (Icc 1 R) (fun d => (crtLambdaCoefficient d:ℂ))
  let P := properPrimePowerWave n
  have hS : Continuous S := by unfold S centralPrimeWave E;fun_prop
  have hA : Continuous A := by unfold A smallDivisorWave positiveDivisorRow E;fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E;fun_prop
  have heq : ∀t,terminalLargeWave n t=S t-(A t-P t) := by
    intro t
    have h := primeWave_largeDivisor_decomposition (hRQ.trans hQn) t
    change S t=terminalLargeWave n t+(A t-P t) at h
    rw [h,add_sub_cancel_right]
  have h1 := waveDiffEnergy hi hS (hA.sub hP)
  have h2 := waveDiffEnergy hi hA hP
  change (∫ t in V,‖S t-(A t-P t)‖^2)≤ 2*(∫ t in V,‖S t‖^2)+2*(∫t in V,‖A t-P t‖^2) at h1
  have hs := centralPrimeWave_local_energy_chebyshev n hi
  have ha := fullRange_mobius_energy hR hQ0 hRQ hQn hQ hRroot
  have hp := properPrimePowerWave_energy n hi
  change (∫ t in V,‖S t‖^2)≤_ at hs
  change (∫ t in V,‖A t‖^2)≤368640*(n:ℝ)/L^2 at ha
  change (∫ t in V,‖P t‖^2)≤_ at hp
  have h4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hLsq : L≤L^2 := by nlinarith [sq_nonneg (L-1)]
  have hsc : Real.log 4*n*Real.log n≤4*(n:ℝ)*L^2 := by gcongr;exact hlog.trans hLsq
  have hac : 368640*(n:ℝ)/L^2≤368640*(n:ℝ)*L^2 := by
    calc
      _ ≤ 368640*(n:ℝ) := div_le_self (by positivity) (one_le_pow₀ hL1)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
  have hpc : 2*Real.sqrt n*(Real.log n)^2≤2*(n:ℝ)*L^2 := by gcongr
  change (∫ t in V,‖terminalLargeWave n t‖^2)≤1500000*(n:ℝ)*L^2
  simp_rw [heq]
  nlinarith only [h1,h2,hs.trans hsc,ha.trans hac,hp.trans hpc,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (sq_nonneg L)]

theorem terminalLargeWave_high_L1 :
    ∀ᶠ n : ℕ in atTop,(∫ t in highNaturalPrimeTubes n,‖terminalLargeWave n t‖) ≤
      1500001*Real.sqrt n*(1+Real.log n) := by
  filter_upwards [terminalLargeWave_high_L2,highNaturalPrimeTubes_geometry,eventually_ge_atTop (1:ℕ)]
    with n he hg hn
  let V := highNaturalPrimeTubes n
  let G := terminalLargeWave n
  let A := Real.sqrt n*(1+Real.log n)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hA : 0<A := by dsimp [A];positivity
  have hG : Continuous G := by unfold G terminalLargeWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hI {f : ℝ → ℝ} (h : Continuous f) : IntegrableOn f V := h.integrableOn_Icc.mono_set hg.1
  have h (t : ℝ) : A*‖G t‖≤A^2+‖G t‖^2 := by nlinarith only [sq_nonneg (A-‖G t‖),sq_nonneg A,sq_nonneg ‖G t‖]
  have hm := integral_mono (hI (continuous_const.mul hG.norm))
    (hI (continuous_const.add (hG.norm.pow 2))) h
  change (∫ t in V,A*‖G t‖)≤∫ t in V,A^2+‖G t‖^2 at hm
  rw [integral_const_mul,integral_add (f:=fun _ => A^2) (g:=fun t => ‖G t‖^2)
    (hI continuous_const) (hI (hG.norm.pow 2)),setIntegral_const,smul_eq_mul] at hm
  have hv : volume.real V≤1 := (high_tube_volume_upper hn).trans (by norm_num)
  have hs : A^2=(n:ℝ)*(1+Real.log n)^2 := by dsimp [A];rw [mul_pow,Real.sq_sqrt hn'.le]
  change (∫ t in V,‖G t‖^2)≤_ at he
  change (∫ t in V,‖G t‖)≤_
  apply (le_of_mul_le_mul_left (a:=A) _ hA)
  have hp := mul_le_mul_of_nonneg_right hv (sq_nonneg A)
  change A*(∫t in V,‖G t‖)≤A*(1500001*Real.sqrt n*(1+Real.log n))
  rw [show 1500001*Real.sqrt n*(1+Real.log n)=1500001*A by dsimp [A];ring]
  nlinarith only [hm,hp,he,hs]


private theorem real_rows_as_integral (R Q : ℕ) (hQ : 0<Q) (f : ℝ→ℝ) (hc : Continuous f) :
    (∑ j∈Ico R Q,∑ a∈(range (j+1)).filter (fun a => a.Coprime (j+1)),
      ∫ β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),
        f (β+(a:ℝ)/((j+1:ℕ):ℝ))) = ∫ t in naturalTubeUnion R Q (3*Q),f t := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,←intervalIntegral.integral_ofReal,←integral_complex_ofReal]
  rw [naturalTubeUnion_integral_rows R Q (3*Q) (by omega) (fun t => (f t:ℂ)) (Complex.continuous_ofReal.comp hc)]
  apply sum_congr rfl
  intro j _
  symm
  apply sum_bij (fun (a : (ZMod (j+1))ˣ) _ => (a:ZMod (j+1)).val)
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro a ha
    obtain ⟨hm,h⟩ := mem_filter.mp ha
    exact ⟨ZMod.unitOfCoprime a h,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hm)⟩
  · intro _ _;rfl

/-- Replace only the resonant factor in the mixed term; the genuine nonresonant square stays exact. -/
noncomputable def modelMixedMobiusMass (n D R Q : ℕ) (M : ℕ→ℝ→ℂ) : ℂ :=
  ∑ j∈Ico R Q,∑ a∈(range (j+1)).filter (fun a => a.Coprime (j+1)),
    ∫ β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),
      let t := β+(a:ℝ)/((j+1:ℕ):ℝ)
      let N := nonresonantMobiusWave n D (j+1) t
      (N^2 + 2*N*M (j+1) β)*E (-(n:ℝ)*t)

theorem mixedMobiusModel_comparison (n D R Q : ℕ) (hR : 0<R) (hQ : 0<Q)
    (M : ℕ→ℝ→ℂ) (hc : ∀ q,Continuous (M q)) {Z K : ℝ}
    (hK : ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤K)
    (happrox : ∀ j∈Ico R Q,∀ β∈Set.Icc (-(naturalTubeRadius (3*Q) (j+1))) (naturalTubeRadius (3*Q) (j+1)),
        ‖resonantMobiusWave n D n (j+1) β-M (j+1) β‖≤Z) :
    let V := naturalTubeUnion R Q (3*Q)
    let G := smallDivisorWave n (Ioc D n) (fun d => (crtLambdaCoefficient d:ℂ))
    ‖nonresonantMobiusRemainderMass n D R Q-modelMixedMobiusMass n D R Q M‖ ≤
      2*Z*((∫ t in V,‖G t‖)+K*volume.real V) := by
  let V := naturalTubeUnion R Q (3*Q)
  let G := smallDivisorWave n (Ioc D n) (fun d => (crtLambdaCoefficient d:ℂ))
  let f := fun t : ℝ => 2*Z*(‖G t‖+K)
  have hG : Continuous G := by unfold G smallDivisorWave positiveDivisorRow E;fun_prop
  have hf : Continuous f := continuous_const.mul (hG.norm.add continuous_const)
  have hi : V⊆Set.Icc 0 1 := naturalTubeUnion_inside_unit hR (by omega : 0<3*Q)
  have hI {g : ℝ→ℝ} (h : Continuous g) : IntegrableOn g V := h.integrableOn_Icc.mono_set hi
  change ‖_‖≤2*Z*((∫ t in V,‖G t‖)+K*volume.real V)
  have hint : (∫ t in V,f t)=2*Z*((∫ t in V,‖G t‖)+K*volume.real V) := by
    unfold f
    rw [integral_const_mul,integral_add (f:=fun t => ‖G t‖) (g:=fun _ => K)
      (hI hG.norm) (hI continuous_const),setIntegral_const,smul_eq_mul,mul_comm (volume.real V)]
  rw [←hint,←real_rows_as_integral R Q hQ f hf]
  unfold nonresonantMobiusRemainderMass modelMixedMobiusMass
  rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro j hj
  rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro a _
  let q := j+1
  let ρ := naturalTubeRadius (3*Q) q
  let t := fun β:ℝ => β+(a:ℝ)/(q:ℝ)
  let N := nonresonantMobiusWave n D q
  let T := resonantMobiusWave n D n q
  let F := fun β => (N (t β)^2+2*N (t β)*T (t β))*E (-(n:ℝ)*t β)
  let B := fun β => (N (t β)^2+2*N (t β)*M q β)*E (-(n:ℝ)*t β)
  have hN : Continuous N := by unfold N nonresonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hT : Continuous T := by unfold T resonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hF : Continuous F := by dsimp only [F,t,E];fun_prop
  have hB : Continuous B := by have HM := hc q;dsimp only [B,t,E];fun_prop
  have hρ : 0≤ρ := by dsimp [ρ,naturalTubeRadius]; positivity
  have hab : -ρ≤ρ := by linarith
  change ‖(∫ β in -ρ..ρ,F β)-(∫ β in -ρ..ρ,B β)‖≤∫ β in -ρ..ρ,f (t β)
  rw [←intervalIntegral.integral_sub (hF.intervalIntegrable _ _) (hB.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  apply intervalIntegral.integral_mono_on hab ((hF.sub hB).norm.intervalIntegrable _ _)
    ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
  intro β hβ
  have hp : ‖E (-(n:ℝ)*t β)‖=1 := Complex.norm_exp_ofReal_mul_I _
  have heq : T (t β)=T β := resonantMobiusWave_at_center (Nat.succ_pos j) n D n a β
  have hNt : ‖N (t β)‖≤‖G (t β)‖+K := by
    have hh := largeMobiusWave_split n D q (t β)
    have hdiff : N (t β)=G (t β)-T (t β) := by
      change G (t β)=T (t β)+N (t β) at hh
      rw [hh,add_sub_cancel_left]
    rw [hdiff]
    exact (norm_sub_le ..).trans (add_le_add le_rfl (hK j hj _))
  change ‖F β-B β‖≤f (t β)
  rw [show F β-B β = (2:ℂ)*N (t β)*(T β-M q β)*E (-(n:ℝ)*t β) by dsimp only [F,B];rw [heq];ring]
  rw [norm_mul,norm_mul,norm_mul,hp,mul_one]
  norm_num
  dsimp only [f]
  calc
    _ ≤ 2*(‖G (t β)‖+K)*Z := mul_le_mul
      (mul_le_mul_of_nonneg_left hNt (by norm_num)) (happrox j hj β hβ) (norm_nonneg _) (by linarith [norm_nonneg (N (t β))])
    _ = _ := by ring


theorem mixedMobiusModel_terminal_error (M : ℕ→ℕ→ℝ→ℂ) (hc : ∀ n q,Continuous (M n q))
    (approx : ∀ᶠ n : ℕ in atTop,∀ j∈Ico (terminalPrimeArcCutoff n) (naturalTubeScale n),
      ∀ β∈Set.Icc (-(naturalTubeRadius (3*naturalTubeScale n) (j+1))) (naturalTubeRadius (3*naturalTubeScale n) (j+1)),
      ‖resonantMobiusWave n (terminalPrimeArcCutoff n) n (j+1) β-M n (j+1) β‖≤
        Real.sqrt n/(1+Real.log n)^8) :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n;let Q := naturalTubeScale n
      ‖nonresonantMobiusRemainderMass n R R Q-modelMixedMobiusMass n R R Q (M n)‖≤
        3000004*(n:ℝ)/(1+Real.log n) := by
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),terminalLargeWave_high_L1,approx]
    with n hg hn hG happrox
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let V := highNaturalPrimeTubes n
  let L := 1+Real.log (n:ℝ)
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL1 : 1≤L := by dsimp [L];linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hlog : Real.log n≤L := by dsimp [L];linarith
  have hQ : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hR : 0<R := hg.1.trans_le hg.2.1
  have hfloor : Real.sqrt n/L^5 < (R:ℝ)+1 := Nat.lt_floor_add_one _
  have hT j (hj : j∈Ico R Q) (β : ℝ) :
      ‖resonantMobiusWave n R n (j+1) β‖≤Real.sqrt n*L^7 := by
    have hj0 : (0:ℝ)<((j+1:ℕ):ℝ) := by positivity
    have hRj : (R:ℝ)+1 ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (mem_Ico.mp hj).1
    have hjr := (div_le_iff₀ (by positivity : 0<L^5)).mp (hfloor.le.trans hRj)
    apply (resonantMobiusWave_bound n R n (j+1) (by omega) β).trans
    apply (div_le_iff₀ hj0).mpr
    change (n:ℝ)*Real.log n*L ≤ _
    calc
      _ ≤ (n:ℝ)*L*L := by gcongr
      _ = (Real.sqrt n*L^2)*Real.sqrt n := by nlinarith only [congrArg (fun x:ℝ => L^2*x) (Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n))]
      _ ≤ (Real.sqrt n*L^2)*(((j+1:ℕ):ℝ)*L^5) := mul_le_mul_of_nonneg_left hjr (by positivity)
      _ = _ := by ring
  have he := mixedMobiusModel_comparison n R R Q hR hQ (M n) (hc n) hT happrox
  apply he.trans
  have hv : volume.real V≤1 := (high_tube_volume_upper hn).trans (by norm_num)
  have hs : L≤L^7 := by simpa using pow_le_pow_right₀ hL1 (by decide : 1≤7)
  change (∫ t in V,‖terminalLargeWave n t‖)≤1500001*Real.sqrt n*L at hG
  change 2*(Real.sqrt n/L^8)*((∫ t in V,‖terminalLargeWave n t‖)+(Real.sqrt n*L^7)*volume.real V)≤3000004*(n:ℝ)/L
  calc
    _ ≤ 2*(Real.sqrt n/L^8)*((1500001*Real.sqrt n*L^7)+(Real.sqrt n*L^7)*1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (hG.trans (mul_le_mul_of_nonneg_left hs (by positivity))) (mul_le_mul_of_nonneg_left hv (by positivity))
    _ = _ := by
      field_simp
      nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)]

end GoldbachPartial