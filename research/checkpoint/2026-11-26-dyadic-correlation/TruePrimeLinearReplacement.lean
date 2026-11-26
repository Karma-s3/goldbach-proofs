import MixedMobiusPrincipalModel
import TrueMixedFrequencies
import ResonantModelEnergy

namespace GoldbachPartial
open Filter Finset MeasureTheory ExtendedArcCoefficient
open scoped Topology

noncomputable def primeLinearRows {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R Q : ℕ) (F : ℕ → ℕ → ℝ → E) : E :=
  ∑ j∈Ico R Q, ∑ a∈(range (j+1)).filter (fun a => a.Coprime (j+1)),
    ∫ β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1), F (j+1) a β

private theorem rows_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R Q : ℕ) (F G : ℕ → ℕ → ℝ → E) (hF : ∀ q a, Continuous (F q a))
    (hG : ∀ q a, Continuous (G q a)) :
    primeLinearRows R Q (fun q a β => F q a β+G q a β) =
    primeLinearRows R Q F+primeLinearRows R Q G := by
  unfold primeLinearRows
  simp_rw [intervalIntegral.integral_add ((hF _ _).intervalIntegrable _ _) ((hG _ _).intervalIntegrable _ _)]
  simp only [sum_add_distrib]

private theorem rows_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R Q : ℕ) (F G : ℕ → ℕ → ℝ → E) (hF : ∀ q a, Continuous (F q a))
    (hG : ∀ q a, Continuous (G q a)) :
    primeLinearRows R Q (fun q a β => F q a β-G q a β) =
    primeLinearRows R Q F-primeLinearRows R Q G := by
  unfold primeLinearRows
  simp_rw [intervalIntegral.integral_sub ((hF _ _).intervalIntegrable _ _) ((hG _ _).intervalIntegrable _ _)]
  simp only [sum_sub_distrib]

private theorem real_rows_mul (R Q : ℕ) (c:ℝ) (f : ℕ → ℕ → ℝ → ℝ) :
    primeLinearRows R Q (fun q a β => c*f q a β)=c*primeLinearRows R Q f := by
  unfold primeLinearRows
  simp only [intervalIntegral.integral_const_mul,mul_sum]

private theorem rowNormBound (R Q : ℕ) (F : ℕ→ℕ→ℝ→ℂ) (H : ℕ→ℕ→ℝ→ℝ)
    (hF : ∀ q a, Continuous (F q a)) (hH : ∀ q a, Continuous (H q a))
    (hh : ∀ j∈Ico R Q,∀ a, ∀ β∈Set.Icc (-(naturalTubeRadius (3*Q) (j+1))) (naturalTubeRadius (3*Q) (j+1)),
      ‖F (j+1) a β‖≤H (j+1) a β) :
    ‖primeLinearRows R Q F‖≤primeLinearRows R Q H := by
  unfold primeLinearRows
  apply (norm_sum_le ..).trans
  apply sum_le_sum; intro j hj
  apply (norm_sum_le ..).trans
  apply sum_le_sum; intro a _
  have hρ : 0≤naturalTubeRadius (3*Q) (j+1) := by unfold naturalTubeRadius;positivity
  have hab := neg_le_self hρ
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  exact intervalIntegral.integral_mono_on hab ((hF _ _).norm.intervalIntegrable _ _)
    ((hH _ _).intervalIntegrable _ _) (hh j hj a)

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

noncomputable abbrev primeLinearRowCenter (q a : ℕ) (β : ℝ) := β+(a:ℝ)/(q:ℝ)

private theorem rowRealIntegral (R Q : ℕ) (hQ : 0<Q) (f : ℝ→ℝ) (hc : Continuous f) :
    primeLinearRows R Q (fun q a β => f (primeLinearRowCenter q a β))=∫ t in naturalTubeUnion R Q (3*Q),f t :=
  real_rows_as_integral R Q hQ f hc

noncomputable def primeBilinearMass (n R Q : ℕ) (F P : ℕ→ℝ→ℂ) : ℂ :=
  primeLinearRows R Q (fun q a β => 2*F q (primeLinearRowCenter q a β)*P q β*E (-(n:ℝ)*primeLinearRowCenter q a β))

/-- The signed linear contribution of the true prime wave against the principal model on each tube. -/
noncomputable def truePrimeLinearMass (n : ℕ) : ℂ :=
  primeBilinearMass n (terminalPrimeArcCutoff n) (naturalTubeScale n)
    (fun _ => centralPrimeWave n) (resonantPrincipalModel n)

private theorem row_young (s a b : ℝ) (hs : 0<s) : 2*a*b≤ s*a^2+s⁻¹*b^2 := by
  apply le_of_mul_le_mul_left (a:=s) _ hs
  field_simp
  nlinarith only [sq_nonneg (s*a-b)]

private theorem row_congr (R Q : ℕ) {F G : ℕ→ℕ→ℝ→ℂ} (hg : ∀ q,0<q → ∀ a β,F q a β=G q a β) :
    primeLinearRows R Q F = primeLinearRows R Q G := by
  unfold primeLinearRows
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro a _
  apply intervalIntegral.integral_congr;intro β _
  exact hg _ (Nat.succ_pos j) a β

private theorem exactGT (n : ℕ) :
    let R := terminalPrimeArcCutoff n; let Q := naturalTubeScale n
    nonresonantSquareMass n R R Q +
      primeBilinearMass n R Q (fun _ => terminalLargeWave n) (resonantMobiusWave n R n) =
    nonresonantMobiusRemainderMass n R R Q +
      (allResonantMobiusHighMass n R + allResonantMobiusHighMass n R) := by
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let T := resonantMobiusWave n R n
  let N := nonresonantMobiusWave n R
  let G := terminalLargeWave n
  let phase := fun q a β => E (-(n:ℝ)*primeLinearRowCenter q a β)
  let ns := fun q a β => (N q (primeLinearRowCenter q a β))^2*phase q a β
  let gt := fun q a β => 2*G (primeLinearRowCenter q a β)*T q β*phase q a β
  let remn := fun q a β => (N q (primeLinearRowCenter q a β)^2+2*N q (primeLinearRowCenter q a β)*T q (primeLinearRowCenter q a β))*phase q a β
  let ts := fun q a β => (T q (primeLinearRowCenter q a β))^2*phase q a β
  have hG : Continuous G := by unfold G terminalLargeWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hT q : Continuous (T q) := by unfold T resonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hN q : Continuous (N q) := by unfold N nonresonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hns q a : Continuous (ns q a) := by dsimp only [ns,phase,primeLinearRowCenter,E];fun_prop
  have hgt q a : Continuous (gt q a) := by dsimp only [gt,phase,primeLinearRowCenter,E];fun_prop
  have hrm q a : Continuous (remn q a) := by dsimp only [remn,phase,primeLinearRowCenter,E];fun_prop
  have hts q a : Continuous (ts q a) := by dsimp only [ts,phase,primeLinearRowCenter,E];fun_prop
  change primeLinearRows R Q ns+primeLinearRows R Q gt=primeLinearRows R Q remn+
    (primeLinearRows R Q ts+primeLinearRows R Q ts)
  rw [←rows_add _ _ _ _ hns hgt, ←rows_add _ _ _ _ hts hts,
    ←rows_add R Q remn (fun q a β => ts q a β+ts q a β) hrm (fun q a => (hts q a).add (hts q a))]
  apply row_congr;intro q hq a β
  have hg : G (primeLinearRowCenter q a β)=T q (primeLinearRowCenter q a β)+N q (primeLinearRowCenter q a β) := largeMobiusWave_split .. 
  have ht : T q (primeLinearRowCenter q a β)=T q β := resonantMobiusWave_at_center hq n R n a β
  dsimp only [ns,gt,remn,ts]
  rw [hg,ht];ring

private theorem row_bilinear_error (n R Q : ℕ) (hQ : 0<Q)
    (S G : ℝ→ℂ) (T M : ℕ→ℝ→ℂ) (hS : Continuous S) (hG : Continuous G)
    (hT : ∀ q, Continuous (T q)) (hM : ∀ q, Continuous (M q))
    (s Z : ℝ) (hs : 0<s)
    (htm : ∀ j∈Ico R Q, ∀ β∈Set.Icc (-(naturalTubeRadius (3*Q) (j+1))) (naturalTubeRadius (3*Q) (j+1)),
      ‖T (j+1) β-M (j+1) β‖≤Z) :
    let V := naturalTubeUnion R Q (3*Q)
    ‖primeBilinearMass n R Q (fun _ => G) T-primeBilinearMass n R Q (fun _ => S) M‖≤
      (2*Z)*(∫ t in V, ‖G t‖)+s*(∫ t in V, ‖G t-S t‖^2)+
      s⁻¹*primeLinearRows R Q (fun q _ β => ‖M q β‖^2) := by
  let phase := fun q a β => E (-(n:ℝ)*primeLinearRowCenter q a β)
  let gt := fun q a β => 2*G (primeLinearRowCenter q a β)*T q β*phase q a β
  let sm := fun q a β => 2*S (primeLinearRowCenter q a β)*M q β*phase q a β
  let g := fun q a β => ‖G (primeLinearRowCenter q a β)‖
  let gs := fun q a β => ‖G (primeLinearRowCenter q a β)-S (primeLinearRowCenter q a β)‖^2
  let mm := fun q (_:ℕ) β => ‖M q β‖^2
  have hc1 q a : Continuous (gt q a) := by dsimp only [gt,phase,primeLinearRowCenter,E];fun_prop
  have hc2 q a : Continuous (sm q a) := by dsimp only [sm,phase,primeLinearRowCenter,E];fun_prop
  have hcg q a : Continuous (g q a) := by dsimp only [g,primeLinearRowCenter];fun_prop
  have hcs q a : Continuous (gs q a) := by dsimp only [gs,primeLinearRowCenter];fun_prop
  have hcm q a : Continuous (mm q a) := (hM q).norm.pow 2
  change ‖primeLinearRows R Q gt-primeLinearRows R Q sm‖≤_
  rw [←rows_sub _ _ _ _ hc1 hc2,←rowRealIntegral R Q hQ _ hG.norm,
    ←rowRealIntegral R Q hQ (fun t => ‖G t-S t‖^2) ((hG.sub hS).norm.pow 2)]
  change _≤(2*Z)*primeLinearRows R Q g+s*primeLinearRows R Q gs+s⁻¹*primeLinearRows R Q mm
  rw [←real_rows_mul,←real_rows_mul,←real_rows_mul,
    ←rows_add R Q (fun q a β => 2*Z*g q a β) (fun q a β => s*gs q a β) (fun q a => continuous_const.mul (hcg q a)) (fun q a => continuous_const.mul (hcs q a)),
    ←rows_add R Q (fun q a β => 2*Z*g q a β+s*gs q a β) (fun q a β => s⁻¹*mm q a β) (fun q a => (continuous_const.mul (hcg q a)).add (continuous_const.mul (hcs q a)))
      (fun q a => continuous_const.mul (hcm q a))]
  apply rowNormBound _ _ _ _ (fun q a => (hc1 q a).sub (hc2 q a))
    (fun q a => ((continuous_const.mul (hcg q a)).add (continuous_const.mul (hcs q a))).add
      (continuous_const.mul (hcm q a)))
  intro j hj a β hβ
  let x := primeLinearRowCenter (j+1) a β
  let u := phase (j+1) a β
  have hu : ‖u‖=1 := Complex.norm_exp_ofReal_mul_I _
  let t := T (j+1) β
  let m := M (j+1) β
  have ht : ‖t-m‖≤Z := htm j hj β hβ
  change ‖2*G x*t*u-2*S x*m*u‖≤ 2*Z*‖G x‖+s*‖G x-S x‖^2+s⁻¹*‖m‖^2
  rw [show 2*G x*t*u-2*S x*m*u=(2*G x*(t-m)+2*(G x-S x)*m)*u by ring,norm_mul,hu,mul_one]
  apply (norm_add_le ..).trans
  simp only [norm_mul,Complex.norm_ofNat]
  have ha := mul_le_mul_of_nonneg_left ht (by positivity : 0≤2*‖G x‖)
  linarith only [row_young s ‖G x-S x‖ ‖m‖ hs,ha]


private theorem differenceEnergyPrimeLinear {V : Set ℝ} (hi : V⊆Set.Icc 0 1) {F G:ℝ→ℂ}
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

theorem terminalLargePrimeDifference_energy :
    ∀ᶠ n : ℕ in atTop,(∫ t in highNaturalPrimeTubes n,‖terminalLargeWave n t-centralPrimeWave n t‖^2)
        ≤ 737284*(n:ℝ)/(1+Real.log n)^2 := by
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
  have hproper : 4*Real.sqrt n*(Real.log n)^2 ≤ 4*(n:ℝ)/L^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (4*Real.sqrt n*L^2)*L^2 := by gcongr
      _ = 4*Real.sqrt n*L^4 := by ring
      _ ≤ 4*Real.sqrt n*Real.sqrt n := by gcongr
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  let S := centralPrimeWave n
  let A := smallDivisorWave n (Icc 1 R) (fun d => (crtLambdaCoefficient d:ℂ))
  let P := properPrimePowerWave n
  have hA : Continuous A := by unfold A smallDivisorWave positiveDivisorRow E;fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E;fun_prop
  have hh := differenceEnergyPrimeLinear hV hA hP
  have hp := properPrimePowerWave_energy n hV
  change (∫ t in V,‖A t‖^2)≤368640*(n:ℝ)/L^2 at hen
  change (∫ t in V,‖P t‖^2)≤_ at hp
  change (∫ t in V,‖terminalLargeWave n t-S t‖^2)≤737284*(n:ℝ)/L^2
  have heq (t : ℝ) : ‖terminalLargeWave n t-S t‖=‖A t-P t‖ := by
    have ht := primeWave_largeDivisor_decomposition (hRQ.trans hQn) t
    change S t=terminalLargeWave n t+(A t-P t) at ht
    rw [ht,sub_add_cancel_left, norm_neg]
  simp_rw [heq]
  simp only [div_eq_mul_inv] at hen hproper ⊢
  nlinarith only [hh,hen,hp,hproper]

private theorem currentGT_bound (hψ : grhAllUniform) :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n;let Q := naturalTubeScale n
      ‖primeBilinearMass n R Q (fun _ => terminalLargeWave n) (resonantMobiusWave n R n)-
        truePrimeLinearMass n‖ ≤ 3737294*(n:ℝ)/Real.sqrt (1+Real.log n) := by
  filter_upwards [terminalLargeWave_high_L1,terminalLargePrimeDifference_energy,
      resonantMobius_geometric_high_pointwise hψ,resonantArcModel_terminal_energy,eventually_ge_atTop (1:ℕ)]
    with n hG hE happrox hM hn
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let V := highNaturalPrimeTubes n
  let L := 1+Real.log (n:ℝ)
  let G := terminalLargeWave n
  let S := centralPrimeWave n
  let T := resonantMobiusWave n R n
  let M := resonantPrincipalModel n
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hQ : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hL1 : 1≤L := by dsimp [L];linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hsc : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hG' : Continuous G := by unfold G terminalLargeWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hS' : Continuous S := by unfold S centralPrimeWave E;fun_prop
  have hT' q : Continuous (T q) := by unfold T resonantMobiusWave smallDivisorWave positiveDivisorRow E;fun_prop
  have hM' q : Continuous (M q) := by unfold M resonantPrincipalModel dirichletGeometricKernel E;fun_prop
  have herr := row_bilinear_error n R Q hQ S G T M hS' hG' hT' hM' (L*Real.sqrt L) (Real.sqrt n/L^8)
    (by positivity) (by
      intro j hj β hβ
      obtain ⟨hl,hu⟩ := mem_Ico.mp hj
      exact happrox (j+1) (by omega) (by omega) β (abs_le.mpr hβ))
  change (∫ t in V,‖G t‖)≤1500001*Real.sqrt n*L at hG
  change (∫ t in V,‖G t-S t‖^2)≤737284*(n:ℝ)/L^2 at hE
  change primeLinearRows R Q (fun q _ β => ‖M q β‖^2)≤8*(n:ℝ)*L at hM
  change _ ≤ 3737294*(n:ℝ)/Real.sqrt L
  apply herr.trans
  change (2*(Real.sqrt n/L^8))*(∫ t in V,‖G t‖)+(L*Real.sqrt L)*(∫ t in V, ‖G t-S t‖^2)+
      (L*Real.sqrt L)⁻¹*primeLinearRows R Q (fun q _ β => ‖M q β‖^2)≤_
  have he : Real.sqrt L≤L^7 := by
    apply (Real.sqrt_le_iff.mpr ⟨hL.le,by simpa using pow_le_pow_right₀ hL1 (by decide : 1≤2)⟩).trans
    simpa using pow_le_pow_right₀ hL1 (by decide : 1≤7)
  calc
    _ ≤ (2*(Real.sqrt n/L^8))*(1500001*Real.sqrt n*L)+(L*Real.sqrt L)*(737284*(n:ℝ)/L^2)+
        (L*Real.sqrt L)⁻¹*(8*(n:ℝ)*L) := by
      gcongr
    _ = 3000002*(n:ℝ)/L^7+737292*(n:ℝ)/Real.sqrt L := by
      have hn2 := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
      have hls := Real.sq_sqrt hL.le
      field_simp
      linear_combination 3000002*Real.sqrt L*hn2 + (L^6*737284*(n:ℝ))*hls
    _ ≤ 3000002*(n:ℝ)/Real.sqrt L+737292*(n:ℝ)/Real.sqrt L := by gcongr
    _ = _ := by ring

theorem largeMobius_primeLinear_eventually_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n; let Q := naturalTubeScale n
      ‖(∫ t in highNaturalPrimeTubes n,largeMobiusKernel n R t)-
        (nonresonantSquareMass n R R Q+truePrimeLinearMass n)‖≤ε*n := by
  have hL : Tendsto (fun n : ℕ => 1+Real.log (n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog := (Real.tendsto_sqrt_atTop.comp hL).eventually_ge_atTop (2*3737294/ε)
  filter_upwards [currentGT_bound hψ,allResonantMobiusHighMass_eventually_small (show 0<ε/2 by positivity),
      hlog,eventually_ge_atTop (1:ℕ)] with n hgt ht hl hn
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let U := ∫ t in highNaturalPrimeTubes n,largeMobiusKernel n R t
  let N := nonresonantSquareMass n R R Q
  let GT := primeBilinearMass n R Q (fun _ => terminalLargeWave n) (resonantMobiusWave n R n)
  let T := allResonantMobiusHighMass n R
  let M := truePrimeLinearMass n
  let L := 1+Real.log (n:ℝ)
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hQ : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have h1 : U-nonresonantMobiusRemainderMass n R R Q=T := largeMobiusHighMass_sub_remainder hQ R
  have h2 : N+GT=nonresonantMobiusRemainderMass n R R Q+(T+T) := exactGT n
  have hid : U-(N+M)=(GT-M)-T := by linear_combination h1-h2
  change ‖U-(N+M)‖ ≤_
  rw [hid]
  change ‖GT-M‖≤3737294*(n:ℝ)/Real.sqrt L at hgt
  change 2*3737294/ε≤Real.sqrt L at hl
  have hpos : 0<Real.sqrt L := by dsimp [L];positivity
  have hb : 3737294*(n:ℝ)/Real.sqrt L≤(ε/2)*n := by
    apply (div_le_iff₀ hpos).mpr
    have hs := (div_le_iff₀ hε).mp hl
    nlinarith only [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) n)]
  apply (norm_sub_le _ _).trans
  linarith only [hgt.trans hb,ht R]

/-- The mixed frequency band itself has the same signed mass as the true-prime linear term. -/
theorem trueMixed_primeLinear_eventually_small (hψ : grhAllUniform) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let R := terminalPrimeArcCutoff n; let Q := naturalTubeScale n
      ‖trueMixedFrequencyBand n R R Q (Icc 1 n)-truePrimeLinearMass n‖≤ε*n := by
  have h : 0<ε/2 := by positivity
  filter_upwards [largeMobius_primeLinear_eventually_small hψ h,
      largeMobiusHighMass_remainder_eventually_small h] with n h1 h2
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let U := ∫ t in highNaturalPrimeTubes n,largeMobiusKernel n R t
  let N := nonresonantSquareMass n R R Q
  let M := truePrimeLinearMass n
  let F := trueMixedFrequencyBand n R R Q (Icc 1 n)
  have he : nonresonantMobiusRemainderMass n R R Q=N+F := trueMixedFrequencyBand_complete n R R Q
  have hh := h2 R
  rw [he] at hh
  change ‖U-(N+F)‖≤(ε/2)*n at hh
  change ‖U-(N+M)‖≤(ε/2)*n at h1
  change ‖F-M‖≤_
  rw [show F-M=(U-(N+M))-(U-(N+F)) by ring]
  exact (norm_sub_le _ _).trans (by linarith only [h1,hh])

end GoldbachPartial
