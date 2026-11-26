import DistantPrimePairReduction
import AbelParsevalPrimeArc
import GoldbachCRTRemainder
import NaturalTubeDilation
import TruePrimeCenteringYoung

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private theorem rowSum_weighted_energy {U : Set ℝ} (hi : U⊆Set.Icc 0 1)
    (I : Finset ℕ) (a : ℕ → ℂ) (B : ℕ → ℝ → ℂ)
    (hc : ∀ d∈I,Continuous (B d)) {K : ℝ}
    (hK : ∀ d∈I,(∫ t in U, ‖B d t‖^2) ≤ K) :
    (∫ t in U,‖∑ d ∈ I,a d*B d t‖^2) ≤ K*(∑ d ∈ I,‖a d‖)^2 := by
  let A := ∑ d ∈ I,‖a d‖
  let G := fun d t => ‖a d‖*‖B d t‖^2
  have hA : 0≤A := sum_nonneg fun _ _ => norm_nonneg _
  have hG (d) (hd : d∈I) : IntegrableOn (G d) U :=
    ((continuous_const.mul ((hc d hd).norm.pow 2)).integrableOn_Icc).mono_set hi
  have hU : IntegrableOn (fun t => ‖∑ d ∈ I,a d*B d t‖^2) U :=
    ((continuous_finsetSum I (fun d hd => continuous_const.mul (hc d hd))).norm.pow 2).integrableOn_Icc.mono_set hi
  have hp (t : ℝ) : ‖∑ d ∈ I,a d*B d t‖^2 ≤ A*∑ d ∈ I,G d t := by
    have ht := norm_sum_le I (fun d => a d*B d t)
    simp only [norm_mul] at ht
    apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul I (fun d _ => norm_nonneg (a d))
      (fun d _ => mul_nonneg (norm_nonneg (a d)) (sq_nonneg _))
    intro d _
    exact le_of_eq (by ring)
  apply (integral_mono hU ((integrable_finsetSum I hG).const_mul A) hp).trans
  rw [integral_const_mul,integral_finsetSum I hG]
  have hterm (d) (hd : d∈I) : (∫ t in U,G d t)≤‖a d‖*K := by
    dsimp only [G]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hK d hd) (norm_nonneg _)
  calc
    _ ≤ A*∑ d ∈ I,‖a d‖*K := mul_le_mul_of_nonneg_left (sum_le_sum hterm) hA
    _ = _ := by rw [←sum_mul]; change A*(A*K)=K*A^2; ring

/-- Fourier row for positive multiples of d up to n. -/
noncomputable def positiveDivisorRow (n d : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ (Icc 1 n).filter (fun k => d∣k), E ((k:ℝ)*t)

theorem positiveDivisorRow_eq {n d : ℕ} (hd : 0<d) (hdn : d≤n) (t : ℝ) :
    positiveDivisorRow n d t = E ((d:ℝ)*t)*dirichletGeometricKernel (n/d-1) ((d:ℝ)*t) := by
  have hL : 0<n/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa)
  unfold positiveDivisorRow dirichletGeometricKernel
  rw [mul_sum]
  symm
  apply sum_bij (fun j _ => (j+1)*d)
  · intro j hj
    have hj' := mem_range.mp hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos (by omega) hd,?_⟩,dvd_mul_left _ _⟩
    apply (Nat.le_div_iff_mul_le hd).mp
    omega
  · intro i _ j _ hij
    have he := Nat.eq_of_mul_eq_mul_right hd hij
    omega
  · intro k hk
    obtain ⟨hkI,hdk⟩ := mem_filter.mp hk
    obtain ⟨hk1,hkn⟩ := mem_Icc.mp hkI
    have hkd : d≤k := Nat.le_of_dvd hk1 hdk
    have hdiv : 1≤k/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa)
    refine ⟨k/d-1,mem_range.mpr (by have hquot : k/d≤n/d := Nat.div_le_div_right hkn; omega),?_⟩
    rw [Nat.sub_add_cancel hdiv,Nat.div_mul_cancel hdk]
  · intro j _
    rw [←phase_add]
    push_cast
    congr 1
    ring

noncomputable def smallDivisorWave (n : ℕ) (I : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :=
  ∑ d ∈ I, a d*positiveDivisorRow n d t

theorem smallDivisorWave_coefficients (n : ℕ) (I : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    smallDivisorWave n I a t = ∑ k ∈ Icc 1 n,(∑ d ∈ I.filter (fun d => d∣k),a d)*E ((k:ℝ)*t) := by
  unfold smallDivisorWave positiveDivisorRow
  simp_rw [mul_sum,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [sum_mul]
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

open scoped ArithmeticFunction.vonMangoldt

noncomputable def properPrimePowerWave (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), ((Λ k-weight k:ℝ):ℂ)*E ((k:ℝ)*t)

theorem primeWave_largeDivisor_decomposition {n D : ℕ} (hD : D≤n) (t : ℝ) :
    centralPrimeWave n t =
      smallDivisorWave n (Ioc D n) (fun d => (crtLambdaCoefficient d:ℂ)) t +
      (smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t -
        properPrimePowerWave n t) := by
  let a := fun d => (crtLambdaCoefficient d:ℂ)
  have hdis : Disjoint (Icc 1 D) (Ioc D n) := by
    simp only [Finset.disjoint_left,mem_Icc,mem_Ioc]; omega
  have hU : Icc 1 D ∪ Ioc D n=Icc 1 n := by
    ext d
    simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have hab : smallDivisorWave n (Icc 1 D) a t + smallDivisorWave n (Ioc D n) a t =
      smallDivisorWave n (Icc 1 n) a t := by
    unfold smallDivisorWave
    rw [←sum_union hdis,hU]
  have hco (k : ℕ) (hk : k∈Icc 1 n) :
      ∑ d ∈ (Icc 1 n).filter (fun d => d∣k),a d = ((Λ k:ℝ):ℂ) := by
    obtain ⟨hk0,hkn⟩ := mem_Icc.mp hk
    have hs : (Icc 1 n).filter (fun d => d∣k)=k.divisors := by
      ext d
      simp only [mem_filter,mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨_,hd⟩; exact ⟨hd,by omega⟩
      · rintro ⟨hd,_⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk0,(Nat.le_of_dvd hk0 hd).trans hkn⟩,hd⟩
    rw [hs]
    change (∑ d ∈ k.divisors,((crtLambdaCoefficient d:ℝ):ℂ))=_
    rw [←Complex.ofReal_sum]
    apply congrArg Complex.ofReal
    have hm := ArithmeticFunction.sum_moebius_mul_log_eq (n:=k)
    simp only [ArithmeticFunction.log_apply] at hm
    simp only [crtLambdaCoefficient,neg_mul,sum_neg_distrib,hm,neg_neg]
  have hfull : smallDivisorWave n (Icc 1 n) a t=centralPrimeWave n t+properPrimePowerWave n t := by
    rw [smallDivisorWave_coefficients]
    unfold centralPrimeWave properPrimePowerWave
    rw [←sum_add_distrib]
    have hI : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp only [mem_range,mem_insert,mem_Icc]; omega
    rw [hI,sum_insert (by simp)]
    simp only [weight,Nat.not_prime_zero,ite_false,Complex.ofReal_zero,zero_mul,
      ArithmeticFunction.map_zero,sub_zero,add_zero,zero_add]
    apply sum_congr rfl
    intro k hk
    rw [hco k hk,Complex.ofReal_sub]
    ring
  have hsum := hab.trans hfull
  change _=smallDivisorWave n (Ioc D n) a t + (smallDivisorWave n (Icc 1 D) a t-properPrimePowerWave n t)
  linear_combination -hsum

theorem properPrimePowerWave_energy (n : ℕ) {V : Set ℝ} (hi : V⊆Set.Icc 0 1) :
    (∫ t in V,‖properPrimePowerWave n t‖^2) ≤ 2*Real.sqrt n*(Real.log n)^2 := by
  let F := fun t => ‖properPrimePowerWave n t‖^2
  have hc : Continuous F := by unfold F properPrimePowerWave E; fun_prop
  have hn (k:ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hper : Function.Periodic (properPrimePowerWave n) 1 := by
    intro t
    unfold properPrimePowerWave
    simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
  have hF : Function.Periodic F 1 := fun t => congrArg (fun z:ℂ => ‖z‖^2) (hper t)
  have hshift := hF.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at hshift
  have he := finiteAbelWave_unit_energy (range (n+1)) (fun k => ((Λ k-weight k:ℝ):ℂ))
  change (∫ t in (-(1/2):ℝ)..(1/2),F t)=_ at he
  have hm : (∫ t in V,F t) ≤ ∫ t in Set.Icc (0:ℝ) 1,F t :=
    setIntegral_mono_set hc.integrableOn_Icc (Eventually.of_forall fun _ => sq_nonneg _) hi.eventuallySubset
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),←hshift,he] at hm
  apply hm.trans
  have hw (k : ℕ) : weight k≤Λ k := by
    by_cases hp : k.Prime
    · simp [weight,hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [weight,hp]
  have hL (k : ℕ) (hk : k≤n) : |Λ k-weight k|≤Real.log n := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hw _))]
    have hw0 : 0≤weight k := by
      dsimp only [weight]; split_ifs <;> first | exact le_rfl | exact Real.log_natCast_nonneg _
    apply (sub_le_self _ hw0).trans
    rcases Nat.eq_zero_or_pos k with rfl|hp
    · simpa using Real.log_natCast_nonneg n
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hk))
  simp only [Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ∑ k ∈ range (n+1),|Λ k-weight k| * Real.log n := by
      apply sum_le_sum
      intro k hk
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hL _ (by have := mem_range.mp hk;omega)) (abs_nonneg _)
    _ ≤ _ := by
      rw [←sum_mul]
      exact (mul_le_mul_of_nonneg_right (primePowerError_le n) (Real.log_natCast_nonneg _)).trans_eq (by ring)

theorem smallDivisorWave_energy {n : ℕ} {I : Finset ℕ} {U : Set ℝ} {K : ℝ}
    (hi : U⊆Set.Icc 0 1) (hd : ∀ d∈I,0<d ∧ d≤n)
    (hrow : ∀ d∈I, (∫ t in U,‖dirichletGeometricKernel (n/d-1) ((d:ℝ)*t)‖^2)≤K)
    (a : ℕ → ℂ) :
    (∫ t in U,‖smallDivisorWave n I a t‖^2) ≤ K*(∑ d ∈ I,‖a d‖)^2 := by
  apply rowSum_weighted_energy hi I a (positiveDivisorRow n)
  · intro d _
    unfold positiveDivisorRow E
    fun_prop
  · intro d hdI
    simp_rw [positiveDivisorRow_eq (hd d hdI).1 (hd d hdI).2,norm_mul,
      show ∀ x:ℝ, ‖E x‖=1 from fun x => Complex.norm_exp_ofReal_mul_I _,one_mul]
    exact hrow d hdI

theorem smallMobiusWave_energy {n D : ℕ} {U : Set ℝ} {K : ℝ}
    (hi : U⊆Set.Icc 0 1) (hDn : D≤n) (hK : 0≤K)
    (hrow : ∀ d∈Icc 1 D,(∫ t in U,‖dirichletGeometricKernel (n/d-1) ((d:ℝ)*t)‖^2)≤K) :
    (∫ t in U,‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t‖^2) ≤
      K*((D:ℝ)*Real.log n)^2 := by
  apply (smallDivisorWave_energy hi (fun d hd => ⟨(mem_Icc.mp hd).1,((mem_Icc.mp hd).2).trans hDn⟩)
    hrow (fun d => (crtLambdaCoefficient d:ℂ))).trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply pow_le_pow_left₀ (sum_nonneg fun _ _ => norm_nonneg _)
  calc
    _ ≤ ∑ _d ∈ Icc 1 D,Real.log n := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd0,hdD⟩ := mem_Icc.mp hd
      simp only [Complex.norm_real,Real.norm_eq_abs,crtLambdaCoefficient,abs_mul,abs_neg,
        abs_of_nonneg (Real.log_natCast_nonneg d)]
      have hm : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
      calc
        _ ≤ 1*Real.log d := mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact Real.log_le_log (by exact_mod_cast hd0) (by exact_mod_cast hdD.trans hDn)
    _ = _ := by simp [nsmul_eq_mul]

theorem smallMobius_sub_power_energy {n D : ℕ} {U : Set ℝ} {K : ℝ}
    (hi : U⊆Set.Icc 0 1) (hDn : D≤n) (hK : 0≤K)
    (hrow : ∀ d∈Icc 1 D,(∫ t in U,‖dirichletGeometricKernel (n/d-1) ((d:ℝ)*t)‖^2)≤K) :
    (∫ t in U,‖smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t -
      properPrimePowerWave n t‖^2) ≤ 2*K*((D:ℝ)*Real.log n)^2+4*Real.sqrt n*(Real.log n)^2 := by
  let S := smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ))
  let P := properPrimePowerWave n
  have hS : Continuous S := by unfold S smallDivisorWave positiveDivisorRow E; fun_prop
  have hP : Continuous P := by unfold P properPrimePowerWave E; fun_prop
  have hI {f:ℝ→ℝ} (h:Continuous f) : IntegrableOn f U := h.integrableOn_Icc.mono_set hi
  have h (t : ℝ) : ‖S t-P t‖^2≤2*‖S t‖^2+2*‖P t‖^2 := by
    have h' := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (S t) (P t)) 2
    nlinarith only [h',sq_nonneg (‖S t‖-‖P t‖)]
  change (∫ t in U,‖S t-P t‖^2)≤_
  apply (integral_mono (hI ((hS.sub hP).norm.pow 2)) (hI ((continuous_const.mul (hS.norm.pow 2)).add
    (continuous_const.mul (hP.norm.pow 2)))) h).trans
  change (∫ t in U,2*‖S t‖^2+2*‖P t‖^2)≤_
  rw [integral_add (f:=fun t => 2*‖S t‖^2) (g:=fun t => 2*‖P t‖^2)
    (hI (continuous_const.mul (hS.norm.pow 2))) (hI (continuous_const.mul (hP.norm.pow 2))),
    integral_const_mul,integral_const_mul]
  have hs := smallMobiusWave_energy hi hDn hK hrow
  have hp := properPrimePowerWave_energy n hi
  change (∫ t in U,‖S t‖^2)≤_ at hs
  change (∫ t in U,‖P t‖^2)≤_ at hp
  linarith only [hs,hp]

/-- Keep only divisors beyond D in the exact Möbius formula for the von Mangoldt wave. -/
noncomputable def largeMobiusKernel (n D : ℕ) (t : ℝ) : ℂ :=
  (smallDivisorWave n (Ioc D n) (fun d => (crtLambdaCoefficient d:ℂ)) t)^2*E (-(n:ℝ)*t)

theorem largeMobiusKernel_naturalTube_bound {n D R Q : ℕ} (hR : 0<R) (hQ : 0<Q) (hDR : D≤R) (hDn : D≤n)
    {s : ℝ} (hs : 0<s) :
    let U := naturalTubeUnion R Q (3*Q)
    ‖(∫ t in U,primeSquareKernel n t)-(∫ t in U,largeMobiusKernel n D t)‖ ≤
      s*(((n:ℝ)+1)*(Real.log n)^2)+(1+s⁻¹)*
        (24*(Q:ℝ)*((D:ℝ)*Real.log n)^2+4*Real.sqrt n*(Real.log n)^2) := by
  let U := naturalTubeUnion R Q (3*Q)
  let B := fun t => smallDivisorWave n (Icc 1 D) (fun d => (crtLambdaCoefficient d:ℂ)) t-properPrimePowerWave n t
  have hB : Continuous B := by
    unfold B smallDivisorWave positiveDivisorRow properPrimePowerWave E
    fun_prop
  have hi := naturalTubeUnion_inside_unit (B:=R) (R:=Q) hR (by omega : 0<3*Q)
  have he := truePrime_centering_young n hi B hB hs
  have hsame : centeredTruePrimeKernel n B=largeMobiusKernel n D := by
    ext1 t
    unfold centeredTruePrimeKernel largeMobiusKernel
    congr 2
    have hh := primeWave_largeDivisor_decomposition hDn t
    change centralPrimeWave n t - B t = _
    change centralPrimeWave n t = _ + B t at hh
    rw [hh,add_sub_cancel_right]
  rw [hsame] at he
  apply he.trans
  have hrow (d : ℕ) (hd : d∈Icc 1 D) := naturalTube_dilate_geometricKernel_energy
    (Q:=Q) (mem_Icc.mp hd).1 ((mem_Icc.mp hd).2.trans hDR) (n/d-1)
  have hE := smallMobius_sub_power_energy hi hDn (by positivity : 0≤12*(Q:ℝ)) hrow
  change (∫ t in U,‖B t‖^2) ≤ _ at hE
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hE.trans_eq (by ring)

noncomputable def smallMobiusCutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/4:ℝ)/(1+Real.log n)^4⌋₊

theorem largeMobiusKernel_high_error :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (smallMobiusCutoff n) t)‖ ≤
        58*(n:ℝ)/(1+Real.log n)^2 := by
  let t := fun n : ℕ => (n:ℝ)^(1/32:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 2,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht2 hl1
  let L := 1+Real.log (n:ℝ)
  let A := (n:ℝ)^(1/4:ℝ)
  let D := smallMobiusCutoff n
  let Q := naturalTubeScale n
  let T := t n
  have hT2 : 2≤T := ht2
  have hT : 0<T := by linarith
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL1 : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hlog : Real.log n≤L := by dsimp [L]; linarith
  have hpow (k : ℕ) : T^k=(n:ℝ)^((1/32:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤(n:ℝ))]
  have h16 : T^16=Real.sqrt n := by rw [hpow,Real.sqrt_eq_rpow]; norm_num
  have hL2T : L≤2*T := by
    change Real.log n/T<1 at hl1
    dsimp only [L]
    linarith [(div_lt_iff₀ hT).mp hl1]
  have hL8 : L^8 ≤ Real.sqrt n := calc
    _ ≤ (2*T)^8 := pow_le_pow_left₀ hL.le hL2T _
    _ ≤ (T*T)^8 := by gcongr
    _ = T^16 := by ring
    _ = _ := h16
  have hA2 : A^2=Real.sqrt n := by
    dsimp only [A]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤(n:ℝ)),Real.sqrt_eq_rpow]
    norm_num
  have hA : 0≤A := by dsimp [A]; positivity
  have hA4 : A^2*A^2=(n:ℝ) := by rw [hA2,Real.mul_self_sqrt (by positivity)]
  have hD : (D:ℝ)≤A/L^4 := Nat.floor_le (by positivity)
  have hDR : D ≤ terminalPrimeArcCutoff n := by
    apply Nat.le_trans (m:=medDeskD n) _ hg.2.1
    apply Nat.floor_mono
    apply (div_le_self hA (one_le_pow₀ hL1)).trans
    exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  have hDn : D≤n := hDR.trans hg.2.2.2.1
  have hQ0 : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hQ : (Q:ℝ)≤Real.sqrt n := Nat.floor_le (by positivity)
  have hlow := largeMobiusKernel_naturalTube_bound (R:=terminalPrimeArcCutoff n) (Q:=Q)
    (hg.1.trans_le hg.2.1) hQ0 hDR hDn (s:=(L^4)⁻¹) (by positivity)
  apply hlow.trans
  have hsmall : 24*(Q:ℝ)*((D:ℝ)*Real.log n)^2 ≤ 24*(n:ℝ)/L^6 := calc
    _ ≤ 24*(Real.sqrt n)*((A/L^4)*L)^2 := by gcongr
    _ = _ := by rw [←hA2,←hA4]; field_simp
  have hproper : 4*Real.sqrt n*(Real.log n)^2 ≤ 4*(n:ℝ)/L^6 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (4*Real.sqrt n*L^2)*L^6 := by gcongr
      _ = 4*Real.sqrt n*L^8 := by ring
      _ ≤ 4*Real.sqrt n*Real.sqrt n := by gcongr
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (by positivity)]
  have htot := add_le_add hsmall hproper
  change _≤58*(n:ℝ)/L^2
  rw [inv_inv]
  have hX : (n:ℝ)+1≤2*(n:ℝ) := by linarith
  have h4one := one_le_pow₀ hL1 (n:=4)
  calc
    _ ≤ (L^4)⁻¹*((2*(n:ℝ))*L^2)+(2*L^4)*(24*(n:ℝ)/L^6+4*(n:ℝ)/L^6) := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul (by linarith only [h4one]) htot (by positivity) (by positivity)
    _ = _ := by field_simp; ring

noncomputable def largeMobiusArcMass (n : ℕ) : ℝ :=
  primeArcMass (highNaturalPrimeTubes n)ᶜ n +
    (∫ t in highNaturalPrimeTubes n,largeMobiusKernel n (smallMobiusCutoff n) t).re

theorem largeMobiusArcMass_error :
    ∀ᶠ n : ℕ in atTop, |largeMobiusArcMass n-corr n| ≤ 58*(n:ℝ)/(1+Real.log n)^2 := by
  filter_upwards [largeMobiusKernel_high_error,highNaturalPrimeTubes_geometry] with n h hg
  let V := highNaturalPrimeTubes n
  have hm : MeasurableSet V := naturalTubeUnion_measurable ..
  have hs := corr_eq_primeArcMass n V hm
  rw [primeArcMass_eq_setIntegral_re_of_subset_Icc n hm hg.1] at hs
  let z := (∫ t in V,primeSquareKernel n t) - (∫ t in V,largeMobiusKernel n (smallMobiusCutoff n) t)
  have hh : |z.re|≤58*(n:ℝ)/(1+Real.log n)^2 := (Complex.abs_re_le_norm _).trans h
  have he : largeMobiusArcMass n-corr n= -z.re := by
    unfold largeMobiusArcMass
    dsimp only [z,Complex.sub_re]
    change corr n=(∫ t in V,primeSquareKernel n t).re + primeArcMass Vᶜ n at hs
    change primeArcMass Vᶜ n + _ - corr n = _
    linarith only [hs]
  simpa only [he,abs_neg] using hh

theorem largeMobiusArcMass_close {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |largeMobiusArcMass n-corr n|≤ε*(n:ℝ) := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (58/ε)
  filter_upwards [largeMobiusArcMass_error,hl] with n h hn
  change 58/ε≤Real.log (n:ℝ) at hn
  have hL : 1≤1+Real.log n := by linarith [Real.log_natCast_nonneg n]
  apply h.trans
  rw [div_le_iff₀ (by positivity : 0<(1+Real.log (n:ℝ))^2)]
  have hsq : Real.log n≤(1+Real.log n)^2 := by nlinarith [Real.log_natCast_nonneg n,sq_nonneg (Real.log n)]
  have hh := (div_le_iff₀ hε).mp (hn.trans hsq)
  linarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) n)]

/-- The exact frozen dyadic floor is equivalent to positivity after all divisor rows up to
n^(1/4)/(1+log n)^4 are removed on the large-denominator arcs. -/
theorem dyadic_floor_iff_largeMobiusArcMass :
    (∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p))) ↔
    (∃ d : ℝ, 0<d ∧ ∀ᶠ n : ℕ in atTop, Even n → d*(n:ℝ)≤largeMobiusArcMass n) := by
  constructor
  · rintro ⟨c,N,hc,hfloor⟩
    refine ⟨c/2,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),
      largeMobiusArcMass_close (ε:=c/2) (by positivity)] with n hn hn1 he
    intro hev
    have h : c*(n:ℝ)≤corr n := hfloor n n hn le_rfl (by omega) hev
    linarith only [h,(abs_le.mp he).1]
  · rintro ⟨d,hd,hrest⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hrest.and (largeMobiusArcMass_close (ε:=d/2) (by positivity)))
    refine ⟨d/2,N,by positivity,?_⟩
    intro X n hX hXn _ hev
    change _≤corr n
    obtain ⟨hm,he⟩ := hN n (hX.trans hXn)
    linarith only [hm hev,(abs_le.mp he).2]

end GoldbachPartial