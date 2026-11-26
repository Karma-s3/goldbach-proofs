import VerifiedFixedUniformMajorArcs
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical
open private GoldbachMajorArc.class_error_trivial from PinnedUpstream316

private theorem uniform_class_endpoint (K d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ u : ℕ in atTop,
      ∀ q a : ℕ, 0<q → (q:ℝ)≤(Real.log u)^d → a<q →
        |GoldbachMajorArc.classError (u+1) q a| ≤ C*u/(Real.log u)^(K+d+1) := by
  let A : ℕ := K+d+1
  have hA : 0 < (A:ℝ) := by dsimp [A]; positivity
  obtain ⟨M,hM,x₀,_,hap⟩ := GoldbachMajorArc.all_class_error (A:ℝ) (d:ℝ) hA (by exact_mod_cast hd)
  refine ⟨M+5,by positivity,?_⟩
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((A+2:ℕ):ℝ) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [htlog,hpow,eventually_ge_atTop (max 1 ⌈x₀⌉₊)] with u hlog hpow hu
  intro q a hq hqL ha
  let L := Real.log u
  have hx : x₀≤(u:ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right 1 ⌈x₀⌉₊).trans hu)
  have huR : (1:ℝ)≤u := by exact_mod_cast (le_max_left 1 ⌈x₀⌉₊).trans hu
  change 1≤L at hlog
  have hL : 0<L := by linarith
  have hbig : L^(A+2) ≤ Real.sqrt u := by simpa only [L,Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow] using hpow
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) u)
  have hnext := (pow_le_pow_right₀ hlog (by omega : A+1≤A+2)).trans hbig
  have hroot : Real.sqrt u≤(u:ℝ) := by
    have h1 : 1≤Real.sqrt (u:ℝ) := by simpa using Real.sqrt_le_sqrt huR
    nlinarith only [hr,mul_nonneg (zero_le_one.trans h1) (sub_nonneg.mpr h1)]
  have hqlog : Real.log q≤L := by
    apply Real.log_le_log (by exact_mod_cast hq)
    exact hqL.trans ((pow_le_pow_right₀ hlog (by dsimp [A]; omega : d≤A+2)).trans (hbig.trans hroot))
  have hnat : (Nat.log 2 u:ℝ)≤2*L := by
    have h := Real.natLog_le_logb u 2
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    simp only [Nat.cast_ofNat,Real.logb] at h
    apply h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr _)
    nlinarith only [mul_nonneg hL.le (show 0≤2*Real.log 2-1 by linarith)]
  have hAP := hap u q a hx hq (by simpa only [Real.rpow_natCast] using hqL) ha
  change _ ≤ M*(u:ℝ)*L^(-(A:ℝ))+(Nat.log 2 u:ℝ)*Real.log q+2*Real.sqrt u*L+1 at hAP
  rw [Real.rpow_neg hL.le,Real.rpow_natCast,←div_eq_mul_inv] at hAP
  apply hAP.trans
  have hx1 : (Nat.log 2 u:ℝ)*Real.log q ≤ 2*(u:ℝ)/L^A := by
    apply (mul_le_mul hnat hqlog (Real.log_natCast_nonneg _) (by positivity)).trans
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
  have hx3:1≤(u:ℝ)/L^A := by
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    rw [one_mul]
    exact (pow_le_pow_right₀ hlog (by omega : A≤A+2)).trans (hbig.trans hroot)
  change _≤(M+5)*(u:ℝ)/L^A
  linear_combination hx1+hx2+hx3


theorem commonWidth_SW_class_prefix (K b:ℕ):
    ∃C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀q:ℕ,0<q→(q:ℝ)≤(Real.log n)^b→
      ∀m≤n+1,∀a<q,|GoldbachMajorArc.classError m q a|≤C*(n:ℝ)/(Real.log n)^K := by
  obtain ⟨c,hc,hend⟩:=uniform_class_endpoint K (b+1) (Nat.succ_pos _)
  obtain ⟨T,hT⟩:=eventually_atTop.mp hend
  let C:=c*(2:ℝ)^K+2*(Real.log 4+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hr:=Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp:∀ᶠ n:ℕ in atTop,(Real.log n)^K≤Real.sqrt n:=by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
        (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (K:ℝ) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hl.eventually_ge_atTop (2*(2:ℝ)^b),hr.eventually_ge_atTop (T:ℝ),hp,
    eventually_ge_atTop (2:ℕ)] with n hnhr hroot hp hn
  intro q hq hqL m hm a ha
  let L:=Real.log (n:ℝ)
  let x:=Real.sqrt (n:ℝ)
  have hL':2*(2:ℝ)^b≤L:=hnhr
  have hL:0<L:=Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hxx:x^2=(n:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  have hx1:1≤x:=by simpa only [x,Real.sqrt_one] using Real.sqrt_le_sqrt (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega))
  have hxs:x≤(n:ℝ)/L^K := by
    rw [le_div_iff₀ (pow_pos hL _)]
    exact (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)).trans_eq (by rw [←sq,hxx])
  cases m with
  | zero =>
    simp only [GoldbachMajorArc.classError,GoldbachMajorArc.classMass,range_zero,filter_empty,sum_empty,Nat.cast_zero,zero_div,ite_self,sub_zero,abs_zero]
    dsimp [C];positivity
  | succ u =>
    have hun:u≤n:=by omega
    have hur: (u:ℝ)≤n:=by exact_mod_cast hun
    by_cases hs:(u:ℝ)<x
    · apply (GoldbachMajorArc.class_error_trivial u q a hq).trans
      have hsum: (u:ℝ)+1≤2*((n:ℝ)/L^K):=by linarith only [hs,hx1,hxs]
      have hc':2*(Real.log 4+1)≤C:=by dsimp [C];linarith only [show 0≤c*(2:ℝ)^K by positivity]
      calc _ ≤ (Real.log 4+1)*(2*((n:ℝ)/L^K)) := mul_le_mul_of_nonneg_left hsum (by positivity)
           _ = (2*(Real.log 4+1))*(n:ℝ)/L^K:=by ring
           _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)) (by positivity)
    · have hxu:=le_of_not_gt hs
      have hu:(0:ℝ)<u:=by linarith only [hx1,hxu]
      have hcmp:=Real.log_le_log (zero_lt_one.trans_le hx1) hxu
      change Real.log (Real.sqrt (n:ℝ))≤Real.log (u:ℝ) at hcmp
      rw [Real.log_sqrt (Nat.cast_nonneg _)] at hcmp
      have h2:L≤2*Real.log (u:ℝ):=by change L/2≤_ at hcmp;linarith
      have huu:(2:ℝ)^b≤Real.log u:=by linarith only [h2,hL']
      have hlog:1≤Real.log (u:ℝ):=(one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans huu
      have hlogp:0<Real.log (u:ℝ):=zero_lt_one.trans_le hlog
      have ht:T≤u:=by exact_mod_cast (show (T:ℝ)≤u from le_trans hroot hxu)
      have hqb:(q:ℝ)≤(Real.log u)^(b+1) := calc
        _ ≤ (2*Real.log (u:ℝ))^b := hqL.trans (pow_le_pow_left₀ hL.le h2 b)
        _ = (2:ℝ)^b*(Real.log u)^b:=mul_pow .. 
        _ ≤ _ := by rw [pow_succ,mul_comm ((Real.log u)^b)];gcongr
      have hh:=hT u ht q a hq hqb ha
      have hden:L^K≤(2:ℝ)^K*(Real.log u)^K:=by rw [←mul_pow];exact pow_le_pow_left₀ hL.le h2 _
      have hpre: |GoldbachMajorArc.classError (u+1) q a|≤c*(u:ℝ)/(Real.log u)^K:=
        hh.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hlogp _) (pow_le_pow_right₀ hlog (by omega)))
      apply hpre.trans
      apply (div_le_div_iff₀ (pow_pos hlogp _) (pow_pos hL _)).mpr
      have hc':c*(2:ℝ)^K≤C:=by dsimp [C];linarith only [show 0≤2*(Real.log 4+1) by positivity]
      calc _ ≤ (c*n)*((2:ℝ)^K*(Real.log u)^K) := mul_le_mul (mul_le_mul_of_nonneg_left hur hc.le) hden (by positivity) (by positivity)
           _ = (c*(2:ℝ)^K)*(n:ℝ)*(Real.log u)^K:=by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)) (by positivity)

theorem commonWidth_SW_wave (A b:ℕ):
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℕ in atTop,∀q a:ℕ,0<q→(q:ℝ)≤(Real.log N)^b→
      ∀β:ℝ,(N:ℝ)*|β|≤(Real.log N)^b →
        ‖centralPrimeWave N ((a:ℝ)/q+β)-GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β‖≤
          C*(N:ℝ)/(Real.log N)^A := by
  let K:=A+b+b
  obtain ⟨c,hc,hh⟩:=commonWidth_SW_class_prefix K b
  refine ⟨c*(1+2*Real.pi),by positivity,?_⟩
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hh,hl.eventually_ge_atTop 1] with N hn hL1
  intro q a hq hsize β hβ
  let L:=Real.log (N:ℝ)
  have h1:1≤L:=hL1
  have hL:0<L:=zero_lt_one.trans_le h1
  have hs: GoldbachMajorArc.prefixError N ((a:ℝ)/q) (GoldbachMajorArc.unitMean q a)≤
      L^b*(c*N/L^K) := by
    unfold GoldbachMajorArc.prefixError
    apply Finset.sup'_le
    intro m hm
    apply (GoldbachMajorArc.center_prefix_bound hq a m).trans
    calc _ ≤ ∑_r∈range q,c*(N:ℝ)/L^K :=
           sum_le_sum (fun r hr=>hn q hq hsize m (by have:=mem_range.mp hm;omega) r (mem_range.mp hr))
         _ ≤ _ := by simp only [sum_const,card_range,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right hsize (by positivity)
  have hfac:1+2*Real.pi*(N:ℝ)*|β|≤(1+2*Real.pi)*L^b:=by
    have hsc:=mul_le_mul_of_nonneg_left hβ (show 0≤2*Real.pi by positivity)
    linarith only [hsc,one_le_pow₀ h1 (n:=b)]
  apply (GoldbachMajorArc.shifted_sum_error N ((a:ℝ)/q) β (GoldbachMajorArc.unitMean q a)).trans
  calc _ ≤ (L^b*(c*N/L^K))*((1+2*Real.pi)*L^b):= mul_le_mul hs hfac (by positivity) (by positivity)
       _ = _:=by dsimp only [K];rw [pow_add,pow_add];change _=c*(1+2*Real.pi)*N/L^A;field_simp

end GoldbachPartial
