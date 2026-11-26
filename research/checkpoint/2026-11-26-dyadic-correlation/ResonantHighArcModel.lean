import ResonantGridAbel
import ResonantPrincipalPrefix
import NaturalDirichletTubeGeometry

namespace GoldbachPartial
open Finset Filter ExtendedArcCoefficient
open scoped Topology

theorem resonantMobius_geometric_grh (hψ:grhAllUniform) :
    ∃K:ℝ,0<K ∧ ∀n d q:ℕ,d<q → q≤n → ∀β:ℝ,
    ‖resonantMobiusWave n d n q β-
       (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*dirichletGeometricKernel n β‖ ≤
      ((K*(Real.log (2*(q:ℝ)*(n/q:ℕ)))^2+3+Real.log q)*Real.sqrt (n/q:ℕ)*
        smoothRootEuler q+(q:ℝ)/q.totient)*(1+2*Real.pi*n*|β|) := by
  obtain ⟨K,hK,h⟩ := resonantReducedCoefficient_prefix_bound hψ
  refine ⟨K,hK,?_⟩
  intro n d q hd hqn β
  have hq : 0<q := by omega
  apply resonantMobiusWave_geometric_of_prefix hd
  intro j hj
  have hp := h q (n/q) hq (Nat.div_pos hqn hq) j hj
  convert hp using 3
  push_cast
  ring

theorem resonantMobius_geometric_high_pointwise (hψ:grhAllUniform) :
    ∀ᶠ n:ℕ in atTop,∀q:ℕ,terminalPrimeArcCutoff n<q → q≤naturalTubeScale n → ∀β:ℝ,
      |β|≤naturalTubeRadius (3*naturalTubeScale n) q →
    ‖resonantMobiusWave n (terminalPrimeArcCutoff n) n q β-
       (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*dirichletGeometricKernel n β‖ ≤
       Real.sqrt n/(terminalPrimeArcLog n)^8 := by
  obtain ⟨K,hK,hrow⟩ := resonantMobius_geometric_grh hψ
  obtain ⟨C,hC,hZ⟩ := smoothRootEuler_le_smallPower (ε:=1/64) (by norm_num)
  let t := fun n:ℕ=>(n:ℝ)^(1/64:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/64)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n:ℕ=>(Real.log n)^8/t n) atTop (𝓝 0) := by
    simpa only [t,Function.comp_def,Real.rpow_ofNat] using
      ((isLittleO_log_rpow_rpow_atTop (8:ℝ) (by norm_num : (0:ℝ)<1/64)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_ge_atTop 8, ht.eventually_ge_atTop K,
    ht.eventually_ge_atTop C,ht.eventually_ge_atTop (1+2*Real.pi),hlog.eventually_ge_atTop 1,
    hl.eventually_lt_const (by norm_num : (0:ℝ)<1/256)] with n hn ht8 htK htC htπ hln hsmall
  intro q hlow hu β hβ
  let T := t n
  let L := terminalPrimeArcLog n
  let Q := naturalTubeScale n
  let X := n/q
  have hT8 : 8≤T := ht8
  have hT1 : 1≤T := by linarith
  have hT : 0<T := by linarith
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  change 1≤Real.log (n:ℝ) at hln
  have hL8 : L^8≤T := by
    have hsm := (div_lt_iff₀ hT).mp hsmall
    have hle : L ≤ 2*Real.log n := by dsimp only [L,terminalPrimeArcLog]; linarith
    have hp := pow_le_pow_left₀ hL.le hle 8
    rw [mul_pow] at hp
    linarith only [hp,hsm]
  have hL5 := (pow_le_pow_right₀ hL1 (by decide : 5≤8)).trans hL8
  have hL2 := (pow_le_pow_right₀ hL1 (by decide : 2≤8)).trans hL8
  have hLe : L≤T := (le_self_pow₀ hL1 (by decide:8≠0)).trans hL8
  have h32 : T^32=Real.sqrt n := by
    dsimp only [T,t]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg n),Real.sqrt_eq_rpow]
    norm_num
  have hq : 0<q := by omega
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hQ : 0<Q := hq.trans_le hu
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hNr : (2:ℝ)≤n := by exact_mod_cast hn
  have hroot := Real.sqrt_nonneg (n:ℝ)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hQroot : (Q:ℝ)≤Real.sqrt n := Nat.floor_le hroot
  have hrootQ : Real.sqrt n≤3*(Q:ℝ) := by
    have hh : Real.sqrt n<(Q:ℝ)+1 := Nat.lt_floor_add_one _
    have h1 : (1:ℝ)≤Q := by exact_mod_cast hQ
    linarith
  have hqn : q≤n := by
    have hs := (show (q:ℝ)≤Q by exact_mod_cast hu).trans hQroot
    exact_mod_cast hs.trans (by nlinarith [mul_nonneg (show 0≤(n:ℝ)-1 by linarith) (Nat.cast_nonneg (α:=ℝ) n)] : Real.sqrt n≤(n:ℝ))
  have hqsmall : Real.sqrt n≤(q:ℝ)*L^5 := by
    exact (div_le_iff₀ (pow_pos hL 5)).mp (Nat.lt_of_floor_lt hlow).le
  have hnq : (n:ℝ)≤(q:ℝ)*Real.sqrt n*L^5 := by
    calc (n:ℝ) = (Real.sqrt n)^2 := hrootsq.symm
         _ ≤ Real.sqrt n*((q:ℝ)*L^5) := by rw [sq]; gcongr
         _ = _ := by ring
  have hX : (X:ℝ)≤T^33 := by
    have hm : (q:ℝ)*X ≤ n := by exact_mod_cast Nat.mul_div_le n q
    have h' : (X:ℝ)≤Real.sqrt n*L^5 := by
      apply (mul_le_mul_iff_right₀ hqr).mp
      exact hm.trans (hnq.trans_eq (by ring))
    calc _ ≤ Real.sqrt n*T := h'.trans (mul_le_mul_of_nonneg_left hL5 hroot)
         _ = _ := by rw [←h32]; ring
  have hrootX : Real.sqrt (X:ℝ)≤T^17 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hX.trans ?_⟩
    rw [←pow_mul]
    exact pow_le_pow_right₀ hT1 (by decide)
  have hZq : smoothRootEuler q≤T^2 := by
    apply (hZ q hq).trans
    have hqt : (q:ℝ)^(1/64:ℝ)≤T := Real.rpow_le_rpow hqr.le (by exact_mod_cast hqn) (by norm_num)
    calc _ ≤ T*T := mul_le_mul htC hqt (by positivity) hT.le
         _ = _ := (sq T).symm
  have hlogq : Real.log q ≤L := calc
    _ ≤ Real.log n := Real.log_le_log hqr (by exact_mod_cast hqn)
    _ ≤ L := by dsimp only [L,terminalPrimeArcLog]; linarith
  have hXpos : 0<X := Nat.div_pos hqn hq
  have hlogarg : Real.log (2*(q:ℝ)*X)≤2*L := by
    have hmul : (q:ℝ)*X ≤ n := by exact_mod_cast Nat.mul_div_le n q
    calc
      _ ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by positivity) (by linarith only [hmul])
      _ = Real.log 2+Real.log n := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by dsimp only [L,terminalPrimeArcLog]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogarg0 : 0≤Real.log (2*(q:ℝ)*X) := by
    apply Real.log_nonneg
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
    have hx1 : (1:ℝ)≤X := by exact_mod_cast hXpos
    nlinarith only [mul_le_mul hq1 hx1 (by norm_num) hqr.le]
  have hfront : K*(Real.log (2*(q:ℝ)*X))^2+3+Real.log q≤T^3 := by
    have hsq := pow_le_pow_left₀ hlogarg0 hlogarg 2
    rw [mul_pow] at hsq
    have hs : (Real.log (2*(q:ℝ)*X))^2 ≤4*T := by linarith only [hsq,hL2]
    have hm := mul_le_mul htK hs (sq_nonneg _) hT.le
    have hLq := hlogq.trans hLe
    have ht3 := mul_le_mul_of_nonneg_right hT8 (sq_nonneg T)
    nlinarith only [hm,hLq,ht3,hT8,sq_nonneg (T-1)]
  have hbase : (K*(Real.log (2*(q:ℝ)*X))^2+3+Real.log q)*Real.sqrt X*smoothRootEuler q+
        (q:ℝ)/q.totient≤T^23 := by
    have hrat := (resonant_totient_ratio_le_rootEuler q hq).trans hZq
    have hz0 : 0≤smoothRootEuler q := (div_nonneg hqr.le (Nat.cast_nonneg _)).trans (resonant_totient_ratio_le_rootEuler q hq)
    calc _ ≤ T^3*T^17*T^2+T^2 := by gcongr
         _ ≤ T^23 := by
           have h22 : T^2≤T^22 := pow_le_pow_right₀ hT1 (by decide)
           have hlarge := mul_le_mul_of_nonneg_right hT8 (pow_nonneg hT.le 22)
           nlinarith only [h22,hlarge]
  have hw : (n:ℝ)*|β|≤T := by
    have hβ' : |β|≤1/((q:ℝ)*(3*(Q:ℝ))) := by simpa only [naturalTubeRadius,Nat.cast_mul,Nat.cast_ofNat] using hβ
    have hw := (le_div_iff₀ (by positivity : 0<(q:ℝ)*(3*(Q:ℝ)))).mp hβ'
    have hbig : (n:ℝ) ≤ q*(3*(Q:ℝ))*L^5 := hnq.trans (by gcongr)
    calc _ ≤ ((q:ℝ)*(3*(Q:ℝ))*L^5)*|β| := mul_le_mul_of_nonneg_right hbig (abs_nonneg _)
         _ = (|β| *((q:ℝ)*(3*(Q:ℝ))))*L^5 := by ring
         _ ≤ 1*L^5 := mul_le_mul_of_nonneg_right hw (by positivity)
         _ ≤ T := by simpa only [one_mul] using hL5
  have htw : 1+2*Real.pi*n*|β|≤T^2 := by
    have hw' := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le)
    have hπ := mul_le_mul_of_nonneg_right htπ hT.le
    nlinarith only [hw',hπ,hT1]
  apply (hrow n _ q hlow hqn β).trans
  change _≤Real.sqrt n/L^8
  calc
    _ ≤ T^23*T^2 := mul_le_mul hbase htw (by positivity) (by positivity)
    _ ≤ Real.sqrt n/L^8 := by
      apply (le_div_iff₀ (pow_pos hL 8)).mpr
      rw [←h32]
      calc _ ≤ (T^23*T^2)*T := by gcongr
           _ = T^26 := by ring
           _ ≤ _ := pow_le_pow_right₀ hT1 (by decide)

end GoldbachPartial