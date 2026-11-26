import VerifiedThinRootMass

namespace GoldbachPartial
open Filter

private theorem thin_exponential_budget : ∀ᶠ t : ℕ in atTop, (128:ℝ)^4*(t:ℝ)^34≤2^t := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) 34 (by norm_num : (1:ℝ)<2)).bound
    (show (0:ℝ)<1/128^4 by positivity)
  filter_upwards [h] with t ht
  simp only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ)≤(t:ℝ)^34 by positivity),
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) t)] at ht
  linarith only [ht]

private theorem thin_scales {t u : ℕ} (ht : 5≤t) (hul : 2^(t^8)≤u) (huu : u<2^((t+1)^8)) :
    Real.log u ≤ 256*(t:ℝ)^8 ∧
    (Real.log (3*Real.log u)≤776*(t:ℝ)) ∧
    ((t:ℝ)^6/2≤Real.log (((2^(t^6):ℕ):ℝ)+1)) ∧
    Real.log (2^(t^6):ℕ)≤(t:ℝ)^6 := by
  have ht0 : (1:ℝ)≤t := by exact_mod_cast (by omega : 1≤t)
  have hu2 : 2≤u := by
    apply le_trans _ hul
    calc 2=2^1 := by norm_num
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.one_le_pow _ _ (by omega))
  have hu0 : (1:ℝ)<u := by exact_mod_cast (by omega : 1<u)
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<u) (show (u:ℝ)≤(2:ℝ)^((t+1)^8) by exact_mod_cast huu.le)
  rw [Real.log_pow] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hhalf := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hhalf htwo
  have hhi : ((t:ℝ)+1)^8≤(2*(t:ℝ))^8 := pow_le_pow_left₀ (by positivity) (by linarith only [ht0]) _
  have hlo : Real.log u ≤ 256*(t:ℝ)^8 := by
    push_cast at hlog
    have hg := (mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤((t:ℝ)+1)^8 by positivity))
    linarith only [hlog,hhi,hg]
  refine ⟨hlo,?_,?_,?_⟩
  · have h3 := Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<3) (Real.log_pos hu0))
      (show 3*Real.log u≤768*(t:ℝ)^8 by linarith only [hlo])
    rw [Real.log_mul (show (768:ℝ)≠0 by norm_num) (show (t:ℝ)^8≠0 by positivity),Real.log_pow] at h3
    push_cast at h3
    linarith only [h3,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<768),
      Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one ht0),ht0]
  · have hg:=Real.log_le_log (show (0:ℝ)<(2:ℝ)^(t^6) by positivity)
      (show (2:ℝ)^(t^6)≤((2^(t^6):ℕ):ℝ)+1 by push_cast;linarith)
    rw [Real.log_pow] at hg
    push_cast at hg
    have hl := mul_le_mul_of_nonneg_left hhalf (show (0:ℝ)≤(t:ℝ)^6 by positivity)
    push_cast; linarith only [hg,hl]
  · push_cast
    rw [Real.log_pow]
    push_cast
    simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤(t:ℝ)^6 by positivity)

private theorem thin_support_budget {t u : ℕ} (ht : 5≤t) (hul : 2^(t^8)≤u) :
    (2*2^(t^6):ℕ)*2^t≤u ∧ (2^(t^6):ℕ)^(2*t)*2^(2*t)*2^t≤u := by
  have ht7 : t≤t^7 := by
    calc _ = t^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hmain : t^6*(2*t)+2*t+t≤t^8 := by
    calc _ = 2*t^7+3*t := by ring
         _ ≤ 5*t^7 := by omega
         _ ≤ t*t^7 := Nat.mul_le_mul_right _ ht
         _ = _ := by ring
  have hmain' : 1+t^6+t≤t^8 := by
    have h1 : t^6≤t^6*(2*t) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  constructor
  · apply le_trans _ hul
    calc _ = 2^(1+t^6+t) := by rw [pow_add,pow_add,pow_one]
         _ ≤ _ := Nat.pow_le_pow_right (by decide) hmain'
  · apply le_trans _ hul
    calc _ = 2^(t^6*(2*t)+2*t+t) := by rw [←pow_mul,←pow_add,←pow_add]
         _ ≤ _ := Nat.pow_le_pow_right (by decide) hmain

private theorem thin_mass_scaled {n u t : ℕ} (ht : 5≤t)
    (hpow : (128:ℝ)^4*(t:ℝ)^34≤2^t) (hul : 2^(t^8)≤u) (huu : u<2^((t+1)^8))
    (hn : n≤u^2) (hlog : 1≤Real.log n) (hne : Even n) :
    thinRootPrimeMass n u*(t:ℝ)^10 ≤ 1000000000000*(u:ℝ)^2 := by
  let z := 2^(t^6)
  let k := 2*t
  let x := (t:ℝ)
  have hx : 1≤x := by dsimp [x];exact_mod_cast (show 1≤t by omega)
  have hx0 : 0<x := zero_lt_one.trans_le hx
  obtain ⟨hlu,hLL,hzlo,hzhi⟩ := thin_scales ht hul huu
  have hzpos : 1≤z := Nat.one_le_two_pow
  have hroot := thinRootPrimeMass_log_upper n u z k hn hlog hne hzpos (even_two_mul t)
  have h10 : x^10≤(2:ℝ)^t := by
    have h1 := pow_le_pow_right₀ hx (show 10≤34 by decide)
    have h2 : x^34≤128^4*x^34 := by nlinarith only [pow_nonneg hx0.le 34]
    exact h1.trans (h2.trans hpow)
  have hu1 : 1≤(u:ℝ) := by exact_mod_cast (Nat.one_le_two_pow.trans hul)
  have hlogU0 : 0<Real.log u := by
    apply Real.log_pos
    exact_mod_cast (show 1<u by
      have hg : 2^1≤2^(t^8) := Nat.pow_le_pow_right (by decide) (Nat.one_le_pow _ _ (by omega))
      omega)
  have hlogUbig : 1≤3*Real.log u := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^(t^8))
      (show (2:ℝ)^(t^8)≤(u:ℝ) by exact_mod_cast hul)
    rw [Real.log_pow] at h
    push_cast at h
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    have h8 : 1≤x^8 := one_le_pow₀ hx
    change (x^8)*Real.log 2≤_ at h
    nlinarith only [h,hh,mul_nonneg (sub_nonneg.mpr h8) (Real.log_nonneg (by norm_num : (1:ℝ)≤2))]
  let a := 128*(1+Real.log (3*Real.log u))/Real.log ((z:ℝ)+1)
  have ha : 0≤a := by
    dsimp only [a]
    have hu := Real.log_nonneg hlogUbig
    have hzl : 0≤Real.log ((z:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) z;linarith)
    positivity
  have hden : 0<Real.log ((z:ℝ)+1) := by
    apply Real.log_pos
    have : (1:ℝ)≤z := by exact_mod_cast hzpos
    linarith
  have hA : a ≤ 200000*x/x^6 := by
    show _/Real.log ((z:ℝ)+1)≤_
    apply (div_le_div_iff₀ hden (pow_pos hx0 6)).mpr
    have he : 128*(1+Real.log (3*Real.log u))≤100000*x := by
      change Real.log (3*Real.log u)≤776*x at hLL
      linarith only [hx,hLL]
    have hd : x^6/2≤Real.log ((z:ℝ)+1) := hzlo
    have h1 := mul_le_mul_of_nonneg_right he (pow_nonneg hx0.le 6)
    have h2 := mul_le_mul_of_nonneg_left hd (show 0≤200000*x by positivity)
    linarith only [h1,h2]
  have hMain : a^2*x^10≤200000^2 := by
    calc _ ≤ (200000*x/x^6)^2*x^10 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hA 2) (by positivity)
         _ = _ := by field_simp
  let e := (64*(1+Real.log z))^4/(2:ℝ)^(k+1)
  have hRank : e*x^10≤1 := by
    have h1 : 64*(1+Real.log z)≤128*x^6 := by
      have h6 : 1≤x^6 := one_le_pow₀ hx
      change Real.log z≤x^6 at hzhi
      linarith only [h6,hzhi]
    have hbox := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg z;positivity) h1 4
    have hg : (64*(1+Real.log z))^4*x^10≤(2:ℝ)^t := by
      calc _ ≤ (128*x^6)^4*x^10 := mul_le_mul_of_nonneg_right hbox (by positivity)
           _ = 128^4*x^34 := by ring
           _ ≤ _ := hpow
    dsimp only [e]
    rw [div_mul_eq_mul_div,div_le_one (by positivity)]
    exact hg.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [k];omega))
  obtain ⟨hzS,hkS⟩ := thin_support_budget ht hul
  have hsmall1 : (2*(z:ℝ))*x^10≤u := by
    apply (mul_le_mul_of_nonneg_left h10 (show 0≤2*(z:ℝ) by positivity)).trans
    exact_mod_cast hzS
  have hsmall2 : ((z:ℝ)^k*2^k)*x^10≤u := by
    apply (mul_le_mul_of_nonneg_left h10 (show 0≤(z:ℝ)^k*2^k by positivity)).trans
    exact_mod_cast hkS
  have htot : (2*(z:ℝ)+(2*(u:ℝ))*(a^2+e)+(z:ℝ)^k*2^k)*x^10 ≤ 80000000004*u := by
    have ha1 := mul_le_mul_of_nonneg_left hMain (show 0≤2*(u:ℝ) by positivity)
    have ha2 := mul_le_mul_of_nonneg_left hRank (show 0≤2*(u:ℝ) by positivity)
    linarith only [hsmall1,hsmall2,ha1,ha2]
  have hfour := Real.log_le_sub_one_of_pos (show 0<(4:ℝ) by norm_num)
  change thinRootPrimeMass n u≤(4*Real.log 4)*(u:ℝ)*_ at hroot
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (pow_nonneg hx0.le 10)
    _ = ((4*Real.log 4)*(u:ℝ))*((2*(z:ℝ)+2*u*(a^2+e)+(z:ℝ)^k*2^k)*x^10) := by rw [mul_assoc]
    _ ≤ ((4*Real.log 4)*(u:ℝ))*(80000000004*u) := mul_le_mul_of_nonneg_left htot (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hfour (sq_nonneg (u:ℝ)),sq_nonneg (u:ℝ)]

/-- The log-weight of primes p for which n-p is a semiprime with smaller
factor strictly above sqrt(n)/2 is o(n/log n) along every even n. -/
theorem thinSemiprimePrimes_weight_little_o (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (∑p∈thinSemiprimePrimes n,weight p)≤ε*((n:ℝ)/Real.log n) := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.1 thin_exponential_budget
  obtain ⟨T₁,hT₁⟩ := exists_nat_gt (2048000000000000/ε)
  let T := max 5 (max T₀ T₁)
  let c (t : ℕ) := 2^(t^8)
  have hc : Tendsto c atTop atTop := by
    apply tendsto_atTop.2
    intro v
    filter_upwards [eventually_ge_atTop (max 1 v)] with k hk
    have hk' : 1≤k := (le_max_left ..).trans hk
    have h8 : k≤k^8 := by
      calc _ = k^1 := by simp
           _ ≤ _ := Nat.pow_le_pow_right hk' (by decide)
    exact ((le_max_right ..).trans hk).trans ((show k<2^k from Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right (by decide) h8))
  filter_upwards [eventually_ge_atTop (max 4 ((c T)^2))] with n hn hne
  have hn4 : 4≤n := (le_max_left ..).trans hn
  have hn0 : 0<n := by omega
  let u := n.sqrt+1
  have hu : c T≤u := (Nat.le_sqrt'.mpr ((le_max_right ..).trans hn)).trans (Nat.le_succ _)
  obtain ⟨t,ht,hul,huu⟩ := hc.exists_le_lt_succ hu
  have ht5 : 5≤t := (le_max_left ..).trans ht
  have ht0 : T₀≤t := ((le_max_left ..).trans (le_max_right ..)).trans ht
  have ht1 : T₁≤t := ((le_max_right ..).trans (le_max_right ..)).trans ht
  have hpos : (0:ℝ)<t := by exact_mod_cast (by omega : 0<t)
  have hlog : (1:ℝ)≤Real.log n := by
    have h4 : (4:ℝ)≤n := by exact_mod_cast hn4
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    have hz := Real.log_le_log (by norm_num : (0:ℝ)<4) h4
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hz
    norm_num at hz
    linarith only [hh,hz]
  have hnu : n≤u^2 := (Nat.sqrt_lt'.mp (Nat.lt_succ_self n.sqrt)).le
  have hus : 1≤n.sqrt := Nat.le_sqrt'.mpr (by omega)
  have hu4 : u^2≤4*n := by
    dsimp only [u]
    have h1 := Nat.sqrt_le' n
    have h2 := Nat.pow_le_pow_left (show n.sqrt+1≤2*n.sqrt by omega) 2
    nlinarith only [h1,h2]
  have hscale := thin_mass_scaled ht5 (hT₀ t ht0) hul huu hnu hlog hne
  let M := ∑p∈thinSemiprimePrimes n,weight p
  have hM : M*(t:ℝ)^10 ≤ 4000000000000*(n:ℝ) := by
    have h := (mul_le_mul_of_nonneg_right (thinSemiprimePrimes_mass_le n) (show (0:ℝ)≤(t:ℝ)^10 by positivity)).trans hscale
    have h4 : (u:ℝ)^2≤4*(n:ℝ) := by exact_mod_cast hu4
    linarith only [h,h4]
  have hl : Real.log n≤512*(t:ℝ)^8 := by
    have hh := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast hn0)
      (show (n:ℝ)≤(u:ℝ)^2 by exact_mod_cast hnu)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith only [hh,(thin_scales ht5 hul huu).1]
  have hfinal : M*(t:ℝ)^10*Real.log n ≤ (2048000000000000*(n:ℝ))*(t:ℝ)^8 := by
    have h := mul_le_mul hM hl (zero_le_one.trans hlog) (by positivity)
    linarith only [h]
  have hcut : 2048000000000000 ≤ ε*(t:ℝ)^2 := by
    have htr : (T₁:ℝ)≤t := by exact_mod_cast ht1
    have hh := (div_lt_iff₀ hε).mp (hT₁.trans_le htr)
    have htR : (1:ℝ)≤t := by exact_mod_cast (by omega : 1≤t)
    nlinarith only [hh,mul_nonneg hε.le (mul_nonneg hpos.le (sub_nonneg.mpr htR))]
  change M≤_
  rw [←mul_div_assoc,le_div_iff₀ (zero_lt_one.trans_le hlog)]
  apply (mul_le_mul_iff_left₀ (pow_pos hpos 10)).mp
  have hend := mul_le_mul_of_nonneg_right hcut (show 0≤(n:ℝ)*(t:ℝ)^8 by positivity)
  linarith only [hfinal,hend]

open Asymptotics in
theorem thinSemiprimePrimes_isLittleO :
    (fun n : ℕ => ∑p∈thinSemiprimePrimes n,weight p)
      =o[(atTop : Filter ℕ) ⊓ Filter.principal {n | Even n}] (fun n => (n:ℝ)/Real.log n) := by
  apply isLittleO_iff.mpr
  intro ε hε
  apply eventually_inf_principal.mpr
  filter_upwards [thinSemiprimePrimes_weight_little_o ε hε] with n hn he
  have hw (p : ℕ) : 0≤weight p := by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun p _ => hw p)),
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg (α:=ℝ) n) (Real.log_natCast_nonneg n))] using hn he

end GoldbachPartial