import VerifiedQuarterBrunAfterThin

namespace GoldbachPartial
open Finset Filter
noncomputable section

def thinWidePrimeShell (H u : ℕ) : Finset ℕ :=
  (Ioc 0 u).filter (fun L=>L.Prime ∧ u≤H*L)

def thinWidePrimeMass (H n u : ℕ) : ℝ := ∑L∈thinWidePrimeShell H u,
  ∑b∈thinPrimePairSet n L (H*u),weight (n-L*b)

theorem thinWidePrimeMass_log_upper (H n u z K : ℕ) (hHu : H^2≤u) (hn : n≤u^2) (hlog : 1≤Real.log n)
    (hne : Even n) (hz : 1≤z) (hK : Even K) :
    thinWidePrimeMass H n u ≤ (4*Real.log 4)*(u:ℝ)*
      (2*(z:ℝ)+((H:ℝ)*(u:ℝ))*((128*(1+Real.log (3*Real.log u))/Real.log ((z:ℝ)+1))^2+
        (64*(1+Real.log z))^4/(2:ℝ)^(K+1))+(z:ℝ)^K*(2:ℝ)^K) := by
  have hn0 : 0<n := by
    by_contra! h
    have hh : n=0 := by omega
    norm_num [hh] at hlog
  have hlz : 0<Real.log ((z:ℝ)+1) := by
    apply Real.log_pos
    have : (1:ℝ)≤z := by exact_mod_cast hz
    linarith
  let A := 2*(z:ℝ)+((H:ℝ)*(u:ℝ))*((128*(1+Real.log (3*Real.log u))/Real.log ((z:ℝ)+1))^2+
        (64*(1+Real.log z))^4/(2:ℝ)^(K+1))+(z:ℝ)^K*(2:ℝ)^K
  have hA : 0≤A := by dsimp [A]; positivity
  let S := thinWidePrimeShell H u
  have hp (L : ℕ) (h : L∈S) := (mem_filter.mp h).2
  have hu (L : ℕ) (h : L∈S) : L≤u := (mem_Ioc.mp (mem_filter.mp h).1).2
  have hpt (L : ℕ) (h : L∈S) : ((thinPrimePairSet n L (H*u)).card:ℝ)≤A := by
    obtain ⟨hprime,_⟩ := hp L h
    have hnL : n≤n*L := Nat.le_mul_of_pos_right _ hprime.pos
    have hm : 1≤Real.log (n*L:ℕ) := hlog.trans (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnL))
    have he : 2∣n*L := dvd_mul_of_dvd_left (even_iff_two_dvd.mp hne) L
    have hcard := thinPrimePairSet_log_upper n L (H*u) z K hprime.pos hz hK he hm
    have hnu : n*L≤u^3 := by
      calc _ ≤ u^2*u := Nat.mul_le_mul hn (hu L h)
           _ = _ := by ring
    have h3 := Real.log_le_log (show (0:ℝ)<(n*L:ℕ) by exact_mod_cast Nat.mul_pos hn0 hprime.pos)
      (show ((n*L:ℕ):ℝ)≤((u^3:ℕ):ℝ) by exact_mod_cast hnu)
    rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at h3
    have hLL := Real.log_le_log (zero_lt_one.trans_le hm) h3
    push_cast only [Nat.cast_mul,Nat.cast_ofNat] at hcard
    apply hcard.trans
    dsimp only [A]
    have hpos : 0≤Real.log (Real.log (n*L:ℕ)) := Real.log_nonneg hm
    push_cast only [Nat.cast_mul] at hpos hLL
    gcongr
  have hweight (L b : ℕ) (hL : L∈S) (hb : b∈thinPrimePairSet n L (H*u)) :
      weight (n-L*b)≤4*Real.log L := by
    obtain ⟨hpr,hhalf⟩ := hp L hL
    have hpb := (mem_filter.mp hb).2.2
    rw [weight,ite_eq_left hpb]
    have hQ : u≤L^2 := by
      rcases le_total H L with hh|hh
      · exact hhalf.trans (by simpa only [pow_two] using Nat.mul_le_mul_right L hh)
      · have hHl : H*L≤H^2 := by simpa only [pow_two] using Nat.mul_le_mul_left H hh
        have heq : H*L=H^2 := le_antisymm hHl (hHu.trans hhalf)
        by_cases hH : H=0
        · simp [hH] at hhalf; omega
        · rw [pow_two] at heq
          exact hhalf.trans (by rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH) heq,pow_two])
    have hnL : n≤L^4 := by
      calc _ ≤ u^2 := hn
           _ ≤ (L^2)^2 := Nat.pow_le_pow_left hQ _
           _ = _ := by ring
    have hR := Real.log_le_log (show (0:ℝ)<(n-L*b:ℕ) by exact_mod_cast hpb.pos)
      (show ((n-L*b:ℕ):ℝ)≤((L^4:ℕ):ℝ) by exact_mod_cast (Nat.sub_le n (L*b)).trans hnL)
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using hR
  have hP : S⊆(Ioc 0 u).filter Nat.Prime := fun L h => mem_filter.mpr ⟨(mem_filter.mp h).1,(hp L h).1⟩
  have hsum : (∑L∈S,Real.log L)≤Real.log 4*u := by
    apply (sum_le_sum_of_subset_of_nonneg hP (fun L _ _=>Real.log_natCast_nonneg _)).trans
    simpa only [Chebyshev.theta,Nat.floor_natCast] using Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α:=ℝ) u)
  calc
    _ ≤ ∑L∈S,A*(4*Real.log L) := by
      apply sum_le_sum
      intro L hL
      have h := sum_le_sum (fun b hb=>hweight L b hL hb)
      simpa only [sum_const,nsmul_eq_mul] using h.trans ((sum_const _).trans_le (by
        rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hpt L hL) (by positivity)))
    _ = (A*4)*(∑L∈S,Real.log L) := by simp only [mul_sum,mul_assoc]
    _ ≤ _ := by
      change (A*4)*(∑L∈S,Real.log L)≤(4*Real.log 4)*(u:ℝ)*A
      simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (by norm_num : (0:ℝ)≤4))
open scoped Classical

def thinWideSemiprimePrimes (H n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun p=>p.Prime ∧ ∃L b : ℕ, L.Prime ∧ b.Prime ∧
    L≤b ∧ L^2≤n ∧ n<(H*L)^2 ∧ n=p+L*b)

theorem thinWideSemiprimePrimes_mass_le (H n : ℕ) :
    (∑p∈thinWideSemiprimePrimes H n,weight p)≤thinWidePrimeMass H n (n.sqrt+1) := by
  classical
  let u := n.sqrt+1
  let T := (thinWidePrimeShell H u).sigma (fun L=>thinPrimePairSet n L (H*u))
  let f := fun v : Sigma (fun _ : ℕ => ℕ) => n-v.1*v.2
  have hsub : thinWideSemiprimePrimes H n⊆T.image f := by
    intro p hp
    obtain ⟨_,hp',L,b,hL,hb,_hLb,hLn,hL4,he⟩ := mem_filter.mp hp
    have hU : n<u*u := Nat.lt_succ_sqrt n
    have h2 : u≤H*L := Nat.sqrt_lt'.mpr hL4
    have hLu : L≤u := by
      by_contra! h
      have hh : u*u≤L*L := Nat.mul_le_mul h.le h.le
      nlinarith only [hU,hLn,hh]
    have hbu : b≤H*u := Nat.le_of_mul_le_mul_left (by
      have h : u*u ≤ (H*L)*u := Nat.mul_le_mul_right u h2
      nlinarith only [h,he,hU,Nat.zero_le p]) hL.pos
    have hf : n-L*b=p := by omega
    refine mem_image.mpr ⟨⟨L,b⟩,mem_sigma.mpr ⟨?_,?_⟩,hf⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hL.pos,hLu⟩,hL,h2⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hb.pos,hbu⟩,hb,hf ▸ hp'⟩
  have hnon (p : ℕ) : 0≤weight p := by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hnon p)).trans
  have hImage := sum_image_le_of_nonneg (s:=T) (g:=f) (fun p _=>hnon p)
  exact hImage.trans_eq (sum_sigma ..)


open private thin_exponential_budget thin_scales thin_support_budget from VerifiedThinSemiprimeAsymptotic
private theorem thinWide_mass_scaled (H : ℕ) {n u t : ℕ} (hHu : H^2≤u) (ht : 5≤t)
    (hpow : (128:ℝ)^4*(t:ℝ)^34≤2^t) (hul : 2^(t^8)≤u) (huu : u<2^((t+1)^8))
    (hn : n≤u^2) (hlog : 1≤Real.log n) (hne : Even n) :
    thinWidePrimeMass H n u*(t:ℝ)^10 ≤ ((H:ℝ)+1)*1000000000000*(u:ℝ)^2 := by
  let z := 2^(t^6)
  let k := 2*t
  let x := (t:ℝ)
  have hx : 1≤x := by dsimp [x];exact_mod_cast (show 1≤t by omega)
  have hx0 : 0<x := zero_lt_one.trans_le hx
  obtain ⟨hlu,hLL,hzlo,hzhi⟩ := thin_scales ht hul huu
  have hzpos : 1≤z := Nat.one_le_two_pow
  have hroot := thinWidePrimeMass_log_upper H n u z k hHu hn hlog hne hzpos (even_two_mul t)
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
  have htot : (2*(z:ℝ)+((H:ℝ)*(u:ℝ))*(a^2+e)+(z:ℝ)^k*2^k)*x^10 ≤ ((H:ℝ)+1)*(80000000004*u) := by
    have ha1 := mul_le_mul_of_nonneg_left hMain (show 0≤(H:ℝ)*(u:ℝ) by positivity)
    have ha2 := mul_le_mul_of_nonneg_left hRank (show 0≤(H:ℝ)*(u:ℝ) by positivity)
    nlinarith only [hsmall1,hsmall2,ha1,ha2, mul_nonneg (Nat.cast_nonneg (α:=ℝ) H) (Nat.cast_nonneg (α:=ℝ) u),Nat.cast_nonneg (α:=ℝ) u]
  have hfour := Real.log_le_sub_one_of_pos (show 0<(4:ℝ) by norm_num)
  change thinWidePrimeMass H n u≤(4*Real.log 4)*(u:ℝ)*_ at hroot
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (pow_nonneg hx0.le 10)
    _ = ((4*Real.log 4)*(u:ℝ))*((2*(z:ℝ)+H*u*(a^2+e)+(z:ℝ)^k*2^k)*x^10) := by rw [mul_assoc]
    _ ≤ ((4*Real.log 4)*(u:ℝ))*(((H:ℝ)+1)*(80000000004*u)) := mul_le_mul_of_nonneg_left htot (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hfour (show 0≤((H:ℝ)+1)*(u:ℝ)^2 by positivity),show 0≤((H:ℝ)+1)*(u:ℝ)^2 by positivity]


theorem thinWideSemiprimePrimes_weight_little_o (H : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (∑p∈thinWideSemiprimePrimes H n,weight p)≤ε*((n:ℝ)/Real.log n) := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.1 thin_exponential_budget
  obtain ⟨T₁,hT₁⟩ := exists_nat_gt ((((H:ℝ)+1)*2048000000000000)/ε)
  let T := max 5 (max T₀ (max T₁ (H^2)))
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
  have ht1 : T₁≤t := (le_max_left ..).trans (((le_max_right ..).trans (le_max_right ..)).trans ht)
  have hHt : H^2≤t := (le_max_right ..).trans (((le_max_right ..).trans (le_max_right ..)).trans ht)
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
  have hHu : H^2≤u := by
    have h8 : t≤t^8 := by calc t=t^1 := by simp
                              _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
    exact hHt.trans (((show t<2^t from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) h8)).trans hul)
  have hscale := thinWide_mass_scaled H hHu ht5 (hT₀ t ht0) hul huu hnu hlog hne
  let M := ∑p∈thinWideSemiprimePrimes H n,weight p
  have hM : M*(t:ℝ)^10 ≤ ((H:ℝ)+1)*4000000000000*(n:ℝ) := by
    have h := (mul_le_mul_of_nonneg_right (thinWideSemiprimePrimes_mass_le H n) (show (0:ℝ)≤(t:ℝ)^10 by positivity)).trans hscale
    have h4 : (u:ℝ)^2≤4*(n:ℝ) := by exact_mod_cast hu4
    nlinarith only [h,mul_le_mul_of_nonneg_left h4 (show 0≤((H:ℝ)+1) by positivity)]
  have hl : Real.log n≤512*(t:ℝ)^8 := by
    have hh := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast hn0)
      (show (n:ℝ)≤(u:ℝ)^2 by exact_mod_cast hnu)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith only [hh,(thin_scales ht5 hul huu).1]
  have hfinal : M*(t:ℝ)^10*Real.log n ≤ ((((H:ℝ)+1)*2048000000000000)*(n:ℝ))*(t:ℝ)^8 := by
    have h := mul_le_mul hM hl (zero_le_one.trans hlog) (by positivity)
    linarith only [h]
  have hcut : (((H:ℝ)+1)*2048000000000000) ≤ ε*(t:ℝ)^2 := by
    have htr : (T₁:ℝ)≤t := by exact_mod_cast ht1
    have hh := (div_lt_iff₀ hε).mp (hT₁.trans_le htr)
    have htR : (1:ℝ)≤t := by exact_mod_cast (by omega : 1≤t)
    nlinarith only [hh,mul_nonneg hε.le (mul_nonneg hpos.le (sub_nonneg.mpr htR))]
  change M≤_
  rw [←mul_div_assoc,le_div_iff₀ (zero_lt_one.trans_le hlog)]
  apply (mul_le_mul_iff_left₀ (pow_pos hpos 10)).mp
  have hend := mul_le_mul_of_nonneg_right hcut (show 0≤(n:ℝ)*(t:ℝ)^8 by positivity)
  linarith only [hfinal,hend]


/-- Seed primes with a semiprime complement whose smaller factor exceeds
a fixed real multiple of the square root of the target. -/
def thinFixedRatioPrimes (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun p=>p.Prime ∧ ∃L b : ℕ, L.Prime ∧ b.Prime ∧
    L≤b ∧ L^2≤n ∧ c*Real.sqrt n < L ∧ n=p+L*b)

theorem thinFixedRatioPrimes_weight_little_o (c : ℝ) (hc : 0<c) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (∑p∈thinFixedRatioPrimes c n,weight p)≤ε*((n:ℝ)/Real.log n) := by
  let H := ⌈1/c⌉₊
  have hH : 1/c≤(H:ℝ) := Nat.le_ceil _
  have hH0 : (0:ℝ)<H := (one_div_pos.mpr hc).trans_le hH
  have hprod : 1≤(H:ℝ)*c := (div_le_iff₀ hc).mp hH
  filter_upwards [thinWideSemiprimePrimes_weight_little_o H ε hε] with n hn he
  apply le_trans _ (hn he)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hI,hp',L,b,hL,hb,hLb,hLn,hcL,hadd⟩ := mem_filter.mp hp
    have h1 := mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg (n:ℝ))
    have h2 := mul_lt_mul_of_pos_left hcL hH0
    have hlt : Real.sqrt n < (H:ℝ)*L := by linarith only [h1,h2]
    have hsq := sq_lt_sq' (show -((H:ℝ)*L)<Real.sqrt n by
      have hl : (0:ℝ)<L := by exact_mod_cast hL.pos
      linarith only [mul_pos hH0 hl,Real.sqrt_nonneg (n:ℝ)]) hlt
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    exact mem_filter.mpr ⟨hI,hp',L,b,hL,hb,hLb,hLn,by exact_mod_cast hsq,hadd⟩
  · intro p _ _
    unfold weight
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl

def quarterBrunAfterFixedRatio (c : ℝ) (n : ℕ) : Finset ℕ :=
  fixedTargetBoundedFactorPrimes n (quarterBrunSieveLevel n) 808 \ thinFixedRatioPrimes c n

/-- A fixed even target still has this many squarefree rough complements of
at most 808 prime factors after removal of its near-square-root semiprimes. -/
theorem quarterBrun_after_fixed_ratio (c : ℝ) (hc : 0<c) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (n:ℝ)/(32768*Real.log n) ≤ ∑p∈quarterBrunAfterFixedRatio c n, Real.log p ∧
      (n:ℝ)/(32768*(Real.log n)^2) ≤ ((quarterBrunAfterFixedRatio c n).card:ℝ) := by
  filter_upwards [quarterBrun_squarefree_almost_primes,
    thinFixedRatioPrimes_weight_little_o c hc (1/32768) (by norm_num),eventually_ge_atTop (2:ℕ)] with n hB hT hn
  intro he
  let S := fixedTargetBoundedFactorPrimes n (quarterBrunSieveLevel n) 808
  let T := thinFixedRatioPrimes c n
  let U := quarterBrunAfterFixedRatio c n
  let L := Real.log n
  have hL : 0<L := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hp (p : ℕ) (h : p∈S) := (boundedFactorPrimes_iff n _ 808 p).mp h
  have hsplit : (∑p∈U,Real.log p)+(∑p∈S∩T,Real.log p)=∑p∈S,Real.log p := by
    have h := sum_filter_add_sum_filter_not S (fun p => p∈T) (fun p => Real.log p)
    have hi : S.filter (fun p => p∈T)=S∩T := by ext p;simp
    have hd : S.filter (fun p => p∉T)=U := by ext p;simp [U,quarterBrunAfterFixedRatio,S,T]
    rw [hi,hd] at h
    rw [add_comm]; exact h
  have hRemoved : (∑p∈S∩T,Real.log p)≤∑p∈T,weight p := by
    calc
      _ = ∑p∈S∩T,weight p := sum_congr rfl fun p h =>
        (ite_eq_left (by exact (hp p (mem_inter.mp h).1).2.2.1) : weight p=Real.log p).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (inter_subset_right ..)
        (fun p _ _ => by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl)
  have hmass := (hB he).1
  have hLos := hT he
  change (n:ℝ)/(16384*L) ≤ ∑p∈S,Real.log p at hmass
  change (∑p∈T,weight p)≤(1/32768)*((n:ℝ)/L) at hLos
  have H : (n:ℝ)/(32768*L)≤∑p∈U,Real.log p := by
    have h1 : (n:ℝ)/(16384*L)=2*((n:ℝ)/(32768*L)) := by field_simp;ring
    have h2 : (1/32768)*((n:ℝ)/L)=((n:ℝ)/(32768*L)) := by ring
    linarith only [hsplit,hRemoved,hmass,hLos,h1,h2]
  refine ⟨H,?_⟩
  have hcnt : (∑p∈U,Real.log p)≤(U.card:ℝ)*L := by
    calc
      _ ≤ ∑_p∈U,L := by
        apply sum_le_sum
        intro p h
        obtain ⟨_,hpn,hpr,_⟩ := hp p (mem_sdiff.mp h).1
        exact Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast (by omega : p≤n))
      _ = _ := by simp
  change (n:ℝ)/(32768*L^2)≤(U.card:ℝ)
  apply (div_le_iff₀ (by positivity)).mpr
  have h := (div_le_iff₀ (by positivity)).mp (H.trans hcnt)
  linarith only [h]

end
end GoldbachPartial