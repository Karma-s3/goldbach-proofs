import VerifiedQuarterLevelAlmostPrimes

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

def balancedBrunIndex (n:ℕ):ℕ:=Nat.log 2 ((Nat.log 2 n-2)/2452)
def balancedBrunSmall (n:ℕ):ℕ:=brunBlockBoundary (balancedBrunIndex n)
def balancedBrunLarge (n:ℕ):ℕ:=(balancedBrunSmall n)^512

theorem balancedBrunIndex_tendsto : Tendsto balancedBrunIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^(2452*2^b+2):ℕ)] with n hn
  have hs:2452*2^b+2≤Nat.log 2 n:=by
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) hn
  have ht:2^b≤(Nat.log 2 n-2)/2452 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  simpa only [balancedBrunIndex,Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) ht

theorem balancedBrunSmall_tendsto : Tendsto balancedBrunSmall atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [balancedBrunIndex_tendsto.eventually_ge_atTop b] with n hb
  have hh (k:ℕ) : k≤2^k:=(Nat.lt_two_pow_self (n:=k)).le
  exact hb.trans ((hh _).trans (hh _))

set_option exponentiation.threshold 5200 in
theorem balancedBrun_geometry :
    ∀ᶠ n:ℕ in atTop, let y:=balancedBrunSmall n
      let w:=balancedBrunLarge n
      2≤y ∧ y≤n/4 ∧ (w*y^101)^4≤n/4 ∧ n<w^10 ∧ n<y^4905 := by
  filter_upwards [balancedBrunIndex_tendsto.eventually_ge_atTop 13,balancedBrunSmall_tendsto.eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with n hJ hy hn
  let s:=Nat.log 2 n
  let t:=(s-2)/2452
  let e:=2^(balancedBrunIndex n)
  have he:13≤balancedBrunIndex n:=hJ
  have hl:8192≤e:=Nat.pow_le_pow_right (by decide : 0<2) he
  have ht0:t≠0 := by
    intro hh
    change 13≤Nat.log 2 t at hJ
    simp [hh] at hJ
  have he1:e≤t := Nat.pow_log_le_self 2 ht0
  have he2:t<2*e := by
    have h:=Nat.lt_pow_succ_log_self (by decide : 1<2) t
    rw [pow_succ,mul_comm] at h;exact h
  have hs:s-2<t*2452+2452 := by
    rw [Nat.mul_comm t 2452]
    simpa only [Nat.mul_add,Nat.mul_one] using Nat.lt_mul_div_succ (s-2) (by decide : 0<2452)
  have hslo:e*2452+2≤s:=by
    have hu:=Nat.div_mul_le_self (s-2) 2452
    change t*2452≤s-2 at hu
    have hs2:2≤s:=by
      by_contra! hs2
      exact ht0 (by simp [t,Nat.sub_eq_zero_of_le hs2.le])
    exact (Nat.add_le_add_right ((Nat.mul_le_mul_right 2452 he1).trans hu) 2).trans_eq (Nat.sub_add_cancel hs2)
  have hshi:s+1≤e*4905:=by omega
  let y:=balancedBrunSmall n
  have hq:((y^512)*y^101)^4≤n/4 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    change (((2^e)^512)*(2^e)^101)^4*4≤n
    calc _ = 2^(e*2452+2) := by rw [pow_add,←pow_add,←pow_mul,←pow_mul];congr 2
         _ ≤ 2^s := Nat.pow_le_pow_right (by decide) hslo
         _ ≤ _ := Nat.pow_log_le_self 2 (by omega)
  have hcap:n<y^4905 := by
    change n < (2^e)^4905
    rw [←pow_mul];exact (Nat.lt_pow_succ_log_self (by decide) n).trans_le (Nat.pow_le_pow_right (by decide) hshi)
  have hy0:0<y:=by change 2≤y at hy;omega
  refine ⟨hy,?_,hq,?_,hcap⟩
  · have ha:y≤y^613 := Nat.le_self_pow (by decide) _
    have hb:y^613≤(y^613)^4 := Nat.le_self_pow (by decide) _
    rw [←pow_add] at hq
    exact ha.trans (hb.trans hq)
  · change n<(y^512)^10
    rw [←pow_mul]
    exact hcap.trans_le (Nat.pow_le_pow_right hy0 (by decide))


private theorem reciprocal_abel_bound (A B:ℕ→ℝ) (δ:ℝ)
    (hA:∀k:ℕ,A k≤(k:ℝ)+δ) (hB:B 1=0) (ha:A 1=0)
    (hstep:∀k:ℕ,0<k→B (k+1)-B k≤(A (k+1)-A k)/(k:ℝ)) (N:ℕ) (hN:0<N) :
    B (N+1)≤1+(harmonic N:ℝ)+δ := by
  have hi:∀k:ℕ,0<k → B (k+1)+(((k:ℝ)+1+δ)-A (k+1))/k≤1+(harmonic k:ℝ)+δ := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro _
      by_cases hk:k=0
      · subst k
        have h:=hstep 1 (by decide)
        norm_num [hB,ha] at h
        norm_num
        linarith only [h]
      · have hk':0<k:=Nat.pos_of_ne_zero hk
        have ih':=ih hk'
        have hs:=hstep (k+1) (by omega)
        have hkp:(0:ℝ)<k:=by exact_mod_cast hk'
        have hp:0≤(k:ℝ)+1+δ-A (k+1):=by simpa only [Nat.cast_add,Nat.cast_one,sub_nonneg] using hA (k+1)
        have hd:((k:ℝ)+1+δ-A (k+1))/((k:ℝ)+1)≤((k:ℝ)+1+δ-A (k+1))/k :=
          div_le_div_of_nonneg_left hp hkp (by linarith)
        rw [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
        push_cast at hs ⊢
        calc _ = B (k+1)+(B (k+2)-B (k+1))+(((k:ℝ)+2+δ)-A (k+2))/(k+1) := by ring
             _ ≤ B (k+1)+((A (k+2)-A (k+1))/((k:ℝ)+1))+(((k:ℝ)+2+δ)-A (k+2))/(k+1) := by linarith only [hs]
             _ = B (k+1)+(((k:ℝ)+1+δ)-A (k+1))/(k+1)+1/(k+1) := by ring
             _ ≤ _ := by rw [←one_div];linarith only [hd,ih']
  have hpos:=div_nonneg (sub_nonneg.mpr (show A (N+1)≤(N:ℝ)+1+δ by simpa only [Nat.cast_add,Nat.cast_one] using hA (N+1))) (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [hi N hN,hpos]

theorem brun_medium_reciprocal_abel (y N:ℕ)(B:Finset ℕ) (hy:2≤y)(hN:0<N)
    (hB:B⊆Ioc y (y^(N+1)))(hp:∀p∈B,p.Prime) :
    (∑p∈B,1/(p:ℝ)) ≤ 1+(harmonic N:ℝ)+Real.log 4/Real.log y := by
  let L:=Real.log (y:ℝ)
  let A (k:ℕ):ℝ:= (∑p∈B,if p≤y^k then Real.log p/(p:ℝ) else 0)/L
  let F (k:ℕ):ℝ:= ∑p∈B,if p≤y^k then 1/(p:ℝ) else 0
  have hL:0<L:=Real.log_pos (by exact_mod_cast (show 1<y by omega))
  have hy':0<(y:ℝ):=by exact_mod_cast (show 0<y by omega)
  have hcap (k:ℕ) : A k≤(k:ℝ)+Real.log 4/L := by
    apply (div_le_iff₀ hL).mpr
    rw [←sum_filter]
    have hs:B.filter (fun p=>p≤y^k)⊆(Ioc 0 (y^k)).filter Nat.Prime := by
      intro p h
      obtain ⟨hm,hle⟩:=mem_filter.mp h
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hp p hm).pos,hle⟩,hp p hm⟩
    calc _ ≤ ∑p∈(Ioc 0 (y^k)).filter Nat.Prime,Real.log p/(p:ℝ) :=
            sum_le_sum_of_subset_of_nonneg hs (fun p _ _=>div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
         _ ≤ Real.log ((y^k:ℕ):ℝ)+Real.log 4:=prime_log_reciprocal_upto _ (pow_pos (by omega) _)
         _ = _ := by rw [Nat.cast_pow,Real.log_pow];change (k:ℝ)*L+Real.log 4=_;field_simp
  have h1 (p:ℕ)(hm:p∈B) : ¬p≤y^1 := by rw [pow_one];exact (mem_Ioc.mp (hB hm)).1.not_ge
  have ha:A 1=0:=by dsimp only [A];rw [sum_eq_zero (fun p hm=>ite_eq_right (h1 p hm)),zero_div]
  have hf:F 1=0:=by apply sum_eq_zero;intro p hm;exact ite_eq_right (h1 p hm)
  have hstep (k:ℕ)(hk:0<k) : F (k+1)-F k≤(A (k+1)-A k)/(k:ℝ) := by
    have hkp:(0:ℝ)<k := by exact_mod_cast hk
    rw [le_div_iff₀ hkp]
    dsimp only [A,F]
    rw [←sub_div,le_div_iff₀ hL,←sum_sub_distrib,sum_mul,sum_mul,←sum_sub_distrib]
    apply sum_le_sum
    intro p hm
    have hpy:=Nat.pow_le_pow_right (by omega : 0<y) (Nat.le_succ k)
    by_cases h0:p≤y^k
    · simp [h0,h0.trans hpy]
    · by_cases h₁:p≤y^(k+1)
      · simp only [ite_eq_left h₁,ite_eq_right h0,sub_zero]
        have hh:=Real.log_le_log (pow_pos hy' k) (by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge h0)) : (y:ℝ)^k≤p)
        rw [Real.log_pow] at hh
        calc _ = ((k:ℝ)*L)/(p:ℝ) := by ring
             _ ≤ _ := div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
      · simp [h₁,h0]
  have htop:F (N+1)=∑p∈B,1/(p:ℝ):=sum_congr rfl (fun p hm=>ite_eq_left (mem_Ioc.mp (hB hm)).2)
  rw [←htop]
  exact reciprocal_abel_bound A F _ hcap hf ha hstep N hN

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2500000 in
private theorem harmonic_511_numeric : harmonic 511 < (69/10:ℚ) := by decide +kernel

set_option exponentiation.threshold 1024 in
theorem balancedBrun_medium_weight :
    ∀ᶠ n:ℕ in atTop,∀B:Finset ℕ,B⊆Ioc (balancedBrunSmall n) (balancedBrunLarge n) →
      (∀p∈B,p.Prime)→(∑p∈B,brunEulerWeight p)≤8 := by
  have ht:=Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp balancedBrunSmall_tendsto)
  filter_upwards [balancedBrunSmall_tendsto.eventually_ge_atTop 1001,ht.eventually_ge_atTop (100*Real.log 4)]
    with n hy hlog
  intro B hb hp
  let y:=balancedBrunSmall n
  have hL : 0<Real.log (y:ℝ):=Real.log_pos (by exact_mod_cast (show 1<y by dsimp [y];omega))
  have hd : Real.log 4/Real.log y≤1/100 := by apply (div_le_iff₀ hL).mpr;change 100*Real.log 4≤Real.log y at hlog;linarith only [hlog]
  have hnum:(harmonic 511:ℝ)<69/10 := by
    have hh:((harmonic 511:ℚ):ℝ)<((69/10:ℚ):ℝ):=Rat.cast_lt.mpr harmonic_511_numeric
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hh
  have hm:=brun_medium_reciprocal_abel y 511 B (by dsimp [y];omega) (by decide) hb hp
  have hs : (∑p∈B,1/(p:ℝ))≤791/100 := by linarith only [hm,hnum,hd]
  calc _ ≤ ∑p∈B,(1001/1000:ℝ)*(1/(p:ℝ)) := by
         apply sum_le_sum;intro p h
         have hpr:(1001:ℝ)≤p:=by exact_mod_cast hy.trans (mem_Ioc.mp (hb h)).1.le
         dsimp only [brunEulerWeight];rw [←div_eq_mul_one_div,div_le_div_iff₀ (by linarith) (by linarith)]
         linarith only [hpr]
       _ ≤ _ := by rw [←mul_sum];linarith only [hs]

theorem brun_quarter_error_uniform  {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, ∀D:ℕ, D^4≤n/4 →
      fixedTargetBrunDistributionError n D≤ε*(n:ℝ)/Real.log n := by
  obtain ⟨C,hC,hp⟩:=prime_progressions_quarter_level 2
  obtain ⟨T,hT⟩:=eventually_atTop.mp hp
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (4*T),
    eventually_ge_atTop (40:ℕ),hl.eventually_ge_atTop (8*C/ε)] with n ht hn hl'
  intro D hD
  let L:=Real.log (n:ℝ)
  have hL:0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsc (u:ℕ)(hu:n/4≤u)(hun:u≤n) :
      (∑d∈Icc 1 D,brunPrimePrefixMaxError u d)≤4*C*n/L^2 := by
    have hlog : 0<Real.log (u:ℝ):=Real.log_pos (by exact_mod_cast (show 1<u by omega))
    have hnu : n≤u^2 := by nlinarith only [show n≤5*u by omega,show 5≤u by omega]
    have hcmp:=Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hnu : (n:ℝ)≤(u:ℝ)^2)
    rw [Real.log_pow] at hcmp
    have hL2:L^2≤4*(Real.log u)^2 := by
      have hh:=pow_le_pow_left₀ hL.le hcmp 2
      norm_num at hh;linarith only [hh]
    apply (hT u (by omega) D (hD.trans hu)).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hlog) (sq_pos_of_pos hL)).mpr
    calc _ ≤ (C*u)*(4*(Real.log u)^2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
         _ ≤ (C*n)*(4*(Real.log u)^2) := by gcongr
         _ = _ := by ring
  apply (fixedTargetBrunDistributionError_le_prefix_max n D).trans
  apply (add_le_add (hsc (n/2) (by omega) (Nat.div_le_self ..)) (hsc (n/4) le_rfl (Nat.div_le_self ..))).trans
  have hbound:8*C≤L*ε:=(div_le_iff₀ hε).mp hl'
  rw [←two_mul,le_div_iff₀ hL,mul_div_assoc',div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hL)]
  nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hL.le) (sub_nonneg.mpr hbound)]


theorem balancedBrun_distribution_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,fixedTargetBrunDistributionError n ((balancedBrunLarge n)*(balancedBrunSmall n)^101)
      ≤ε*(n:ℝ)/Real.log n := by
  filter_upwards [brun_quarter_error_uniform hε,balancedBrun_geometry] with n he hg
  exact he _ hg.2.2.1

set_option exponentiation.threshold 5200 in
theorem balancedBrun_log_comparison :
    ∀ᶠ n:ℕ in atTop, Real.log (n:ℝ) ≤ 4905*Real.log (balancedBrunSmall n) ∧
      2452*Real.log (balancedBrunSmall n)≤Real.log n := by
  filter_upwards [balancedBrun_geometry,eventually_ge_atTop (2:ℕ)] with n hg hn
  let y:=balancedBrunSmall n
  have hy:0<(y:ℝ):=by exact_mod_cast (show 0<y by have hh:=hg.1;change 2≤y at hh;omega)
  have h1:= Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hg.2.2.2.2.le : (n:ℝ)≤(y:ℝ)^4905)
  have hq:=hg.2.2.1
  change ((y^512)*y^101)^4≤n/4 at hq
  rw [←pow_add,←pow_mul] at hq
  change y^2452≤n/4 at hq
  have hw:y^2452≤n:=hq.trans (Nat.div_le_self n 4)
  have hcast:((y^2452:ℕ):ℝ)≤n:=Nat.cast_le.mpr hw
  rw [Nat.cast_pow] at hcast
  have h2:=Real.log_le_log (pow_pos hy _) hcast
  rw [Real.log_pow] at h1 h2
  exact ⟨h1,h2⟩


open private sf_inverse_tail from VerifiedSquarefreeBrunSurvivors

set_option exponentiation.threshold 5200 in
theorem balancedBrun_nonsquarefree_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,fixedTargetNonsquarefreeMass n (balancedBrunSmall n) ≤ ε*n/Real.log n := by
  have ht : Tendsto (fun z:ℕ=>(Real.log z)^2/(z:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [balancedBrun_geometry,balancedBrunSmall_tendsto.eventually
    (ht.eventually_lt_const (show 0<ε/(2*4905^2:ℝ) by positivity)),eventually_ge_atTop (2:ℕ)] with n hg hs hn
  let y:=balancedBrunSmall n
  let L:=Real.log (n:ℝ)
  have hy:2≤y:=hg.1
  have hy0:(0:ℝ)<y:=by exact_mod_cast (show 0<y by omega)
  have hL : 0<L:=Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hly:=Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hg.2.2.2.2.le : (n:ℝ)≤(y:ℝ)^4905)
  rw [Real.log_pow] at hly
  have hsq:=pow_le_pow_left₀ hL.le hly 2
  have hs' : (Real.log y)^2<ε/(2*4905^2:ℝ)*y := (div_lt_iff₀ hy0).mp hs
  have ha:2*L^2≤ε*((y:ℝ)+1) := by
    norm_num at hsq
    nlinarith only [hsq,hs',hε]
  have he:=fixedTargetNonsquarefree_split n y y hg.2.1
  simp only [Ioc_self,filter_empty,sum_empty,zero_add] at he
  apply he.trans
  calc _ ≤ ∑p∈Ioc y n,((n:ℝ)*L)*(1/(p:ℝ)^2) := by
         apply sum_le_sum;intro p _
         apply (fixedTargetDivisorRow_trivial n (p^2)).trans_eq
         push_cast;dsimp only [L];ring
       _ = ((n:ℝ)*L)*(∑p∈Ioc y n,1/(p:ℝ)^2) := (mul_sum ..).symm
       _ ≤ ((n:ℝ)*L)*(2/((y:ℝ)+1)) := mul_le_mul_of_nonneg_left (sf_inverse_tail y n) (by positivity)
       _ ≤ _ := by
         rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) hL]
         nlinarith only [mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α:=ℝ) n)]

end GoldbachPartial