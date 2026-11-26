import VerifiedFourNinthsBrun
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

theorem prime_progressions_near_half (k A:ℕ):
    ∃C:ℝ,0<C ∧ ∀ᶠ u:ℕ in atTop,∀D:ℕ,D^(2*k+1)≤u^k →
      (∑q∈Icc 1 D,brunPrimePrefixMaxError u q)≤C*u/(Real.log u)^A := by
  obtain ⟨d,C,hC,hh⟩:=prime_progressions_half_level A
  refine ⟨C,hC,?_⟩
  have ht:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp:∀ᶠ u:ℕ in atTop,(Real.log u)^((2*(2*(2*k+1)))*d)≤u:=by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
        (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (((2*(2*(2*k+1)))*d:ℕ):ℝ) (by norm_num : (0:ℝ)<1))
  filter_upwards [hh,ht.eventually_ge_atTop 2,hp] with u h hL hlog
  intro D hD
  let L:=Real.log (u:ℝ)
  have hL':2≤L:=hL
  have hL2:1+L≤L^2:=by nlinarith only [hL',sq_nonneg (L-2)]
  have hbig:(1+L)^((2*(2*k+1))*d)≤(u:ℝ):=by
    calc _ ≤ (L^2)^((2*(2*k+1))*d):=pow_le_pow_left₀ (by dsimp [L];positivity) hL2 _
         _ = L^((2*(2*(2*k+1)))*d):=by rw [←pow_mul];congr 1;ring
         _ ≤ _:=hlog
  have hD9:(D:ℝ)^(2*k+1)≤(u:ℝ)^k:=by exact_mod_cast hD
  have hs:(D:ℝ)^(2*(2*k+1))≤(u:ℝ)^(2*k):=by
    simpa only [←pow_mul,mul_comm _ 2] using pow_le_pow_left₀ (by positivity) hD9 2
  apply h D
  apply le_of_pow_le_pow_left₀ (by omega : 2*(2*k+1)≠0) (Real.sqrt_nonneg _)
  rw [mul_pow,←pow_mul,mul_comm d (2*(2*k+1))]
  have hz:(Real.sqrt (u:ℝ))^(2*(2*k+1))=(u:ℝ)^(2*k+1):=by
    rw [pow_mul,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hz]
  exact (mul_le_mul hs hbig (by positivity) (by positivity)).trans_eq (by rw [pow_succ])

theorem fixedTargetNineNineteenthsError_uniform  {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, ∀D:ℕ, D^19≤(n/4)^9 →
      fixedTargetBrunDistributionError n D≤ε*(n:ℝ)/Real.log n := by
  obtain ⟨C,hC,hp⟩:=prime_progressions_near_half 9 2
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
    apply (hT u (by omega) D (hD.trans (Nat.pow_le_pow_left hu 9))).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hlog) (sq_pos_of_pos hL)).mpr
    calc _ ≤ (C*u)*(4*(Real.log u)^2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
         _ ≤ (C*n)*(4*(Real.log u)^2) := by gcongr
         _ = _ := by ring
  apply (fixedTargetBrunDistributionError_le_prefix_max n D).trans
  apply (add_le_add (hsc (n/2) (by omega) (Nat.div_le_self ..)) (hsc (n/4) le_rfl (Nat.div_le_self ..))).trans
  have hbound:8*C≤L*ε:=(div_le_iff₀ hε).mp hl'
  rw [←two_mul,le_div_iff₀ hL,mul_div_assoc',div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hL)]
  nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hL.le) (sub_nonneg.mpr hbound)]




def sevenBrunIndex (n:ℕ):ℕ:=Nat.log 2 (Nat.log 2 n/216)
def sevenBrunSmall (n:ℕ):ℕ:=brunBlockBoundary (sevenBrunIndex n)
def sevenBrunMesh (n:ℕ):ℕ:=brunBlockBoundary (sevenBrunIndex n-4)

theorem sevenBrunIndex_tendsto : Tendsto sevenBrunIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^(216*2^b):ℕ)] with n hh
  have h:216*2^b≤Nat.log 2 n:=by simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) hh
  have h':2^b≤Nat.log 2 n/216:=(Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  change b≤Nat.log 2 (Nat.log 2 n/216)
  simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) h'

theorem sevenBrunSmall_tendsto : Tendsto sevenBrunSmall atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [sevenBrunIndex_tendsto.eventually_ge_atTop b] with n hn
  exact hn.trans ((Nat.lt_two_pow_self (n:=sevenBrunIndex n)).le.trans (Nat.lt_two_pow_self (n:=2^sevenBrunIndex n)).le)

theorem sevenBrunMesh_tendsto : Tendsto sevenBrunMesh atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [sevenBrunIndex_tendsto.eventually_ge_atTop (b+4)] with n hn
  have hh:b≤sevenBrunIndex n-4 :=by omega
  exact hh.trans ((Nat.lt_two_pow_self (n:=sevenBrunIndex n-4)).le.trans (Nat.lt_two_pow_self (n:=2^(sevenBrunIndex n-4))).le)

set_option exponentiation.threshold 3000 in
theorem sevenBrun_geometry :
    ∀ᶠ n:ℕ in atTop, let y:=sevenBrunSmall n
      let w:=halfLevelBrunLarge n
      2≤y ∧ y≤w ∧ w≤n/4 ∧ n<w^3 ∧ (y^101)^19≤(n/4)^9 ∧ (w*y^29)^19≤(n/4)^9 ∧
        w≤y^145 ∧ n≤y^432 ∧ y=(sevenBrunMesh n)^16 := by
  filter_upwards [sevenBrunIndex_tendsto.eventually_ge_atTop 5,eventually_ge_atTop (2:ℕ)]
    with n hJ hn
  let s:=Nat.log 2 n
  let t:=s/216
  let e:=2^(sevenBrunIndex n)
  let y:=sevenBrunSmall n
  have he:0<e:=by dsimp [e];positivity
  have tpos:t≠0:=by intro ht;change 5≤Nat.log 2 t at hJ;simp [ht] at hJ
  have hel:e≤t:=Nat.pow_log_le_self 2 tpos
  have heu:t<2*e:=by have hh:=Nat.lt_pow_succ_log_self (by decide : 1<2) t;rw [pow_succ,mul_comm] at hh;exact hh
  have hlow:e*216≤s:=(Nat.mul_le_mul_right 216 hel).trans (Nat.div_mul_le_self ..)
  have hhi:s<e*432:=by
    have hh:=Nat.lt_mul_div_succ s (by decide : 0<216)
    change s<216*(t+1) at hh
    omega
  have hs2:2≤s:=by omega
  have hx:2^(s-2)≤n/4:=by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc 2^(s-2)*4 = 2^(s-2+2):=by rw [pow_add];rfl
         _ = 2^s:=by rw [Nat.sub_add_cancel hs2]
         _ ≤ n:=Nat.pow_log_le_self 2 (by omega)
  have heb:32≤e:=Nat.pow_le_pow_right (by decide : 0<2) hJ
  refine ⟨show 2≤2^e by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<2) he,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change 2^e≤2^(s/3+1)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · change 2^(s/3+1)≤n/4
    exact (Nat.pow_le_pow_right (by decide) (by omega : s/3+1≤s-2)).trans hx
  · change n<(2^(s/3+1))^3
    rw [←pow_mul];exact (Nat.lt_pow_succ_log_self (by decide) n).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · change ((2^e)^101)^19≤(n/4)^9
    rw [←pow_mul,←pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (by omega : e*(101*19)≤(s-2)*9)).trans ((pow_mul ..).le.trans (Nat.pow_le_pow_left hx _))
  · change (2^(s/3+1)*(2^e)^29)^19≤(n/4)^9
    rw [←pow_mul,←pow_add,←pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (by omega : (s/3+1+e*29)*19≤(s-2)*9)).trans ((pow_mul ..).le.trans (Nat.pow_le_pow_left hx _))
  · change 2^(s/3+1)≤(2^e)^145
    rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  · change n≤(2^e)^432
    rw [←pow_mul];exact (Nat.lt_pow_succ_log_self (by decide) n).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · change 2^(2^(sevenBrunIndex n)) = (2^(2^(sevenBrunIndex n-4)))^16
    rw [←pow_mul]
    congr 1
    rw [←show (2:ℕ)^4=16 by decide,←pow_add,Nat.sub_add_cancel (by omega : 4≤sevenBrunIndex n)]



private theorem reciprocal_abel_from_sixteen (A B:ℕ→ℝ) (δ:ℝ)
    (hA:∀k:ℕ,16≤k→ A k≤(k:ℝ)+δ) (hB:B 16=0) (ha:A 16=0)
    (hstep:∀k:ℕ,16≤k→B (k+1)-B k≤(A (k+1)-A k)/(k:ℝ)) (N:ℕ) (hN:16≤N) :
    B (N+1)≤1+δ/16+(harmonic N:ℝ)-(harmonic 15:ℝ) := by
  have hi:∀k:ℕ,16≤k → B (k+1)+(((k:ℝ)+1+δ)-A (k+1))/k≤1+δ/16+(harmonic k:ℝ)-(harmonic 15:ℝ) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hbound
      by_cases hk:k+1=16
      · rw [hk]
        have h:=hstep 16 (by decide)
        rw [hB,ha,sub_zero,sub_zero] at h
        have hp : (harmonic 16:ℝ) = (harmonic 15:ℝ)+1/16 := by
          rw [show (16:ℕ)=15+1 by decide,harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
          norm_num
        norm_num only [Nat.cast_ofNat] at h ⊢
        linarith only [h,hp]
      · have hk':16≤k:=by omega
        have ih':=ih hk'
        have hs:=hstep (k+1) (by omega)
        have hkp:(0:ℝ)<k:=by exact_mod_cast (show 0<k by omega)
        have hp:0≤(k:ℝ)+1+δ-A (k+1):=by simpa only [Nat.cast_add,Nat.cast_one,sub_nonneg] using hA (k+1) (by omega)
        have hd:((k:ℝ)+1+δ-A (k+1))/((k:ℝ)+1)≤((k:ℝ)+1+δ-A (k+1))/k :=
          div_le_div_of_nonneg_left hp hkp (by linarith)
        rw [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
        push_cast at hs ⊢
        calc _ = B (k+1)+(B (k+2)-B (k+1))+(((k:ℝ)+2+δ)-A (k+2))/(k+1) := by ring
             _ ≤ B (k+1)+((A (k+2)-A (k+1))/((k:ℝ)+1))+(((k:ℝ)+2+δ)-A (k+2))/(k+1) := by linarith only [hs]
             _ = B (k+1)+(((k:ℝ)+1+δ)-A (k+1))/(k+1)+1/(k+1) := by ring
             _ ≤ _ := by rw [←one_div];linarith only [hd,ih']
  have hpos:=div_nonneg (sub_nonneg.mpr (show A (N+1)≤(N:ℝ)+1+δ by simpa only [Nat.cast_add,Nat.cast_one] using hA (N+1) (by omega))) (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [hi N hN,hpos]


theorem brun_medium_reciprocal_mesh (y N:ℕ)(B:Finset ℕ) (hy:2≤y)(hN:16≤N)
    (hB:B⊆Ioc (y^16) (y^(N+1)))(hp:∀p∈B,p.Prime)
    (hlo:(9/10:ℝ)*Real.log ((y^16:ℕ):ℝ)≤∑p∈(Ioc 0 (y^16)).filter Nat.Prime,Real.log p/(p:ℝ)) :
    (∑p∈B,1/(p:ℝ)) ≤ 1+(Real.log 4/Real.log y-9/10*16)/16+(harmonic N:ℝ)-(harmonic 15:ℝ) := by
  let L:=Real.log (y:ℝ)
  let A (k:ℕ):ℝ:= (∑p∈B,if p≤y^k then Real.log p/(p:ℝ) else 0)/L
  let F (k:ℕ):ℝ:= ∑p∈B,if p≤y^k then 1/(p:ℝ) else 0
  have hL:0<L:=Real.log_pos (by exact_mod_cast (show 1<y by omega))
  have hy':0<(y:ℝ):=by exact_mod_cast (show 0<y by omega)
  have hcap (k:ℕ) (hk:16≤k) : A k≤(k:ℝ)+(Real.log 4/L-9/10*16) := by
    apply (div_le_iff₀ hL).mpr
    rw [←sum_filter]
    have hs:B.filter (fun p=>p≤y^k)⊆(Ioc 0 (y^k)).filter Nat.Prime := by
      intro p h
      obtain ⟨hm,hle⟩:=mem_filter.mp h
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hp p hm).pos,hle⟩,hp p hm⟩
    let W:=B.filter (fun p=>p≤y^k)
    let Z:=(Ioc 0 (y^16)).filter Nat.Prime
    have hd : Disjoint W Z := disjoint_left.mpr fun p hw hz=>(mem_Ioc.mp (hB (mem_filter.mp hw).1)).1.not_ge (mem_Ioc.mp (mem_filter.mp hz).1).2
    have hzz:Z⊆(Ioc 0 (y^k)).filter Nat.Prime := by
      intro p hm
      obtain ⟨hi,hp'⟩:=mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.pow_le_pow_right (by omega) hk)⟩,hp'⟩
    have hh: (∑p∈W,Real.log p/(p:ℝ))+(∑p∈Z,Real.log p/(p:ℝ))≤k*L+Real.log 4 := by
      rw [←sum_union hd]
      apply (sum_le_sum_of_subset_of_nonneg (union_subset hs hzz) (fun p _ _=>div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))).trans
      simpa only [Nat.cast_pow,Real.log_pow,L] using prime_log_reciprocal_upto (y^k) (pow_pos (by omega) _)
    change _≤_
    have hden:(Real.log 4/L)*L=Real.log 4:=div_mul_cancel₀ _ hL.ne'
    rw [Nat.cast_pow,Real.log_pow] at hlo
    change 9/10*(16*L) ≤ ∑p∈Z,Real.log p/(p:ℝ) at hlo
    change (∑p∈W,Real.log p/(p:ℝ))≤_
    nlinarith only [hh,hlo,hden]
  have h1 (p:ℕ)(hm:p∈B) : ¬p≤y^16 := by exact (mem_Ioc.mp (hB hm)).1.not_ge
  have ha:A 16=0:=by dsimp only [A];rw [sum_eq_zero (fun p hm=>ite_eq_right (h1 p hm)),zero_div]
  have hf:F 16=0:=by apply sum_eq_zero;intro p hm;exact ite_eq_right (h1 p hm)
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
  exact reciprocal_abel_from_sixteen A F _ hcap hf ha (fun k hk=>hstep k (by omega)) N hN

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
private theorem harmonic_2319_15_numeric : harmonic 2319 - harmonic 15 < (504/100:ℚ) := by decide +kernel

set_option exponentiation.threshold 3000 in
theorem sevenBrun_medium_weight :
    ∀ᶠ n:ℕ in atTop, ∀ B:Finset ℕ, B⊆Ioc (sevenBrunSmall n) (halfLevelBrunLarge n) →
      (∀p∈B,p.Prime)→ (∑p∈B,brunEulerWeight p)≤519/100 := by
  have ht:=Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp sevenBrunMesh_tendsto)
  filter_upwards [sevenBrunSmall_tendsto.eventually_ge_atTop 1001,sevenBrunMesh_tendsto.eventually_ge_atTop 2,
    sevenBrunSmall_tendsto.eventually prime_log_reciprocal_eventually_lower,ht.eventually_ge_atTop (100*Real.log 4),
    sevenBrun_geometry] with n hy hz hlo hlog hg
  intro B hb hp
  let z:=sevenBrunMesh n
  have hL : 0<Real.log (z:ℝ):=Real.log_pos (by exact_mod_cast (show 1<z by exact hz))
  have hd : Real.log 4/Real.log z≤1/100 := by
    apply (div_le_iff₀ hL).mpr
    change 100*Real.log 4≤Real.log z at hlog
    linarith only [hlog]
  obtain ⟨_,_,_,_,_,_,hw,_,he⟩:=hg
  change sevenBrunSmall n=z^16 at he
  have htop:halfLevelBrunLarge n≤z^(2319+1):=by
    rw [he,←pow_mul] at hw
    exact hw
  have hsub:B⊆Ioc (z^16) (z^(2319+1)):=by
    intro p hm
    exact mem_Ioc.mpr ⟨by rw [←he];exact (mem_Ioc.mp (hb hm)).1, (mem_Ioc.mp (hb hm)).2.trans htop⟩
  rw [he] at hlo
  have hm:=brun_medium_reciprocal_mesh z 2319 B hz (by decide) hsub hp hlo
  have hnum:(harmonic 2319:ℝ)-(harmonic 15:ℝ)<504/100:=by
    have hh:((harmonic 2319-harmonic 15:ℚ):ℝ)<((504/100:ℚ):ℝ):=Rat.cast_lt.mpr harmonic_2319_15_numeric
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using hh
  have hs : (∑p∈B,1/(p:ℝ))≤515/100 := by linarith only [hm,hnum,hd]
  calc _ ≤ ∑p∈B,(1001/1000:ℝ)*(1/(p:ℝ)) := by
         apply sum_le_sum;intro p h
         have hpr:(1001:ℝ)≤p:=by exact_mod_cast hy.trans (mem_Ioc.mp (hb h)).1.le
         dsimp only [brunEulerWeight];rw [←div_eq_mul_one_div,div_le_div_iff₀ (by linarith) (by linarith)]
         linarith only [hpr]
       _ ≤ _ := by rw [←mul_sum];linarith only [hs]

theorem sevenBrun_distribution {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      fixedTargetBrunDistributionError n ((sevenBrunSmall n)^101) ≤ ε*n/Real.log n ∧
      fixedTargetBrunDistributionError n (halfLevelBrunLarge n*(sevenBrunSmall n)^29) ≤ ε*n/Real.log n := by
  filter_upwards [sevenBrun_geometry,fixedTargetNineNineteenthsError_uniform hε] with n hg hh
  exact ⟨hh _ hg.2.2.2.2.1,hh _ hg.2.2.2.2.2.1⟩

end GoldbachPartial
