import VerifiedBalancedBrunParameters
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

theorem prime_log_reciprocal_eventually_lower :
    ∀ᶠ y:ℕ in atTop, (9/10:ℝ)*Real.log y≤∑p∈(Ioc 0 y).filter Nat.Prime,Real.log p/(p:ℝ) := by
  let f (p:ℕ):ℝ:=Real.log p/(p:ℝ)
  let g (p:ℕ):ℝ:=Real.log p/((p:ℝ)-1)
  let C:=∑p∈(Ioc 0 101).filter Nat.Prime,g p
  have hg (p:ℕ)(hp:p.Prime):0≤g p:=by
    have h:(2:ℝ)≤p:=by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_natCast_nonneg _) (by linarith)
  have ht:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (100*(|C|+Real.log 32+1)),eventually_ge_atTop (64:ℕ)] with y hlog hy
  let P:=(Ioc 0 y).filter Nat.Prime
  let F:=y.factorial.primeFactors
  have hy0:(0:ℝ)<y:=by exact_mod_cast (show 0<y by omega)
  have hfac : Real.log y.factorial ≤ y*(∑p∈P,g p) := by
    have hh:=congrArg (fun n:ℕ=>Real.log (n:ℝ)) (Nat.prod_primeFactors_pow_factorization (Nat.factorial_ne_zero y))
    simp only [Nat.cast_prod,Nat.cast_pow] at hh
    rw [Real.log_prod (fun p hp=>pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)),] at hh
    simp_rw [Real.log_pow] at hh
    rw [hh,mul_sum]
    apply sum_le_sum_of_injOn id
    · exact Set.injOn_id _
    · intro p hm
      have hp:p∈F:=by change p∈y.factorial.primeFactors;simpa only [image_id] using hm
      have hpr:=Nat.prime_of_mem_primeFactors hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpr.pos,hpr.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)⟩,hpr⟩
    · intro p hp
      have hpr:=Nat.prime_of_mem_primeFactors hp
      have h:=Nat.factorization_factorial_le_div_pred hpr y
      have hh':((y.factorial.factorization p:ℕ):ℝ)≤(y:ℝ)/(p-1:ℕ) := (Nat.cast_le.mpr h).trans Nat.cast_div_le
      rw [Nat.cast_sub hpr.one_le,Nat.cast_one] at hh'
      exact (mul_le_mul_of_nonneg_right hh' (Real.log_natCast_nonneg p)).trans_eq (by dsimp [g];ring)
    · intro p hm _
      exact mul_nonneg hy0.le (hg p (mem_filter.mp hm).2)
  have hlow : ((31/32:ℝ)*y)*(Real.log y-Real.log 32)≤Real.log y.factorial := by
    have he: (∑j∈Ioc 0 y,Real.log j)=Real.log y.factorial :=
      (mangoldt_floor_sum_logSum y).symm.trans (mangoldt_floor_sum_log_factorial y)
    rw [←he]
    have hnon : 0≤Real.log y-Real.log 32:=sub_nonneg.mpr (Real.log_le_log (by norm_num) (by exact_mod_cast (show 32≤y by omega)))
    have hc: (31/32:ℝ)*y≤((Ioc (y/32) y).card:ℝ):=by
      rw [Nat.card_Ioc,Nat.cast_sub (Nat.div_le_self ..)]
      have h:=(Nat.cast_div_le : ((y/32:ℕ):ℝ)≤(y:ℝ)/(32:ℕ))
      push_cast at h;linarith only [h]
    calc _ ≤ ∑_j∈Ioc (y/32) y,(Real.log y-Real.log 32) := by
           simp only [sum_const,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right hc hnon
         _ ≤ ∑j∈Ioc (y/32) y,Real.log j := by
           apply sum_le_sum;intro j hj
           have hj':=mem_Ioc.mp hj
           rw [←Real.log_div hy0.ne' (by norm_num)]
           apply Real.log_le_log (by positivity)
           rw [div_le_iff₀ (by norm_num : (0:ℝ)<32)]
           exact_mod_cast (show y≤j*32 by omega)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun j hj=>mem_Ioc.mpr ⟨by have:= (mem_Ioc.mp hj).1;omega,(mem_Ioc.mp hj).2⟩)
           (fun j _ _=>Real.log_natCast_nonneg j)
  have hab : (∑p∈P,g p) ≤ C+(101/100:ℝ)*(∑p∈P,f p) := by
    rw [←sum_filter_add_sum_filter_not P (fun p=>p≤101) g]
    apply add_le_add
    · apply sum_le_sum_of_subset_of_nonneg
      · intro p h;obtain ⟨hP,hh⟩:=mem_filter.mp h
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_filter.mp hP).2.pos,hh⟩,(mem_filter.mp hP).2⟩
      · exact fun p hp _=>hg p (mem_filter.mp hp).2
    · rw [mul_sum]
      apply le_trans _ (sum_le_sum_of_subset_of_nonneg (filter_subset (fun p:ℕ=>¬p≤101) P) (fun p _ _ => show 0≤(101/100:ℝ)*f p by dsimp [f];positivity))
      apply sum_le_sum;intro p hp
      have hr:(101:ℝ)<p:=by exact_mod_cast (lt_of_not_ge (mem_filter.mp hp).2 : 101<p)
      dsimp only [g,f]
      rw [mul_div_assoc',div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith only [mul_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hr.le)]
  have hf:=hlow.trans hfac
  have hh:(31/32:ℝ)*(Real.log y-Real.log 32)≤∑p∈P,g p:=by
    apply le_of_mul_le_mul_left (a:=(y:ℝ)) _ hy0
    convert hf using 1;ring
  have hl:100*(|C|+Real.log 32+1)≤Real.log y:=hlog
  change _≤∑p∈P,f p
  linarith only [hh,hab,hl,le_abs_self C,abs_nonneg C,Real.log_nonneg (by norm_num : (1:ℝ)≤32)]

open private reciprocal_abel_bound harmonic_511_numeric from VerifiedBalancedBrunParameters

theorem brun_medium_reciprocal_abel_lower_endpoint (y N:ℕ)(B:Finset ℕ) (hy:2≤y)(hN:0<N)
    (hB:B⊆Ioc y (y^(N+1)))(hp:∀p∈B,p.Prime)
    (hlo:(9/10:ℝ)*Real.log y≤∑p∈(Ioc 0 y).filter Nat.Prime,Real.log p/(p:ℝ)) :
    (∑p∈B,1/(p:ℝ)) ≤ 1+(harmonic N:ℝ)+Real.log 4/Real.log y-9/10 := by
  let L:=Real.log (y:ℝ)
  let A (k:ℕ):ℝ:= (∑p∈B,if p≤y^k then Real.log p/(p:ℝ) else 0)/L
  let F (k:ℕ):ℝ:= ∑p∈B,if p≤y^k then 1/(p:ℝ) else 0
  have hL:0<L:=Real.log_pos (by exact_mod_cast (show 1<y by omega))
  have hy':0<(y:ℝ):=by exact_mod_cast (show 0<y by omega)
  have hcap (k:ℕ) (hk:0<k) : A k≤(k:ℝ)+(Real.log 4/L-9/10) := by
    apply (div_le_iff₀ hL).mpr
    rw [←sum_filter]
    have hs:B.filter (fun p=>p≤y^k)⊆(Ioc 0 (y^k)).filter Nat.Prime := by
      intro p h
      obtain ⟨hm,hle⟩:=mem_filter.mp h
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hp p hm).pos,hle⟩,hp p hm⟩
    let W:=B.filter (fun p=>p≤y^k)
    let Z:=(Ioc 0 y).filter Nat.Prime
    have hd : Disjoint W Z := disjoint_left.mpr fun p hw hz=>(mem_Ioc.mp (hB (mem_filter.mp hw).1)).1.not_ge (mem_Ioc.mp (mem_filter.mp hz).1).2
    have hzz:Z⊆(Ioc 0 (y^k)).filter Nat.Prime := by
      intro p hm
      obtain ⟨hi,hp'⟩:=mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.le_self_pow hk.ne' _)⟩,hp'⟩
    have hh: (∑p∈W,Real.log p/(p:ℝ))+(∑p∈Z,Real.log p/(p:ℝ))≤k*L+Real.log 4 := by
      rw [←sum_union hd]
      apply (sum_le_sum_of_subset_of_nonneg (union_subset hs hzz) (fun p _ _=>div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))).trans
      simpa only [Nat.cast_pow,Real.log_pow,L] using prime_log_reciprocal_upto (y^k) (pow_pos (by omega) _)
    change _≤_
    have hden:(Real.log 4/L)*L=Real.log 4:=div_mul_cancel₀ _ hL.ne'
    change 9/10*L ≤ ∑p∈Z,Real.log p/(p:ℝ) at hlo
    change (∑p∈W,Real.log p/(p:ℝ))≤_
    nlinarith only [hh,hlo,hden]
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
  let δ:= Real.log 4/L-9/10
  let A' (k:ℕ):ℝ:=if k=0 then δ else A k
  have hs' (k:ℕ)(hk:0<k):F (k+1)-F k≤(A' (k+1)-A' k)/(k:ℝ):=by
    simpa only [A',ite_eq_right hk.ne',Nat.succ_ne_zero,ite_false] using hstep k hk
  have hc' (k:ℕ):A' k≤(k:ℝ)+δ:=by
    rcases Nat.eq_zero_or_pos k with rfl|hk
    · simp [A']
    · simpa only [A',ite_eq_right hk.ne'] using hcap k hk
  have hh:=reciprocal_abel_bound A' F δ hc' hf (by simpa [A'] using ha) hs' N hN
  dsimp only [δ,L] at hh
  linarith only [hh]

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 6000 in
set_option exponentiation.threshold 1024 in
theorem balancedBrun_medium_weight_seven :
    ∀ᶠ n:ℕ in atTop,∀B:Finset ℕ,B⊆Ioc (balancedBrunSmall n) (balancedBrunLarge n) →
      (∀p∈B,p.Prime)→(∑p∈B,brunEulerWeight p)≤7 := by
  have ht:=Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp balancedBrunSmall_tendsto)
  filter_upwards [balancedBrunSmall_tendsto.eventually_ge_atTop 1001,balancedBrunSmall_tendsto.eventually prime_log_reciprocal_eventually_lower,ht.eventually_ge_atTop (1000*Real.log 4)]
    with n hy hlo hlog
  intro B hb hp
  let y:=balancedBrunSmall n
  have hL : 0<Real.log (y:ℝ):=Real.log_pos (by exact_mod_cast (show 1<y by dsimp [y];omega))
  have hd : Real.log 4/Real.log y≤1/1000 := by apply (div_le_iff₀ hL).mpr;change 1000*Real.log 4≤Real.log y at hlog;linarith only [hlog]
  have hnum:(harmonic 511:ℝ)<689/100 := by
    have hh:((harmonic 511:ℚ):ℝ)<((689/100:ℚ):ℝ):=Rat.cast_lt.mpr (by decide +kernel : harmonic 511 < (689/100:ℚ))
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hh
  have hm:=brun_medium_reciprocal_abel_lower_endpoint y 511 B (by dsimp [y];omega) (by decide) hb hp hlo
  have hs : (∑p∈B,1/(p:ℝ))≤6992/1000 := by linarith only [hm,hnum,hd]
  calc _ ≤ ∑p∈B,(1001/1000:ℝ)*(1/(p:ℝ)) := by
         apply sum_le_sum;intro p h
         have hpr:(1001:ℝ)≤p:=by exact_mod_cast hy.trans (mem_Ioc.mp (hb h)).1.le
         dsimp only [brunEulerWeight];rw [←div_eq_mul_one_div,div_le_div_iff₀ (by linarith) (by linarith)]
         linarith only [hpr]
       _ ≤ _ := by rw [←mul_sum];linarith only [hs]

end GoldbachPartial