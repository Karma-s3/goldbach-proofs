import VerifiedPrimeQuarterDistribution
import VerifiedBoundedFactorBrun
set_option exponentiation.threshold 1024
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

def quarterBrunSieveLevel (n:ℕ):ℕ:=2^((Nat.log 2 n-2)/808)

theorem quarterBrunSieveLevel_tendsto : Tendsto quarterBrunSieveLevel atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^(808*b+2):ℕ)] with n hn
  have hs:808*b+2≤Nat.log 2 n:=by
    have hh:=Nat.log_mono_right (b:=2) hn
    simpa only [Nat.log_pow (by decide : 1<2)] using hh
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n:=b))).trans
    (Nat.pow_le_pow_right (by decide) (show b≤(Nat.log 2 n-2)/808 by omega))

theorem quarterBrunSieveLevel_geometry :
    ∀ᶠ n:ℕ in atTop, let y:=quarterBrunSieveLevel n
      2≤y ∧ y≤n/4 ∧ (y^202)^4≤n/4 ∧ n<y^809 := by
  filter_upwards [eventually_ge_atTop (2^(808*812+2):ℕ),quarterBrunSieveLevel_tendsto.eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with n hn hy hp
  have hL:808*812+2≤Nat.log 2 n:=by
    have hh:=Nat.log_mono_right (b:=2) hn
    simpa only [Nat.log_pow (by decide : 1<2)] using hh
  clear hn
  let s:=Nat.log 2 n
  let j:=(s-2)/808
  have hhi:s+1≤j*809:=by change 808*812+2≤s at hL;dsimp only [j];omega
  have hlo:j*808+2≤s:=by
    calc j*808+2≤(s-2)+2 := Nat.add_le_add_right (Nat.div_mul_le_self _ _) 2
         _ = s := Nat.sub_add_cancel ((by decide : 2≤808*812+2).trans hL)
  let y:=quarterBrunSieveLevel n
  have hq : (y^202)^4≤n/4 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    change ((2^j)^202)^4*4≤n
    calc _ = 2^(j*808+2) := by rw [pow_add,←pow_mul,←pow_mul];congr 2
         _ ≤ 2^s := Nat.pow_le_pow_right (by decide) hlo
         _ ≤ _ := Nat.pow_log_le_self 2 (by omega)
  refine ⟨hy,?_,hq,?_⟩
  · have h1 : y≤y^202 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<y) (by decide : 1≤202)
    have hh : 0<y^202 := pow_pos (by omega) _
    have hh' : y^202≤(y^202)^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hh (by decide : 1≤4)
    exact h1.trans (hh'.trans hq)
  · change n < (2^j)^809
    rw [←pow_mul]
    exact (Nat.lt_pow_succ_log_self (by decide) n).trans_le (Nat.pow_le_pow_right (by decide) hhi)

theorem rough_complement_cardFactors_le {n y k K:ℕ} (hk:k∈fixedTargetBrunPrimeSurvivors n y)
    (hy:1≤y) (hK:n<y^(K+1)) : ArithmeticFunction.cardFactors (n-k)≤K := by
  obtain ⟨hi,_,hr⟩:=mem_filter.mp hk
  have hi':=mem_Ioc.mp hi
  have hn:0<n-k := by omega
  have hp:y^(ArithmeticFunction.cardFactors (n-k))≤n-k := by
    refine le_trans ?_ (Nat.prod_primeFactorsList hn.ne').le
    rw [ArithmeticFunction.cardFactors_apply]
    apply List.pow_length_le_prod
    intro p h
    exact le_of_lt (lt_of_not_ge (fun hh=>hr p (Nat.prime_of_mem_primeFactorsList h) hh (Nat.dvd_of_mem_primeFactorsList h)))
  by_contra! hs
  exact (not_lt_of_ge ((Nat.pow_le_pow_right (by omega : 0<y) hs).trans (hp.trans (Nat.sub_le ..)))) hK


def BrunQuarterDistribution : Prop :=
  ∀ A:ℕ, ∃ C:ℝ, 0<C ∧ ∀ᶠ u:ℕ in atTop, ∀ Q:ℕ,Q^4≤u →
    (∑q∈Icc 1 Q,brunPrimePrefixMaxError u q)≤C*u/(Real.log u)^A

theorem quarterBrunDistributionError_small (hb:BrunQuarterDistribution) :
    ∀ᶠ n:ℕ in atTop, fixedTargetBrunDistributionError n ((quarterBrunSieveLevel n)^202)
      ≤(n:ℝ)/(8192*Real.log n) := by
  obtain ⟨C,hC,hp⟩:=hb 2
  obtain ⟨T,hT⟩:=eventually_atTop.mp hp
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [quarterBrunSieveLevel_geometry,eventually_ge_atTop (4*T),
    eventually_ge_atTop (40:ℕ),hl.eventually_ge_atTop (65536*C)] with n hg ht hn hl'
  let D:=(quarterBrunSieveLevel n)^202
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
    apply (hT u (by omega) D (hg.2.2.1.trans hu)).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hlog) (sq_pos_of_pos hL)).mpr
    calc _ ≤ (C*u)*(4*(Real.log u)^2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
         _ ≤ (C*n)*(4*(Real.log u)^2) := by gcongr
         _ = _ := by ring
  apply (fixedTargetBrunDistributionError_le_prefix_max n D).trans
  apply (add_le_add (hsc (n/2) (by omega) (Nat.div_le_self ..)) (hsc (n/4) le_rfl (Nat.div_le_self ..))).trans
  have hbound:65536*C≤L:=hl'
  rw [←two_mul,le_div_iff₀ (by positivity),mul_div_assoc',div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hL)]
  nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hL.le) (sub_nonneg.mpr hbound)]

theorem quarterBrun_rough_mass (hb:BrunQuarterDistribution) :
    ∀ᶠ n:ℕ in atTop, Even n →
      (n:ℝ)/(8192*Real.log n)≤fixedTargetBrunSurvivorMass n (quarterBrunSieveLevel n) := by
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [quarterBrunSieveLevel_geometry,quarterBrunDistributionError_small hb,
    eventually_ge_atTop (20:ℕ),hl.eventually_ge_atTop 1] with n hg he hn hl'
  intro hev
  let y:=quarterBrunSieveLevel n
  let B:=fixedTargetBrunPrimes n y
  let L:=Real.log (n:ℝ)
  have hL:1≤L:=hl'
  have hLp:0<L:=zero_lt_one.trans_le hL
  have hy:2≤y:=hg.1
  have hyn:y≤n/4:=hg.2.1
  have hB (p:ℕ)(hp:p∈B) : p∈Icc 3 y ∧ p.Prime := by
    obtain ⟨hm,hpr,hd⟩:=mem_filter.mp hp
    have hne:p≠2:=fun h=>hd (h ▸ even_iff_two_dvd.mp hev)
    exact ⟨mem_Icc.mpr ⟨by have:=hpr.two_le;omega,mem_range_succ_iff.mp hm⟩,hpr⟩
  have heul:=brunEuler_product_log_lower y B (fun p hp=>(hB p hp).1) (fun p hp=>(hB p hp).2)
  have hly:Real.log y≤L:=Real.log_le_log (by exact_mod_cast (show 0<y by omega)) (by exact_mod_cast (show y≤n by omega))
  have he2:1/(256*L)≤∏p∈B,(1-brunEulerWeight p) :=
    (one_div_le_one_div_of_le (by positivity) (by linarith only [hly,hL])).trans heul
  have hlen:(n:ℝ)/16≤((n/2-n/4:ℕ):ℝ)/2 := by
    have hh:(n:ℝ)≤8*((n/2-n/4:ℕ):ℝ):=by exact_mod_cast (show n≤8*(n/2-n/4) by omega)
    linarith only [hh]
  have hh:=mul_le_mul hlen he2 (by positivity) (by positivity)
  have hh':(n:ℝ)/(4096*L)≤((n/2-n/4:ℕ):ℝ)/2*(∏p∈B,(1-brunEulerWeight p)) := by
    apply le_trans _ hh
    apply le_of_eq
    field_simp;ring
  have hmass:=fixedTarget_Brun_mass_of_distribution_any_cutoff n y hev hyn hy
  have hd : (n:ℝ)/(4096*L)=2*((n:ℝ)/(8192*L)) := by field_simp;ring
  rw [hd] at hh'
  change _≤(n:ℝ)/(8192*L) at he
  change _-_≤_ at hmass
  change (n:ℝ)/(8192*L)≤_
  linarith only [hh',he,hmass]


open private sf_inverse_tail from VerifiedSquarefreeBrunSurvivors

theorem quarterBrun_nonsquarefree_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,fixedTargetNonsquarefreeMass n (quarterBrunSieveLevel n) ≤ ε*n/Real.log n := by
  have ht : Tendsto (fun z:ℕ=>(Real.log z)^2/(z:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [quarterBrunSieveLevel_geometry,quarterBrunSieveLevel_tendsto.eventually
    (ht.eventually_lt_const (show 0<ε/(2*809^2:ℝ) by positivity)),eventually_ge_atTop (2:ℕ)] with n hg hs hn
  let y:=quarterBrunSieveLevel n
  let L:=Real.log (n:ℝ)
  have hy:2≤y:=hg.1
  have hy0:(0:ℝ)<y:=by exact_mod_cast (show 0<y by omega)
  have hL : 0<L:=Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hly:=Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hg.2.2.2.le : (n:ℝ)≤(y:ℝ)^809)
  rw [Real.log_pow] at hly
  have hsq:=pow_le_pow_left₀ hL.le hly 2
  have hs' : (Real.log y)^2<ε/(2*809^2:ℝ)*y := (div_lt_iff₀ hy0).mp hs
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

theorem quarterBrun_squarefree_almost_primes :
    ∀ᶠ n:ℕ in atTop,Even n →
      let y:=quarterBrunSieveLevel n
      let S:=fixedTargetBoundedFactorPrimes n y 808
      (n:ℝ)/(16384*Real.log n) ≤ ∑k∈S,Real.log k ∧
      (n:ℝ)/(16384*(Real.log n)^2) ≤ (S.card:ℝ) := by
  filter_upwards [quarterBrun_rough_mass prime_progressions_quarter_level,quarterBrunSieveLevel_geometry,
    quarterBrun_nonsquarefree_small (ε:=1/16384) (by norm_num),eventually_ge_atTop (2:ℕ)]
    with n hm hg he hn
  intro hev
  let y:=quarterBrunSieveLevel n
  let S:=fixedTargetBoundedFactorPrimes n y 808
  let L:=Real.log (n:ℝ)
  have hL : 0<L:=Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hcut : S = (fixedTargetBrunPrimeSurvivors n y).filter (fun k=>Squarefree (n-k)) := by
    apply filter_eq_self.mpr
    intro k hk
    exact rough_complement_cardFactors_le (mem_filter.mp hk).1 (by have:=hg.1;change 2≤y at this;omega) hg.2.2.2
  have hid: (∑k∈S,Real.log k)+fixedTargetNonsquarefreeMass n y=fixedTargetBrunSurvivorMass n y := by
    rw [hcut]
    exact fixedTarget_squarefree_partition n y
  have hh:=hm hev
  have hnume : (n:ℝ)/(8192*L)=(n:ℝ)/(16384*L)+(n:ℝ)/(16384*L) := by field_simp;ring
  change (n:ℝ)/(8192*L)≤fixedTargetBrunSurvivorMass n y at hh
  have he':fixedTargetNonsquarefreeMass n y≤(n:ℝ)/(16384*L):= by
    change fixedTargetNonsquarefreeMass n y≤1/16384*(n:ℝ)/L at he
    apply he.trans_eq
    field_simp
  rw [hnume] at hh
  have hmass:(n:ℝ)/(16384*L)≤∑k∈S,Real.log k := by linarith only [hh,he',hid]
  refine ⟨hmass,?_⟩
  have hlog:(∑k∈S,Real.log k)≤(S.card:ℝ)*L := by
    calc _ ≤ ∑_k∈S,L := by
           apply sum_le_sum;intro k hk
           obtain ⟨_,hk',hp,-⟩:=(boundedFactorPrimes_iff n y 808 k).mp hk
           exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show k≤n by omega))
         _ = _ := by simp
  change (n:ℝ)/(16384*L^2)≤_
  apply (div_le_iff₀ (by positivity)).mpr
  have hfinal: (n:ℝ)≤(S.card:ℝ)*L*(16384*L) := (div_le_iff₀ (by positivity)).mp (hmass.trans hlog)
  apply hfinal.trans_eq
  ring

end GoldbachPartial
