import VerifiedMovingPrimeBands
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

open private primeFactor_log_sum_le from PrimeFactorLogMean

noncomputable def fullPrimeMarkedMass (n : ℕ) (P : Finset ℕ) : ℝ :=
  ∑k∈(range (n+1)).filter (fun k=>∃p∈P,p∣n-k),weight k

private theorem marked_nonneg (k:ℕ) : 0≤weight k := by
  unfold weight
  split <;> first | exact Real.log_natCast_nonneg _ | rfl

theorem fullPrimeMarkedMass_ap_upper (n D:ℕ) (P:Finset ℕ) (hn : 0<n)
    (hP : ∀p∈P,p.Prime ∧ p≤D) :
    fullPrimeMarkedMass n P ≤ (n:ℝ)*(∑p∈P,brunEulerWeight p)+
      ∑d∈Icc 1 D,brunPrimePrefixMaxError n d + Real.log n := by
  let R := P.filter (fun p=>¬p∣n)
  let T := P.filter (fun p=>p∣n)
  let row (p:ℕ) := ∑k∈(range (n+1)).filter (fun k=>p∣n-k),weight k
  have hm : fullPrimeMarkedMass n P ≤ ∑p∈P,row p := by
    unfold fullPrimeMarkedMass row
    rw [sum_filter]
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro k hk
    split_ifs with hh
    · obtain ⟨p,hp,hdiv⟩ := hh
      exact le_trans (by rw [ite_eq_left hdiv] : weight k ≤ (if p∣n-k then weight k else 0))
        (single_le_sum (f:=fun i=>if i∣n-k then weight k else 0) (fun i _ => by split <;> first | exact marked_nonneg k | rfl) hp)
    · apply sum_nonneg
      intro p _
      split <;> first | exact marked_nonneg k | rfl
  have hrow (p:ℕ) : row p=GoldbachMajorArc.classMass (n+1) p (n%p) := by
    unfold row GoldbachMajorArc.classMass
    simp_rw [sum_filter]
    apply sum_congr rfl
    intro k hk
    exact if_congr (Nat.modEq_iff_dvd' (mem_range_succ_iff.mp hk)).symm rfl rfl
  have hRsub : R ⊆ Icc 1 D := fun p hp => mem_Icc.mpr ⟨(hP p (mem_filter.mp hp).1).1.one_le,(hP p (mem_filter.mp hp).1).2⟩
  have hu (p:ℕ) (hp : p∈R) : row p≤(n:ℝ)*brunEulerWeight p+brunPrimePrefixMaxError n p := by
    obtain ⟨hpP,hd⟩ := mem_filter.mp hp
    have hpr := (hP p hpP).1
    have hc := (hpr.coprime_iff_not_dvd.mpr hd).symm
    have hcp : (n%p).Coprime p := by rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm]; exact hc
    have hmod := Nat.mod_lt n hpr.pos
    have hu : |GoldbachMajorArc.classMass (n+1) p (n%p)-(n:ℝ)/p.totient|≤brunPrimePrefixMaxError n p := by
      unfold brunPrimePrefixMaxError
      exact le_trans (by rw [ite_eq_left ⟨hmod,hcp⟩]) (le_sup' _ (mem_range_succ_iff.mpr hmod.le))
    rw [hrow]
    rw [Nat.totient_prime hpr] at hu
    rw [Nat.cast_sub hpr.one_le,Nat.cast_one] at hu
    unfold brunEulerWeight
    linarith only [(abs_le.mp hu).2,show (n:ℝ)*(1/((p:ℝ)-1))=n/(p-1:ℝ) by ring]
  have hTsub : T⊆n.primeFactors := by
    intro p hp
    obtain ⟨h0,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p h0).1,hd,hn.ne'⟩
  have hnon (p:ℕ) (hp:p∈T) : row p≤Real.log p := by
    obtain ⟨hpP,hd⟩ := mem_filter.mp hp
    have hpr := (hP p hpP).1
    unfold row
    have hmem : p ∈ (range (n+1)).filter (fun k=>p∣n-k) := mem_filter.mpr ⟨mem_range_succ_iff.mpr (Nat.le_of_dvd hn hd),Nat.dvd_sub hd (dvd_refl p)⟩
    rw [sum_eq_single_of_mem p hmem]
    · rw [weight,ite_eq_left hpr]
    · intro k hk hne
      obtain ⟨hk',hd'⟩ := mem_filter.mp hk
      have hkN := mem_range_succ_iff.mp hk'
      have hpk : p∣k := Nat.sub_sub_self hkN ▸ Nat.dvd_sub hd hd'
      have hnpr : ¬k.Prime := fun h=>hne ((Nat.prime_dvd_prime_iff_eq hpr h).mp hpk).symm
      simp [weight,hnpr]

  have hT : (∑p∈T,row p)≤Real.log n :=
    (sum_le_sum hnon).trans ((sum_le_sum_of_subset_of_nonneg hTsub (fun p _ _=>Real.log_natCast_nonneg p)).trans (primeFactor_log_sum_le n hn))
  have hsub : (∑p∈R,brunEulerWeight p)≤∑p∈P,brunEulerWeight p :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p hp _=> by
      unfold brunEulerWeight
      exact one_div_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast (hP p hp).1.one_le)))
  have hR : (∑p∈R,row p)≤(n:ℝ)*(∑p∈P,brunEulerWeight p)+∑d∈Icc 1 D,brunPrimePrefixMaxError n d := by
    apply (sum_le_sum hu).trans
    rw [sum_add_distrib,←mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _))
      (sum_le_sum_of_subset_of_nonneg hRsub (fun d _ _=>brunPrimePrefixMaxError_nonneg n d))
  apply hm.trans
  rw [←sum_filter_add_sum_filter_not P (fun p=>p∣n) row]
  change (∑p∈T,row p)+(∑p∈R,row p)≤_
  linarith

theorem movingPrimeCutoff_half_level {b : ℝ} (hb : b<1/2) (D : ℕ) :
    ∀ᶠ n:ℕ in atTop, (movingPrimeCutoff n b:ℝ)*(1+Real.log n)^D≤Real.sqrt n := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((2*D:ℕ):ℝ) (sub_pos.mpr hb))
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h,hln.eventually_ge_atTop (2:ℝ),eventually_ge_atTop (1:ℕ)] with n hs hL hn
  change (Real.log n)^((2*D:ℕ):ℝ)≤(n:ℝ)^((1/2:ℝ)-b) at hs
  rw [Real.rpow_natCast] at hs
  change 2≤Real.log n at hL
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hpow : (1+Real.log n)^D≤(Real.log n)^(2*D) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by linarith)
    nlinarith only [hL,sq_nonneg (Real.log n-2)]
  have hc : (movingPrimeCutoff n b:ℝ)≤(n:ℝ)^b := Nat.floor_le (by positivity)
  calc
    _ ≤ (n:ℝ)^b * (n:ℝ)^((1/2:ℝ)-b) := mul_le_mul hc (hpow.trans hs) (by positivity) (by positivity)
    _ = Real.sqrt n := by rw [←Real.rpow_add hn',add_sub_cancel,Real.sqrt_eq_rpow]

theorem movingPrimeBand_fullPrimeMarkedMass_small {a ε : ℝ} (ha:0<a) (ha' : a<1/2) (hε : 0<ε) :
    ∃ b:ℝ,a<b ∧ b<1/2 ∧ ∀ᶠ n:ℕ in atTop, fullPrimeMarkedMass n (movingPrimeBand n a b)≤ε*(n:ℝ) := by
  obtain ⟨b,hab,hb,hband⟩ := movingPrimeBand_arbitrarily_small ha ha' (show 0<ε/3 by linarith)
  obtain ⟨D,C,hC,hap⟩ := prime_progressions_half_level 1
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlittle := ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show 0<ε/3 by linarith)
  refine ⟨b,hab,hb,?_⟩
  filter_upwards [movingPrimeCutoff_half_level hb D,hap,hband,eventually_ge_atTop (2:ℕ),
    hln.eventually_ge_atTop (3*C/ε),hlittle] with n hsc hp hs hn hL ht
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hg : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  change Real.log n/(n:ℝ)<ε/3 at ht
  have ha1 := hp _ hsc
  rw [pow_one] at ha1
  have ha2 : C*n/Real.log n ≤ (ε/3)*n := by
    rw [div_le_iff₀ hg]
    change 3*C/ε ≤ Real.log n at hL
    nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hL) hn'.le]
  have h1 := fullPrimeMarkedMass_ap_upper n (movingPrimeCutoff n b) (movingPrimeBand n a b)
    (by omega) (fun p hp => ⟨(mem_filter.mp hp).2,(mem_Ioc.mp (mem_filter.mp hp).1).2⟩)
  linarith only [h1,ha1,ha2,mul_le_mul_of_nonneg_left hs hn'.le,(div_lt_iff₀ hn').mp ht]

end GoldbachPartial