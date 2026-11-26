import VerifiedFixedTargetBrunEulerSharp
import VerifiedRoughP2ParityGap
import VerifiedShortBrunTrueBounds
import VerifiedSevenFactorParameters
namespace GoldbachPartial
open Finset Filter
open scoped Classical

noncomputable def reflectedPrefixRow (n d : ℕ) : ℝ :=
  GoldbachMajorArc.classMass (n+1) d (n%d)

theorem prefix_shortBrun_error_sum (n J : ℕ) (B : Finset ℕ) (c : Finset ℕ→ℝ)
    (hprime : ∀p∈B,p.Prime ∧ ¬p∣n)
    (hc : ∀S⊆B,|c S|≤1)
    (hsupp : ∀S⊆B,c S≠0→(∏p∈S,p)≤(brunBlockBoundary J)^29) :
    let h : ℝ := n
    |(∑S∈B.powerset,c S*reflectedPrefixRow n (∏p∈S,p)) -
      h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p)| ≤
        ∑d∈Icc 1 ((brunBlockBoundary J)^29),brunPrimePrefixMaxError n d := by
  intro h
  let W := B.powerset.filter (fun S => c S≠0)
  let f := fun S : Finset ℕ => ∏p∈S,p
  let T := Icc 1 ((brunBlockBoundary J)^29)
  have hsub {S : Finset ℕ} (hw : S∈W) : S⊆B := mem_powerset.mp (mem_filter.mp hw).1
  have hpr {S : Finset ℕ} (hw : S∈W) : ∀p∈S,p.Prime := fun p hp => (hprime p (hsub hw hp)).1
  have hpf {S : Finset ℕ} (hw : S∈W) : (f S).primeFactors=S := Nat.primeFactors_prod (hpr hw)
  have him {S : Finset ℕ} (hw : S∈W) : f S∈T := by
    have hsize := hsupp S (hsub hw) (mem_filter.mp hw).2
    exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hpr hw p hp).pos),hsize⟩
  have hsum : (∑S∈W,brunPrimePrefixMaxError n (f S))≤ ∑d∈T,brunPrimePrefixMaxError n d := by
    apply sum_le_sum_of_injOn f
    · intro S hs S' hs' he
      exact (hpf hs).symm.trans ((congrArg Nat.primeFactors he).trans (hpf hs'))
    · intro d hd
      obtain ⟨S,hs,rfl⟩ := mem_image.mp hd
      exact him hs
    · intro _ _;exact le_rfl
    · intro _ _ _; exact brunPrimePrefixMaxError_nonneg ..
  have hfilter (g : Finset ℕ→ℝ) : (∑S∈W,c S*g S)=∑S∈B.powerset,c S*g S := by
    rw [sum_filter]
    apply sum_congr rfl
    intro S _
    by_cases hc : c S=0 <;> simp [hc]
  rw [←hfilter (fun S => reflectedPrefixRow n (∏p∈S,p)),←hfilter (fun S=>∏p∈S,brunEulerWeight p),
    mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans (le_trans ?_ hsum)
  apply sum_le_sum
  intro S hS
  change |c S*reflectedPrefixRow n (f S)-h*(c S*(∏p∈S,brunEulerWeight p))|≤brunPrimePrefixMaxError n (f S)
  rw [brunSubset_product_eulerWeight S (hpr hS)]
  have hcp : n.Coprime (f S) := Nat.coprime_prod_right_iff.mpr fun p hp =>
    ((hpr hS p hp).coprime_iff_not_dvd.mpr (hprime p (hsub hS hp)).2).symm
  have hm := Nat.mod_lt n (show 0<f S from prod_pos (fun p hp => (hpr hS p hp).pos))
  have hrow : |reflectedPrefixRow n (f S)-h/(f S).totient| ≤ brunPrimePrefixMaxError n (f S) := by
    unfold reflectedPrefixRow brunPrimePrefixMaxError
    apply le_trans _ (le_sup' _ (mem_range_succ_iff.mpr hm.le))
    rw [ite_eq_left ⟨hm,show (n % f S).Coprime (f S) by rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm];exact hcp⟩]
  apply le_trans _ hrow
  rw [show c S*reflectedPrefixRow n (f S)-h*(c S*(1/((f S).totient:ℝ))) =
    c S*(reflectedPrefixRow n (f S)-h/(f S).totient) by ring,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hc S (hsub hS))



/-- Upper sieve on the complete prime prefix. The cutoff excludes primes
strictly smaller than z, as in the rough two-factor candidate set. -/
theorem reflectedP2LogMass_sieve_upper (n z J : ℕ) (he : Even n) (hz : brunBlockBoundary J<z) :
    let y := brunBlockBoundary J
    let B := fixedTargetBrunPrimes n y
    reflectedP2LogMass n z ≤ (Real.log n)*((8/7:ℝ)*n*(∏p∈B,(1-brunEulerWeight p))+
      ∑d∈Icc 1 (y^29),brunPrimePrefixMaxError n d) := by
  let y := brunBlockBoundary J
  let B := fixedTargetBrunPrimes n y
  let c := brunShortOrdinaryBlockWeight J B
  let F := fun k : ℕ=>∑S∈B.powerset,if ∀p∈S,p∣n-k then c S else 0
  have hBpr (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hBle (p : ℕ) (hp : p∈B) : p≤y := mem_range_succ_iff.mp (mem_filter.mp hp).1
  have hB : B⊆Icc 3 y := by
    intro p hp
    have hh := (hBpr p hp).1.two_le
    have h2 : p≠2 := fun h => (hBpr p hp).2 (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by omega,hBle p hp⟩
  have hF (k : ℕ) : (if ∀p∈B,¬p∣n-k then (1:ℝ) else 0)≤F k := by
    convert brunShortOrdinaryBlock_majorizes J B hB (fun p => p∣n-k) using 1
    · split_ifs <;> rfl
    · apply sum_congr rfl;intro S _;split_ifs <;> rfl
  have hF0 (k : ℕ) : 0≤F k := (show 0≤(if ∀p∈B,¬p∣n-k then (1:ℝ) else 0) by split <;> norm_num).trans (hF k)
  have hw (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  let C := reflectedP2Set n z
  have hm (k : ℕ) (hk : k∈C) := (mem_filter.mp hk).2
  have hsurv (k : ℕ) (hk : k∈C) : 1≤F k := by
    have hno (p : ℕ) (hp : p∈B) (hd : p∣n-k) : False :=
      (hBle p hp).not_gt (hz.trans_le ((hm k hk).2.2.2 p (hBpr p hp).1 hd))
    simpa only [ite_eq_left hno] using hF k
  have hbound : reflectedP2LogMass n z ≤ (Real.log n)*∑k∈range (n+1),weight k*F k := by
    rw [mul_sum]
    change (∑k∈C,Real.log k*Real.log (n-k:ℕ)) ≤ _
    have hsub : C ⊆ range (n+1) := filter_subset ..
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _=>mul_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (hw k) (hF0 k))))
    apply sum_le_sum
    intro k hk
    have hpr := (hm k hk).1
    have hmpos := (hm k hk).2.1
    have hlog := Real.log_le_log (show 0<((n-k:ℕ):ℝ) by exact_mod_cast (by omega : 0<n-k)) (by exact_mod_cast Nat.sub_le n k : ((n-k:ℕ):ℝ)≤(n:ℝ))
    rw [weight,ite_eq_left hpr]
    calc _ ≤ Real.log k*Real.log n := mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg _)
         _ ≤ _ := by
           have hh := le_mul_of_one_le_right (Real.log_natCast_nonneg k) (hsurv k hk)
           linarith only [mul_le_mul_of_nonneg_left hh (Real.log_natCast_nonneg n)]
  have hrow (S : Finset ℕ) (hS : S∈B.powerset) :
      (∑k∈range (n+1),weight k*(if ∀p∈S,p∣n-k then c S else 0)) =
        c S*reflectedPrefixRow n (∏p∈S,p) := by
    let d := ∏p∈S,p
    unfold reflectedPrefixRow GoldbachMajorArc.classMass
    rw [sum_filter,mul_sum]
    apply sum_congr rfl
    intro k hk
    have hd := fixedTarget_prime_subset_product_dvd S (fun p hp=>(hBpr p (mem_powerset.mp hS hp)).1) (n-k)
    have heq : (∀p∈S,p∣n-k) ↔ k%d=n%d := hd.symm.trans (Nat.modEq_iff_dvd' (mem_range_succ_iff.mp hk)).symm
    change weight k*(if ∀p∈S,p∣n-k then c S else 0)=c S*(if k%d=n%d then weight k else 0)
    rw [if_congr heq rfl rfl]
    split_ifs <;> ring
  have heq : (∑k∈range (n+1),weight k*F k) = ∑S∈B.powerset,c S*reflectedPrefixRow n (∏p∈S,p) := by
    dsimp only [F];simp_rw [mul_sum];rw [sum_comm];exact sum_congr rfl hrow
  have hE := (abs_le.mp (prefix_shortBrun_error_sum n J B c hBpr (fun S _=>brunShortOrdinaryBlockWeight_abs_le J B S)
    (fun S hS hc => brunShortOrdinaryBlockWeight_level J B S hB hS hc))).2
  have hupper := mul_le_mul_of_nonneg_left (brunShortOrdinaryBlock_model_upper J B hB (fun p hp=>(hBpr p hp).1)) (Nat.cast_nonneg (α:=ℝ) n)
  rw [heq] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  change _ ≤ (8/7:ℝ)*n*(∏p∈B,(1-brunEulerWeight p))+_
  dsimp only [c] at hE ⊢
  linarith only [hE,hupper]

set_option exponentiation.threshold 2100 in
/-- A pointwise majorant with one power of n/φ(n), valid at every cutoff
z satisfying z^11≥n. The constant is uniform in the target and the cutoff. -/
theorem reflectedP2LogMass_singular_upper :
    ∀ᶠ n:ℕ in atTop, Even n → ∀ z:ℕ, n≤z^11 →
      reflectedP2LogMass n z ≤ 500*(n:ℝ)*((n:ℝ)/n.totient) := by
  obtain ⟨C,hC,hAP⟩ := prime_progressions_quarter_level 2
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [sevenBrun_geometry,hAP,ht.eventually_ge_atTop (max 1 C),eventually_ge_atTop (2:ℕ)] with n hg ha hL hn
  intro he z hz
  let y := sevenBrunSmall n
  let R := (n:ℝ)/n.totient
  let L := Real.log n
  let l := Real.log ((y:ℝ)+1)
  have hy : 2≤y := hg.1
  have hy1 : 1<y := hy
  have hn0 : 0<n := by omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn0
  have hy' : (0:ℝ)<y := by exact_mod_cast (by omega : 0<y)
  have hl : 0<l := Real.log_pos (by linarith only [hy'])
  change max 1 C ≤ L at hL
  have hLp : 0<L := zero_lt_one.trans_le ((le_max_left ..).trans hL)
  have hR : 1≤R := (one_le_div (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr (by exact_mod_cast Nat.totient_le n)
  have hh : (y^101)^19≤(n/4)^9 := hg.2.2.2.2.1
  have h116 : y^116≤n := by
    apply (Nat.pow_le_pow_iff_left (by decide : 9≠0)).mp
    calc _ ≤ (y^101)^19 := by
               rw [←pow_mul,←pow_mul]
               exact Nat.pow_le_pow_right (by omega) (by decide)
         _ ≤ _ := hh.trans (Nat.pow_le_pow_left (Nat.div_le_self n 4) 9)
  have hcut : y<z := by
    by_contra! h
    exact (Nat.pow_lt_pow_right hy1 (by decide : 11<116)).not_ge
      (h116.trans (hz.trans (Nat.pow_le_pow_left h 11)))
  have hpow : n≤y^432 := hg.2.2.2.2.2.2.2.1
  have hlog := Real.log_le_log hn' (by exact_mod_cast hpow : (n:ℝ)≤(y:ℝ)^432)
  rw [Real.log_pow] at hlog
  have hlog' : L≤432*l := by
    have h := Real.log_le_log hy' (by linarith : (y:ℝ)≤(y:ℝ)+1)
    dsimp only [L,l]
    norm_num at hlog
    linarith only [hlog,h]
  have hq : (y^29)^4≤n := by simpa only [←pow_mul,show 29*4=116 by decide] using h116
  have hdist := ha (y^29) hq
  have hpoly := fixedTarget_brunEuler_singular_upper n y hn0 (by omega)
  have hfull := reflectedP2LogMass_sieve_upper n z (sevenBrunIndex n) he hcut
  have hcost : L*(C*n/L^2) ≤ (n:ℝ) := by
    have hc := (le_max_right 1 C).trans hL
    calc _ = C/L*n := by field_simp
         _ ≤ 1*n := mul_le_mul_of_nonneg_right ((div_le_one hLp).mpr hc) hn'.le
         _ = _ := one_mul _
  have hR0 := zero_le_one.trans hR
  have hmain : L*((8/7:ℝ)*n*(R/l)) ≤ ((8/7:ℝ)*432)*(n:ℝ)*R := by
    calc _ = ((8/7:ℝ)*n*R)*(L/l) := by ring
         _ ≤ ((8/7:ℝ)*n*R)*432 := mul_le_mul_of_nonneg_left ((div_le_iff₀ hl).mpr hlog') (by positivity)
         _ = _ := by ring
  apply hfull.trans
  change L*((8/7:ℝ)*n*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))+_)≤_
  apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hpoly (by positivity)) hdist) hLp.le).trans
  change L*((8/7:ℝ)*n*(R/l)+C*n/L^2)≤500*(n:ℝ)*R
  rw [mul_add]
  have hnR := le_mul_of_one_le_right hn'.le hR
  linarith only [hmain,hcost,hnR,mul_nonneg hn'.le hR0]

end GoldbachPartial