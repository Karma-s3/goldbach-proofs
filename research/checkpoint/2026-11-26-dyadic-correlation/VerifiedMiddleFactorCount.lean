import VerifiedQuarterLevelAlmostPrimes
import FixedTargetMarkedPrimeMass

namespace GoldbachPartial
open Finset Filter
open scoped Classical

def middleBrunPrimes (n y w : ℕ) : Finset ℕ :=
  (Ioc y w).filter (fun r => r.Prime ∧ ¬ r ∣ n)

private theorem large_prime_factor_count {m w B : ℕ} (hm : 0 < m) (hw : 1 ≤ w)
    (hB : m < w^(B+1)) : (m.primeFactors.filter (fun r => w<r)).card ≤ B := by
  let S := m.primeFactors.filter (fun r => w<r)
  have hh : w^S.card ≤ ∏ r ∈ S, r := by
    rw [← Finset.prod_const]
    exact prod_le_prod (fun r hr => (mem_filter.mp hr).2.le)
  have hdv : (∏ r ∈ S, r) ∣ m :=
    (prod_dvd_prod_of_subset _ _ id (filter_subset ..)).trans (Nat.prod_primeFactors_dvd m)
  by_contra! h
  have hb := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hw) (show B+1≤S.card from h)
  exact (not_lt_of_ge (hb.trans (hh.trans (Nat.le_of_dvd hm hdv)))) hB

/-- A rough square-free complement can have at most B factors above w.
Every other factor contributes to the count in the middle range. -/
theorem rough_middle_factor_count {n y w B k : ℕ} (hk : k ∈ fixedTargetBrunPrimeSurvivors n y)
    (hsf : Squarefree (n-k)) (hw : 1≤w) (hwn : w≤n/4) (hB : n<w^(B+1)) :
    ArithmeticFunction.cardFactors (n-k) ≤ B + ((middleBrunPrimes n y w).filter (fun r => r∣n-k)).card := by
  obtain ⟨hi,hp,hs⟩ := mem_filter.mp hk
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hi
  have hm : 0<n-k := by omega
  have he := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hm.ne').mpr hsf
  rw [←he,ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  let S := (n-k).primeFactors
  have hlarge := large_prime_factor_count hm hw ((Nat.sub_le n k).trans_lt hB)
  have hsmall : S.filter (fun r => ¬w<r) ⊆ (middleBrunPrimes n y w).filter (fun r => r∣n-k) := by
    intro r hr
    obtain ⟨hr,hwr⟩ := mem_filter.mp hr
    have hp' := Nat.prime_of_mem_primeFactors hr
    have hd := Nat.dvd_of_mem_primeFactors hr
    have hyl : y<r := lt_of_not_ge (fun h => hs r hp' h hd)
    have hnd : ¬ r∣n := by
      intro hv
      have hdk : r∣k := by simpa only [Nat.sub_sub_self (by omega : k≤n)] using Nat.dvd_sub hv hd
      have he := (Nat.prime_dvd_prime_iff_eq hp' hp).mp hdk
      omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hyl,le_of_not_gt hwr⟩,hp',hnd⟩,hd⟩
  have hc := card_filter_add_card_filter_not (s:=S) (fun r => w<r)
  change S.card ≤ _
  rw [←hc]
  exact Nat.add_le_add hlarge (card_le_card hsmall)

/-- Markov's inequality for genuinely distinct middle prime divisors of each
square-free complement. The sum on the right counts marked primes only once. -/
theorem middle_excess_mass_le {n y w B M : ℕ} (hw : 1≤w) (hwn : w≤n/4) (hB : n<w^(B+1)) :
    (M:ℝ) * fixedTargetExcessFactorMass n y (B+M) ≤ fixedTargetMarkedPrimeMass n y (middleBrunPrimes n y w) := by
  let T := ((fixedTargetBrunPrimeSurvivors n y).filter (fun k => Squarefree (n-k))).filter
    (fun k => ¬ ArithmeticFunction.cardFactors (n-k) ≤ B+M)
  let R := middleBrunPrimes n y w
  let S := fixedTargetBrunPrimeSurvivors n y
  rw [fixedTargetMarkedPrimeMass_by_complement]
  change (M:ℝ)*(∑ k∈T,Real.log k) ≤ ∑k∈S, ((R.filter (fun r => r∣n-k)).card:ℝ)*Real.log k
  rw [mul_sum]
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg
    (show T ⊆ S from (filter_subset ..).trans (filter_subset ..))
    (fun k _ _ => mul_nonneg (Nat.cast_nonneg (α:=ℝ) (R.filter (fun r => r∣n-k)).card) (Real.log_natCast_nonneg k)))
  apply sum_le_sum
  intro k hk
  obtain ⟨hh,hnf⟩ := mem_filter.mp hk
  obtain ⟨hs,hsf⟩ := mem_filter.mp hh
  have h := rough_middle_factor_count hs hsf hw hwn hB
  change ArithmeticFunction.cardFactors (n-k) ≤ B + (R.filter (fun r => r∣n-k)).card at h
  apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
  exact_mod_cast (show M ≤ (R.filter (fun r => r∣n-k)).card by omega)

/-- The error is uniform over every sieve support reaching at most the fourth
root of n/4, with both endpoints taken at the same fixed target n. -/
theorem fixedTargetQuarterError_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, D^4 ≤ n/4 →
    fixedTargetBrunDistributionError n D ≤ ε*(n:ℝ)/Real.log n := by
  obtain ⟨C,hC,hp⟩ := prime_progressions_quarter_level 2
  obtain ⟨T,hT⟩ := eventually_atTop.mp hp
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (4*T),eventually_ge_atTop (40:ℕ),
    hl.eventually_ge_atTop (8*C/ε)] with n ht hn hlog
  intro D hD
  let L := Real.log (n:ℝ)
  have hL : 0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsc (u : ℕ) (hu : n/4≤u) (hun : u≤n) :
      (∑ d ∈ Icc 1 D, brunPrimePrefixMaxError u d) ≤ 4*C*n/L^2 := by
    have hup : 0<Real.log (u:ℝ) := Real.log_pos (by exact_mod_cast (show 1<u by omega))
    have hnu : n≤u^2 := by nlinarith only [show n≤5*u by omega,show 5≤u by omega]
    have hcmp := Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hnu : (n:ℝ)≤(u:ℝ)^2)
    rw [Real.log_pow] at hcmp
    have hL2 : L^2≤4*(Real.log u)^2 := by
      have hh := pow_le_pow_left₀ hL.le hcmp 2
      norm_num at hh; linarith only [hh]
    apply (hT u (by omega) D (hD.trans hu)).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hup) (sq_pos_of_pos hL)).mpr
    calc _ ≤ (C*u)*(4*(Real.log u)^2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
         _ ≤ (C*n)*(4*(Real.log u)^2) := by gcongr
         _ = _ := by ring
  have he := (fixedTargetBrunDistributionError_le_prefix_max n D).trans
    (add_le_add (hsc (n/2) (by omega) (Nat.div_le_self ..)) (hsc (n/4) le_rfl (Nat.div_le_self ..)))
  have hc : 8*C ≤ L*ε := (div_le_iff₀ hε).mp hlog
  apply he.trans
  change _ ≤ ε*n/L
  rw [← add_div, div_le_div_iff₀ (sq_pos_of_pos hL) hL]
  nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hL.le)]

open private sf_inverse_tail from VerifiedSquarefreeBrunSurvivors

theorem rough_nonsquarefree_mass_le (n y : ℕ) (hy : y≤n/4) :
    fixedTargetNonsquarefreeMass n y ≤ ((n:ℝ)*Real.log n)*(2/((y:ℝ)+1)) := by
  have h := fixedTargetNonsquarefree_split n y y hy
  simp only [Ioc_self,filter_empty,sum_empty,zero_add] at h
  apply h.trans
  calc _ ≤ ∑ p ∈ Ioc y n, ((n:ℝ)*Real.log n)*(1/(p:ℝ)^2) := by
         apply sum_le_sum
         intro p _
         apply (fixedTargetDivisorRow_trivial n (p^2)).trans_eq
         push_cast; ring
       _ = ((n:ℝ)*Real.log n)*(∑ p ∈ Ioc y n, 1/(p:ℝ)^2) := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (sf_inverse_tail y n) (by positivity)

theorem rough_nonsquarefree_power_small (y : ℕ → ℕ) (K : ℕ) (ht : Tendsto y atTop atTop)
    (hgeo : ∀ᶠ n : ℕ in atTop, y n ≤ n/4 ∧ n ≤ (y n)^K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, fixedTargetNonsquarefreeMass n (y n) ≤ ε*(n:ℝ)/Real.log n := by
  have ht' : Tendsto (fun m : ℕ => (Real.log m)^2/(m:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  let k : ℝ := K+1
  have hk : 0<k := by dsimp [k]; positivity
  filter_upwards [ht.eventually (ht'.eventually_lt_const (show 0<ε/(2*k^2) by positivity)),
    ht.eventually_ge_atTop 2,hgeo,eventually_ge_atTop (2:ℕ)] with n h hy hg hn
  let Y := y n
  let L := Real.log (n:ℝ)
  have hL : 0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hY : (0:ℝ)<Y := by exact_mod_cast (show 0<y n by omega)
  have hlog := Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hg.2 : (n:ℝ)≤(Y:ℝ)^K)
  rw [Real.log_pow] at hlog
  have hlg : L≤k*Real.log Y := hlog.trans (mul_le_mul_of_nonneg_right (by dsimp [k];linarith) (Real.log_natCast_nonneg _))
  have hsq := pow_le_pow_left₀ hL.le hlg 2
  have hε' := (div_lt_iff₀ hY).mp h
  have hε'' : (2*k^2)*(Real.log Y)^2 < ε*Y := by
    calc _ < (2*k^2)*((ε/(2*k^2))*Y) := mul_lt_mul_of_pos_left hε' (by positivity)
         _ = _ := by field_simp
  have ha : 2*L^2 ≤ ε*((Y:ℝ)+1) := by nlinarith only [hsq,hε'',hε]
  apply (rough_nonsquarefree_mass_le n (y n) hg.1).trans
  change ((n:ℝ)*L)*(2/((Y:ℝ)+1)) ≤ ε*n/L
  rw [←mul_div_assoc, div_le_div_iff₀ (by positivity) hL]
  nlinarith only [mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α:=ℝ) n)]

private theorem middle_survivor_model_floor (n y : ℕ) (hn : 20≤n) (he : Even n) (hy : 2≤y)
    (hyn : y≤n/4) (hL : 1≤Real.log n) :
    (n:ℝ)/(2048*Real.log n) ≤ ((n/2-n/4:ℕ):ℝ) *
      ∏ p ∈ fixedTargetBrunPrimes n y, (1-brunEulerWeight p) := by
  let B := fixedTargetBrunPrimes n y
  have hp (p : ℕ) (h : p ∈ B) : 3 ≤ p ∧ p ≤ y ∧ p.Prime := by
    obtain ⟨hm,hpr,hd⟩ := mem_filter.mp h
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact ⟨by have := hpr.two_le;omega, mem_range_succ_iff.mp hm,hpr⟩
  have heul := brunEuler_product_log_lower y B
    (fun p h => mem_Icc.mpr ⟨(hp p h).1,(hp p h).2.1⟩) (fun p h => (hp p h).2.2)
  have hlog := Real.log_le_log (show 0<(y:ℝ) by exact_mod_cast (show 0<y by omega))
    (by exact_mod_cast (show y≤n by omega) : (y:ℝ)≤n)
  have hB : 1/(256*Real.log n) ≤ ∏p∈B, (1-brunEulerWeight p) :=
    (one_div_le_one_div_of_le (by positivity) (by linarith only [hlog,hL])).trans heul
  have hlen : (n:ℝ)/8 ≤ ((n/2-n/4:ℕ):ℝ) := by
    have ht : (n:ℝ)≤8*((n/2-n/4:ℕ):ℝ) := by exact_mod_cast (show n≤8*(n/2-n/4) by omega)
    linarith only [ht]
  apply le_trans _ (mul_le_mul hlen hB (by positivity) (by positivity))
  apply le_of_eq; ring

theorem middle_bounded_factor_lower {n y w B M : ℕ} (hw : 1≤w) (hwn : w≤n/4)
    (hB : n<w^(B+1)) (hM : 1≤M) {P E A : ℝ} (hP : 0≤P)
    (hA : 1+(8/7:ℝ)*A ≤ (M:ℝ)/2)
    (hlow : P/2-E ≤ fixedTargetBrunSurvivorMass n y)
    (hmarked : fixedTargetMarkedPrimeMass n y (middleBrunPrimes n y w) ≤ (8/7:ℝ)*P*A+E)
    (herror : 4*((M:ℝ)+1)*E ≤ P) (hsquare : 4*(M:ℝ)*fixedTargetNonsquarefreeMass n y ≤ P) :
    P/(2*M) ≤ ∑ k ∈ fixedTargetBoundedFactorPrimes n y (B+M), Real.log k := by
  let G := ∑ k ∈ fixedTargetBoundedFactorPrimes n y (B+M), Real.log k
  let F := fixedTargetExcessFactorMass n y (B+M)
  let S := fixedTargetNonsquarefreeMass n y
  have h := (middle_excess_mass_le hw hwn hB (M:=M) (y:=y)).trans hmarked
  have hsplit := fixedTarget_boundedFactor_partition n y (B+M)
  have htotal := fixedTarget_squarefree_partition n y
  have hg : P/2-E ≤ G+F+S := by rw [hsplit,htotal];exact hlow
  have hp := mul_le_mul_of_nonneg_right hA hP
  have hs := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) M)
  change (M:ℝ)*F ≤ _ at h
  change 4*(M:ℝ)*S ≤ P at hsquare
  change P/(2*M) ≤ G
  have hpos : (0:ℝ)<M := by exact_mod_cast hM
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hpos)).mpr
  linarith only [hs,h,herror,hsquare,hp]

/-- Convert the middle-divisor upper bound and the genuine distribution estimate
into a count of distinct primes at a single target. -/
theorem middle_power_sieve_count (J w : ℕ → ℕ) (B M K : ℕ) (hM : 1≤M)
    (A : ℝ) (hA : 1+(8/7:ℝ)*A ≤ (M:ℝ)/2)
    (ht : Tendsto (fun n => brunBlockBoundary (J n)) atTop atTop)
    (hgeo : ∀ᶠ n : ℕ in atTop, let y := brunBlockBoundary (J n)
      2≤y ∧ y≤w n ∧ w n≤n/4 ∧ (w n*y^101)^4≤n/4 ∧ n<(w n)^(B+1) ∧ n≤y^K)
    (hmark : ∀ᶠ n : ℕ in atTop, Even n →
      let y := brunBlockBoundary (J n)
      let P := ((n/2-n/4:ℕ):ℝ) * ∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)
      fixedTargetMarkedPrimeMass n y (middleBrunPrimes n y (w n)) ≤
        (8/7:ℝ)*P*A+fixedTargetBrunDistributionError n (w n*y^101)) :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (brunBlockBoundary (J n)) (B+M)
      (n:ℝ)/(4096*(M:ℝ)*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(4096*(M:ℝ)*(Real.log n)^2) ≤ (S.card:ℝ) := by
  let y := fun n => brunBlockBoundary (J n)
  let ε := 1/(8192*((M:ℝ)+1))
  have hε : 0<ε := by dsimp [ε];positivity
  have hsq := rough_nonsquarefree_power_small y K ht
    (hgeo.mono (fun n h => ⟨h.2.1.trans h.2.2.1,h.2.2.2.2.2⟩)) hε
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hgeo,hmark,hsq,fixedTargetQuarterError_uniform hε,
    eventually_ge_atTop (20:ℕ),hl.eventually_ge_atTop 1] with n hg hmk hs hdist hn hl'
  intro hev
  obtain ⟨hy,hyw,hwn,hD,hbig,_⟩ := hg
  let P := ((n/2-n/4:ℕ):ℝ)*∏p∈fixedTargetBrunPrimes n (y n),(1-brunEulerWeight p)
  let E := fixedTargetBrunDistributionError n (w n*(y n)^101)
  let L := Real.log (n:ℝ)
  have hL : 1≤L := hl'
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  have hw : 1≤w n := by omega
  have he : E≤ε*n/L := hdist _ hD
  have hsf : fixedTargetNonsquarefreeMass n (y n)≤ε*n/L := hs
  have hP : (n:ℝ)/(2048*L) ≤ P := middle_survivor_model_floor n (y n) hn hev hy (hyw.trans hwn) hL
  have hd : (y n)^101 ≤ w n*(y n)^101 := Nat.le_mul_of_pos_left _ hw
  have hlow := fixedTarget_Brun_mass_of_distribution n (y n) (J n) hev (hyw.trans hwn) le_rfl
  have hlow' : P/2-E≤fixedTargetBrunSurvivorMass n (y n) := by
    have hm := fixedTargetBrunDistributionError_mono n hd
    dsimp only [P,E] at *
    linarith only [hm,hlow]
  have hval : 4*((M:ℝ)+1)*(ε*(n:ℝ)/L) = (n:ℝ)/(2048*L) := by dsimp [ε];field_simp;ring
  have hbase : 4*((M:ℝ)+1)*E ≤ P :=
    (mul_le_mul_of_nonneg_left he (by positivity)).trans (hval.le.trans hP)
  have hbase' : 4*(M:ℝ)*fixedTargetNonsquarefreeMass n (y n) ≤ P := by
    have hz : 0≤ε*(n:ℝ)/L := by positivity
    exact (mul_le_mul (by linarith : 4*(M:ℝ)≤4*((M:ℝ)+1)) hsf
      (sum_nonneg fun k _ => Real.log_natCast_nonneg k) (by positivity)).trans (hval.le.trans hP)
  have hraw := middle_bounded_factor_lower hw hwn hbig hM ((by positivity : 0 ≤ (n:ℝ)/(2048*L)).trans hP)
    hA hlow' (hmk hev) hbase hbase'
  let S := fixedTargetBoundedFactorPrimes n (y n) (B+M)
  have hg : (n:ℝ)/(4096*(M:ℝ)*L) ≤ ∑k∈S,Real.log k := by
    refine le_trans ?_ ((div_le_div_of_nonneg_right hP (by positivity)).trans hraw)
    apply le_of_eq;field_simp;ring
  refine ⟨hg,?_⟩
  have hcard : (∑k∈S,Real.log k) ≤ (S.card:ℝ)*L := by
    calc
      _ ≤ ∑ _k∈S,L := by
        apply sum_le_sum
        intro k hk
        obtain ⟨_,hk',hp,-⟩ := (boundedFactorPrimes_iff n (y n) (B+M) k).mp hk
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show k≤n by omega))
      _ = _ := by simp
  change (n:ℝ)/(4096*(M:ℝ)*L^2) ≤ _
  apply (div_le_iff₀ (by positivity)).mpr
  exact ((div_le_iff₀ (by positivity)).mp (hg.trans hcard)).trans_eq (by ring)

end GoldbachPartial