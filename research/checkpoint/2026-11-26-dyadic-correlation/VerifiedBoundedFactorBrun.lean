import VerifiedSquarefreeBrunSurvivors
import GcdDilationFamily
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

noncomputable def brunComplementFactorLimit (n:ℕ):ℕ := ⌈6*Real.log (Real.log (n:ℝ))⌉₊

noncomputable def fixedTargetBoundedFactorPrimes (n z K:ℕ) : Finset ℕ :=
  ((fixedTargetBrunPrimeSurvivors n z).filter (fun k=>Squarefree (n-k))).filter
    (fun k=>ArithmeticFunction.cardFactors (n-k)≤K)

noncomputable def fixedTargetExcessFactorMass (n z K:ℕ):ℝ :=
  ∑k∈((fixedTargetBrunPrimeSurvivors n z).filter (fun k=>Squarefree (n-k))).filter
    (fun k=>¬ArithmeticFunction.cardFactors (n-k)≤K), Real.log k

theorem boundedFactorPrimes_iff (n z K k:ℕ) :
    k∈fixedTargetBoundedFactorPrimes n z K ↔
      n/4<k ∧ k≤n/2 ∧ k.Prime ∧ (∀p:ℕ,p.Prime→p≤z→¬p∣n-k) ∧
      Squarefree (n-k) ∧ ArithmeticFunction.cardFactors (n-k)≤K := by
  simp only [fixedTargetBoundedFactorPrimes,fixedTargetBrunPrimeSurvivors,mem_filter,mem_Ioc]
  tauto

theorem squarefree_two_pow_factors_le {m:ℕ} (hm:Squarefree m) : 2^(ArithmeticFunction.cardFactors m)≤m.divisors.card := by
  have hh := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hm.ne_zero).mpr hm
  rw [←hh,ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,←card_powerset]
  apply card_le_card_of_injOn (fun t:Finset ℕ=>∏p∈t,p)
  · intro t ht
    exact Nat.mem_divisors.mpr ⟨(prod_dvd_prod_of_subset _ _ id (mem_powerset.mp ht)).trans (Nat.prod_primeFactors_dvd m),hm.ne_zero⟩
  · intro t ht u hu he
    have h₁:=mem_powerset.mp ht
    have h₂:=mem_powerset.mp hu
    exact (Nat.primeFactors_prod (fun p hp=>Nat.prime_of_mem_primeFactors (h₁ hp))).symm.trans
      ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (fun p hp=>Nat.prime_of_mem_primeFactors (h₂ hp))))

theorem fixedTargetExcessFactor_bound (n z K:ℕ) :
    fixedTargetExcessFactorMass n z K ≤ (n:ℝ)*Real.log n*(1+Real.log n)/(2:ℝ)^K := by
  let S:=((fixedTargetBrunPrimeSurvivors n z).filter (fun k=>Squarefree (n-k))).filter
    (fun k=>¬ArithmeticFunction.cardFactors (n-k)≤K)
  let f (k:ℕ):ℕ:=n-k-1
  have hrs (k:ℕ) (hk:k∈S) : n/4<k ∧ k≤n/2 := mem_Ioc.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hk).1).1).1
  have hfs (k:ℕ) (hk:k∈S) : f k+1=n-k := by dsimp [f];have := hrs k hk;omega
  have hmap : Set.MapsTo f S (range n) := by
    intro k hk
    have hh:=hrs k hk
    apply mem_range.mpr
    dsimp [f];omega
  have hinj : (S:Set ℕ).InjOn f := by
    intro k hk l hl he
    have h₁:=hrs k hk;have h₂:=hrs l hl;dsimp [f] at he;omega
  have hb : (∑k∈S,((n-k).divisors.card:ℝ))≤(n:ℝ)*(1+Real.log n) := by
    calc _ = ∑j∈S.image f,((j+1).divisors.card:ℝ) := by
           rw [sum_image (by exact fun k hk l hl h=>hinj hk hl h)]
           exact sum_congr rfl (fun k hk=>by rw [hfs k hk])
         _ ≤ ∑j∈range n,((j+1).divisors.card:ℝ) := sum_le_sum_of_subset_of_nonneg
           (fun j hj=>by obtain ⟨k,hk,rfl⟩:=mem_image.mp hj;exact hmap hk) (fun _ _ _=>by positivity)
         _ ≤ _ := divisorCard_sum_le_log n
  apply (le_div_iff₀ (by positivity)).mpr
  change (∑k∈S,Real.log k)*(2:ℝ)^K≤_
  rw [sum_mul]
  calc _ ≤ ∑k∈S,Real.log n*((n-k).divisors.card:ℝ) := by
         apply sum_le_sum;intro k hk
         have hh:=hrs k hk
         have hk' : 0<k := by omega
         have hlarge := (mem_filter.mp hk).2
         have hsf := (mem_filter.mp (mem_filter.mp hk).1).2
         have h2 : (2:ℕ)^K≤(n-k).divisors.card := (Nat.pow_le_pow_right (by decide) (by omega : K≤ArithmeticFunction.cardFactors (n-k))).trans (squarefree_two_pow_factors_le hsf)
         apply mul_le_mul (Real.log_le_log (by exact_mod_cast hk') (by exact_mod_cast (show k≤n by omega)))
           (by exact_mod_cast h2) (by positivity) (Real.log_natCast_nonneg n)
       _ = Real.log n*(∑k∈S,((n-k).divisors.card:ℝ)) := (mul_sum ..).symm
       _ ≤ _ := by
         apply (mul_le_mul_of_nonneg_left hb (Real.log_natCast_nonneg n)).trans_eq
         ring

theorem fixedTarget_boundedFactor_partition (n z K:ℕ) :
    (∑k∈fixedTargetBoundedFactorPrimes n z K,Real.log k)+fixedTargetExcessFactorMass n z K =
      fixedTargetSquarefreeMass n z := sum_filter_add_sum_filter_not _ _ _

theorem brunComplementFactorLimit_pow {n:ℕ} (hL:1≤Real.log (n:ℝ)) :
    (Real.log n)^3 ≤ (2:ℝ)^(brunComplementFactorLimit n) := by
  let L := Real.log (n:ℝ)
  have hl : 0≤Real.log L := Real.log_nonneg hL
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have h2' : 1/2≤Real.log 2 := by norm_num at h2 ⊢;linarith
  have hk : 6*Real.log L≤(brunComplementFactorLimit n:ℝ) := Nat.le_ceil _
  rw [←Real.log_le_log_iff (pow_pos (zero_lt_one.trans_le hL) _) (by positivity),Real.log_pow,Real.log_pow]
  change (3:ℝ)*Real.log L≤(brunComplementFactorLimit n:ℝ)*Real.log 2
  nlinarith only [mul_le_mul_of_nonneg_right hk (by linarith only [h2'] : 0≤Real.log 2),
    mul_le_mul_of_nonneg_left h2' hl]

theorem fixedTargetExcessFactor_polylog_small (z:ℕ→ℕ) (A:ℕ)
    (hsize:∀ᶠ n:ℕ in atTop,(z n:ℝ)≤(Real.log n)^A) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, fixedTargetExcessFactorMass n (z n) (brunComplementFactorLimit n)
      ≤ ε*(n:ℝ)/(1+Real.log (z n)) := by
  let L := fun n:ℕ=>Real.log (n:ℝ)
  have hl : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h1 : Tendsto (fun n=>1/L n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hl
  have hlog : Tendsto (fun n=>Real.log (L n)/(L n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp hl)
  have ht : Tendsto (fun n=>(1+(A:ℝ)*Real.log (L n))/(L n)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using h1.add (hlog.const_mul (A:ℝ))
  filter_upwards [hl.eventually_ge_atTop 1,hsize,ht.eventually_lt_const (show 0<ε/2 by positivity)] with n hL hsz hs
  let D:=1+Real.log (z n)
  have hD : 0<D := by dsimp only [D];positivity
  have hL' : 0<L n := zero_lt_one.trans_le hL
  have hD' : D≤1+(A:ℝ)*Real.log (L n) := by
    apply add_le_add_right
    by_cases hz:z n=0
    · rw [hz];simp only [Nat.cast_zero,Real.log_zero];exact mul_nonneg (by positivity) (Real.log_nonneg hL)
    · have hh:=Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hsz
      simpa only [Real.log_pow] using hh
  have hcap := fixedTargetExcessFactor_bound n (z n) (brunComplementFactorLimit n)
  have hpow := brunComplementFactorLimit_pow hL
  have hn': 0≤(n:ℝ) := Nat.cast_nonneg _
  apply hcap.trans
  calc _ ≤ (n:ℝ)*(L n)*(1+L n)/(L n)^3 :=
         div_le_div_of_nonneg_left (by positivity) (pow_pos hL' _) hpow
       _ ≤ (2*(n:ℝ))/(L n) := by
         apply (div_le_div_iff₀ (pow_pos hL' _) hL').mpr
         nlinarith only [mul_nonneg (mul_nonneg hn' (sq_nonneg (L n))) (sub_nonneg.mpr hL)]
       _ ≤ _ := by
         apply (div_le_div_iff₀ hL' hD).mpr
         have hh := (div_lt_iff₀ hL').mp hs
         nlinarith only [mul_le_mul_of_nonneg_left hD' hn',mul_le_mul_of_nonneg_left hh.le hn']

theorem fixedTarget_boundedFactor_quality (z:ℕ→ℕ) (A:ℕ)
    (hsize:∀ᶠ n:ℕ in atTop,(z n:ℝ)≤(Real.log n)^A) {c:ℝ} (hc:0<c)
    (hm:∀ᶠ n:ℕ in atTop, Even n → c*(n:ℝ)/(1+Real.log (z n)) ≤ fixedTargetSquarefreeMass n (z n)) :
    ∀ᶠ n:ℕ in atTop, Even n →
      let S:=fixedTargetBoundedFactorPrimes n (z n) (brunComplementFactorLimit n)
      c*(n:ℝ)/(2*(1+Real.log (z n))) ≤ ∑k∈S,Real.log k ∧
      c*(n:ℝ)/(2*(1+Real.log (z n))*Real.log n) ≤ (S.card:ℝ) := by
  filter_upwards [fixedTargetExcessFactor_polylog_small z A hsize (ε:=c/2) (by positivity),
    hm,eventually_ge_atTop (2:ℕ)] with n he hmass hn
  intro hev
  let D:=1+Real.log (z n)
  let S:=fixedTargetBoundedFactorPrimes n (z n) (brunComplementFactorLimit n)
  have hD : 0<D := by dsimp only [D];positivity
  have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have htotal := fixedTarget_boundedFactor_partition n (z n) (brunComplementFactorLimit n)
  have hm' := hmass hev
  have hfin : c*(n:ℝ)/(2*D)≤ ∑k∈S,Real.log k := by
    have hid : c*(n:ℝ)/D = c*n/(2*D)+(c/2)*n/D := by field_simp;ring
    change c*(n:ℝ)/D ≤ _ at hm'
    rw [hid] at hm'
    change _≤(c/2)*(n:ℝ)/D at he
    change (∑k∈S,Real.log k)+_=_ at htotal
    linarith only [htotal,hm',he]
  refine ⟨hfin,?_⟩
  have hh : (∑k∈S,Real.log k)≤(S.card:ℝ)*Real.log n := by
    calc _ ≤ ∑_k∈S,Real.log n := by
           apply sum_le_sum;intro k hk
           have h:= (boundedFactorPrimes_iff ..).mp hk
           exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast (show k≤n by omega))
         _ = _ := by simp
  rw [←div_div]
  exact (div_le_iff₀ hL).mpr (hfin.trans hh)


theorem fixedTarget_boundedFactor_quality_of_survivor (z:ℕ→ℕ) (A:ℕ)
    (hz:Tendsto z atTop atTop) (hsize:∀ᶠ n:ℕ in atTop,(z n:ℝ)≤(Real.log n)^A)
    {c:ℝ} (hc:0<c)
    (hm:∀ᶠ n:ℕ in atTop, Even n → c*(n:ℝ)/(1+Real.log (z n)) ≤ fixedTargetBrunSurvivorMass n (z n)) :
    ∀ᶠ n:ℕ in atTop, Even n →
      let S:=fixedTargetBoundedFactorPrimes n (z n) (brunComplementFactorLimit n)
      c*(n:ℝ)/(2*(1+Real.log (z n))) ≤ ∑k∈S,Real.log k ∧
      c*(n:ℝ)/(2*(1+Real.log (z n))*Real.log n) ≤ (S.card:ℝ) := by
  filter_upwards [fixedTargetNonsquarefree_polylog_small z A hz hsize (ε:=c/4) (by positivity),
    fixedTargetExcessFactor_polylog_small z A hsize (ε:=c/4) (by positivity),hm,eventually_ge_atTop (2:ℕ)]
    with n hsf hex hraw hn
  intro hev
  let D:=1+Real.log (z n)
  let S:=fixedTargetBoundedFactorPrimes n (z n) (brunComplementFactorLimit n)
  have hD : 0<D := by dsimp only [D];positivity
  have h1 := fixedTarget_squarefree_partition n (z n)
  have h2 := fixedTarget_boundedFactor_partition n (z n) (brunComplementFactorLimit n)
  have hraw' := hraw hev
  change c*(n:ℝ)/D≤_ at hraw'
  have hid : c*(n:ℝ)/D = c*n/(2*D)+2*((c/4)*n/D) := by field_simp;ring
  rw [hid] at hraw'
  change _≤(c/4)*(n:ℝ)/D at hsf hex
  change (∑k∈S,Real.log k)+_=_ at h2
  have hfin : c*(n:ℝ)/(2*D)≤ ∑k∈S,Real.log k := by linarith only [hraw',h1,h2,hsf,hex]
  refine ⟨hfin,?_⟩
  have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  rw [←div_div]
  apply (div_le_iff₀ hL).mpr (hfin.trans _)
  calc _ ≤ ∑_k∈S,Real.log n := by
         apply sum_le_sum;intro k hk
         have h:= (boundedFactorPrimes_iff ..).mp hk
         exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast (show k≤n by omega))
       _ = _ := by simp [S]

theorem fixedTarget_boundedFactor_nearPower :
    ∀ᶠ n:ℕ in atTop, Even n →
      let z:=brunNearPowerCutoff n
      let S:=fixedTargetBoundedFactorPrimes n z (brunComplementFactorLimit n)
      (n:ℝ)/(8192*(1+Real.log z)) ≤ ∑k∈S,Real.log k ∧
      (n:ℝ)/(8192*(1+Real.log z)*Real.log n) ≤(S.card:ℝ) := by
  have hh:=fixedTarget_boundedFactor_quality brunNearPowerCutoff 1 (c:=1/4096) (by
    filter_upwards [brunNearPower_parameters] with n hn
    have hne : brunNearPowerRank n≠0 := by obtain ⟨m,hm⟩:=hn.1;omega
    have h := (Nat.le_self_pow hne _).trans hn.2.2.1
    rw [pow_one]
    exact (by exact_mod_cast h : (brunNearPowerCutoff n:ℝ)≤(⌊Real.log n⌋₊:ℕ)).trans (Nat.floor_le (Real.log_natCast_nonneg n))) (by norm_num) (by
      filter_upwards [fixedTargetSquarefree_nearPower_mass] with n hn
      intro he
      convert hn he using 1
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring)
  filter_upwards [hh] with n hn
  intro he
  obtain ⟨h₁,h₂⟩:=hn he
  dsimp only
  constructor
  · apply le_trans _ h₁
    apply le_of_eq
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · apply le_trans _ h₂
    apply le_of_eq
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end GoldbachPartial
