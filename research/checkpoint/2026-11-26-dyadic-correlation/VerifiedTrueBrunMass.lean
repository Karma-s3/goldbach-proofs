import FixedTargetBrunBonferroni
import VerifiedBrunLogEulerTail
namespace GoldbachPartial
open scoped Topology
open Finset Filter

private theorem truncated_sieve_comparison
    (B : Finset ℕ) (K : ℕ) (a row : Finset ℕ→ℝ) (b : ℕ→ℝ)
    {mass error tail sift : ℝ} (hM : 0≤mass)
    (ha : ∀ t∈B.powerset,a t=∏p∈t,b p)
    (hpos : ∀ t∈B.powerset,0≤a t)
    (hrow : ∀ t∈B.powerset, t.card≤K → |row t-mass*a t|≤error)
    (htail : (∑t∈B.powerset.filter (fun t => K<t.card),a t)≤tail)
    (hbon : (∑t∈B.powerset.filter (fun t => t.card≤K),(-1:ℝ)^t.card*row t)≤sift) :
    mass*((∏p∈B,(1-b p))-tail)-
      (((B.powerset.filter (fun t => t.card≤K)).card:ℕ):ℝ)*error ≤ sift := by
  let I := B.powerset.filter (fun t => t.card≤K)
  let J := B.powerset.filter (fun t => K<t.card)
  let σ := fun t : Finset ℕ => (-1:ℝ)^t.card
  have hs (t : Finset ℕ) : |σ t|=1 := by simp [σ,abs_pow]
  have hfull : (∏p∈B,(1-b p))=∑t∈B.powerset,σ t*a t := by
    simp_rw [sub_eq_add_neg]
    rw [prod_one_add]
    apply sum_congr rfl
    intro t ht
    rw [ha t ht]
    simp only [σ,Finset.prod_neg]
  have hsplit : (∑ t∈I,σ t*a t)+(∑t∈J,σ t*a t)=∏p∈B,(1-b p) := by
    simpa only [I,J,not_le,hfull] using sum_filter_add_sum_filter_not B.powerset (fun t => t.card≤K) (fun t => σ t*a t)
  have habove : (∑t∈J,σ t*a t)≤tail := by
    apply le_trans _ htail
    apply sum_le_sum
    intro t ht
    have hp := hpos t (mem_filter.mp ht).1
    calc _ ≤ |σ t*a t| := le_abs_self _
         _ = _ := by rw [abs_mul,hs,abs_of_nonneg hp,one_mul]
  have hrow' : |(∑t∈I,σ t*row t)-mass*(∑t∈I,σ t*a t)|≤(I.card:ℝ)*error := by
    rw [mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _t∈I,error := by
        apply sum_le_sum
        intro t ht
        rw [show σ t*row t-mass*(σ t*a t)=σ t*(row t-mass*a t) by ring,abs_mul,hs,one_mul]
        exact hrow t (mem_filter.mp ht).1 (mem_filter.mp ht).2
      _ = _ := by simp
  have hc : (∏p∈B,(1-b p))-tail ≤ ∑ t∈I,σ t*a t := by linarith only [hsplit,habove]
  have hmul := mul_le_mul_of_nonneg_left hc hM
  change (∑ t∈I,σ t*row t)≤sift at hbon
  change mass*_- (I.card:ℝ)*error≤_
  linarith only [hmul,(abs_le.mp hrow').1,hbon]

private theorem rough_sieve_mass_comparison (E : ℕ→ℝ)
    (hE : ∀ z K : ℕ,∀ B : Finset ℕ, B⊆Icc 3 z → (∀ p∈B,p.Prime) →
      (∑t∈B.powerset.filter (fun t => K≤t.card),∏p∈t,brunEulerWeight p)≤ E z/(2:ℝ)^K)
    (hE0 : ∀ z,0≤E z) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,Even n → ∀ z K : ℕ,
      1≤z → z≤n/4 → Odd K → ((z^K:ℕ):ℝ)≤Real.log n →
      let B := fixedTargetBrunPrimes n z
      let h : ℝ := (n/2-n/4 : ℕ)
      h*((∏ p∈B,(1-brunEulerWeight p))-E z/(2:ℝ)^K)-C*n/(Real.log n)^7 ≤
        fixedTargetBrunSurvivorMass n z := by
  obtain ⟨C,hC,hrow⟩ := fixedTarget_Brun_subset_row 1 8
  refine ⟨C,hC,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hrow,hlog.eventually_ge_atTop 1] with n hn hL
  intro he z K hz hnz hk hlevel
  let B := fixedTargetBrunPrimes n z
  let I := B.powerset.filter (fun t => t.card≤K)
  let h : ℝ := (n/2-n/4:ℕ)
  let L := Real.log n
  let b := brunEulerWeight
  let a := fun t : Finset ℕ => ∏p∈t,b p
  let f := fun t : Finset ℕ => fixedTargetDivisorRow n (∏p∈t,p)
  have hb (p : ℕ) (hp:p∈B) : p.Prime ∧ p≤z ∧ ¬p∣n := by
    obtain ⟨hu,hp',hd⟩ := mem_filter.mp hp
    exact ⟨hp',by have := mem_range.mp hu;omega,hd⟩
  have hB : B⊆Icc 3 z := by
    intro p hp
    obtain ⟨hp',hz',hd⟩ := hb p hp
    have hne : p≠2 := fun e => hd (e ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hp'.two_le;omega,hz'⟩
  have hcard := truncatedPrimeSubsets_card B (K:=K) hz (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2.1)
  have hI : (I.card:ℝ)≤L := (by exact_mod_cast hcard : (I.card:ℝ)≤(z^K:ℕ)).trans hlevel
  have hbad := hE z (K+1) B hB (fun p hp => (hb p hp).1)
  have ha (t : Finset ℕ) (ht:t∈B.powerset) : 0≤a t :=
    prod_nonneg fun p hp => (brunEulerWeight_bounds (mem_Icc.mp (hB (mem_powerset.mp ht hp))).1).1
  have ht : (∑ t∈B.powerset.filter (fun t => K<t.card),a t) ≤ E z/(2:ℝ)^K := by
    apply hbad.trans
    apply div_le_div_of_nonneg_left (hE0 z) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hr (t : Finset ℕ) (ht' : t∈B.powerset) (hK : t.card≤K) :
      |f t-h*a t|≤C*n/L^8 := by
    have hpz : (∏ p∈t,p)≤z^K := calc
      _ ≤ ∏ _p∈t,z := prod_le_prod (fun p hp => (hb p (mem_powerset.mp ht' hp)).2.1)
      _ = z^t.card := by simp
      _ ≤ _ := Nat.pow_le_pow_right hz hK
    apply hn z t (mem_powerset.mp ht')
    simpa only [pow_one] using (by exact_mod_cast hpz : ((∏p∈t,p:ℕ):ℝ)≤(z^K:ℕ)).trans hlevel
  have hf := truncated_sieve_comparison B K a f b (mass:=h) (by dsimp [h];positivity)
    (fun _ _ => rfl) ha hr ht (fixedTarget_Brun_bonferroni n z K hk hnz)
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have he' : (I.card:ℝ)*(C*n/L^8)≤C*n/L^7 := calc
    _ ≤ L*(C*n/L^8) := mul_le_mul_of_nonneg_right hI (by positivity)
    _ = _ := by field_simp
  exact (sub_le_sub_left he' _).trans hf


private theorem brun_mass_with_density
    (hden : ∀ z : ℕ,∀ B : Finset ℕ, B⊆Icc 3 z → (∀p∈B,p.Prime) →
      1/(128*(1+Real.log z)) ≤ ∏p∈B,(1-brunEulerWeight p))
    (htail : ∀ z K : ℕ,∀ B : Finset ℕ, B⊆Icc 3 z → (∀p∈B,p.Prime) →
      (∑t∈B.powerset.filter (fun t => K≤t.card),∏p∈t,brunEulerWeight p)≤
        (4096*(1+Real.log z)^2)/(2:ℝ)^K) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ z K : ℕ,1≤z → Odd K → ((z^K:ℕ):ℝ)≤Real.log n →
      (2:ℝ)^22*(1+Real.log z)^3≤(2:ℝ)^K →
      (n:ℝ)/(2048*(1+Real.log z)) ≤ fixedTargetBrunSurvivorMass n z := by
  let E := fun z : ℕ => 4096*(1+Real.log z)^2
  obtain ⟨C,hC,hu⟩ := rough_sieve_mass_comparison E htail (fun z => by dsimp [E];positivity)
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hr : Tendsto (fun n:ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hu,hl.eventually_ge_atTop (max 1 (8192*C)),eventually_ge_atTop (20:ℕ),
    hr.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with n hh hL hN hsmall
  intro he z K hz hodd hlevel hpow
  let B := fixedTargetBrunPrimes n z
  let D := 1+Real.log z
  let L := Real.log n
  let m : ℝ := (n/2-n/4:ℕ)
  have h1 : (1:ℝ)≤L := (le_max_left 1 _).trans hL
  have hLp : 0<L := zero_lt_one.trans_le h1
  have hD : 0<D := by dsimp [D];positivity
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hK : K≠0 := by rintro rfl; simp at hodd
  have hzl : (z:ℝ)≤L := (by exact_mod_cast Nat.le_self_pow hK z : (z:ℝ)≤(z^K:ℕ)).trans hlevel
  have hzN : z≤n/4 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    exact_mod_cast (show (z:ℝ)*4≤n by linarith only [hzl,(div_lt_iff₀ hn').mp hsmall])
  have hB (p : ℕ) (hp:p∈B) : p.Prime ∧ p∈Icc 3 z := by
    obtain ⟨hm,hp',hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact ⟨hp',mem_Icc.mpr ⟨by have := hp'.two_le;omega,by have := mem_range.mp hm;omega⟩⟩
  have hV := hden z B (fun _ h => (hB _ h).2) (fun _ h => (hB _ h).1)
  have herr : E z/(2:ℝ)^K≤1/(1024*D) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    change (2:ℝ)^22*D^3≤_ at hpow
    dsimp [E]
    change (4096*D^2)*(1024*D)≤_
    nlinarith only [hpow]
  have hcore : 7/(1024*D) ≤ (∏p∈B,(1-brunEulerWeight p))-E z/(2:ℝ)^K := by
    change 1/(128*D)≤_ at hV
    have hre : 1/(128*D)-1/(1024*D)=7/(1024*D) := by field_simp; norm_num
    linarith only [hV,herr,hre]
  have hm : (n:ℝ)/5≤m := by
    have hnat : n≤5*(n/2-n/4) := by omega
    have hreal : (n:ℝ)≤5*m := by dsimp only [m];exact_mod_cast hnat
    linarith
  have hD' : D≤2*L := by
    have hz' := Real.log_le_sub_one_of_pos (by exact_mod_cast hz : 0<(z:ℝ))
    dsimp [D];linarith only [hz',hzl,hLp]
  have hcoef : 4096*C*D≤L^7 := by
    have hLC : 8192*C≤L := (le_max_right 1 _).trans hL
    have h1' := mul_le_mul_of_nonneg_left hD' (show 0≤4096*C by positivity)
    have h2' := mul_le_mul_of_nonneg_right hLC hLp.le
    exact le_trans (by nlinarith only [h1',h2'] : 4096*C*D≤L^2) (pow_le_pow_right₀ h1 (by decide))
  have herror : C*(n:ℝ)/L^7≤(n:ℝ)/(4096*D) := by
    apply (div_le_div_iff₀ (pow_pos hLp _) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoef hn'.le]
  have hbound := hh he z K hz hzN hodd hlevel
  have hmcore := mul_le_mul hm hcore (by positivity) (by dsimp [m];positivity)
  change m*(_ - _) - C*(n:ℝ)/L^7 ≤ fixedTargetBrunSurvivorMass n z at hbound
  have hx : (n:ℝ)/(2048*D)≤(n:ℝ)/5*(7/(1024*D))-(n:ℝ)/(4096*D) := by
    have hr' : 0≤(n:ℝ)/D := by positivity
    linarith only [show (n:ℝ)/(2048*D)=(n/D)/2048 by field_simp,
      show (n:ℝ)/5*(7/(1024*D))-(n:ℝ)/(4096*D)=(n/D)*(23/20480) by field_simp;ring,hr']
  exact hx.trans ((sub_le_sub hmcore herror).trans hbound)

theorem fixedTarget_Brun_power_rank_mass :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ z K : ℕ,1≤z → Odd K → ((z^K:ℕ):ℝ)≤Real.log n →
      (2:ℝ)^22*(1+Real.log z)^3≤(2:ℝ)^K →
      (n:ℝ)/(2048*(1+Real.log z)) ≤ fixedTargetBrunSurvivorMass n z := by
  apply brun_mass_with_density brunEuler_product_log_lower
  intro z K B hB hp
  apply (brunEuler_prime_powerset_tail z K B hB hp).trans_eq
  ring

end GoldbachPartial