import GRHTruePrimePrefix
import VerifiedConductorMean
namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology
open private primitive_conductor_row from VerifiedConductorMean

theorem primeUnitTransform_prefix {n:ℕ} [NeZero n] (hn:2≤n) (χ:DirichletCharacter ℂ n) (hχ:χ≠1) :
    star (primeUnitTransform n χ) = centeredPrimeArcTransform n (n-1) 0 (((n-1:ℕ):ℂ)+1) χ := by
  have hs:n-1+1=n:=by omega
  rw [centeredPrimeArcTransform,ite_eq_right hχ,sub_zero,weightedArcCharacterSum,hs,primeUnitTransform,star_sum]
  simp only [mul_zero,ExtendedArcCoefficient.E,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,star_mul',Complex.star_def,Complex.conj_ofReal]
  let f (k:ℕ):ℂ:=(weight k:ℂ)*star (χ (k:ZMod n))
  change (∑ u:(ZMod n)ˣ,(weight (u:ZMod n).val:ℂ)*star (χ (u:ZMod n)))=∑k∈range n,f k
  trans ∑u:(ZMod n)ˣ,f (u:ZMod n).val
  · simp [f]
  have hzero: (∑k∈(range n).filter (fun t=>¬ t.Coprime n),f k)=0 := by
    apply sum_eq_zero;intro k hk
    have hu:¬IsUnit (k:ZMod n):=fun h=>(mem_filter.mp hk).2 ((ZMod.isUnit_iff_coprime k n).mp h)
    simp [f,χ.map_nonunit hu]
  rw [←sum_filter_add_sum_filter_not (range n) (fun k=>k.Coprime n) f,hzero,add_zero]
  apply sum_nbij (fun u:(ZMod n)ˣ=>(u:ZMod n).val)
  · intro u _;exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime u⟩
  · intro a _ b _ h;exact Units.ext (ZMod.val_injective n h)
  · intro k hk
    obtain ⟨hr,hc⟩:=mem_filter.mp hk
    exact ⟨ZMod.unitOfCoprime k hc,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hr)⟩
  · intro u _;rfl

theorem native_nonprincipal_energy_of_uniform_psi (hψ:grhAllUniform):
    ∃ C:ℝ,0≤C ∧ ∀ (n:ℕ) [NeZero n],2≤n→∀ S:Finset (DirichletCharacter ℂ n),1∉S →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖ ≤
        (S.card:ℝ)*(C*(n:ℝ)*(Real.log (2*(n:ℝ)^2))^4) := by
  obtain ⟨K,hK,hpre⟩:=true_prime_prefix_uniform_of_grhAllUniform hψ
  refine ⟨K^2,sq_nonneg _,?_⟩
  intro n _ hn S hs
  have hpoint (χ:DirichletCharacter ℂ n)(hχ:χ∈S) :
      ‖χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖≤K^2*n*Real.log (2*(n:ℝ)^2)^4:=by
    have hh:=hpre n hn n le_rfl χ (n-1) (by omega)
    rw [←primeUnitTransform_prefix hn χ (fun he=>hs (he ▸ hχ)),norm_star] at hh
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]
    apply (mul_le_of_le_one_left (sq_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
    calc _ ≤ (K*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2)^2 := pow_le_pow_left₀ (norm_nonneg _) hh _
         _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)];ring
  exact (norm_sum_le ..).trans ((sum_le_sum hpoint).trans_eq (by simp))
theorem native_conductor_card {n D:ℕ} [NeZero n] (S:Finset (DirichletCharacter ℂ n))
    (hs:∀χ∈S,χ.conductor≤D) : (S.card:ℝ) ≤ n.divisors.card*(D:ℝ) := by
  classical
  let F (d:ℕ) (_:DirichletCharacter ℂ d) : ℝ := if d≤D then 1 else 0
  have hF d (χ:DirichletCharacter ℂ d) : 0≤F d χ := by dsimp [F];split <;> norm_num
  have h := primitive_conductor_row (Nat.pos_of_ne_zero (NeZero.ne n)) F hF
  have hmain : (S.card:ℝ) ≤ ∑χ:DirichletCharacter ℂ n,F χ.conductor χ.primitiveCharacter := by
    calc _ = ∑_χ∈S,(1:ℝ) := by simp
         _ = ∑χ∈S,F χ.conductor χ.primitiveCharacter := sum_congr rfl (fun χ hχ=>(ite_eq_left (hs χ hχ)).symm)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun χ _ _=>hF χ.conductor χ.primitiveCharacter)
  apply (hmain.trans h).trans
  calc _ ≤ ∑_d∈n.divisors,(D:ℝ) := by
         apply sum_le_sum;intro d hd
         let _ : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
         let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod d)ˣ) :=
           ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩, rootsOfUnity.isCyclic ..⟩
         by_cases hl:d≤D
         · simp only [F,ite_eq_left hl,sum_const,nsmul_eq_mul,mul_one]
           apply Nat.cast_le.mpr
           apply (card_le_univ _).trans
           rw [←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
           exact (Nat.totient_le _).trans hl
         · simp [F,hl]
       _ = _ := by simp

theorem native_conductor_energy_of_uniform_psi (hψ:grhAllUniform):
    ∃ C:ℝ,0≤C ∧ ∀ (n:ℕ) [NeZero n],2≤n→∀ (D:ℕ) (S:Finset (DirichletCharacter ℂ n)),
      1∉S → (∀χ∈S,χ.conductor≤D) →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖ ≤
        n.divisors.card*(D:ℝ)*(C*(n:ℝ)*(Real.log (2*(n:ℝ)^2))^4) := by
  obtain ⟨C,hC,hh⟩:=native_nonprincipal_energy_of_uniform_psi hψ
  exact ⟨C,hC,fun n _ hn D S hs hD=>(hh n hn S hs).trans
    (mul_le_mul_of_nonneg_right (native_conductor_card S hD) (by positivity))⟩

theorem native_divisor_power (k:ℕ) (hk:0<k) (n:ℕ) :
    n.divisors.card^k ≤ (k^k)^(2^k)*n := by
  classical
  by_cases hn:n=0
  · simp [hn,zero_pow hk.ne']
  let K(p:ℕ):ℕ:=if p<2^k then k^k else 1
  have hpoint (p:ℕ)(hp:p∈n.primeFactors) : (n.factorization p+1)^k ≤ K p*p^(n.factorization p) := by
    let a:=n.factorization p
    have hp2:= (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall:p<2^k
    · have hsize:a+1≤k*(a/k+1):=by have :=Nat.lt_mul_div_succ a hk;omega
      calc (a+1)^k ≤ (k*2^(a/k))^k := Nat.pow_le_pow_left (hsize.trans (Nat.mul_le_mul_left k Nat.lt_two_pow_self)) _
           _ = k^k * 2^((a/k)*k) := by rw [mul_pow,pow_mul]
           _ ≤ k^k*p^a := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self a k)).trans (Nat.pow_le_pow_left hp2 _))
           _ = _ := by simp [K,hsmall,a]
    · simp only [K,hsmall,ite_false,one_mul]
      calc _ ≤ (2^a)^k := Nat.pow_le_pow_left Nat.lt_two_pow_self _
           _ = (2^k)^a := by rw [←pow_mul,←pow_mul,Nat.mul_comm a k]
           _ ≤ _ := Nat.pow_le_pow_left (le_of_not_gt hsmall) _
  have hcard:(n.primeFactors.filter (fun p=>p<2^k)).card≤2^k:=by
    apply (card_le_card (t:=range (2^k)) (fun p hp=>mem_range.mpr (mem_filter.mp hp).2)).trans
    simp
  have hK:(∏p∈n.primeFactors,K p)≤(k^k)^(2^k):=by
    dsimp only [K];rw [←prod_filter,prod_const]
    exact Nat.pow_le_pow_right (pow_pos hk _) hcard
  rw [Nat.card_divisors hn,←prod_pow]
  calc _ ≤ ∏p∈n.primeFactors,(K p*p^(n.factorization p)) :=prod_le_prod hpoint
       _ = (∏p∈n.primeFactors,K p)*n:=by rw [prod_mul_distrib,←Nat.prod_primeFactors_pow_factorization hn]
       _ ≤ _:=Nat.mul_le_mul_right n hK

theorem native_divisor_eventually_rpow {δ:ℝ} (hδ:0<δ):
    ∀ᶠ n:ℕ in atTop,(n.divisors.card:ℝ)≤(n:ℝ)^δ := by
  obtain ⟨k,hk⟩:=exists_nat_gt (1/δ)
  have hkp:0<k:=by exact_mod_cast ((one_div_pos.mpr hδ).trans hk)
  have hpos:0<δ*(k:ℝ)-1:=by have :=(div_lt_iff₀ hδ).mp hk;nlinarith
  have ht: Tendsto (fun n:ℕ=>(n:ℝ)^(δ*(k:ℝ)-1)) atTop atTop :=
    (tendsto_rpow_atTop hpos).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (((k^k)^(2^k):ℕ):ℝ),eventually_ge_atTop (1:ℕ)] with n h hn
  have hn':0<(n:ℝ):=by exact_mod_cast hn
  apply le_of_pow_le_pow_left₀ hkp.ne' (Real.rpow_nonneg hn'.le _)
  calc _ ≤ (((k^k)^(2^k):ℕ):ℝ)*n := by exact_mod_cast native_divisor_power k hkp n
       _ ≤ (n:ℝ)^(δ*(k:ℝ)-1)*n := mul_le_mul_of_nonneg_right h hn'.le
       _ = _ := by rw [←Real.rpow_add_one hn'.ne',sub_add_cancel,Real.rpow_mul_natCast hn'.le]

private theorem native_character_log_pay (C:ℝ) (hC:0≤C) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ n:ℕ in atTop, 2*C*Real.log (2*(n:ℝ)^2)^4≤(n:ℝ)^δ := by
  have hlog: (fun x:ℝ=>Real.log x^4) =o[atTop] (fun x:ℝ=>x^δ) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (4:ℕ) hδ
  have h:=((hlog.const_mul_left (162*C)).bound (by norm_num : (0:ℝ)<1))
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually h,eventually_ge_atTop (2:ℕ)] with n hh hn
  have hn':0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hc:Real.log (2*(n:ℝ)^2)≤3*Real.log n:=by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    have hm:=Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤n by exact_mod_cast hn)
    norm_num;linarith
  have hd:0≤Real.log (2*(n:ℝ)^2):=Real.log_nonneg (by nlinarith [show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega),sq_nonneg ((n:ℝ)-1)])
  have hp:=pow_le_pow_left₀ hd hc 4
  have hh':162*C*Real.log n^4≤(n:ℝ)^δ:=by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤162*C*Real.log n^4),
      abs_of_nonneg (Real.rpow_nonneg hn'.le δ),one_mul] using hh
  exact (mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤2*C)).trans ((by ring : 2*C*(3*Real.log (n:ℝ))^4=162*C*Real.log n^4).le.trans hh')

theorem native_low_conductor_saving (hψ:grhAllUniform) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (S:Finset (DirichletCharacter ℂ n)), 1∉S →
      (∀χ∈S,(χ.conductor:ℝ)≤(n:ℝ)^(1-δ)) →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖/(n.totient:ℝ) ≤ (n:ℝ)^(1-δ/4) := by
  obtain ⟨C,hC,hE⟩:=native_conductor_energy_of_uniform_psi hψ
  let a:=δ/4
  have ha:0<a:=by dsimp [a];linarith
  filter_upwards [native_divisor_eventually_rpow ha,native_character_log_pay C hC ha,eventually_ge_atTop (2:ℕ)] with n hτ hlog hn
  intro _ S hs hS
  have hn':0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hφ:0<(n.totient:ℝ):=by exact_mod_cast Nat.totient_pos.mpr (show 0<n by omega)
  let D:=⌊(n:ℝ)^(1-δ)⌋₊
  have hD:(D:ℝ)≤(n:ℝ)^(1-δ):=Nat.floor_le (Real.rpow_nonneg hn'.le _)
  have he:=hE n hn D S hs (fun χ hχ=>Nat.le_floor (hS χ hχ))
  let τ:ℝ:=n.divisors.card
  have hratio:(n:ℝ)/n.totient ≤ 2*τ:=by
    apply (model_totient_ratio_le_divisor_reciprocals n (by omega)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc _ ≤ ∑_d∈n.divisors,(1:ℝ) := sum_le_sum (fun d hd=>inv_le_one_of_one_le₀ (by exact_mod_cast Nat.pos_of_mem_divisors hd))
         _ = τ := by simp [τ]
  calc _ ≤ (τ*(D:ℝ)*(C*n*Real.log (2*(n:ℝ)^2)^4))/(n.totient:ℝ) := div_le_div_of_nonneg_right he hφ.le
       _ = τ*(D:ℝ)*(C*Real.log (2*(n:ℝ)^2)^4)*((n:ℝ)/n.totient) := by ring
       _ ≤ τ*(D:ℝ)*(C*Real.log (2*(n:ℝ)^2)^4)*(2*τ) := mul_le_mul_of_nonneg_left hratio (by dsimp [τ];positivity)
       _ = τ*τ*(D:ℝ)*(2*C*Real.log (2*(n:ℝ)^2)^4) := by ring
       _ ≤ (n:ℝ)^a*(n:ℝ)^a*(n:ℝ)^(1-δ)*(n:ℝ)^a := by
         apply mul_le_mul _ hlog (by positivity) (by positivity)
         apply mul_le_mul _ hD (by positivity) (by positivity)
         exact mul_le_mul hτ hτ (by positivity) (by positivity)
       _ = _ := by
         simp only [←Real.rpow_add hn']
         congr 1
         dsimp [a];ring

theorem native_high_conductor_signed_reduction (hψ:grhAllUniform) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (S:Finset (DirichletCharacter ℂ n)), 1∉S →
      (∀χ∈S,(χ.conductor:ℝ)≤(n:ℝ)^(1-δ)) →
      ‖(∑χ∈(Finset.univ.erase 1) \ S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)) -
        ((n.totient:ℂ)*((corr n-(if Even n ∧ (n/2).Prime then Real.log ((n/2:ℕ):ℝ)^2 else 0):ℝ):ℂ)-
          (primeUnitMass n:ℂ)^2)‖/(n.totient:ℝ)≤(n:ℝ)^(1-δ/4) := by
  filter_upwards [native_low_conductor_saving hψ hδ,eventually_ge_atTop (2:ℕ)] with n h hn
  intro _ S hs hS
  have hsub:S⊆univ.erase 1:=fun χ hχ=>mem_erase.mpr ⟨fun he=>hs (he ▸ hχ),mem_univ _⟩
  let F (χ:DirichletCharacter ℂ n):ℂ:=χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)
  rw [←nonprincipal_energy_at_target n hn]
  change ‖(∑χ∈(univ.erase 1) \ S,F χ) - ∑χ∈univ.erase 1,F χ‖ / _ ≤ _
  have hsplit:(∑χ∈(univ.erase 1) \ S,F χ)+(∑χ∈S,F χ)=∑χ∈univ.erase 1,F χ := sum_sdiff hsub
  have hdiff: (∑χ∈(univ.erase 1) \ S,F χ)-(∑χ∈univ.erase 1,F χ) = -(∑χ∈S,F χ) := by
    rw [←hsplit];abel
  rw [hdiff,norm_neg]
  exact h _ S hs hS

end GoldbachPartial


