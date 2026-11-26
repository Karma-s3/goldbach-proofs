import VerifiedBrunShortModels
namespace GoldbachPartial
open Finset
open scoped Classical

theorem shortBrun_error_sum (n J : ℕ) (B : Finset ℕ) (c : Finset ℕ→ℝ)
    (hprime : ∀p∈B,p.Prime ∧ ¬p∣n)
    (hc : ∀S⊆B,|c S|≤1)
    (hsupp : ∀S⊆B,c S≠0→(∏p∈S,p)≤(brunBlockBoundary J)^29) :
    let h : ℝ := (n/2-n/4:ℕ)
    |(∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p)) -
      h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p)| ≤
        fixedTargetBrunDistributionError n ((brunBlockBoundary J)^29) := by
  intro h
  let W := B.powerset.filter (fun S => c S≠0)
  let f := fun S : Finset ℕ => ∏p∈S,p
  let T := (Icc 1 ((brunBlockBoundary J)^29)).filter (fun d=>Squarefree d ∧ n.Coprime d)
  have hsub {S : Finset ℕ} (hw : S∈W) : S⊆B := mem_powerset.mp (mem_filter.mp hw).1
  have hpr {S : Finset ℕ} (hw : S∈W) : ∀p∈S,p.Prime := fun p hp => (hprime p (hsub hw hp)).1
  have hpf {S : Finset ℕ} (hw : S∈W) : (f S).primeFactors=S := Nat.primeFactors_prod (hpr hw)
  have him {S : Finset ℕ} (hw : S∈W) : f S∈T := by
    have hsize := hsupp S (hsub hw) (mem_filter.mp hw).2
    have hsf : Squarefree (f S) := by
      have hh := Nat.squarefree_prod_primeFactors (f S)
      rwa [hpf hw] at hh
    have hc : n.Coprime (f S) := Nat.coprime_prod_right_iff.mpr fun p hp =>
      ((hpr hw p hp).coprime_iff_not_dvd.mpr (hprime p (hsub hw hp)).2).symm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨prod_pos (fun p hp => (hpr hw p hp).pos),hsize⟩,hsf,hc⟩
  have hsum : (∑S∈W,fixedTargetIntervalAPError n (f S))≤ ∑d∈T,fixedTargetIntervalAPError n d := by
    apply sum_le_sum_of_injOn f
    · intro S hs S' hs' he
      exact (hpf hs).symm.trans ((congrArg Nat.primeFactors he).trans (hpf hs'))
    · intro d hd
      obtain ⟨S,hs,rfl⟩ := mem_image.mp hd
      exact him hs
    · intro _ _;exact le_rfl
    · intro _ _ _; exact abs_nonneg _
  have hfilter (g : Finset ℕ→ℝ) : (∑S∈W,c S*g S)=∑S∈B.powerset,c S*g S := by
    rw [sum_filter]
    apply sum_congr rfl
    intro S _
    by_cases hc : c S=0 <;> simp [hc]
  rw [←hfilter (fun S => fixedTargetDivisorRow n (∏p∈S,p)),←hfilter (fun S=>∏p∈S,brunEulerWeight p),
    mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans (le_trans ?_ hsum)
  apply sum_le_sum
  intro S hS
  change |c S*fixedTargetDivisorRow n (f S)-h*(c S*(∏p∈S,brunEulerWeight p))|≤fixedTargetIntervalAPError n (f S)
  rw [brunSubset_product_eulerWeight S (hpr hS)]
  change |c S*fixedTargetDivisorRow n (f S)-h*(c S*(1/((f S).totient:ℝ)))|≤|fixedTargetDivisorRow n (f S)-h/(f S).totient|
  rw [show c S*fixedTargetDivisorRow n (f S)-h*(c S*(1/((f S).totient:ℝ))) =
    c S*(fixedTargetDivisorRow n (f S)-h/(f S).totient) by ring,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hc S (hsub hS))


theorem fixedTarget_shortBrun_lower (n y J : ℕ) (he : Even n)
    (hy : y≤n/4) (hscale : y≤brunBlockBoundary J) :
    (((n/2-n/4:ℕ):ℝ)/2)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) -
      fixedTargetBrunDistributionError n ((brunBlockBoundary J)^29) ≤
        fixedTargetBrunSurvivorMass n y := by
  let B := fixedTargetBrunPrimes n y
  let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunShortBlockOrder J)
  let h : ℝ := (n/2-n/4:ℕ)
  have hpr (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hp
    obtain ⟨hmem,hp',hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hp'.two_le; omega,(mem_range_succ_iff.mp hmem).trans hscale⟩
  have hmodel := mul_le_mul_of_nonneg_left (brunShortBlock_joined_model_half J B hB (fun p hp=>(hpr p hp).1))
    (show 0≤h by dsimp [h];positivity)
  have hsupp (S : Finset ℕ) (hS : S⊆B) (hc : c S≠0) := brunJoinedCoefficient_support _ _ _ _ hc
  have herr := (abs_le.mp (shortBrun_error_sum n J B c hpr (fun S _=>brunJoinedCoefficient_abs_le ..)
    (fun S hS hc=>by
      obtain ⟨e,hr⟩:=hsupp S hS hc
      exact brunShortBlock_subset_product_le J e B S hB hS (fun i hi=>hr i (mem_range.mpr hi))))).1
  have hrow := fixedTarget_Brun_joined_rows n y hy (range J) (brunSieveBlock B)
    (fun i _ j _ hij=>brunSieveBlock_disjoint B hij) (brunSieveBlock_partition B J hB)
    (brunShortBlockOrder J) (fun i _ => ⟨6+(J-1-i),by simp only [brunShortBlockOrder];omega⟩)
  apply le_trans _ hrow
  change h/2*(∏p∈B,(1-brunEulerWeight p)) - _ ≤ _
  change h*((1/2:ℝ)*(∏p∈B,(1-brunEulerWeight p))) ≤ h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at hmodel
  change -_ ≤ (∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p))-h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at herr
  change _ ≤ ∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p)
  linear_combination hmodel+herr


theorem fixedTarget_shortBrun_upper (n y J : ℕ) (he : Even n) (hscale : y≤brunBlockBoundary J) :
    fixedTargetBrunSurvivorMass n y ≤ (8/7:ℝ)*((n/2-n/4:ℕ):ℝ)*
      (∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) + fixedTargetBrunDistributionError n ((brunBlockBoundary J)^29) := by
  let B := fixedTargetBrunPrimes n y
  let c := brunShortOrdinaryBlockWeight J B
  let h : ℝ := (n/2-n/4:ℕ)
  have hpr (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hpy (p : ℕ) (hp : p∈B) : p≤y := mem_range_succ_iff.mp (mem_filter.mp hp).1
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hp
    have hne : p≠2 := fun e=>(hpr p hp).2 (e ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := (hpr p hp).1.two_le;omega,(hpy p hp).trans hscale⟩
  let F := fun k : ℕ=>∑S∈B.powerset,if ∀p∈S,p∣n-k then c S else 0
  have hF (k : ℕ) : (if ∀p∈B,¬p∣n-k then (1:ℝ) else 0)≤F k := by
    convert brunShortOrdinaryBlock_majorizes J B hB (fun p=>p∣n-k) using 1
    · split_ifs <;> rfl
    · apply sum_congr rfl;intro S _;split_ifs <;> rfl
  have hge (k : ℕ) : 0≤F k := (show 0≤(if ∀p∈B,¬p∣n-k then (1:ℝ) else 0) by split <;> norm_num).trans (hF k)
  have hw (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  have hrow (S : Finset ℕ) (hS : S∈B.powerset) :
      c S*fixedTargetDivisorRow n (∏p∈S,p) =
      ∑k∈Ioc (n/4) (n/2),weight k*(if ∀p∈S,p∣n-k then c S else 0) := by
    have hh:=mem_powerset.mp hS
    unfold fixedTargetDivisorRow
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    have heq:=fixedTarget_prime_subset_product_dvd S (fun p hp=>(hpr p (hh hp)).1) (n-k)
    by_cases hp : ∀p∈S,p∣n-k <;> simp [heq,hp,mul_comm]
  have htrue : fixedTargetBrunSurvivorMass n y ≤ ∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p) := by
    calc _ ≤ ∑k∈Ioc (n/4) (n/2),weight k*F k := by
           unfold fixedTargetBrunSurvivorMass
           simp only [sum_filter]
           apply sum_le_sum
           intro k hk
           by_cases ha : ∀p:ℕ,p.Prime→p≤y→¬p∣n-k
           · have hh : ∀p∈B,¬p∣n-k := fun p hp=>ha p (hpr p hp).1 (hpy p hp)
             have hf:=hF k
             rw [ite_eq_left hh] at hf
             simpa only [ite_eq_left ha] using le_mul_of_one_le_right (hw k) hf
           · simp only [ite_eq_right ha]; exact mul_nonneg (hw k) (hge k)
         _ = _ := by
           dsimp only [F];simp_rw [mul_sum];rw [sum_comm]
           exact sum_congr rfl (fun S hS=>(hrow S hS).symm)
  have hm := mul_le_mul_of_nonneg_left (brunShortOrdinaryBlock_model_upper J B hB (fun p hp=>(hpr p hp).1))
    (show 0≤h by dsimp [h];positivity)
  have herr := (abs_le.mp (shortBrun_error_sum n J B c hpr (fun S _=>brunShortOrdinaryBlockWeight_abs_le J B S)
    (fun S hS hc=>brunShortOrdinaryBlockWeight_level J B S hB hS hc))).2
  change _≤h*((8/7:ℝ)*(∏p∈B,(1-brunEulerWeight p))) at hm
  change fixedTargetBrunSurvivorMass n y≤(8/7:ℝ)*h*(∏p∈B,(1-brunEulerWeight p))+_
  dsimp only [h,c] at hm htrue ⊢
  dsimp only [c] at herr
  linarith only [hm,htrue,herr]

theorem fixedTarget_shortBrun_two_sided (n y J : ℕ) (he : Even n) (hy : y≤n/4)
    (hscale : y≤brunBlockBoundary J) :
    let M := ((n/2-n/4:ℕ):ℝ)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))
    let E := fixedTargetBrunDistributionError n ((brunBlockBoundary J)^29)
    M/2-E ≤ fixedTargetBrunSurvivorMass n y ∧ fixedTargetBrunSurvivorMass n y ≤ (8/7:ℝ)*M+E := by
  constructor
  · simpa only [div_mul_eq_mul_div] using fixedTarget_shortBrun_lower n y J he hy hscale
  · simpa only [mul_assoc] using fixedTarget_shortBrun_upper n y J he hscale

theorem fixedTarget_shortBrun_any_cutoff (n y : ℕ) (he : Even n) (hy : y≤n/4) (hy' : 2≤y) :
    let M := ((n/2-n/4:ℕ):ℝ)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))
    let E := fixedTargetBrunDistributionError n (y^58)
    M/2-E ≤ fixedTargetBrunSurvivorMass n y ∧ fixedTargetBrunSurvivorMass n y ≤ (8/7:ℝ)*M+E := by
  let J := Nat.log 2 (Nat.log 2 y)+1
  obtain ⟨hlo,hhi⟩ := polylogBlockIndex_bounds hy'
  have hD : (brunBlockBoundary J)^29≤y^58 := calc
    _ ≤ (y^2)^29 := Nat.pow_le_pow_left hhi _
    _ = _ := by rw [←pow_mul]
  have h := fixedTarget_shortBrun_two_sided n y J he hy hlo
  have hm := fixedTargetBrunDistributionError_mono n hD
  exact ⟨(sub_le_sub_left hm _).trans h.1,h.2.trans (add_le_add_right hm _)⟩

end GoldbachPartial