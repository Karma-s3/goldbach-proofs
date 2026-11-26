import VerifiedFixedPowerBrun

namespace GoldbachPartial
open Finset
open scoped Classical

noncomputable def fixedTargetIntervalAPError (n d : ℕ) : ℝ :=
  |fixedTargetDivisorRow n d - ((n/2-n/4:ℕ):ℝ)/d.totient|

noncomputable def fixedTargetBrunDistributionError (n D : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 D).filter (fun d=>Squarefree d ∧ n.Coprime d),fixedTargetIntervalAPError n d

theorem fixedTargetIntervalAPError_le_prefix (n d : ℕ) :
    fixedTargetIntervalAPError n d ≤
      |GoldbachMajorArc.classMass (n/2+1) d (n%d) - ((n/2:ℕ):ℝ)/d.totient| +
      |GoldbachMajorArc.classMass (n/4+1) d (n%d) - ((n/4:ℕ):ℝ)/d.totient| := by
  unfold fixedTargetIntervalAPError
  rw [fixedTargetDivisorRow_prefix,Nat.cast_sub (by omega : n/4≤n/2)]
  apply le_trans (le_of_eq ?_) (abs_sub ..)
  congr 1
  ring

theorem brunSubset_product_eulerWeight (S : Finset ℕ) (hp : ∀p∈S,p.Prime) :
    (∏p∈S,brunEulerWeight p) = 1/((∏p∈S,p).totient:ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpn ih =>
    have hpr := hp p (mem_insert_self ..)
    have hS (l : ℕ) (hl : l∈S) := hp l (mem_insert_of_mem hl)
    have hc : p.Coprime (∏l∈S,l) := Nat.coprime_prod_right_iff.mpr (fun l hl =>
      (Nat.coprime_primes hpr (hS l hl)).mpr (by rintro rfl;exact hpn hl))
    rw [prod_insert hpn,prod_insert hpn,Nat.totient_mul hc,Nat.totient_prime hpr,
      Nat.cast_mul,Nat.cast_sub hpr.one_le,Nat.cast_one,ih hS]
    dsimp only [brunEulerWeight]
    simp only [one_div,mul_inv_rev];ring

/-- One copy of the true absolute progression error per squarefree reduced modulus in the support. -/
theorem brun_joined_error_sum (n J : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J))
    (hprime : ∀ p∈B, p.Prime ∧ ¬p∣n) :
    let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
    let h : ℝ := (n/2-n/4:ℕ)
    |(∑ S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p)) -
      h*(∑ S∈B.powerset,c S*∏p∈S,brunEulerWeight p)| ≤
        fixedTargetBrunDistributionError n ((brunBlockBoundary J)^101) := by
  intro c h
  let W := B.powerset.filter (fun S => c S≠0)
  let f := fun S : Finset ℕ => ∏p∈S,p
  let T := (Icc 1 ((brunBlockBoundary J)^101)).filter (fun d=>Squarefree d ∧ n.Coprime d)
  have hsub {S : Finset ℕ} (hw : S∈W) : S⊆B := mem_powerset.mp (mem_filter.mp hw).1
  have hpr {S : Finset ℕ} (hw : S∈W) : ∀p∈S,p.Prime := fun p hp => (hprime p (hsub hw hp)).1
  have hpf {S : Finset ℕ} (hw : S∈W) : (f S).primeFactors=S := Nat.primeFactors_prod (hpr hw)
  have him {S : Finset ℕ} (hw : S∈W) : f S∈T := by
    obtain ⟨e,he⟩ := brunJoinedCoefficient_support _ _ _ _ (mem_filter.mp hw).2
    have hsize := brunBlock_subset_product_le J e B S hB (hsub hw) (fun i hi => he i (mem_range.mpr hi))
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
  exact mul_le_of_le_one_left (abs_nonneg _) (brunJoinedCoefficient_abs_le ..)

theorem fixedTarget_Brun_mass_of_distribution (n y J : ℕ) (he : Even n)
    (hy : y≤n/4) (hscale : y≤brunBlockBoundary J) :
    (((n/2-n/4:ℕ):ℝ)/2)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) -
      fixedTargetBrunDistributionError n ((brunBlockBoundary J)^101) ≤
        fixedTargetBrunSurvivorMass n y := by
  let B := fixedTargetBrunPrimes n y
  let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
  let h : ℝ := (n/2-n/4:ℕ)
  have hpr (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hp
    obtain ⟨hmem,hp',hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hp'.two_le; omega,(mem_range_succ_iff.mp hmem).trans hscale⟩
  have hmodel := mul_le_mul_of_nonneg_left (brunBlock_joined_model_half J B hB (fun p hp=>(hpr p hp).1))
    (show 0≤h by dsimp [h];positivity)
  have herr := (abs_le.mp (brun_joined_error_sum n J B hB hpr)).1
  have hrow := fixedTarget_Brun_joined_rows n y hy (range J) (brunSieveBlock B)
    (fun i _ j _ hij=>brunSieveBlock_disjoint B hij) (brunSieveBlock_partition B J hB)
    (brunBlockOrder J) (fun i _ => ⟨24+(J-1-i),by simp only [brunBlockOrder];omega⟩)
  apply le_trans _ hrow
  change h/2*(∏p∈B,(1-brunEulerWeight p)) - _ ≤ _
  change h*((1/2:ℝ)*(∏p∈B,(1-brunEulerWeight p))) ≤ h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at hmodel
  change -_ ≤ (∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p))-h*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) at herr
  change _ ≤ ∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p)
  linear_combination hmodel+herr

/-- Maximum of the prime-prefix discrepancy over reduced residue classes. The extra
residue d contributes zero, so the maximum is defined even at modulus zero. -/
noncomputable def brunPrimePrefixMaxError (u d : ℕ) : ℝ :=
  (range (d+1)).sup' (by exact ⟨0,mem_range.mpr (by omega)⟩)
    (fun a=>if a<d ∧ a.Coprime d then
      |GoldbachMajorArc.classMass (u+1) d a-(u:ℝ)/d.totient| else 0)

theorem brunPrimePrefixMaxError_nonneg (u d : ℕ) : 0≤brunPrimePrefixMaxError u d := by
  unfold brunPrimePrefixMaxError
  have hd : d∈range (d+1) := mem_range_succ_iff.mpr le_rfl
  apply le_trans _ (le_sup' _ hd)
  simp

theorem fixedTargetBrunDistributionError_le_prefix_max (n D : ℕ) :
    fixedTargetBrunDistributionError n D ≤
      (∑d∈Icc 1 D,brunPrimePrefixMaxError (n/2) d) + (∑d∈Icc 1 D,brunPrimePrefixMaxError (n/4) d) := by
  unfold fixedTargetBrunDistributionError
  rw [←sum_add_distrib,sum_filter]
  apply sum_le_sum
  intro d hd
  by_cases hc : Squarefree d ∧ n.Coprime d
  · rw [ite_eq_left hc]
    have hm : n%d < d := Nat.mod_lt _ (mem_Icc.mp hd).1
    have hcp : (n%d).Coprime d := by
      rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm]
      exact hc.2
    have hup (u : ℕ) : |GoldbachMajorArc.classMass (u+1) d (n%d)-(u:ℝ)/d.totient| ≤ brunPrimePrefixMaxError u d := by
      unfold brunPrimePrefixMaxError
      apply le_trans _ (le_sup' _ (mem_range_succ_iff.mpr hm.le))
      rw [ite_eq_left ⟨hm,hcp⟩]
    exact (fixedTargetIntervalAPError_le_prefix n d).trans (add_le_add (hup _) (hup _))
  · rw [ite_eq_right hc]
    exact add_nonneg (brunPrimePrefixMaxError_nonneg ..) (brunPrimePrefixMaxError_nonneg ..)

theorem fixedTargetBrunDistributionError_mono (n : ℕ) : Monotone (fixedTargetBrunDistributionError n) := by
  intro d D hle
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hi,hc⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans hle⟩,hc⟩
  · intro k _ _
    exact abs_nonneg _

theorem fixedTarget_Brun_mass_of_distribution_any_cutoff (n y : ℕ) (he : Even n)
    (hy : y≤n/4) (hy' : 2≤y) :
    (((n/2-n/4:ℕ):ℝ)/2)*(∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)) -
      fixedTargetBrunDistributionError n (y^202) ≤ fixedTargetBrunSurvivorMass n y := by
  let J := Nat.log 2 (Nat.log 2 y)+1
  obtain ⟨hlo,hhi⟩ := polylogBlockIndex_bounds hy'
  have hD : (brunBlockBoundary J)^101≤y^202 := calc
    _ ≤ (y^2)^101 := Nat.pow_le_pow_left hhi _
    _ = _ := by rw [←pow_mul]
  exact (sub_le_sub_left (fixedTargetBrunDistributionError_mono n hD) _).trans
    (fixedTarget_Brun_mass_of_distribution n y J he hy hlo)

end GoldbachPartial