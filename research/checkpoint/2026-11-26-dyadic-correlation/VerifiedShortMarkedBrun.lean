import VerifiedBrunShortModels
import FixedTargetMarkedPrimeMass

namespace GoldbachPartial
open Finset
open scoped Classical

theorem fixedTargetShortMarkedPrime_row_upper (n y J r : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hp : ∀p∈B,p.Prime ∧ p≤y)
    (hr : r.Prime) (hy : y<r) :
    (∑ k∈(fixedTargetBrunPrimeSurvivors n y).filter (fun k=>r∣n-k),Real.log k) ≤
      ∑S∈B.powerset,brunShortOrdinaryBlockWeight J B S * fixedTargetDivisorRow n (r*(∏p∈S,p)) := by
  let c := brunShortOrdinaryBlockWeight J B
  let F := fun k : ℕ => ∑S∈B.powerset, if ∀p∈S,p∣n-k then c S else 0
  have hF (k : ℕ) : (if ∀p∈B,¬p∣n-k then (1:ℝ) else 0)≤F k :=
    by
      convert brunShortOrdinaryBlock_majorizes J B hB (fun p=>p∣n-k) using 1
      · split_ifs <;> rfl
      · apply sum_congr rfl;intro S _;split_ifs <;> rfl
  have hge (k : ℕ) : 0≤F k := (show 0≤(if ∀p∈B,¬p∣n-k then (1:ℝ) else 0) by split <;> norm_num).trans (hF k)
  have hw (k : ℕ) : 0≤weight k := by
    unfold weight
    split_ifs with hk
    · exact Real.log_nonneg (by exact_mod_cast hk.one_le)
    · exact le_rfl
  have hrow (S : Finset ℕ) (hS : S∈B.powerset) :
      c S*fixedTargetDivisorRow n (r*(∏p∈S,p)) =
        ∑k∈Ioc (n/4) (n/2),(if r∣n-k then weight k else 0)*
          (if ∀p∈S,p∣n-k then c S else 0) := by
    have hs := mem_powerset.mp hS
    have hrS : r∉S := fun hh => (Nat.not_le.mpr hy) (hp r (hs hh)).2
    have hpr : ∀p∈insert r S,p.Prime := by
      simp only [forall_mem_insert]
      exact ⟨hr,fun p hh=>(hp p (hs hh)).1⟩
    unfold fixedTargetDivisorRow
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    have hf := fixedTarget_prime_subset_product_dvd (insert r S) hpr (n-k)
    rw [prod_insert hrS,forall_mem_insert] at hf
    by_cases h1 : r∣n-k <;> by_cases h2 : ∀p∈S,p∣n-k <;> simp [hf,h1,h2,mul_comm]
  calc
    _ ≤ ∑k∈Ioc (n/4) (n/2),(if r∣n-k then weight k else 0)*F k := by
      simp only [fixedTargetBrunPrimeSurvivors,filter_filter,sum_filter]
      apply sum_le_sum
      intro k _
      by_cases hk : k.Prime ∧ ∀p:ℕ,p.Prime→p≤y→¬p∣n-k
      · have hh : ∀p∈B,¬p∣n-k := fun p hb=>hk.2 p (hp p hb).1 (hp p hb).2
        have h1 := hF k
        rw [ite_eq_left hh] at h1
        by_cases hd : r∣n-k
        · rw [ite_eq_left ⟨hk,hd⟩,ite_eq_left hd]
          rw [←show weight k=Real.log k by simp [weight,hk.1]]
          exact le_mul_of_one_le_right (hw k) h1
        · simp [hd]
      · by_cases hd : r∣n-k
        · rw [ite_eq_right (fun h=>hk h.1),ite_eq_left hd]
          exact mul_nonneg (hw k) (hge k)
        · simp [hd]
    _ = _ := by
      dsimp only [F]
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro S hS
      exact (hrow S hS).symm


set_option maxHeartbeats 800000 in
theorem shortMarkedBrun_progression_error (n y w J : ℕ) (B R : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hp : ∀p∈B,p.Prime ∧ p≤y ∧ ¬p∣n)
    (hR : ∀r∈R,r.Prime ∧ y<r ∧ r≤w ∧ ¬r∣n) :
    let c := brunShortOrdinaryBlockWeight J B
    let h : ℝ := (n/2-n/4:ℕ)
    (∑r∈R,∑S∈B.powerset,c S*fixedTargetDivisorRow n (r*(∏p∈S,p))) ≤
      h*(∑r∈R,brunEulerWeight r)*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) +
        fixedTargetBrunDistributionError n (w*(brunBlockBoundary J)^29) := by
  intro c h
  let W := B.powerset.filter (fun S=>c S≠0)
  let T := (Icc 1 (w*(brunBlockBoundary J)^29)).filter (fun d=>Squarefree d ∧ n.Coprime d)
  let f := fun u : ℕ×Finset ℕ => u.1*(∏p∈u.2,p)
  have hsub {S : Finset ℕ} (hs : S∈W) : S⊆B := mem_powerset.mp (mem_filter.mp hs).1
  have hnot {S : Finset ℕ} (hs : S∈W) {r : ℕ} (hr : r∈R) : r∉S := fun hh=>
    (Nat.not_le.mpr (hR r hr).2.1) (hp r (hsub hs hh)).2.1
  have hpr {S : Finset ℕ} (hs : S∈W) {r : ℕ} (hr : r∈R) : ∀p∈insert r S,p.Prime := by
    simp only [forall_mem_insert]
    exact ⟨(hR r hr).1,fun p hh=>(hp p (hsub hs hh)).1⟩
  have hpf {u : ℕ×Finset ℕ} (hu : u∈R×ˢW) : (f u).primeFactors=insert u.1 u.2 := by
    obtain ⟨hr,hs⟩ := mem_product.mp hu
    have h1 := Nat.primeFactors_prod (hpr hs hr)
    rwa [prod_insert (hnot hs hr)] at h1
  have him {u : ℕ×Finset ℕ} (hu : u∈R×ˢW) : f u∈T := by
    obtain ⟨hr,hs⟩ := mem_product.mp hu
    have hsf := Nat.squarefree_prod_primeFactors (f u)
    rw [hpf hu,prod_insert (hnot hs hr)] at hsf
    have hcp : n.Coprime (∏p∈u.2,p) := Nat.coprime_prod_right_iff.mpr fun p hh=>
      ((hp p (hsub hs hh)).1.coprime_iff_not_dvd.mpr (hp p (hsub hs hh)).2.2).symm
    have hc := Nat.coprime_mul_iff_right.mpr ⟨((hR u.1 hr).1.coprime_iff_not_dvd.mpr (hR u.1 hr).2.2.2).symm,hcp⟩
    have hpos := Nat.mul_pos (hR u.1 hr).1.pos (prod_pos (fun p hh=>(hp p (hsub hs hh)).1.pos))
    have hub := Nat.mul_le_mul (hR u.1 hr).2.2.1 (brunShortOrdinaryBlockWeight_level J B u.2 hB (hsub hs) (mem_filter.mp hs).2)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos,hub⟩,hsf,hc⟩
  have hsums : (∑r∈R,∑S∈W,fixedTargetIntervalAPError n (r*(∏p∈S,p))) ≤
      fixedTargetBrunDistributionError n (w*(brunBlockBoundary J)^29) := by
    change _ ≤ ∑d∈T,fixedTargetIntervalAPError n d
    rw [←sum_product']
    apply sum_le_sum_of_injOn f
    · rintro ⟨r,S⟩ hu ⟨r',S'⟩ hv he
      obtain ⟨hr,hs⟩ := mem_product.mp hu
      obtain ⟨hr',hs'⟩ := mem_product.mp hv
      have hsi : insert r S=insert r' S' := (hpf hu).symm.trans ((congrArg Nat.primeFactors he).trans (hpf hv))
      have hmem : r∈insert r' S' := hsi ▸ mem_insert_self _ _
      obtain hrr | hbad := mem_insert.mp hmem
      · subst r'
        have heq : (∏p∈S,p)=(∏p∈S',p) := Nat.eq_of_mul_eq_mul_left (hR r hr).1.pos he
        have hp1 := Nat.primeFactors_prod (fun p h1=>(hp p (hsub hs h1)).1)
        have hp2 := Nat.primeFactors_prod (fun p h1=>(hp p (hsub hs' h1)).1)
        exact Prod.ext rfl (hp1.symm.trans ((congrArg Nat.primeFactors heq).trans hp2))
      · exact (hnot hs' hr hbad).elim
    · intro d hd
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hd
      exact him hu
    · intro _ _;exact le_rfl
    · intro _ _ _;exact abs_nonneg _
  have hfilt (g : Finset ℕ→ℝ) : (∑ S∈B.powerset,c S*g S)=∑ S∈W,c S*g S := by
    rw [sum_filter];apply sum_congr rfl;intro S _
    by_cases h0 : c S=0 <;> simp [h0]
  have hrow (r : ℕ) (hr : r∈R) (S : Finset ℕ) (hs : S∈W) :
      c S*fixedTargetDivisorRow n (r*(∏p∈S,p)) ≤
        h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) +
          fixedTargetIntervalAPError n (r*(∏p∈S,p)) := by
    have hwt := brunSubset_product_eulerWeight (insert r S) (hpr hs hr)
    rw [prod_insert (hnot hs hr),prod_insert (hnot hs hr)] at hwt
    have hmain : h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) =
        c S*(h/((r*(∏p∈S,p)).totient:ℝ)) := by
      rw [show h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) =
        c S*h*(brunEulerWeight r*(∏p∈S,brunEulerWeight p)) by ring,hwt];ring
    rw [hmain]
    let d := r*(∏p∈S,p)
    have hab : c S*(fixedTargetDivisorRow n d-h/d.totient) ≤ fixedTargetIntervalAPError n d := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (brunShortOrdinaryBlockWeight_abs_le ..)
    change c S*fixedTargetDivisorRow n d≤c S*(h/(d.totient:ℝ))+fixedTargetIntervalAPError n d
    linarith only [hab]
  calc
    _ = ∑r∈R,∑S∈W,c S*fixedTargetDivisorRow n (r*(∏p∈S,p)) := sum_congr rfl (fun r _=>hfilt _)
    _ ≤ ∑r∈R,∑S∈W,(h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p))+
        fixedTargetIntervalAPError n (r*(∏p∈S,p))) := sum_le_sum (fun r hr=>sum_le_sum (hrow r hr))
    _ = (h*(∑r∈R,brunEulerWeight r)*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p))+
        (∑r∈R,∑S∈W,fixedTargetIntervalAPError n (r*(∏p∈S,p))) := by
      simp only [sum_add_distrib]
      congr 1
      rw [hfilt, Finset.mul_sum R _ h, sum_mul]
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
    _ ≤ _ := add_le_add_right hsums _


theorem fixedTargetShortMarkedPrimeMass_upper (n y w J : ℕ) (R : Finset ℕ)
    (he : Even n) (hscale : y≤brunBlockBoundary J)
    (hR : ∀r∈R,r.Prime ∧ y<r ∧ r≤w ∧ ¬r∣n) :
    fixedTargetMarkedPrimeMass n y R ≤ (8/7:ℝ)*((n/2-n/4:ℕ):ℝ)*
      (∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p))*(∑r∈R,brunEulerWeight r) +
        fixedTargetBrunDistributionError n (w*(brunBlockBoundary J)^29) := by
  let B := fixedTargetBrunPrimes n y
  let h : ℝ := (n/2-n/4:ℕ)
  have hp (p : ℕ) (hb : p∈B) : p.Prime ∧ p≤y ∧ ¬p∣n := by
    obtain ⟨hm,hpr,hn⟩ := mem_filter.mp hb
    exact ⟨hpr,mem_range_succ_iff.mp hm,hn⟩
  have hB : B⊆Icc 3 (brunBlockBoundary J) := by
    intro p hb
    obtain ⟨hpr,hy,hn⟩ := hp p hb
    have hne : p≠2 := fun e=>hn (e ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by have := hpr.two_le;omega,hy.trans hscale⟩
  have hpos : 0≤h*(∑r∈R,brunEulerWeight r) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro r hr
    unfold brunEulerWeight
    apply one_div_nonneg.mpr
    exact sub_nonneg.mpr (by exact_mod_cast (hR r hr).1.one_le)
  apply (sum_le_sum (fun r hr=>fixedTargetShortMarkedPrime_row_upper n y J r B hB
    (fun p hb=>⟨(hp p hb).1,(hp p hb).2.1⟩) (hR r hr).1 (hR r hr).2.1)).trans
  apply (shortMarkedBrun_progression_error n y w J B R hB hp hR).trans
  apply add_le_add_left
  change h*(∑r∈R,brunEulerWeight r)*_ ≤ 8/7*h*(∏p∈B,(1-brunEulerWeight p))*(∑r∈R,brunEulerWeight r)
  apply (mul_le_mul_of_nonneg_left (brunShortOrdinaryBlock_model_upper J B hB (fun p hb=>(hp p hb).1)) hpos).trans
  apply le_of_eq
  ring

end GoldbachPartial
