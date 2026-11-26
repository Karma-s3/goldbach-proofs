import VerifiedRoughP2SingularUpper
import VerifiedShortMarkedBrun
namespace GoldbachPartial
open Finset Filter
open scoped Classical
set_option maxHeartbeats 800000 in
theorem prefix_markedBrun_progression_error (n y w J : ℕ) (B R : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hp : ∀p∈B,p.Prime ∧ p≤y ∧ ¬p∣n)
    (hR : ∀r∈R,r.Prime ∧ y<r ∧ r≤w ∧ ¬r∣n) :
    let c := brunShortOrdinaryBlockWeight J B
    let h : ℝ := n
    (∑r∈R,∑S∈B.powerset,c S*reflectedPrefixRow n (r*(∏p∈S,p))) ≤
      h*(∑r∈R,brunEulerWeight r)*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p) +
        (∑d∈Icc 1 (w*(brunBlockBoundary J)^29),brunPrimePrefixMaxError n d) := by
  intro c h
  let W := B.powerset.filter (fun S=>c S≠0)
  let T := Icc 1 (w*(brunBlockBoundary J)^29)
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
    have hpos := Nat.mul_pos (hR u.1 hr).1.pos (prod_pos (fun p hh=>(hp p (hsub hs hh)).1.pos))
    have hub := Nat.mul_le_mul (hR u.1 hr).2.2.1 (brunShortOrdinaryBlockWeight_level J B u.2 hB (hsub hs) (mem_filter.mp hs).2)
    exact mem_Icc.mpr ⟨hpos,hub⟩
  have hsums : (∑r∈R,∑S∈W,brunPrimePrefixMaxError n (r*(∏p∈S,p))) ≤
      (∑d∈Icc 1 (w*(brunBlockBoundary J)^29),brunPrimePrefixMaxError n d) := by
    change _ ≤ ∑d∈T,brunPrimePrefixMaxError n d
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
    · intro _ _ _;exact brunPrimePrefixMaxError_nonneg ..
  have hfilt (g : Finset ℕ→ℝ) : (∑ S∈B.powerset,c S*g S)=∑ S∈W,c S*g S := by
    rw [sum_filter];apply sum_congr rfl;intro S _
    by_cases h0 : c S=0 <;> simp [h0]
  have hrow (r : ℕ) (hr : r∈R) (S : Finset ℕ) (hs : S∈W) :
      c S*reflectedPrefixRow n (r*(∏p∈S,p)) ≤
        h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) +
          brunPrimePrefixMaxError n (r*(∏p∈S,p)) := by
    have hwt := brunSubset_product_eulerWeight (insert r S) (hpr hs hr)
    rw [prod_insert (hnot hs hr),prod_insert (hnot hs hr)] at hwt
    have hmain : h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) =
        c S*(h/((r*(∏p∈S,p)).totient:ℝ)) := by
      rw [show h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p)) =
        c S*h*(brunEulerWeight r*(∏p∈S,brunEulerWeight p)) by ring,hwt];ring
    rw [hmain]
    let d := r*(∏p∈S,p)
    have hab : c S*(reflectedPrefixRow n d-h/d.totient) ≤ brunPrimePrefixMaxError n d := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) (brunShortOrdinaryBlockWeight_abs_le ..)).trans
      have hcp : n.Coprime d := Nat.coprime_mul_iff_right.mpr ⟨((hR r hr).1.coprime_iff_not_dvd.mpr (hR r hr).2.2.2).symm,
        Nat.coprime_prod_right_iff.mpr fun p hh => ((hp p (hsub hs hh)).1.coprime_iff_not_dvd.mpr (hp p (hsub hs hh)).2.2).symm⟩
      have hdp : 0<d := Nat.mul_pos (hR r hr).1.pos (prod_pos (fun p hh=>(hp p (hsub hs hh)).1.pos))
      have hm := Nat.mod_lt n hdp
      unfold reflectedPrefixRow brunPrimePrefixMaxError
      apply le_trans _ (le_sup' _ (mem_range_succ_iff.mpr hm.le))
      rw [ite_eq_left ⟨hm,show (n%d).Coprime d by rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm];exact hcp⟩]
    change c S*reflectedPrefixRow n d≤c S*(h/(d.totient:ℝ))+brunPrimePrefixMaxError n d
    linarith only [hab]
  calc
    _ = ∑r∈R,∑S∈W,c S*reflectedPrefixRow n (r*(∏p∈S,p)) := sum_congr rfl (fun r _=>hfilt _)
    _ ≤ ∑r∈R,∑S∈W,(h*brunEulerWeight r*(c S*(∏p∈S,brunEulerWeight p))+
        brunPrimePrefixMaxError n (r*(∏p∈S,p))) := sum_le_sum (fun r hr=>sum_le_sum (hrow r hr))
    _ = (h*(∑r∈R,brunEulerWeight r)*(∑S∈B.powerset,c S*∏p∈S,brunEulerWeight p))+
        (∑r∈R,∑S∈W,brunPrimePrefixMaxError n (r*(∏p∈S,p))) := by
      simp only [sum_add_distrib]
      congr 1
      rw [hfilt, Finset.mul_sum R _ h, sum_mul]
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
    _ ≤ _ := add_le_add_right hsums _



theorem reflectedP2_marked_row (n z J r : ℕ) (he : Even n) (hz : brunBlockBoundary J<z)
    (hr : r.Prime) (hyr : brunBlockBoundary J<r) :
    let B := fixedTargetBrunPrimes n (brunBlockBoundary J)
    (∑k∈(reflectedP2Set n z).filter (fun p=>r∣n-p),Real.log k*Real.log (n-k:ℕ)) ≤
      Real.log n*∑S∈B.powerset,brunShortOrdinaryBlockWeight J B S*reflectedPrefixRow n (r*(∏p∈S,p)) := by
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
  let C := (reflectedP2Set n z).filter (fun p=>r∣n-p)
  let I := (range (n+1)).filter (fun p=>r∣n-p)
  have hm (k : ℕ) (hk : k∈C) := (mem_filter.mp (mem_filter.mp hk).1).2
  have hsurv (k : ℕ) (hk : k∈C) : 1≤F k := by
    have hno (p : ℕ) (hp : p∈B) (hd : p∣n-k) : False :=
      (hBle p hp).not_gt (hz.trans_le ((hm k hk).2.2.2 p (hBpr p hp).1 hd))
    simpa only [ite_eq_left hno] using hF k
  have hbound : (∑ k∈C,Real.log k*Real.log (n-k:ℕ)) ≤ (Real.log n)*∑k∈I,weight k*F k := by
    rw [mul_sum]
    have hsub : C ⊆ I := fun p hp=>mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
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
      (∑k∈I,weight k*(if ∀p∈S,p∣n-k then c S else 0)) =
        c S*reflectedPrefixRow n (r*(∏p∈S,p)) := by
    have hrS : r∉S := fun hh => hyr.not_ge (hBle r (mem_powerset.mp hS hh))
    have hpr : ∀p∈insert r S,p.Prime := by
      simp only [forall_mem_insert]
      exact ⟨hr,fun p hp=>(hBpr p (mem_powerset.mp hS hp)).1⟩
    let d := r*(∏p∈S,p)
    unfold reflectedPrefixRow GoldbachMajorArc.classMass
    dsimp only [I]
    rw [sum_filter,sum_filter,mul_sum]
    apply sum_congr rfl
    intro k hk
    have hd := fixedTarget_prime_subset_product_dvd (insert r S) hpr (n-k)
    rw [prod_insert hrS,forall_mem_insert] at hd
    have heq : (r∣n-k ∧ ∀p∈S,p∣n-k) ↔ k%d=n%d := hd.symm.trans (Nat.modEq_iff_dvd' (mem_range_succ_iff.mp hk)).symm
    change (if r∣n-k then weight k*(if ∀p∈S,p∣n-k then c S else 0) else 0)=c S*(if k%d=n%d then weight k else 0)
    rw [←if_congr heq rfl rfl]
    by_cases h1 : r∣n-k <;> by_cases h2 : ∀p∈S,p∣n-k <;> simp [h1,h2,mul_comm]
  have heq : (∑k∈I,weight k*F k) = ∑S∈B.powerset,c S*reflectedPrefixRow n (r*(∏p∈S,p)) := by
    dsimp only [F];simp_rw [mul_sum];rw [sum_comm];exact sum_congr rfl hrow
  exact hbound.trans_eq (congrArg (Real.log n*·) heq)

noncomputable def roughP2MarkedLogMass (n z : ℕ) (R : Finset ℕ) : ℝ :=
  ∑ r∈R,∑p∈(reflectedP2Set n z).filter (fun k=>r∣n-k),Real.log p*Real.log (n-p:ℕ)

theorem roughP2MarkedLogMass_coprime_upper (n z J w : ℕ) (R : Finset ℕ) (he : Even n)
    (hz : brunBlockBoundary J<z) (hR : ∀r∈R,r.Prime ∧ brunBlockBoundary J<r ∧ r≤w ∧ ¬r∣n) :
    let y := brunBlockBoundary J
    let B := fixedTargetBrunPrimes n y
    roughP2MarkedLogMass n z R ≤ Real.log n*((8/7:ℝ)*n*(∏p∈B,(1-brunEulerWeight p))*
      (∑r∈R,brunEulerWeight r)+(∑d∈Icc 1 (w*y^29),brunPrimePrefixMaxError n d)) := by
  let y := brunBlockBoundary J
  let B := fixedTargetBrunPrimes n y
  let c := brunShortOrdinaryBlockWeight J B
  have hpr (p : ℕ) (hp : p∈B) : p.Prime ∧ p≤y ∧ ¬p∣n := by
    obtain ⟨hi,hp,hd⟩ := mem_filter.mp hp
    exact ⟨hp,mem_range_succ_iff.mp hi,hd⟩
  have hB : B⊆Icc 3 y := by
    intro p hp
    have ha := (hpr p hp).1.two_le
    have h2 : p≠2 := fun h => (hpr p hp).2.2 (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by omega,(hpr p hp).2.1⟩
  have hr := sum_le_sum (fun r (hr:r∈R)=>reflectedP2_marked_row n z J r he hz (hR r hr).1 (hR r hr).2.1)
  have hs := prefix_markedBrun_progression_error n y w J B R hB hpr hR
  have hu := brunShortOrdinaryBlock_model_upper J B hB (fun p hp=>(hpr p hp).1)
  have hn : 0≤(n:ℝ)*(∑r∈R,brunEulerWeight r) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro r hr
    unfold brunEulerWeight
    exact one_div_nonneg.mpr (by have := (by exact_mod_cast (hR r hr).1.one_le : (1:ℝ)≤r);linarith)
  apply hr.trans
  change (∑r∈R,Real.log n* (∑S∈B.powerset,c S*reflectedPrefixRow n (r*(∏p∈S,p)))) ≤ _
  rw [←mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
  apply hs.trans (add_le_add _ le_rfl)
  apply (mul_le_mul_of_nonneg_left hu hn).trans_eq
  ring

theorem roughP2MarkedLogMass_upper (n z J w : ℕ) (R : Finset ℕ) (he : Even n)
    (hz : brunBlockBoundary J<z) (hR : ∀r∈R,r.Prime ∧ brunBlockBoundary J<r ∧ r≤w) :
    let y := brunBlockBoundary J
    let B := fixedTargetBrunPrimes n y
    roughP2MarkedLogMass n z R ≤ Real.log n*((8/7:ℝ)*n*(∏p∈B,(1-brunEulerWeight p))*
      (∑r∈R,brunEulerWeight r)+(∑d∈Icc 1 (w*y^29),brunPrimePrefixMaxError n d))+w*(Real.log n)^2 := by
  let T := R.filter (fun r=>¬r∣n)
  let U := R.filter (fun r=>¬¬r∣n)
  have hT (r : ℕ) (hr : r∈T) :=
    And.intro (hR r (mem_filter.mp hr).1).1 (And.intro (hR r (mem_filter.mp hr).1).2.1
      (And.intro (hR r (mem_filter.mp hr).1).2.2 (mem_filter.mp hr).2))
  have ht := roughP2MarkedLogMass_coprime_upper n z J w T he hz hT
  have hpart : roughP2MarkedLogMass n z T+roughP2MarkedLogMass n z U=roughP2MarkedLogMass n z R :=
    sum_filter_add_sum_filter_not R (fun r=>¬r∣n) _
  have hsmall (r : ℕ) (hr : r∈U) : (∑p∈(reflectedP2Set n z).filter (fun k=>r∣n-k),
      Real.log p*Real.log (n-p:ℕ)) ≤ (Real.log n)^2 := by
    have hrn := not_not.mp (mem_filter.mp hr).2
    have hpr := (hR r (mem_filter.mp hr).1).1
    let S := (reflectedP2Set n z).filter (fun k=>r∣n-k)
    have hsub : S⊆{r} := by
      intro p hp
      obtain ⟨hpC,hd⟩ := mem_filter.mp hp
      have hp' := mem_filter.mp hpC
      have hpn := mem_range_succ_iff.mp hp'.1
      have hdiv : r∣p := by simpa only [Nat.sub_sub_self hpn] using Nat.dvd_sub hrn hd
      exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hpr hp'.2.1).mp hdiv).symm
    calc _ ≤ ∑_p∈S,(Real.log n)^2 := by
            apply sum_le_sum
            intro p hp
            have hpc := mem_filter.mp (mem_filter.mp hp).1
            have hpn := mem_range_succ_iff.mp hpc.1
            have hm := hpc.2.2.1
            rw [sq]
            exact mul_le_mul (Real.log_le_log (by exact_mod_cast hpc.2.1.pos) (by exact_mod_cast hpn))
              (Real.log_le_log (by exact_mod_cast (by omega : 0<n-p)) (by exact_mod_cast Nat.sub_le n p))
              (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
         _ ≤ ∑_p∈({r}:Finset ℕ),(Real.log n)^2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
         _ = _ := by simp
  have hub : roughP2MarkedLogMass n z U≤w*(Real.log n)^2 := by
    apply (sum_le_sum hsmall).trans
    have hUsub : U⊆Icc 1 w := fun r hr=>mem_Icc.mpr ⟨(hR r (mem_filter.mp hr).1).1.pos,(hR r (mem_filter.mp hr).1).2.2⟩
    have hcnt := card_le_card hUsub
    simp only [Nat.card_Icc,add_tsub_cancel_right] at hcnt
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) (sq_nonneg _)
  rw [←hpart]
  apply add_le_add (ht.trans _) hub
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun r hr _=>?_))
  · apply mul_nonneg (by positivity)
    apply prod_nonneg
    intro p hp
    have hpr := (mem_filter.mp hp).2.1
    have hnd := (mem_filter.mp hp).2.2
    have hneq : p≠2 := fun hh=>hnd (hh ▸ even_iff_two_dvd.mp he)
    have h3 : (2:ℝ)≤p := by exact_mod_cast hpr.two_le
    unfold brunEulerWeight
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  · unfold brunEulerWeight
    exact one_div_nonneg.mpr (by have := (by exact_mod_cast (hR r hr).1.one_le : (1:ℝ)≤r);linarith)

end GoldbachPartial