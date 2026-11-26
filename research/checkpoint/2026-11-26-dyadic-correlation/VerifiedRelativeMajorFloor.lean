import PrimeFactorLogMean
import SignedMajorCharging
import VerifiedBothFarMinorReduction
import VerifiedMajorCoefficientPowerset
import VerifiedDivisorWeightConcentration

namespace GoldbachPartial
open Finset Filter MeasureTheory

private theorem positive_family_lower (n : ℕ) (hn : Even n) (P : Finset ℕ) (C : Finset (Finset ℕ))
    (hP : ∀ p∈P,p.Prime) (hC : C ⊆ P.powerset) (hdvd : ∀ t∈C,∀ p∈t,p∣n)
    (W : ℕ→ℝ) (hw : ∀ q,0≤W q) (hm : ∀ i j : ℕ,0 < i → i≤j → W j≤W i)
    (b : ℝ) (hmin : ∀ t∈C,b≤W (∏ p∈t,p)) :
    (9/16:ℝ)*b*(∑ t∈C,(∏p∈t,1/((p:ℝ)-1))) ≤
       ∑ t∈P.powerset,(∏ p∈t,majorPrimeLocal p n)*W (∏ p∈t,p) := by
  classical
  let c := fun p => majorPrimeLocal p n
  let B := P.filter (fun p => ¬ p∣n)
  have hd : 2∣n := even_iff_two_dvd.mp hn
  have hB (p:ℕ) (hp:p∈B) : p.Prime ∧ 2 < p := by
    obtain ⟨h,h'⟩ := mem_filter.mp hp
    have hp' := hP p h
    exact ⟨hp',lt_of_le_of_ne hp'.two_le (fun e => h' (e ▸ hd))⟩
  have cost_eq : (∑ p ∈ P,max 0 (-c p)) = ∑ p ∈ B,1/((p:ℝ)-1)^2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    have ha : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    by_cases h : p∣n
    · have hv : 0 ≤ 1/((p:ℝ)-1) := by positivity
      simp only [c,majorPrimeLocal,ite_eq_left h,ite_eq_right (not_not_intro h)]
      exact max_eq_left (neg_nonpos.mpr hv)
    · have hv : 0 ≤ 1/((p:ℝ)-1)^2 := by positivity
      simp only [c,majorPrimeLocal,ite_eq_right h,ite_eq_left h,neg_neg]
      exact max_eq_right hv
  have hcost : (∑ p ∈ P,max 0 (-c p)) ≤ 7/16 := cost_eq.trans_le (major_odd_prime_cost B hB)
  let E := fun t:Finset ℕ => max 0 ((∏ p ∈ t,c p)*W (∏ p ∈ t,p))
  have hE (t) : 0 ≤ E t := le_max_left ..


  have hmass : b*(∑ t∈C,(∏p∈t,1/((p:ℝ)-1))) ≤∑ t∈P.powerset,E t := by
    rw [mul_sum]
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hC (f:=E) (fun t _ _ => hE t))
    apply sum_le_sum
    intro t ht
    have hC' : (∏p∈t,c p)=(∏p∈t,1/((p:ℝ)-1)) := by
      apply prod_congr rfl
      intro p hp
      exact ite_eq_left (hdvd t ht p hp)
    apply le_trans _ (le_max_right _ _)
    rw [hC',mul_comm]
    apply mul_le_mul_of_nonneg_left (hmin t ht) (prod_nonneg _)
    intro p hp
    have h : (1:ℝ)<p := by exact_mod_cast (hP p (mem_powerset.mp (hC ht) hp)).one_lt
    positivity
  have hcharge := powerset_signed_charging P c W (fun p hp => (hP p hp).pos) hw hm
  calc
    _ ≤ (9/16:ℝ)*∑ t∈P.powerset,E t := by linarith only [hmass]
    _ ≤ (1-∑ p∈P,max 0 (-c p))*(∑ t∈P.powerset,E t) :=
      mul_le_mul_of_nonneg_right (by linarith only [hcost]) (sum_nonneg fun t _ => hE t)
    _ ≤ _ := hcharge

open GoldbachMajorArc

theorem correctedMajorModel_smallDivisors_floor {n:ℕ} (he:Even n) (hsep:2*(cutoff n)^2<n)
    (hP0 : 0<cutoff n)
    {v:ℝ} (hv0 : 0≤v) (hv:v≤1/2) :
    (9/16:ℝ)*((31/32-v)*(n:ℝ))*smallGoodDivisorMass n (cutoff n) ≤ (modeledContribution n).re-
      v*((n-1:ℕ):ℝ)*finiteRamanujanSingularSum n (medDeskQ n) := by
  let P := cutoff n
  let T := v*((n-1:ℕ):ℝ)
  let W (q:ℕ) := if q∈Icc 1 P then kernelMass n (width n q)-T else 0
  have hn : 0<n := by omega
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hP : (0:ℝ)<P := by exact_mod_cast hP0
  have hPn : 2*(P:ℝ)≤n := by
    exact_mod_cast (show 2*P≤n by have hh : P≤P^2 := Nat.le_self_pow (by decide:2≠0) _;change 2*P^2<n at hsep;omega)
  have hT : T≤(n:ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) (n-1))
    have h' : ((n-1:ℕ):ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
    dsimp only [T];linarith
  have hvT : T≤v*(n:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n 1) hv0
  have hmass {q:ℕ} (hq:q∈Icc 1 P) :
      (n:ℝ)+2-(q:ℝ)*n/(2*P) ≤kernelMass n (width n q) := by
    obtain ⟨hl,_hr⟩ := mem_Icc.mp hq
    have hqr : (1:ℝ)≤q := by exact_mod_cast hl
    have hw : (P:ℝ)/((q:ℝ)*n)≤1/2 := by
      apply (div_le_iff₀ (mul_pos (by linarith) hN)).mpr
      nlinarith only [hPn,mul_nonneg (sub_nonneg.mpr hqr) hN.le]
    exact fejer_denominator_window_lower hn hl hP hw
  have hW (q:ℕ) : 0≤W q := by
    by_cases hq : q∈Icc 1 P
    · have hqP : (q:ℝ)≤P := by exact_mod_cast (mem_Icc.mp hq).2
      have hfrac : (q:ℝ)*n/(2*P)≤(n:ℝ)/2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hqP) hN.le]
      rw [show W q=kernelMass n (width n q)-T by simp only [W,ite_eq_left hq]]
      linarith only [hmass hq,hT,hfrac]
    · simp only [W,ite_eq_right hq,le_refl]
  have hmono (i j:ℕ) (hi : 0 < i) (hij:i≤j) : W j≤W i := by
    by_cases hj : j∈Icc 1 P
    · have hi' := mem_Icc.mpr (And.intro hi (hij.trans (mem_Icc.mp hj).2))
      simp only [W,ite_eq_left hj,ite_eq_left hi',sub_le_sub_iff_right]
      apply kernelMass_mono (by unfold width;positivity)
      unfold width
      exact div_le_div_of_nonneg_left hP.le (mul_pos (by exact_mod_cast hi) hN)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hN.le)
    · simpa only [W,ite_eq_right hj] using hW i
  have hzero (q:ℕ) (hq:P<q) : W q=0 := by
    exact ite_eq_right (fun hh=>Nat.not_le_of_lt hq (mem_Icc.mp hh).2)
  let S := (range (P+1)).filter Nat.Prime
  let C := n.primeFactors.powerset.filter (fun t => 16*(∏ p∈t,p)≤P)
  have ht (t : Finset ℕ) (ht : t∈C) : (∀ p∈t,p.Prime ∧ p∣n) ∧ 16*(∏ p∈t,p)≤P := by
    obtain ⟨hm,hq⟩ := mem_filter.mp ht
    exact ⟨fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_powerset.mp hm hp),
      Nat.dvd_of_mem_primeFactors (mem_powerset.mp hm hp)⟩,hq⟩
  have hCS : C⊆S.powerset := by
    intro t h
    refine mem_powerset.mpr (fun p hp => ?_)
    have hd := ht t h
    have hpg : p≤∏r∈t,r := single_le_prod (f:=id) (fun r hr => (hd.1 r hr).1.pos) hp
    exact mem_filter.mpr ⟨mem_range.mpr (by have := hd.2;omega),(hd.1 p hp).1⟩
  have hmin (t : Finset ℕ) (ht' : t∈C) : (31/32-v)*(n:ℝ)≤W (∏p∈t,p) := by
    let g := ∏p∈t,p
    obtain ⟨hp,hs⟩ := ht t ht'
    change 16*g≤P at hs
    have hg : 0<g := prod_pos (fun p hh => (hp p hh).1.pos)
    have hmem : g∈Icc 1 P := mem_Icc.mpr ⟨hg,by omega⟩
    have hsz : 16*(g:ℝ)≤P := by exact_mod_cast hs
    have hf : (g:ℝ)*n/(2*P)≤(n:ℝ)/32 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hsz hN.le]
    change _≤W g
    simp only [W,ite_eq_left hmem]
    linarith only [hmass hmem,hf,hvT]
  have hB := positive_family_lower n he S C (fun p hp => (mem_filter.mp hp).2)
    hCS (fun t ht' p hp => ((ht t ht').1 p hp).2) W hW hmono _ hmin
  rw [←weightedCoefficient_powerset P n W hzero] at hB
  change (9/16:ℝ)*((31/32-v)*(n:ℝ))*smallGoodDivisorMass n P≤_ at hB
  apply hB.trans_eq
  unfold modeledContribution finiteRamanujanSingularSum
  rw [Complex.re_sum,mul_sum,show medDeskQ n=cutoff n from rfl,←sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [show W q=kernelMass n (width n q)-T by simp only [W,ite_eq_left hq],Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,pinnedCoefficient_eq_ramanujan n q (mem_Icc.mp hq).1]
  dsimp only [T]
  ring



private theorem shortGoodDivisorMass_ge_two {n P : ℕ} (hn : 0<n) (he : Even n) (hP : 32≤P) :
    2≤smallGoodDivisorMass n P := by
  classical
  let C := n.primeFactors.powerset.filter (fun t => 16*(∏ p∈t,p)≤P)
  let F := fun t : Finset ℕ => ∏ p∈t,1/((p:ℝ)-1)
  have hm : 2∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,even_iff_two_dvd.mp he,hn.ne'⟩
  have hsub : ({∅,{2}}:Finset (Finset ℕ))⊆C := by
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl
    · simpa [C] using (show 16≤P by omega)
    · simpa [C,hm] using hP
  have hnon (t : Finset ℕ) (ht:t∈C) : 0≤F t := by
    apply prod_nonneg
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_filter.mp ht).1 hp)
    have hh : (1:ℝ)<p := by exact_mod_cast hp'.one_lt
    positivity
  have hsum := sum_le_sum_of_subset_of_nonneg (f:=F) hsub (fun t ht _ => hnon t ht)
  change 2≤∑ t∈C,F t
  calc
    _ = ∑ t∈({∅,{2}}:Finset (Finset ℕ)),F t := by norm_num [F]
    _ ≤ _ := hsum

private theorem cutoff_log_mean_room :
    ∀ᶠ n : ℕ in atTop, Real.log (Real.log n)+10 ≤
      (51/100:ℝ)*Real.log ((cutoff n:ℝ)/16) := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hll := Real.tendsto_log_atTop.comp hl
  filter_upwards [minorRamanujan_geometry_eventually,hl.eventually_ge_atTop 1,
    hll.eventually_ge_atTop (1000+100*Real.log 64)] with n hg hL hLL
  let L := Real.log (n:ℝ)
  let T := L^(1/8:ℝ)
  obtain ⟨_,_,h8,_,_,_,_,_,_,h16⟩ := hg
  have hsq : L^2≤4*(cutoff n:ℝ) := by
    change T^8=L at h8
    change T^16≤_ at h16
    rw [←h8,←pow_mul]
    exact h16
  change 1≤L at hL
  have hL0 : 0<L := by linarith
  have hcmp : Real.log (L^2/64) ≤ Real.log ((cutoff n:ℝ)/16) := by
    apply Real.log_le_log (by positivity)
    linarith only [hsq]
  rw [Real.log_div (pow_ne_zero _ hL0.ne') (by norm_num),Real.log_pow] at hcmp
  change 1000+100*Real.log 64 ≤ Real.log L at hLL
  change Real.log L + 10 ≤ _
  norm_num at hcmp
  linarith only [hcmp,hLL,show 0≤Real.log 64 from Real.log_nonneg (by norm_num)]


noncomputable def primeDivisorScale (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)/n.totient)

theorem actual_relative_major_floor :
    ∀ᶠ n : ℕ in atTop,Even n →
      max (n:ℝ) (primeDivisorScale n/4)+(n:ℝ)/512 ≤ (majorContribution n).re ∧
      max ((n:ℝ)/2) (primeDivisorScale n/8)+(n:ℝ)/512 ≤ adjustedMajorContribution n := by
  have hE := totalArcError_sublinear.eventually_lt_const (by norm_num : (0:ℝ)<1/1024)
  filter_upwards [primeFactor_log_mean_bound,cutoff_log_mean_room,Pinned316.GoldbachMajorArc.cutoff_tendsto.eventually_ge_atTop 32,
    cutoff_separated,high_tube_volume_eventually_half,hE,eventually_ge_atTop (1:ℕ)]
    with n hmu hlog hP hsep hv herr hn
  intro he
  let P := cutoff n
  let v := volume.real (highNaturalPrimeTubes n)
  let A := smallGoodDivisorMass n P
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hP' : 32≤P := hP
  have h2 : 2≤A := shortGoodDivisorMass_ge_two hn he hP'
  have ha := smallGoodDivisorMass_fortynine hn (by omega : 16<P) (hmu.trans hlog)
  have hF : (49/100:ℝ)*primeDivisorScale n≤(n:ℝ)*A := by
    have h := mul_le_mul_of_nonneg_left ha hn'.le
    simpa only [primeDivisorScale,mul_left_comm,mul_comm,mul_assoc] using h
  have h2' := mul_le_mul_of_nonneg_left h2 hn'.le
  have hS : (n:ℝ)≤primeDivisorScale n := by
    have hp : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
    apply le_mul_of_one_le_right hn'.le
    apply (one_le_div hp).mpr
    exact_mod_cast Nat.totient_le n
  have hraw := correctedMajorModel_smallDivisors_floor he hsep (by omega : 0<P) (v:=0) le_rfl (by norm_num)
  norm_num at hraw
  have hv0 : 0≤v := measureReal_nonneg
  have hcorrect := correctedMajorModel_smallDivisors_floor he hsep (by omega : 0<P) hv0 hv
  have hconst : (135/512:ℝ)*((n:ℝ)*A) ≤ (9/16:ℝ)*((31/32-v)*(n:ℝ))*A := by
    have hh := mul_le_mul_of_nonneg_right hv (mul_nonneg hn'.le (by linarith only [h2] : 0≤A))
    nlinarith only [hh]
  have hcorrect' := hconst.trans hcorrect
  have hdist := Complex.re_le_norm (modeledContribution n-majorContribution n)
  rw [Complex.sub_re,norm_sub_rev] at hdist
  have hcost := (div_lt_iff₀ hn').mp herr
  have hd := hdist.trans (major_error hsep)
  change (9/16:ℝ)*(31/32*(n:ℝ))*A ≤ _ at hraw
  change _≤(modeledContribution n).re-v*((n-1:ℕ):ℝ)*_ at hcorrect'
  constructor
  · rw [←le_sub_iff_add_le,max_le_iff]
    constructor <;> nlinarith only [hraw,h2',hF,hS,hd,hcost,hn'.le]
  · unfold adjustedMajorContribution
    change _≤(majorContribution n).re-v*(((n-1:ℕ):ℝ)*_)
    rw [←le_sub_iff_add_le,max_le_iff]
    constructor <;> nlinarith only [hcorrect',h2',hF,hS,hd,hcost,hn'.le]


/-- The raw minor integral is taken for the true prime weights and the same
frozen major arcs that occur in the major estimate. -/
theorem frozen_floor_of_relative_raw_minor
    (htail : ∀ᶠ n : ℕ in atTop, Even n →
      -max (n:ℝ) (primeDivisorScale n/4) ≤ primeArcMass (arcs n)ᶜ n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hall : ∀ᶠ n : ℕ in atTop, Even n → (1/512:ℝ)*n≤corr n := by
    filter_upwards [actual_relative_major_floor,htail] with n hm ht
    intro he
    have hc := corr_eq_primeArcMass n (arcs n)
      (ExtendedArcCoefficient.measurable_rational_arcs (medDeskQ n) n)
    have hmajor : primeArcMass (arcs n) n=(majorContribution n).re := (pinnedMajorContribution_real n).symm
    rw [hmajor] at hc
    linarith only [(hm he).1,ht he,hc]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/512,N,by norm_num,fun X n hX hXn _ h => hN n (hX.trans hXn) h⟩

theorem frozen_floor_of_relative_far_minor
    (htail : ∀ᶠ n : ℕ in atTop, Even n →
      -max ((n:ℝ)/2) (primeDivisorScale n/8) ≤ bothFarMinorContribution n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  have hall : ∀ᶠ n : ℕ in atTop, Even n → (1/1024:ℝ)*n≤corr n := by
    filter_upwards [actual_relative_major_floor,htail,bothFarMinorContribution_approx (ε:=1/1024) (by norm_num)]
      with n hm ht happrox
    intro he
    have hw (k : ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity
    have hc : 0≤corr n := sum_nonneg (fun k _ => mul_nonneg (hw k) (hw _))
    have hv := mul_nonneg (measureReal_nonneg (μ:=volume) (s:=highNaturalPrimeTubes n)) hc
    linarith only [(hm he).2,ht he,(abs_le.mp happrox).1,hv]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  exact ⟨1/1024,N,by norm_num,fun X n hX hXn _ h => hN n (hX.trans hXn) h⟩

end GoldbachPartial