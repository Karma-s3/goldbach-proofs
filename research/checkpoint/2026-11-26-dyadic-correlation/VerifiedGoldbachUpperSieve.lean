import VerifiedThinBlockEulerUpper
import VerifiedThinBlockRows

namespace GoldbachPartial
open Finset Filter
open scoped Classical
noncomputable section

private theorem thinPairCard_le_survivors (n L X z : ℕ) (B : Finset ℕ) (hL : 0<L)
    (hB : ∀p∈B,p.Prime ∧ ¬p∣n ∧ ¬p∣L) (hBz : ∀p∈B,p≤z) :
    (thinPrimePairSet n L X).card≤2*z+thinSurvivors n L X B := by
  let A := thinPrimePairSet n L X
  let C := A.filter (fun b=>n-L*b≤z)
  let U := (Ioc 0 X).filter (fun b => ∀p∈B,¬thinBad n L b p)
  have hsmall : C.card≤z := by
    have hm : C.card≤(Ioc 0 z).card := by
      apply card_le_card_of_injOn (fun b=>n-L*b)
      · intro b hb
        obtain ⟨hbA,hbz⟩ := mem_filter.mp hb
        exact mem_Ioc.mpr ⟨(mem_filter.mp hbA).2.2.pos,hbz⟩
      · intro b hb c hc he
        have h1 := (mem_filter.mp (mem_filter.mp hb).1).2.2.pos
        have h2 := (mem_filter.mp (mem_filter.mp hc).1).2.2.pos
        change n-L*b=n-L*c at he
        exact Nat.eq_of_mul_eq_mul_left hL (by omega : L*b=L*c)
    simpa using hm
  have hsub : A⊆(Ioc 0 z)∪C∪U := by
    intro b hb
    obtain ⟨hbI,hbp,hpp⟩ := mem_filter.mp hb
    by_cases hbz : b≤z
    · exact mem_union_left _ (mem_union_left _ (mem_Ioc.mpr ⟨(mem_Ioc.mp hbI).1,hbz⟩))
    by_cases hpz : n-L*b≤z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hb,hpz⟩))
    apply mem_union_right _ (mem_filter.mpr ⟨hbI,?_⟩)
    intro p hp hbad
    have hln : L*b≤n := by have hpos:=hpp.pos; omega
    have hv := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left b hln)).mp hbad
    rw [←Nat.mul_sub] at hv
    rcases (hB p hp).1.dvd_mul.mp hv with h|h
    · exact hbz ((Nat.prime_dvd_prime_iff_eq (hB p hp).1 hbp).mp h ▸ hBz p hp)
    · exact hpz ((Nat.prime_dvd_prime_iff_eq (hB p hp).1 hpp).mp h ▸ hBz p hp)
  have hcard := (card_le_card hsub).trans (card_union_le ..)
  have hcard' := card_union_le (Ioc 0 z) C
  have hc : A.card≤2*z+U.card := by simp only [Nat.card_Ioc,Nat.sub_zero] at hcard'; omega
  exact hc

theorem corr_le_card_thin_pairs (n : ℕ) :
    corr n≤((thinPrimePairSet n 1 n).card:ℝ)*(Real.log n)^2 := by
  let S := thinPrimePairSet n 1 n
  have hr : S=(range (n+1)).filter (fun b=>b.Prime ∧ (n-b).Prime) := by
    ext p
    simp only [S,thinPrimePairSet,one_mul,mem_filter,mem_range_succ_iff,mem_Ioc]
    constructor
    · rintro ⟨⟨_,h⟩,hp,hn⟩;exact ⟨h,hp,hn⟩
    · rintro ⟨h,hp,hn⟩;exact ⟨⟨hp.pos,h⟩,hp,hn⟩
  have hcorr : corr n=∑p∈S, Real.log p*Real.log (n-p:ℕ) := by
    rw [hr,corr,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> by_cases hq : (n-p).Prime <;> simp [weight,hp,hq]
  rw [hcorr]
  calc
    _ ≤ ∑_p∈S,(Real.log n)^2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨h1,h2,h3⟩ := mem_filter.mp (hr ▸ hp)
      rw [pow_two]
      exact mul_le_mul
        (Real.log_le_log (by exact_mod_cast h2.pos) (by exact_mod_cast mem_range_succ_iff.mp h1))
        (Real.log_le_log (by exact_mod_cast h3.pos) (by exact_mod_cast Nat.sub_le n p))
        (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := by simp [S]

theorem thinPrimePairSet_fixedBlock_upper (n J : ℕ) (he : Even n) (hn : 0<n) :
    let z := brunBlockBoundary J
    ((thinPrimePairSet n 1 n).card:ℝ) ≤ 2*(z:ℝ) +
      (n:ℝ)*Real.exp 1*((((n:ℝ)/n.totient)/Real.log ((z:ℝ)+1))^2)+(z:ℝ)^202 := by
  let z := brunBlockBoundary J
  let G := thinRegularPrimes n z
  have h2 : 2≤z := brunBlockBoundary_mono (Nat.zero_le J)
  have hG (p : ℕ) (hp : p∈G) := mem_filter.mp hp
  have hpr (p : ℕ) (hp : p∈G) : p.Prime := (mem_filter.mp (hG p hp).1).2
  have hB : G⊆Icc 3 z := by
    intro p hp
    have hi := mem_Icc.mp (mem_filter.mp (hG p hp).1).1
    have hne : p≠2 := fun h => (hG p hp).2 (h ▸ even_iff_two_dvd.mp he)
    exact mem_Icc.mpr ⟨by omega,hi.2⟩
  have hs : ((thinPrimePairSet n 1 n).card:ℝ)≤2*(z:ℝ)+thinSurvivors n 1 n G := by
    exact_mod_cast thinPairCard_le_survivors n 1 n z G (by decide)
      (fun p hp => ⟨hpr p hp,(hG p hp).2,(hpr p hp).not_dvd_one⟩)
      (fun p hp => (mem_Icc.mp (hB hp)).2)
  let D := ∏p∈G,(1-(2:ℝ)/p)
  have hed := thinRegularPrimes_density n z hn
  let l := Real.log ((z:ℝ)+1)
  have hl : 0<l := Real.log_pos (by
    have hz : (0:ℝ)<z := by exact_mod_cast (by omega : 0<z)
    linarith only [hz])
  have ht : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hE : D≤(((n:ℝ)/n.totient)/l)^2 := by
    have hh : D≤(1/(l*(n.totient/n:ℝ)))^2 := by
      rw [div_pow,one_pow,le_div_iff₀ (by positivity),mul_comm]
      exact hed
    convert hh using 1
    field_simp
  have hmodel := thinBrunBlock_model_upper J G hB hpr
  have hfull := thinSurvivors_even_regular_block_upper n J he
  dsimp only at hfull ⊢
  apply hs.trans
  change 2*(z:ℝ)+thinSurvivors n 1 n G≤_
  have h1 := mul_le_mul_of_nonneg_left hmodel (Nat.cast_nonneg (α:=ℝ) n)
  have h2 := mul_le_mul_of_nonneg_left hE (show 0≤(n:ℝ)*Real.exp 1 by positivity)
  change (thinSurvivors n 1 n G:ℝ)≤_ at hfull
  change _≤(n:ℝ)*(Real.exp 1*D) at h1
  change _≤2*(z:ℝ)+(n:ℝ)*Real.exp 1*(((n:ℝ)/n.totient)/l)^2+(z:ℝ)^202
  linarith only [hfull,h1,h2]

set_option exponentiation.threshold 1000 in
theorem corr_upper_totient_sq (n : ℕ) (he : Even n) :
    corr n ≤ (Real.exp 1+3)*808^2*(n:ℝ)*((n:ℝ)/n.totient)^2 := by
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp [corr,weight]
  let N := (n:ℝ)
  let R := (n:ℝ)/n.totient
  let L := Real.log n
  have hN : 0≤N := Nat.cast_nonneg _
  have hL : 0≤L := Real.log_natCast_nonneg _
  have ht : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hR : 1≤R := by
    apply (one_le_div ht).mpr
    exact_mod_cast Nat.totient_le n
  have hR2 : 1≤R^2 := one_le_pow₀ hR
  have hNR : N≤N*R^2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR2 hN
  let c (j : ℕ) := (brunBlockBoundary j)^404
  by_cases hsmall : n<c 0
  · have hlog := Real.log_le_log (by exact_mod_cast hn : (0:ℝ)<n)
      (show (n:ℝ)≤(2:ℝ)^404 by exact_mod_cast hsmall.le)
    rw [Real.log_pow] at hlog
    norm_num at hlog
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hlu : L≤404 := by dsimp only [L]; linarith only [hlog,h2]
    have hp : (thinPrimePairSet n 1 n).card≤n := by
      apply le_trans (card_le_card (filter_subset ..)) _
      simp
    have hC := (corr_le_card_thin_pairs n).trans
      (mul_le_mul (show ((thinPrimePairSet n 1 n).card:ℝ)≤N by dsimp only [N];exact_mod_cast hp)
        (pow_le_pow_left₀ hL hlu 2) (sq_nonneg _) hN)
    change _≤(Real.exp 1+3)*808^2*N*R^2
    have h0 := mul_nonneg (Real.exp_pos 1).le (mul_nonneg hN (sq_nonneg R))
    linarith only [hC,hNR,hN,h0]
  have hseq : Tendsto c atTop atTop := by
    apply tendsto_atTop.2
    intro v
    filter_upwards [eventually_ge_atTop v] with j hj
    have h1 : j≤2^j := (show j<2^j from Nat.lt_two_pow_self).le
    have h2 : 2^j≤brunBlockBoundary j := (show 2^j<2^(2^j) from Nat.lt_two_pow_self).le
    have h3 : brunBlockBoundary j≤c j := by
      dsimp only [c]
      calc _ = (brunBlockBoundary j)^1 := by simp
           _ ≤ _ := Nat.pow_le_pow_right (by dsimp [brunBlockBoundary]; exact Nat.one_le_two_pow) (by decide)
    exact hj.trans (h1.trans (h2.trans h3))
  obtain ⟨j,_hj,hlo,hhi⟩ := hseq.exists_le_lt_succ (Nat.le_of_not_gt hsmall)
  let z := brunBlockBoundary j
  have hz2 : 2≤z := brunBlockBoundary_mono (Nat.zero_le j)
  have hzR : (1:ℝ)≤z := by exact_mod_cast (by omega : 1≤z)
  have hz0 : (0:ℝ)<z := zero_lt_one.trans_le hzR
  have heq : brunBlockBoundary (j+1)=(brunBlockBoundary j)^2 := by
    rw [brunBlockBoundary,brunBlockBoundary,pow_succ,pow_mul]
  have hhi' : n<z^808 := by simpa only [c,heq,←pow_mul] using hhi
  have h404 : (z:ℝ)^404≤N := by
    change z^404≤n at hlo
    dsimp only [N]; exact_mod_cast hlo
  have hlog := Real.log_le_log (by exact_mod_cast hn : (0:ℝ)<n)
    (show (n:ℝ)≤(z:ℝ)^808 by exact_mod_cast hhi'.le)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  let l := Real.log ((z:ℝ)+1)
  have hl : 0<l := Real.log_pos (by linarith only [hz0])
  have hlog' : L≤808*l := by
    have hg := Real.log_le_log hz0 (show (z:ℝ)≤(z:ℝ)+1 by linarith)
    change L≤808*Real.log (z:ℝ) at hlog
    dsimp only [l];linarith only [hg,hlog]
  have hlogz : L≤808*z := by
    change L≤808*Real.log (z:ℝ) at hlog
    linarith only [hlog,Real.log_le_sub_one_of_pos hz0]
  have hMain : (R/l)^2*L^2 ≤ 808^2*R^2 := by
    have hdiv : R*(L/l)≤808*R := by
      rw [mul_comm (808:ℝ) R]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hl).mpr hlog') (zero_le_one.trans hR)
    calc _ = (R*(L/l))^2 := by ring
         _ ≤ (808*R)^2 := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hR) (div_nonneg hL hl.le)) hdiv 2
         _ = _ := by ring
  have herr : (2*(z:ℝ)+(z:ℝ)^202)*L^2 ≤ 3*808^2*N := by
    have h202 : (z:ℝ)≤(z:ℝ)^202 := by
      simpa only [pow_one] using pow_le_pow_right₀ hzR (show 1≤202 by decide)
    have h204 := (pow_le_pow_right₀ hzR (show 204≤404 by decide)).trans h404
    calc _ ≤ (3*(z:ℝ)^202)*(808*z)^2 := mul_le_mul (by linarith only [h202])
             (pow_le_pow_left₀ hL hlogz 2) (sq_nonneg _) (by positivity)
         _ = (3*808^2)*(z:ℝ)^204 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left h204 (by norm_num)
  have hp := thinPrimePairSet_fixedBlock_upper n j he hn
  change ((thinPrimePairSet n 1 n).card:ℝ)≤2*(z:ℝ)+N*Real.exp 1*(R/l)^2+(z:ℝ)^202 at hp
  have hA := (corr_le_card_thin_pairs n).trans (mul_le_mul_of_nonneg_right hp (sq_nonneg L))
  have hB := mul_le_mul_of_nonneg_left hMain (mul_nonneg hN (Real.exp_pos 1).le)
  change corr n ≤ (Real.exp 1+3)*808^2*N*R^2
  linarith only [hA,hB,herr,hNR]

end
end GoldbachPartial