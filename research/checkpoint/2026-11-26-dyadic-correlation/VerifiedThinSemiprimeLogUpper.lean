import VerifiedBrunLogEulerTail
import VerifiedThinSemiprimeUpper
namespace GoldbachPartial
open Finset

private theorem thinTotientRatio (m : ℕ) (hm : 0<m) :
    (m.totient:ℝ)/m=∏p∈m.primeFactors,(1-(p:ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors m)
  push_cast at h
  apply (div_eq_iff (by positivity : (m:ℝ)≠0)).mpr
  simpa only [mul_comm] using h

private theorem thinLog_le_harmonic (z : ℕ) : Real.log ((z:ℝ)+1)≤∑a∈Icc 1 z,(a:ℝ)⁻¹ := by
  induction z with
  | zero => norm_num
  | succ z ih =>
    rw [sum_Icc_succ_top (by omega : 1≤z+1)]
    push_cast
    have h : (0:ℝ)<(z:ℝ)+1 := by positivity
    have hl := Real.log_le_sub_one_of_pos (show (0:ℝ)<((z:ℝ)+1+1)/(z+1) by positivity)
    rw [Real.log_div (by positivity) h.ne'] at hl
    have he : ((z:ℝ)+1+1)/(z+1)-1=((z:ℝ)+1)⁻¹ := by field_simp; ring
    rw [he] at hl
    linarith only [hl,ih]

theorem thinEuler_prime_product_log (z : ℕ) :
    Real.log ((z:ℝ)+1)*(∏p∈(Icc 2 z).filter Nat.Prime,(1-(p:ℝ)⁻¹))≤1 := by
  let m := z.factorial
  have hm : 0<m := Nat.factorial_pos _
  have hP : m.primeFactors=(Icc 2 z).filter Nat.Prime := by
    ext p
    simp only [m,Nat.mem_primeFactors,mem_filter,mem_Icc]
    constructor
    · rintro ⟨hp,hd,_⟩
      exact ⟨⟨hp.two_le,hp.dvd_factorial.mp hd⟩,hp⟩
    · rintro ⟨⟨_,h⟩,hp⟩
      exact ⟨hp,hp.dvd_factorial.mpr h,hm.ne'⟩
  have hsub : Icc 1 z ⊆ m.divisors := by
    intro a ha
    have hh:=mem_Icc.mp ha
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hh.1 hh.2,hm.ne'⟩
  have hbound (a : ℕ) (ha : a∈Icc 1 z) : (m.totient:ℝ)*(a:ℝ)⁻¹≤((m/a).totient:ℝ) := by
    have had := (Nat.mem_divisors.mp (hsub ha)).1
    have ha0 : 0<a := (mem_Icc.mp ha).1
    have hab : a*(m/a)=m := Nat.mul_div_cancel' had
    have hb : 0<m/a := by exact Nat.div_pos (Nat.le_of_dvd hm had) ha0
    have hpsub := Nat.primeFactors_mono (Nat.div_dvd_of_dvd had) hm.ne'
    have hq : (m.totient:ℝ)/m≤((m/a).totient:ℝ)/(m/a:ℕ) := by
      rw [thinTotientRatio m hm,thinTotientRatio _ hb]
      apply prod_le_prod_of_subset_of_le_one₀ hpsub
      · intro p hp
        have h : (1:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
        exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
      · intro p _ _
        linarith only [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) p)]
    have h1 : (0:ℝ)<m := by exact_mod_cast hm
    have h2 : (0:ℝ)<(m/a:ℕ) := by exact_mod_cast hb
    have h3 : (0:ℝ)<a := by exact_mod_cast ha0
    have h4 : (a:ℝ)*((m/a:ℕ):ℝ)=(m:ℝ) := by exact_mod_cast hab
    rw [div_le_div_iff₀ h1 h2,←h4] at hq
    rw [←div_eq_mul_inv,div_le_iff₀ h3]
    exact (mul_le_mul_iff_left₀ h2).mp (by linarith only [hq])
  have hs : (m.totient:ℝ)*(∑a∈Icc 1 z,(a:ℝ)⁻¹) ≤ m := by
    rw [mul_sum]
    calc
      _ ≤ ∑a∈Icc 1 z,((m/a).totient:ℝ) := sum_le_sum hbound
      _ ≤ ∑a∈m.divisors,((m/a).totient:ℝ) := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := by exact_mod_cast (Nat.sum_div_divisors m Nat.totient).trans (Nat.sum_totient m)
  rw [←hP,←thinTotientRatio m hm,mul_div_assoc',div_le_iff₀ (by positivity : (0:ℝ)<m),one_mul,mul_comm]
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact thinLog_le_harmonic z

def thinRegularPrimes (m z : ℕ) : Finset ℕ := ((Icc 2 z).filter Nat.Prime).filter (fun p=>¬p∣m)

theorem thinRegularPrimes_density (m z : ℕ) (hm : 0<m) :
    ((Real.log ((z:ℝ)+1))*((m.totient:ℝ)/m))^2*
      (∏p∈thinRegularPrimes m z,(1-(2:ℝ)/p))≤1 := by
  let P := (Icc 2 z).filter Nat.Prime
  let G := thinRegularPrimes m z
  let F := P.filter (fun p=>p∣m)
  let g (p : ℕ) := 1-(p:ℝ)⁻¹
  have hg {p : ℕ} (hp : p.Prime) : 0≤g p := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le))
  have hGP (p : ℕ) (hp : p∈G) : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
  have hfun : (∏p∈G,g p)*(∏p∈F,g p)=∏p∈P,g p := by
    have h := prod_filter_mul_prod_filter_not P (fun p => p∣m) g
    rw [mul_comm]; exact h
  have hFsub : F⊆m.primeFactors := by
    intro p hp
    obtain ⟨hp',hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp').2,hd,hm.ne'⟩
  have hF : (m.totient:ℝ)/m≤∏p∈F,g p := by
    rw [thinTotientRatio m hm]
    apply prod_le_prod_of_subset_of_le_one₀ hFsub
    · exact fun p hp => hg (Nat.prime_of_mem_primeFactors hp)
    · intro p _ _
      linarith only [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) p)]
  have hD : (∏p∈G,(1-(2:ℝ)/p))≤(∏p∈G,g p)^2 := by
    rw [←prod_pow]
    apply prod_le_prod₀
    · intro p hp
      have hh : (2:ℝ)≤p := by exact_mod_cast (hGP p hp).two_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hh)
    · intro p _
      dsimp only [g]
      rw [div_eq_mul_inv]
      nlinarith only [sq_nonneg (p:ℝ)⁻¹]
  let lg := Real.log ((z:ℝ)+1)
  have hl : 0≤lg := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) z; linarith)
  have hG : 0≤∏p∈G,g p := prod_nonneg fun p hp => hg (hGP p hp)
  have hmain : lg*(((m.totient:ℝ)/m)*(∏p∈G,g p))≤1 := by
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF hG) hl).trans
    rw [mul_comm (∏p∈F,g p),hfun]
    exact thinEuler_prime_product_log z
  have h0 : 0≤lg*(((m.totient:ℝ)/m)*(∏p∈G,g p)) :=
    mul_nonneg hl (mul_nonneg (by positivity) hG)
  calc
    _ ≤ (lg*((m.totient:ℝ)/m))^2*(∏p∈G,g p)^2 := mul_le_mul_of_nonneg_left hD (sq_nonneg _)
    _ = (lg*(((m.totient:ℝ)/m)*(∏p∈G,g p)))^2 := by ring
    _ ≤ 1 := by nlinarith only [mul_nonneg h0 (sub_nonneg.mpr hmain),hmain]

theorem thinRegularPrimes_generator (m z : ℕ) (h2 : 2∣m) :
    (∏p∈thinRegularPrimes m z,(1+(4:ℝ)/p))≤(64*(1+Real.log z))^4 := by
  let G := thinRegularPrimes m z
  have hP (p : ℕ) (hp : p∈G) : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
  have hz : G⊆Icc 3 z := by
    intro p hp
    have hi := mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1
    have hne : p≠2 := by rintro rfl; exact (mem_filter.mp hp).2 h2
    exact mem_Icc.mpr ⟨by omega,hi.2⟩
  have hG := brunEuler_positive_product_log_bound z G hz hP
  have H (p : ℕ) (hp : p∈G) : 0≤brunEulerWeight p :=
    (brunEulerWeight_bounds (mem_Icc.mp (hz hp)).1).1
  calc
    _ ≤ ∏p∈G,(1+brunEulerWeight p)^4 := by
      apply prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      have h3 : (3:ℝ)≤p := by exact_mod_cast (mem_Icc.mp (hz hp)).1
      have h1 : 1/(p:ℝ)≤brunEulerWeight p := by
        exact one_div_le_one_div_of_le (by linarith : (0:ℝ)<p-1) (by linarith)
      have hb := H p hp
      have hb3 := pow_nonneg hb 3
      rw [show (4:ℝ)/(p:ℝ)=4*(1/(p:ℝ)) by ring]
      nlinarith only [h1,hb3,sq_nonneg (brunEulerWeight p),sq_nonneg ((brunEulerWeight p)^2)]
    _ = (∏p∈G,(1+brunEulerWeight p))^4 := prod_pow ..
    _ ≤ _ := pow_le_pow_left₀ (prod_nonneg (fun p hp => by linarith only [H p hp])) hG 4

theorem thinTotient_loglog (m : ℕ) (hm : 1≤Real.log m) :
    (m:ℝ)/m.totient ≤ 128*(1+Real.log (Real.log m)) := by
  let L := Real.log m
  let Y := ⌈L⌉₊
  let U := (16*Y)^2
  have hm0 : 0<m := by
    by_contra! h
    have hm' : m=0 := by omega
    norm_num [hm'] at hm
  have hL : 1≤L := hm
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hY : L≤(Y:ℝ) := Nat.le_ceil _
  have hY0 : (0:ℝ)<Y := hL0.trans_le hY
  have hY1 : 0<Y := by exact_mod_cast hY0
  have hU : 1<U := by dsimp only [U];nlinarith only [hY1,Nat.succ_le_of_lt hY1]
  have hYb : (Y:ℝ)≤2*L := by linarith only [Nat.ceil_lt_add_one hL0.le,hL]
  have huLog : Real.log U=2*(4*Real.log 2+Real.log Y) := by
    dsimp only [U];push_cast
    rw [Real.log_pow,Real.log_mul (by norm_num) hY0.ne',show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have h2lo := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
  norm_num at h2lo
  have hmean : (∑p∈m.primeFactors,Real.log p/(p:ℝ)) ≤ (1/2:ℝ)*Real.log (((16*U:ℕ):ℝ)/16) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,show (16*(U:ℝ))/16=(U:ℝ) by ring,huLog]
    have h := primeFactor_log_mean_bound_sharp hm
    rw [h4] at h
    change _ ≤ Real.log L + 2*Real.log 2+1 at h
    linarith only [h,Real.log_le_log hL0 hY,h2lo]
  have htot := (smallGoodDivisorMass_of_log_mean hm0 (by omega : 16<16*U) (1/2) hmean).trans
    (smallGoodDivisorMass_totient_bound m U)
  have hlogY := Real.log_le_log hY0 hYb
  rw [Real.log_mul (by norm_num) hL0.ne'] at hlogY
  rw [huLog] at htot
  change _≤128*(1+Real.log L)
  linarith only [htot,hlogY,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_nonneg hL]

theorem thinPrimePairSet_log_upper (n L X z K : ℕ) (hL : 0<L) (hz : 1≤z) (hK : Even K)
    (he : 2∣n*L) (hm : 1≤Real.log (n*L:ℕ)) :
    ((thinPrimePairSet n L X).card:ℝ)≤2*(z:ℝ) +
      (X:ℝ)*((128*(1+Real.log (Real.log (n*L:ℕ)))/Real.log ((z:ℝ)+1))^2+
        (64*(1+Real.log z))^4/(2:ℝ)^(K+1))+(z:ℝ)^K*(2:ℝ)^K := by
  let m := n*L
  let G := thinRegularPrimes m z
  have hm0 : 0<m := by
    by_contra! h
    have hh : n*L=0 := by change m=0; omega
    norm_num [hh] at hm
  have hD := thinRegularPrimes_density m z hm0
  let v := ∏p∈G,(1-(2:ℝ)/p)
  let w := 128*(1+Real.log (Real.log m))
  let l := Real.log ((z:ℝ)+1)
  have hl : 0<l := Real.log_pos (by
    have hz' : (1:ℝ)≤z := by exact_mod_cast hz
    linarith only [hz'])
  have hm' : (0:ℝ)<m := by exact_mod_cast hm0
  have ht : (0:ℝ)<m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have htmp : v≤(1/(l*((m.totient:ℝ)/m)))^2 := by
    rw [div_pow,one_pow,le_div_iff₀ (by positivity),mul_comm]
    exact hD
  have hRatio : 1/(l*((m.totient:ℝ)/m))≤ w/l := by
    rw [show 1/(l*((m.totient:ℝ)/m))=((m:ℝ)/m.totient)/l by field_simp]
    exact div_le_div_of_nonneg_right (thinTotient_loglog m hm) hl.le
  have hfinal := htmp.trans (pow_le_pow_left₀ (by positivity) hRatio 2)
  have hP (p : ℕ) (hp : p∈G) : p.Prime ∧ ¬p∣n ∧ ¬p∣L := by
    have h := (mem_filter.mp hp).2
    exact ⟨(mem_filter.mp (mem_filter.mp hp).1).2,fun hd=>h (dvd_mul_of_dvd_left hd L),
      fun hd=>h (dvd_mul_of_dvd_right hd n)⟩
  have hmax (p : ℕ) (hp : p∈G) : p≤z := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
  apply (thinPrimePairSet_upper n L X z K G hL hz hK hP hmax).trans
  gcongr
  exact thinRegularPrimes_generator m z he

end GoldbachPartial