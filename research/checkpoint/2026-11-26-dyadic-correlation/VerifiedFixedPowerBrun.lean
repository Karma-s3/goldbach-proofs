import VerifiedBrunBlockSupport
import VerifiedBrunJoinedModelHalf
import VerifiedBrunJoinedRows
import VerifiedBrunLogEulerTail
namespace GoldbachPartial
open Finset Filter
open scoped Topology

noncomputable def polylogSieveLevel (a n : ℕ) := ⌊(Real.log n)^a⌋₊
noncomputable def polylogBlockIndex (a n : ℕ) := Nat.log 2 (Nat.log 2 (polylogSieveLevel a n))+1

theorem polylogBlockIndex_bounds {y : ℕ} (hy : 2≤y) :
    let J := Nat.log 2 (Nat.log 2 y)+1
    y≤brunBlockBoundary J ∧ brunBlockBoundary J≤y^2 := by
  let s := Nat.log 2 y
  let k := Nat.log 2 s
  have hs : 0<s := Nat.log_pos (by decide) hy
  have hsk : s<2^(k+1) := Nat.lt_pow_succ_log_self (by decide) _
  have hks : 2^k≤s := Nat.pow_log_le_self 2 hs.ne'
  have h1 : 2^s≤y := Nat.pow_log_le_self 2 (by omega)
  have h2 : y<2^(s+1) := Nat.lt_pow_succ_log_self (by decide) _
  change y≤2^(2^(k+1)) ∧ 2^(2^(k+1))≤y^2
  constructor
  · exact h2.le.trans (Nat.pow_le_pow_right (by decide) hsk)
  · have he : 2^(k+1)≤s*2 := by rw [pow_succ];omega
    exact (Nat.pow_le_pow_right (by decide) he).trans (by rw [pow_mul]; exact Nat.pow_le_pow_left h1 _)

theorem fixedPower_sieve_geometry (a : ℕ) (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop, let y := polylogSieveLevel a n
      let z := brunBlockBoundary (polylogBlockIndex a n)
      2≤y ∧ y≤z ∧ z≤y^2 ∧ z≤n/4 ∧ ((z^101:ℕ):ℝ)≤(Real.log n)^(202*a) := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hf := tendsto_nat_floor_atTop.comp ((tendsto_pow_atTop ha.ne').comp hl)
  have hr : Tendsto (fun n : ℕ => (Real.log n)^(2*a)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop ((2*a:ℕ):ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hf.eventually_ge_atTop 2,hr.eventually_lt_const (by norm_num : (0:ℝ)<1/4),
    eventually_ge_atTop (1:ℕ)] with n hh hsmall hn
  let y := polylogSieveLevel a n
  let z := brunBlockBoundary (polylogBlockIndex a n)
  have hy : 2≤y := hh
  obtain ⟨hlo,hup⟩ := polylogBlockIndex_bounds hy
  change y≤z at hlo
  change z≤y^2 at hup
  have hyL : (y:ℝ)≤(Real.log n)^a := Nat.floor_le (by positivity)
  have hzp : (z:ℝ)≤(Real.log n)^(2*a) := calc
    _ ≤ (y:ℝ)^2 := by exact_mod_cast hup
    _ ≤ ((Real.log n)^a)^2 := pow_le_pow_left₀ (by positivity) hyL _
    _ = _ := by rw [←pow_mul,mul_comm a 2]
  have hpos : 0<(n:ℝ) := by exact_mod_cast hn
  refine ⟨hy,hlo,hup,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le (by decide)).mpr
    exact_mod_cast (show (z:ℝ)*4≤n by linarith only [hzp,(div_lt_iff₀ hpos).mp hsmall])
  · rw [Nat.cast_pow]
    calc
      _ ≤ ((Real.log n)^(2*a))^101 := pow_le_pow_left₀ (by positivity) hzp _
      _ = _ := by rw [←pow_mul];congr 1;ring
private theorem brun_signed_row_error (n z J : ℕ) (B : Finset ℕ)
    (hB : B⊆Icc 3 (brunBlockBoundary J)) (hprime : ∀p∈B,p.Prime)
    (hz : z=brunBlockBoundary J) (D : ℝ) (hD : 0≤D)
    (hrow : ∀S⊆B,(∏p∈S,p)≤z^101 →
      |fixedTargetDivisorRow n (∏p∈S,p)-((n/2-n/4:ℕ):ℝ)*∏p∈S,1/((p:ℝ)-1)|≤D) :
    let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
    let h : ℝ := (n/2-n/4:ℕ)
    |(∑S∈B.powerset,c S*fixedTargetDivisorRow n (∏p∈S,p))-
      h*(∑S∈B.powerset,c S*∏p∈S,1/((p:ℝ)-1))| ≤ ((z^101:ℕ):ℝ)*D := by
  classical
  subst z
  let z := brunBlockBoundary J
  let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
  let W := B.powerset.filter (fun S => c S≠0)
  let h : ℝ := (n/2-n/4:ℕ)
  have hf (S : Finset ℕ) (hS:S∈W) : S⊆B ∧ ∃ e : ℕ, ∀ i<J,
      (S∩brunSieveBlock B i).card≤brunBlockOrder J i+(if i=e then 1 else 0) := by
    obtain ⟨hS,hc⟩ := mem_filter.mp hS
    obtain ⟨e,he⟩ := brunJoinedCoefficient_support _ _ _ _ hc
    exact ⟨mem_powerset.mp hS,e,fun i hi => he i (mem_range.mpr hi)⟩
  have hW : W.card≤z^101 := brunBlock_supported_family_card J B W hB hprime hf
  let R := fun S => fixedTargetDivisorRow n (∏p∈S,p)
  let A := fun S : Finset ℕ => ∏p∈S,1/((p:ℝ)-1)
  have hfilter (g : Finset ℕ→ℝ) : (∑S∈W,c S*g S)=∑S∈B.powerset,c S*g S := by
    rw [sum_filter]
    apply sum_congr rfl
    intro S _
    by_cases hc : c S=0 <;> simp [hc]
  change |(∑S∈B.powerset,c S*R S)-h*(∑S∈B.powerset,c S*A S)|≤_
  rw [←hfilter R,←hfilter A,mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑_S∈W,D := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hsub,e,he⟩ := hf S hS
      have hsize := brunBlock_subset_product_le J e B S hB hsub he
      have ha : |R S-h*A S|≤D := hrow S hsub hsize
      rw [show c S*R S-h*(c S*A S)=c S*(R S-h*A S) by ring,abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (brunJoinedCoefficient_abs_le ..)).trans ha
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hW) hD


theorem fixedPower_Brun_mass (a : ℕ) (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop, Even n →
      (n:ℝ)/(8192*(1+Real.log (polylogSieveLevel a n))) ≤
        fixedTargetBrunSurvivorMass n (polylogSieveLevel a n) := by
  classical
  let m := 202*a
  obtain ⟨C,hC,hu⟩ := fixedTarget_Brun_subset_row m (m+3)
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hu,fixedPower_sieve_geometry a ha,eventually_ge_atTop (20:ℕ),
    hL.eventually_ge_atTop (max 1 (8192*C*((a:ℝ)+1)))] with n hp hg hn hL'
  intro he
  let L := Real.log n
  let y := polylogSieveLevel a n
  let J := polylogBlockIndex a n
  let z := brunBlockBoundary J
  let B := fixedTargetBrunPrimes n z
  let c := brunJoinedCoefficient (range J) (brunSieveBlock B) (brunBlockOrder J)
  let h : ℝ := (n/2-n/4:ℕ)
  let D := 1+Real.log y
  have hLp : 0<L := zero_lt_one.trans_le ((le_max_left 1 _).trans hL')
  have hL1 : 1≤L := (le_max_left 1 _).trans hL'
  have hLn : 0≤(n:ℝ) := by positivity
  obtain ⟨hy,hyz,hzy,hzn,hbig⟩ := hg
  change 2≤y at hy
  change z≤y^2 at hzy
  change ((z^101:ℕ):ℝ)≤L^m at hbig
  have hy0 : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hz0 : (0:ℝ)<z := by exact_mod_cast (show 0<z from lt_of_lt_of_le (by omega : 0<y) hyz)
  have hDp : 0<D := by dsimp [D];positivity
  have hpr (p : ℕ) (hp:p∈B) : p.Prime ∧ p∈Icc 3 z := by
    obtain ⟨hm,hp',hd⟩ := mem_filter.mp hp
    have hne : p≠2 := fun h => hd (h ▸ even_iff_two_dvd.mp he)
    exact ⟨hp',mem_Icc.mpr ⟨by have := hp'.two_le;omega,by have := mem_range.mp hm;omega⟩⟩
  have hB : B⊆Icc 3 z := fun p hp => (hpr p hp).2
  have hP := fun p hp => (hpr p hp).1
  have hV := brunEuler_product_log_lower z B hB hP
  have hM := brunBlock_joined_model_half J B hB hP
  have hZY : Real.log z ≤ 2*Real.log y := by
    have h := Real.log_le_log hz0 (by exact_mod_cast hzy : (z:ℝ)≤(y:ℝ)^2)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have h512 : 1/(512*D)≤(1/2:ℝ)*(∏p∈B,(1-brunEulerWeight p)) := by
    have hh : (1/(256*D):ℝ)≤1/(128*(1+Real.log z)) := by
      apply one_div_le_one_div_of_le (by positivity)
      dsimp only [D];linarith only [hZY,Real.log_natCast_nonneg y]
    have hmul := mul_le_mul_of_nonneg_left (hh.trans hV) (by norm_num : 0≤(1/2:ℝ))
    convert hmul using 1
    field_simp; norm_num
  have hsmodel := h512.trans hM
  have hlen : (n:ℝ)/8≤h := by
    have h': n≤8*(n/2-n/4) := by omega
    dsimp [h]; have hr : (n:ℝ)≤8*((n/2-n/4:ℕ):ℝ) := by exact_mod_cast h'
    linarith only [hr]
  have hprod := mul_le_mul hlen hsmodel (by positivity) (by dsimp [h];positivity)
  have hx := brun_signed_row_error n z J B hB hP rfl (C*n/L^(m+3)) (by positivity)
    (fun S hS hs => hp z S hS ((by exact_mod_cast hs : ((∏p∈S,p:ℕ):ℝ)≤(z^101:ℕ)).trans hbig))
  have hSW : ((z^101:ℕ):ℝ)*(C*n/L^(m+3))≤C*n/L^3 := calc
    _ ≤ (L^m)*(C*n/L^(m+3)) := mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = _ := by rw [pow_add];field_simp
  have hsmall : C*(n:ℝ)/L^3≤(n:ℝ)/(8192*D) := by
    have hyl : (y:ℝ)≤L^a := Nat.floor_le (by positivity)
    have hloga := Real.log_le_log hy0 hyl
    rw [Real.log_pow] at hloga
    have hl' := Real.log_le_sub_one_of_pos hLp
    have haL := mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (α:=ℝ) a)
    have hD : D≤((a:ℝ)+1)*L := by dsimp [D];nlinarith only [hloga,haL,hL1,Nat.cast_nonneg (α:=ℝ) a]
    have hC' : 8192*C*((a:ℝ)+1)≤L := (le_max_right 1 _).trans hL'
    have h2 := mul_le_mul_of_nonneg_right hC' hLp.le
    have h3 := mul_le_mul_of_nonneg_left hD (show 0≤8192*C by positivity)
    have hb : 8192*C*D≤L^3 := (by nlinarith only [h2,h3] : 8192*C*D≤L^2).trans (pow_le_pow_right₀ hL1 (by decide))
    apply (div_le_div_iff₀ (pow_pos hLp _) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hb hLn]
  have hb := fixedTarget_Brun_joined_rows n z hzn (range J) (brunSieveBlock B)
    (fun i _ j _ hij => brunSieveBlock_disjoint B hij) (brunSieveBlock_partition B J hB)
    (brunBlockOrder J) (fun i _ => ⟨24+(J-1-i),by simp only [brunBlockOrder];omega⟩)
  let T := ∑S∈B.powerset,c S * fixedTargetDivisorRow n (∏p∈S,p)
  let M := ∑S∈B.powerset,c S * ∏p∈S,brunEulerWeight p
  change T≤fixedTargetBrunSurvivorMass n z at hb
  change |T-h*M|≤_ at hx
  change (n:ℝ)/8 * (1/(512*D)) ≤ h*M at hprod
  have hnum : (n:ℝ)/8*(1/(512*D))=2*((n:ℝ)/(8192*D)) := by field_simp;ring
  have hsurv : (n:ℝ)/(8192*D)≤fixedTargetBrunSurvivorMass n z := by
    linarith only [hb,(abs_le.mp (hx.trans (hSW.trans hsmall))).1,hprod,hnum]
  apply hsurv.trans
  unfold fixedTargetBrunSurvivorMass
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hki,hk'⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨hki,fun p hpr hp => hk' p hpr (hp.trans hyz)⟩
  · intro k _ _
    unfold weight
    split_ifs <;> positivity

end GoldbachPartial