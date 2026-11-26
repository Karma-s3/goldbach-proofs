import VerifiedPrimeHalfDistribution
import VerifiedMediumBrunSeven
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

theorem prime_progressions_four_ninths (A:ℕ):
    ∃C:ℝ,0<C ∧ ∀ᶠ u:ℕ in atTop,∀D:ℕ,D^9≤u^4 →
      (∑q∈Icc 1 D,brunPrimePrefixMaxError u q)≤C*u/(Real.log u)^A := by
  obtain ⟨d,C,hC,hh⟩:=prime_progressions_half_level A
  refine ⟨C,hC,?_⟩
  have ht:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp:∀ᶠ u:ℕ in atTop,(Real.log u)^(36*d)≤u:=by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
        (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((36*d:ℕ):ℝ) (by norm_num : (0:ℝ)<1))
  filter_upwards [hh,ht.eventually_ge_atTop 2,hp] with u h hL hlog
  intro D hD
  let L:=Real.log (u:ℝ)
  have hL':2≤L:=hL
  have hL2:1+L≤L^2:=by nlinarith only [hL',sq_nonneg (L-2)]
  have hbig:(1+L)^(18*d)≤(u:ℝ):=by
    calc _ ≤ (L^2)^(18*d):=pow_le_pow_left₀ (by dsimp [L];positivity) hL2 _
         _ = L^(36*d):=by rw [←pow_mul];congr 1;ring
         _ ≤ _:=hlog
  have hD9:(D:ℝ)^9≤(u:ℝ)^4:=by exact_mod_cast hD
  have hs:(D:ℝ)^18≤(u:ℝ)^8:=by
    convert pow_le_pow_left₀ (by positivity) hD9 2 using 1 <;> ring
  apply h D
  apply le_of_pow_le_pow_left₀ (by decide : 18≠0) (Real.sqrt_nonneg _)
  rw [mul_pow,←pow_mul,mul_comm d 18]
  have hz:(Real.sqrt (u:ℝ))^18=(u:ℝ)^9:=by
    rw [show 18=2*9 by decide,pow_mul,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hz]
  exact (mul_le_mul hs hbig (by positivity) (by positivity)).trans_eq (by ring)

theorem fixedTargetFourNinthsError_uniform  {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, ∀D:ℕ, D^9≤(n/4)^4 →
      fixedTargetBrunDistributionError n D≤ε*(n:ℝ)/Real.log n := by
  obtain ⟨C,hC,hp⟩:=prime_progressions_four_ninths 2
  obtain ⟨T,hT⟩:=eventually_atTop.mp hp
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (4*T),
    eventually_ge_atTop (40:ℕ),hl.eventually_ge_atTop (8*C/ε)] with n ht hn hl'
  intro D hD
  let L:=Real.log (n:ℝ)
  have hL:0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsc (u:ℕ)(hu:n/4≤u)(hun:u≤n) :
      (∑d∈Icc 1 D,brunPrimePrefixMaxError u d)≤4*C*n/L^2 := by
    have hlog : 0<Real.log (u:ℝ):=Real.log_pos (by exact_mod_cast (show 1<u by omega))
    have hnu : n≤u^2 := by nlinarith only [show n≤5*u by omega,show 5≤u by omega]
    have hcmp:=Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hnu : (n:ℝ)≤(u:ℝ)^2)
    rw [Real.log_pow] at hcmp
    have hL2:L^2≤4*(Real.log u)^2 := by
      have hh:=pow_le_pow_left₀ hL.le hcmp 2
      norm_num at hh;linarith only [hh]
    apply (hT u (by omega) D (hD.trans (Nat.pow_le_pow_left hu 4))).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hlog) (sq_pos_of_pos hL)).mpr
    calc _ ≤ (C*u)*(4*(Real.log u)^2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
         _ ≤ (C*n)*(4*(Real.log u)^2) := by gcongr
         _ = _ := by ring
  apply (fixedTargetBrunDistributionError_le_prefix_max n D).trans
  apply (add_le_add (hsc (n/2) (by omega) (Nat.div_le_self ..)) (hsc (n/4) le_rfl (Nat.div_le_self ..))).trans
  have hbound:8*C≤L*ε:=(div_le_iff₀ hε).mp hl'
  rw [←two_mul,le_div_iff₀ hL,mul_div_assoc',div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hL)]
  nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hL.le) (sub_nonneg.mpr hbound)]



def halfLevelBrunLarge (n:ℕ):ℕ:=2^(Nat.log 2 n/3+1)

set_option exponentiation.threshold 5200 in
theorem halfLevelBrun_geometry :
    ∀ᶠ n:ℕ in atTop, let y:=balancedBrunSmall n
      let w:=halfLevelBrunLarge n
      2≤y ∧ y≤w ∧ w≤n/4 ∧ n<w^3 ∧ (w*y^101)^9≤(n/4)^4 ∧ w≤y^1636 := by
  filter_upwards [balancedBrun_geometry,eventually_ge_atTop (2:ℕ)] with n hg hn
  let s:=Nat.log 2 n
  let e:=2^(balancedBrunIndex n)
  let y:=balancedBrunSmall n
  let w:=halfLevelBrunLarge n
  have he:0<e:=by dsimp [e];positivity
  have hy:0<y:=by have hh:=hg.1;change 2≤y at hh;omega
  have hlo:y^2452≤n/4:=by
    have hh:=hg.2.2.1
    change ((y^512)*y^101)^4≤n/4 at hh
    rw [←pow_add,←pow_mul] at hh;exact hh
  have hel:e*2452≤s:=by
    have h2:2^(e*2452)≤n:=by rw [pow_mul];exact hlo.trans (Nat.div_le_self ..)
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) h2
  have heu:s≤e*4905:=by
    have h2:n≤2^(e*4905):=by rw [pow_mul];exact hg.2.2.2.2.le
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) h2
  have hs2:2≤s:=by omega
  have hx:2^(s-2)≤n/4:=by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc 2^(s-2)*4 = 2^(s-2+2):=by rw [pow_add];rfl
         _ = 2^s:=by rw [Nat.sub_add_cancel hs2]
         _ ≤ n:=Nat.pow_log_le_self 2 (by omega)
  refine ⟨hg.1,?_,?_,?_,?_,?_⟩
  · change 2^e≤2^(s/3+1)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · change 2^(s/3+1)≤n/4
    exact (Nat.pow_le_pow_right (by decide) (by omega : s/3+1≤s-2)).trans hx
  · change n<(2^(s/3+1))^3
    rw [←pow_mul]
    exact (Nat.lt_pow_succ_log_self (by decide : 1<2) n).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  · change (2^(s/3+1)*(2^e)^101)^9≤(n/4)^4
    rw [←pow_mul,←pow_add,←pow_mul]
    calc _ ≤ 2^((s-2)*4):=Nat.pow_le_pow_right (by decide) (by omega)
         _ = (2^(s-2))^4:=pow_mul .. 
         _ ≤ _:=Nat.pow_le_pow_left hx _
  · change 2^(s/3+1)≤(2^e)^1636
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)

theorem halfLevelBrun_distribution_small {ε:ℝ}(hε:0<ε):
    ∀ᶠ n:ℕ in atTop,
      fixedTargetBrunDistributionError n (halfLevelBrunLarge n*(balancedBrunSmall n)^101)
        ≤ε*(n:ℝ)/Real.log n := by
  filter_upwards [halfLevelBrun_geometry,fixedTargetFourNinthsError_uniform hε] with n hg hd
  exact hd _ hg.2.2.2.2.1

end GoldbachPartial
