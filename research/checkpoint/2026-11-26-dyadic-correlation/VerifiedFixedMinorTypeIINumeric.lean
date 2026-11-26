import VerifiedFareyLargeSieve
namespace GoldbachPartial
open Filter
open scoped Topology

private theorem minor_block_budget {x q m n L:ℝ} (hx:0<x)(hL:2≤L)
    (hq:L^14≤q)(hm:L^14≤m)(hn:L^14≤n)(hqx:q*L^14≤x)(hmn:m*n≤x)
    {l:ℝ}(hl:l≤3*L)(hl0:0≤l):
    (8*(1+L)^3*(2*m)) * ((2*(Real.log 4+4)*(1+L)*(2*n))*((n/q+1)*(6*m+8*q*l))) ≤
      (10000*x/L^4)^2 := by
  have hLp:0<L:=by linarith
  have hL1:1≤L:=by linarith
  have hp0:0<L^14:=pow_pos hLp _
  have hq0:=hp0.trans_le hq
  have hm0:=hp0.trans_le hm
  have hn0:=hp0.trans_le hn
  let Y:=x/L^14
  have hmp:m≤Y:=(le_div_iff₀ hp0).mpr ((mul_le_mul_of_nonneg_left hn hm0.le).trans hmn)
  have hnp:n≤Y:=(le_div_iff₀ hp0).mpr ((mul_le_mul_of_nonneg_left hm hn0.le).trans (by simpa only [mul_comm] using hmn))
  have hqY:q≤Y:=(le_div_iff₀ hp0).mpr hqx
  have hmx:m*n/q≤Y:=(div_le_div_of_nonneg_left (mul_nonneg hm0.le hn0.le) hp0 hq).trans
    (div_le_div_of_nonneg_right hmn hp0.le)
  have hY:0≤Y:=div_nonneg hx.le hp0.le
  have hYL:Y≤Y*L:=le_mul_of_one_le_right hY hL1
  have hnL:n*l≤3*(Y*L):=(mul_le_mul hnp hl hl0 hY).trans_eq (by ring)
  have hqL:q*l≤3*(Y*L):=(mul_le_mul hqY hl hl0 hY).trans_eq (by ring)
  have hbr:(n/q+1)*(6*m+8*q*l) ≤ 60*(Y*L) := by
    have he:(n/q+1)*(6*m+8*q*l)=6*(m*n/q)+8*(n*l)+6*m+8*(q*l):=by field_simp;ring
    rw [he]
    linarith only [hmx.trans hYL,hnL,hmp.trans hYL,hqL]
  have hB0:0≤(n/q+1)*(6*m+8*q*l):=by positivity
  have hfact: (8*(1+L)^3*(2*m))*(2*(Real.log 4+4)*(1+L)*(2*n)) ≤ 7168*L^4*x:=by
    have hh : (1+L)^4≤(2*L)^4:=pow_le_pow_left₀ (by positivity) (by linarith) _
    have hlg:Real.log 4+4≤(7:ℝ):=by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    calc _ = 64*(Real.log 4+4)*(1+L)^4*(m*n):=by ring
         _ ≤ (64*7)*(2*L)^4*x:=by
           apply mul_le_mul _ hmn (mul_nonneg hm0.le hn0.le) (by positivity)
           exact mul_le_mul (mul_le_mul_of_nonneg_left hlg (by norm_num)) hh (by positivity) (by norm_num)
         _ = _:=by ring
  rw [←mul_assoc]
  apply (mul_le_mul hfact hbr hB0 (by positivity)).trans
  dsimp only [Y]
  have hpow':430080*L^13≤100000000*L^14 := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by decide : 13≤14)) (by norm_num : (0:ℝ)≤430080)).trans
    gcongr;norm_num
  have hfinal:430080*x^2*L^13≤100000000*x^2*L^14 := by
    nlinarith only [mul_le_mul_of_nonneg_left hpow' (sq_nonneg x)]
  apply (le_of_mul_le_mul_left (a:=L^14*L^8) _ (by positivity))
  convert hfinal using 1 <;> field_simp <;> ring

theorem vaughan_fixed_typeII_numeric :
    ∀ᶠ X:ℕ in atTop, let P:=⌊(Real.log X)^64⌋₊
      let U:=⌊(Real.log X)^24⌋₊
      ∀q M N:ℕ, P<q→q≤X/P→1≤M→1≤N→U≤2*M→U≤2*N→M*N≤X→
      (8*(1+Real.log X)^3*(2*(M:ℝ))) *
      ((2*(Real.log 4+4)*(1+Real.log X)*(2*(N:ℝ)))*
      (((N:ℝ)/q+1)*(6*(M:ℝ)+8*(q:ℝ)*(1+Real.log (q+2:ℕ))))) ≤
      (10000*(X:ℝ)/(Real.log X)^4)^2 := by
  have ht:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 2,eventually_ge_atTop (3:ℕ)] with X hlog hX
  let L:=Real.log (X:ℝ)
  let P:=⌊L^64⌋₊
  let U:=⌊L^24⌋₊
  have hL:2≤L:=hlog
  have hLp:0<L:=by linarith
  have hL1:1≤L:=by linarith
  have hfour:4≤L^10:=by have h:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hL 10;norm_num at h;linarith
  have h₀:1≤L^14:=one_le_pow₀ hL1
  have hU:2*L^14≤(U:ℝ):=by
    have hFloor:L^24<(U:ℝ)+1:=Nat.lt_floor_add_one _
    have h34:=mul_le_mul_of_nonneg_right hfour (pow_nonneg hLp.le 14)
    rw [←pow_add] at h34
    change 4*L^14≤L^24 at h34
    linarith only [hFloor,h₀,h34]
  have hUP: U≤P:=Nat.floor_mono (pow_le_pow_right₀ hL1 (by decide : 24≤64))
  have hP : L^14≤(P:ℝ):=by linarith only [hU,show (U:ℝ)≤P by exact_mod_cast hUP,h₀]
  have hP0:0<P:=by exact_mod_cast (show (0:ℝ)<P by linarith only [hP,h₀])
  dsimp only
  intro q M N hq hqX _ _ hu hv hMN
  have hq₁: L^14≤(q:ℝ):=hP.trans (by exact_mod_cast hq.le)
  have hq₂:(q:ℝ)*L^14≤X:= (mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _)).trans
    (by exact_mod_cast (Nat.le_div_iff_mul_le hP0).mp hqX)
  have hm:L^14≤(M:ℝ):=by linarith only [hU,show (U:ℝ)≤2*(M:ℝ) by exact_mod_cast hu]
  have hn:L^14≤(N:ℝ):=by linarith only [hU,show (U:ℝ)≤2*(N:ℝ) by exact_mod_cast hv]
  have hqle:q≤X:=hqX.trans (Nat.div_le_self ..)
  have hqpow:q+2≤X^2:=by nlinarith only [hqle,hX,Nat.mul_le_mul_left X hX]
  have hlg:=Real.log_le_log (show (0:ℝ)<(q+2:ℕ) by positivity) (by exact_mod_cast hqpow : ((q+2:ℕ):ℝ)≤(X:ℝ)^2)
  rw [Real.log_pow] at hlg
  apply minor_block_budget (show (0:ℝ)<X by positivity) hL hq₁ hm hn hq₂ (by exact_mod_cast hMN)
  · change Real.log ((q+2:ℕ):ℝ)≤(2:ℕ)*L at hlg
    simp only [Nat.cast_ofNat] at hlg
    linarith only [hlg,hL1]
  · positivity

end GoldbachPartial
