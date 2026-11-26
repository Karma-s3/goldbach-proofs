import VerifiedSevenFactorParameters

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

def brunBandIndex (K n:ℕ):ℕ := Nat.log 2 (Nat.log 2 n/K)
def brunBandLevel (K n:ℕ):ℕ := brunBlockBoundary (brunBandIndex K n)

theorem brunBand_select {a:ℝ} (ha:0<a) (ha':a<1/2) :
    ∃ B:ℝ,a<B ∧ B<1/2 ∧ ∃ K:ℕ,11<K ∧ 1/(K:ℝ)<min a (1/11) ∧ B+29/(K:ℝ)<1/2 := by
  let B:ℝ:=(a+1/2)/2
  have hb:a<B:=by dsimp [B];linarith
  have hb':B<1/2:=by dsimp [B];linarith
  obtain ⟨K,hK⟩:=exists_nat_gt (max (max 11 (1/a)) (29/(1/2-B)))
  have hk11:(11:ℝ)<K:=((le_max_left ..).trans (le_max_left ..)).trans_lt hK
  have hKa:1/a<(K:ℝ):=((le_max_right ..).trans (le_max_left ..)).trans_lt hK
  have hKb:29/(1/2-B)<(K:ℝ):=(le_max_right ..).trans_lt hK
  have hkpos:(0:ℝ)<K:=by linarith
  refine ⟨B,hb,hb',K,by exact_mod_cast hk11,lt_min ?_ ?_,?_⟩
  · apply (div_lt_iff₀ hkpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hKa
  · exact one_div_lt_one_div_of_lt (by norm_num) hk11
  · have hlt:29/(K:ℝ)<1/2-B:=(div_lt_iff₀ hkpos).mpr (by
      have hh:=(div_lt_iff₀ (sub_pos.mpr hb')).mp hKb
      simpa only [mul_comm] using hh)
    linarith

theorem brunBandIndex_tendsto {K:ℕ} (hK:0<K) : Tendsto (brunBandIndex K) atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop (2^(K*2^j):ℕ)] with n hn
  have hh:K*2^j≤Nat.log 2 n:=by simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) hn
  have he:2^j≤Nat.log 2 n/K:=(Nat.le_div_iff_mul_le hK).mpr (by simpa [mul_comm] using hh)
  change j≤Nat.log 2 (Nat.log 2 n/K)
  simpa only [Nat.log_pow (by decide:1<2)] using Nat.log_mono_right (b:=2) he

theorem brunBandLevel_tendsto {K:ℕ} (hK:0<K) : Tendsto (brunBandLevel K) atTop atTop := by
  apply tendsto_atTop.mpr;intro j
  filter_upwards [(brunBandIndex_tendsto hK).eventually_ge_atTop j] with n hn
  exact hn.trans ((Nat.lt_two_pow_self (n:=brunBandIndex K n)).le.trans (Nat.lt_two_pow_self (n:=2^(brunBandIndex K n))).le)

theorem brunBandLevel_geometry {K:ℕ} (hK:0<K):
    ∀ᶠ n:ℕ in atTop,2≤brunBandLevel K n ∧ (brunBandLevel K n)^K≤n ∧ n≤(brunBandLevel K n)^(2*K) := by
  filter_upwards [(brunBandIndex_tendsto hK).eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with n hj hn
  let s:=Nat.log 2 n
  let t:=s/K
  let e:=2^(brunBandIndex K n)
  have he:0<e:=by dsimp [e];positivity
  have ht:t≠0:=by intro h;change 1≤Nat.log 2 t at hj;simp [h] at hj
  have hel:e≤t:=Nat.pow_log_le_self 2 ht
  have heu:t<e*2:=by change t<2^(Nat.log 2 t)*2;simpa only [pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1<2) t
  have hlow:e*K≤s:=(Nat.mul_le_mul_right K hel).trans (Nat.div_mul_le_self ..)
  have hhi:s<e*(2*K):=calc
    _ < K*(t+1) := Nat.lt_mul_div_succ s hK
    _ ≤ K*(e*2) := Nat.mul_le_mul_left K heu
    _ = _ := by ring
  change 2≤2^e ∧ (2^e)^K≤n ∧ n≤(2^e)^(2*K)
  rw [←pow_mul,←pow_mul]
  exact ⟨by simpa only [pow_one] using Nat.pow_le_pow_right (by decide:0<2) he,
    (Nat.pow_le_pow_right (by decide) hlow).trans (Nat.pow_log_le_self _ (by omega)),
    (Nat.lt_pow_succ_log_self (by decide) n).le.trans (Nat.pow_le_pow_right (by decide) hhi)⟩

theorem brunBandLevel_gap {K:ℕ} (hK:11<K) {a:ℝ} (ha:1/(K:ℝ)≤a) :
    ∀ᶠ n:ℕ in atTop,(brunBandLevel K n)≤⌊(n:ℝ)^a⌋₊ ∧ ∀ z:ℕ,n≤z^11 → brunBandLevel K n<z := by
  filter_upwards [brunBandLevel_geometry (show 0<K by omega),eventually_ge_atTop (1:ℕ)] with n hg hn
  let y:=brunBandLevel K n
  have hK':0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hy:2≤y:=hg.1
  have hk:y^K≤n:=hg.2.1
  constructor
  · apply Nat.le_floor
    have hpow := Real.rpow_le_rpow (show 0≤(y:ℝ)^K by positivity) (show (y:ℝ)^K≤n by exact_mod_cast hk) (one_div_pos.mpr hK').le
    apply le_trans _ (hpow.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha))
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _),mul_one_div_cancel hK'.ne',Real.rpow_one]
  · intro z hz
    by_contra! h
    have hbad:(y^K:ℕ)≤y^11:=hk.trans (hz.trans (Nat.pow_le_pow_left h 11))
    exact (Nat.pow_lt_pow_right (show 1<y by omega) hK).not_ge hbad

theorem brunBand_log_pay (d:ℕ) {g ε:ℝ} (hg:0<g) (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,(1+Real.log n)^d ≤ ε*(n:ℝ)^g := by
  have hh:(fun x:ℝ=>Real.log x^d) =o[atTop] (fun x:ℝ=>x^g):=by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (d:ℕ) hg
  have he:=((hh.const_mul_left ((2:ℝ)^d)).bound hε)
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually he,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1] with n hb hl
  have h0:0≤Real.log (n:ℝ):=Real.log_natCast_nonneg _
  have hterm:0≤(2:ℝ)^d*Real.log n^d:=by positivity
  have hb':(2:ℝ)^d*Real.log n^d≤ε*(n:ℝ)^g:=by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hterm,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) g)] using hb
  change 1≤Real.log (n:ℝ) at hl
  calc _ ≤ (2*Real.log (n:ℝ))^d := pow_le_pow_left₀ (by positivity) (by linarith) _
       _ ≤ _ := by rw [mul_pow];exact hb'

theorem brunBand_prefix_budget {K:ℕ} (hK:11<K) {B:ℝ} (hB:B+29/(K:ℝ)<1/2)
    {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀ b:ℝ,b≤B →
      (∑q∈Icc 1 (⌊(n:ℝ)^b⌋₊*(brunBandLevel K n)^29),brunPrimePrefixMaxError n q) ≤ ε*n/Real.log n ∧
      (⌊(n:ℝ)^b⌋₊:ℝ)*Real.log n^2 ≤ ε*n := by
  obtain ⟨d,C,hC,hpre⟩:=prime_progressions_half_level 2
  let g:=1/2-(B+29/(K:ℝ))
  have hg:0<g:=sub_pos.mpr hB
  have hK':0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hB':0<1-B:=by have :=div_pos (by norm_num : (0:ℝ)<29) hK';linarith
  have hlog:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hpre,brunBandLevel_gap hK (a:=1/(K:ℝ)) le_rfl,brunBand_log_pay d hg (by norm_num:(0:ℝ)<1),
    brunBand_log_pay 2 hB' hε,hlog.eventually_ge_atTop (C/ε),eventually_ge_atTop (2:ℕ)] with n hpreN hy hpay hbpay hlogN hn
  intro b hb
  let L:=Real.log (n:ℝ)
  let y:=brunBandLevel K n
  let m:=⌊(n:ℝ)^b⌋₊
  have hn':0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hL:0<L:=Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hm:(m:ℝ)≤(n:ℝ)^B:=(Nat.floor_le (Real.rpow_nonneg hn'.le _)).trans (Real.rpow_le_rpow_of_exponent_le hn1 hb)
  have hyr:(y:ℝ)≤(n:ℝ)^(1/(K:ℝ)):=(show (y:ℝ)≤⌊(n:ℝ)^(1/(K:ℝ))⌋₊ by exact_mod_cast hy.1).trans
    (Nat.floor_le (Real.rpow_nonneg hn'.le _))
  have hp29:(y:ℝ)^29≤(n:ℝ)^(29/(K:ℝ)):=calc
    _ ≤ ((n:ℝ)^(1/(K:ℝ)))^29 := pow_le_pow_left₀ (Nat.cast_nonneg _) hyr _
    _ = _ :=by rw [←Real.rpow_mul_natCast hn'.le];congr 1;push_cast;ring
  have hlevel:((m*y^29:ℕ):ℝ)*(1+L)^d ≤Real.sqrt n:=by
    push_cast
    apply (mul_le_mul (mul_le_mul hm hp29 (by positivity) (by positivity)) (by simpa only [one_mul,L] using hpay)
      (by positivity : 0≤(1+L)^d) (by positivity)).trans_eq
    rw [←Real.rpow_add hn',←Real.rpow_add hn',Real.sqrt_eq_rpow]
    congr 1;dsimp [g];ring
  constructor
  · apply (hpreN _ hlevel).trans
    have hh:C≤L*ε:=(div_le_iff₀ hε).mp hlogN
    change C*(n:ℝ)/L^2≤ε*n/L
    rw [div_le_div_iff₀ (sq_pos_of_pos hL) hL]
    nlinarith only [mul_nonneg (mul_nonneg hn'.le hL.le) (sub_nonneg.mpr hh)]
  · have hh:L^2≤ε*(n:ℝ)^(1-B):=(pow_le_pow_left₀ hL.le (show L≤1+L by linarith) 2).trans hbpay
    change (m:ℝ)*L^2≤ε*n
    calc _ ≤ (n:ℝ)^B*(ε*(n:ℝ)^(1-B)) := mul_le_mul hm hh (sq_nonneg _) (by positivity)
         _ = _ := by rw [mul_left_comm,←Real.rpow_add hn',show B+(1-B)=1 by ring,Real.rpow_one]

end GoldbachPartial
