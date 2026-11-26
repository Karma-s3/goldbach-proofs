import AbelParsevalPrimeArc
import NearRootShell

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

noncomputable def parsevalLogArcRadius (n q : ℕ) : ℝ :=
  1/((q:ℝ)*Real.sqrt n*(terminalPrimeArcLog n)^4)

noncomputable def parsevalLogArcRowEnergy (n j : ℕ) : ℝ :=
  let ρ := parsevalLogArcRadius n (j+1)
  ∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy (j+1) a n t
    (∑ k ∈ range (n+1), E ((k:ℝ)*t))‖^2

noncomputable def parsevalLogArcEnergy (n : ℕ) : ℝ :=
  ∑ j ∈ Ico (medDeskD n) (terminalPrimeArcCutoff n), parsevalLogArcRowEnergy n j

noncomputable def parsevalLogArcChange (n : ℕ) : ℂ :=
  ∑ j ∈ Ico (medDeskD n) (terminalPrimeArcCutoff n),
    primeArcSignedChange (j+1) n (parsevalLogArcRadius n (j+1))

private theorem harmonicSuccessors_le (R : ℕ) :
    (∑ j ∈ range R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    by_cases h : R=0
    · subst R; norm_num
    · have hR : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(R:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hR)
      rw [Real.log_div hp.ne' hR.ne',inv_div] at hl
      have he : 1-(R:ℝ)/(R+1) = ((R:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]


private theorem parsevalLogArc_harmonic (Y R : ℕ) :
    (∑ j ∈ Ico Y R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R :=
  (sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
    (fun _ _ _ => by positivity)).trans (harmonicSuccessors_le R)

private theorem parsevalLogArc_radius_bounds {n : ℕ} (hn : 4≤n) (j : ℕ) :
    0 ≤ parsevalLogArcRadius n (j+1) ∧ parsevalLogArcRadius n (j+1) ≤ 1/2 := by
  have hL : 1 ≤ terminalPrimeArcLog n := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hs : 2≤Real.sqrt (n:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hn)
  have hq : (1:ℝ)≤(j+1:ℕ) := by exact_mod_cast Nat.le_add_left 1 j
  unfold parsevalLogArcRadius
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by norm_num)
    calc
      2 ≤ ((j+1:ℕ):ℝ)*Real.sqrt n := by nlinarith only [mul_le_mul hq hs (by norm_num) (by positivity : (0:ℝ)≤(j+1:ℕ))]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)

noncomputable abbrev parsevalLogArcConstant (C : ℝ) := (4*C)^2*(8+16*Real.pi^2)+4

theorem parsevalLogArcEnergy_bound_at {n:ℕ} (hn : 4≤n) {C:ℝ} (hC : 0≤C)
    (hp : terminalPrimeArcPrefixAt C n) :
    parsevalLogArcEnergy n ≤ parsevalLogArcConstant C*(n:ℝ)/(terminalPrimeArcLog n)^3 := by
  let L := terminalPrimeArcLog n
  let R := terminalPrimeArcCutoff n
  let D := C*Real.sqrt n*Real.log (2*(n:ℝ)^2)^2
  let V := parsevalLogArcConstant C
  let J := Ico (medDeskD n) R
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hL : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hs0 := Real.sqrt_pos.mpr hn0
  have hsq := Real.sq_sqrt hn0.le
  have hR : (R:ℝ) ≤ Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hRn : (R:ℝ) ≤ n :=
    (hR.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL))).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hn1))
  have hlogR : Real.log R ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos R with hz | hr
    · rw [hz,Nat.cast_zero,Real.log_zero]; exact Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hr) hRn
  have hlogadd : 1+Real.log R ≤ L := add_le_add le_rfl hlogR
  have hlogRL : Real.log R ≤ L := by linarith
  have hlogbig : Real.log (2*(n:ℝ)^2) ≤ 2*L := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),Real.log_pow]
    dsimp only [L,terminalPrimeArcLog]; push_cast
    linarith [Real.log_le_sub_one_of_pos (x:=2) (by norm_num)]
  have hlogbig0 : 0 ≤ Real.log (2*(n:ℝ)^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((n:ℝ)-1)])
  have hDb : D ≤ (4*C)*Real.sqrt n*L^2 := calc
    D ≤ C*Real.sqrt n*(2*L)^2 := by dsimp only [D]; gcongr
    _ = _ := by ring

  have hD2 : D^2 ≤ (4*C)^2*n*L^4 := by
    have hd0 : 0≤D := by dsimp only [D]; positivity
    apply (pow_le_pow_left₀ hd0 hDb 2).trans_eq
    rw [mul_pow,mul_pow,hsq]
    ring
  have hV : 0≤V := by dsimp only [V,parsevalLogArcConstant]; positivity
  have hrow (j:ℕ) (hj:j∈J) : parsevalLogArcRowEnergy n j ≤ (V*n/L^4)*((j+1:ℕ):ℝ)⁻¹ := by
    let q := j+1
    let r := parsevalLogArcRadius n q
    have hq0 : (0:ℝ)<q := by dsimp only [q]; positivity
    have hqR : (q:ℝ) ≤ R := by exact_mod_cast (mem_Ico.mp hj).2
    have hq5 := (le_div_iff₀ (pow_pos hL0 5)).mp (hqR.trans hR)
    have hq4 : (q:ℝ)*L^4 ≤ Real.sqrt n := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 4≤5)) hq0.le).trans hq5
    have hnr : 1 ≤ (n:ℝ)*r := by
      dsimp only [r,parsevalLogArcRadius]
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hq4 hs0.le,hsq]
    have hr := parsevalLogArc_radius_bounds hn j
    have ht : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hlogq0 := Real.log_natCast_nonneg q
    have hlogq := (Real.log_le_log hq0 (hqR.trans hRn)).trans (by dsimp only [L,terminalPrimeArcLog]; linarith : Real.log n≤L)
    have hlogq2 : (Real.log q)^2 ≤ (n:ℝ)*L^4*((n:ℝ)*r) := calc
      _ ≤ L^2 := pow_le_pow_left₀ hlogq0 hlogq 2
      _ ≤ L^4 := pow_le_pow_right₀ hL (by decide)
      _ ≤ (n:ℝ)*L^4 := le_mul_of_one_le_left (by positivity) hn1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hnr
    have hF : 8+16*Real.pi^2*(n:ℝ)*r ≤ (8+16*Real.pi^2)*((n:ℝ)*r) := by linarith
    have he := primeArc_tube_abel_parseval_of_prefix q n hr.1 hr.2 (hp j hj)
    calc
      parsevalLogArcRowEnergy n j ≤ _ := he
      _ ≤ r*(q:ℝ)*(((4*C)^2*n*L^4)*((8+16*Real.pi^2)*((n:ℝ)*r)) + 4*((n:ℝ)*L^4*((n:ℝ)*r))) := by
        change r*(q.totient:ℝ)*(D^2*(8+16*Real.pi^2*(n:ℝ)*r)+4*(Real.log q)^2) ≤ _
        have hr0 : 0≤r := hr.1
        gcongr
      _ = _ := by
        change _ = (V*n/L^4)*(q:ℝ)⁻¹
        have hr' : r=((q:ℝ)*Real.sqrt n*L^4)⁻¹ := by exact one_div _
        rw [hr']
        dsimp only [V,parsevalLogArcConstant]
        generalize Real.sqrt (n:ℝ)=x at hs0 hsq ⊢
        rw [←hsq]
        field_simp
  have hsum := (parsevalLogArc_harmonic (medDeskD n) R).trans hlogadd
  calc
    parsevalLogArcEnergy n ≤ ∑ j ∈ J, (V*n/L^4)*((j+1:ℕ):ℝ)⁻¹ := sum_le_sum hrow
    _ = (V*n/L^4)*∑ j ∈ J, ((j+1:ℕ):ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ (V*n/L^4)*L := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      change (V*n/L^4)*L=V*n/L^3
      field_simp

private theorem parsevalLogArc_row_young (n j : ℕ) (hn : 4≤n) {s : ℝ} (hs : 0<s) :
    ‖primeArcSignedChange (j+1) n (parsevalLogArcRadius n (j+1))‖ ≤
      (1+s)*parsevalLogArcRowEnergy n j + s⁻¹*((n:ℝ)+1)/(j+1).totient := by
  let q := j+1
  let ρ := parsevalLogArcRadius n q
  have hρ := parsevalLogArc_radius_bounds hn j
  classical
  let P := fun (a : (ZMod q)ˣ) (t : ℝ) => E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))
  have hf (a : (ZMod q)ˣ) : Continuous (shiftedTruePrimeWave q a n) := by
    unfold shiftedTruePrimeWave E; fun_prop
  have hm : Continuous (geometricPrimeArcModel q n) := by unfold geometricPrimeArcModel E; fun_prop
  have hh := signed_squares_on_arcs (Finset.univ : Finset (ZMod q)ˣ) (fun _ => -ρ) (fun _ => ρ)
    (fun a => shiftedTruePrimeWave q a n) (fun _ => geometricPrimeArcModel q n) P hs
    (fun _ _ => by change -parsevalLogArcRadius n (j+1) ≤ _; linarith [hρ.1]) (fun a _ => hf a) (fun _ _ => hm)
    (by intro a _; dsimp [P,E]; fun_prop)
    (fun a _ t _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hint : (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, ‖shiftedTruePrimeWave q a n t - geometricPrimeArcModel q n t‖^2) =
      ∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy q a n t (∑ k ∈ range (n+1), E ((k:ℝ)*t))‖^2 := by
    symm
    exact intervalIntegral.integral_finsetSum (fun a _ => (((hf a).sub hm).norm.pow 2).intervalIntegrable _ _)
  have hmod : (∑ _a : (ZMod q)ˣ, ∫ t in -ρ..ρ, ‖geometricPrimeArcModel q n t‖^2) =
      (q.totient:ℝ)*∫ t in -ρ..ρ, ‖geometricPrimeArcModel q n t‖^2 := by
    simp [ZMod.card_units_eq_totient,nsmul_eq_mul]
  change ‖primeArcSignedChange q n ρ‖ ≤ _ at hh
  simp only [hint,hmod] at hh

  have hM := geometricPrimeArcModel_window_energy q n hρ.1 hρ.2 (principal_unitGauss_norm_le_one _)
  exact hh.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hs.le)).trans_eq (by ring)))
theorem parsevalLogArcChange_bound_at {n : ℕ} (hn : 4≤n) {C:ℝ} (hC : 0≤C)
    (hp : terminalPrimeArcPrefixAt C n) :
    ‖parsevalLogArcChange n‖ ≤ (2*parsevalLogArcConstant C+4)*(n:ℝ)/Real.sqrt (terminalPrimeArcLog n) := by
  let L := terminalPrimeArcLog n
  let R := terminalPrimeArcCutoff n
  let V := parsevalLogArcConstant C
  let J := Ico (medDeskD n) R
  let K := 1+(Nat.log 2 R:ℝ)
  let s := L^2*Real.sqrt L
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hL : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL0 : 0<L := by linarith
  have hs1 : 1≤s := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) (Real.one_le_sqrt.mpr hL)
  have hs : 0<s := zero_lt_one.trans_le hs1
  have hR : (R:ℝ) ≤ Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hRn : (R:ℝ) ≤ n :=
    (hR.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL))).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hn1))
  have hlogR : Real.log R ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos R with hz | hr
    · rw [hz,Nat.cast_zero,Real.log_zero]; exact Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hr) hRn
  have hlogadd : 1+Real.log R ≤ L := add_le_add le_rfl hlogR
  have hlogRL : Real.log R ≤ L := by linarith
  have hbase : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x:=2) (by norm_num)
    norm_num at h ⊢; linarith
  have hK : 1+(Nat.log 2 R:ℝ) ≤ 2*L := by
    have hb := Real.natLog_le_logb R 2
    simp only [Real.logb, Nat.cast_ofNat] at hb
    have hb' : Real.log R/Real.log 2 ≤ 2*Real.log n := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      nlinarith [mul_nonneg (Real.log_natCast_nonneg n) (sub_nonneg.mpr hbase)]
    dsimp only [L,terminalPrimeArcLog]
    linarith
  have hK0 : 0≤K := by dsimp only [K]; positivity
  have hφ (j:ℕ) (hj:j∈J) : ((j+1).totient:ℝ)⁻¹ ≤ K*((j+1:ℕ):ℝ)⁻¹ := by
    have hhφ : (0:ℝ)<(j+1).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos j)
    have hq0 : (0:ℝ)<(j+1:ℕ) := by positivity
    have hratio : ((j+1:ℕ):ℝ) ≤ K*((j+1).totient:ℝ) := by
      dsimp only [K]
      rw [add_comm (1:ℝ) (Nat.log 2 R:ℝ)]
      exact_mod_cast (nat_le_totient_mul_log2_succ (Nat.succ_pos j)).trans
        (Nat.mul_le_mul_right (j+1).totient
          (Nat.add_le_add_right (Nat.log_mono_right (b:=2) (mem_Ico.mp hj).2) 1))
    rw [←one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hhφ hq0).mpr (by simpa using hratio)
  have hsum : ∑ j ∈ J, ((j+1).totient:ℝ)⁻¹ ≤ 2*L^2 := calc
    _ ≤ ∑ j ∈ J, K*((j+1:ℕ):ℝ)⁻¹ := sum_le_sum hφ
    _ = K*∑ j ∈ J, ((j+1:ℕ):ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ (2*L)*L := mul_le_mul hK ((parsevalLogArc_harmonic (medDeskD n) R).trans hlogadd)
      (sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = _ := by ring
  have hfirst : (1+s)*parsevalLogArcEnergy n ≤ 2*V*(n:ℝ)/Real.sqrt L := by
    have hV : 0≤V := by dsimp only [V,parsevalLogArcConstant]; positivity
    calc
      _ ≤ (1+s)*(V*(n:ℝ)/L^3) := mul_le_mul_of_nonneg_left (parsevalLogArcEnergy_bound_at hn hC hp) (by positivity)
      _ ≤ (2*s)*(V*(n:ℝ)/L^3) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
        dsimp only [s]
        field_simp [Real.sqrt_ne_zero'.mpr hL0]
        rw [Real.sq_sqrt hL0.le]
  have hsecond : (s⁻¹*((n:ℝ)+1))*(∑ j ∈ J, ((j+1).totient:ℝ)⁻¹) ≤ 4*(n:ℝ)/Real.sqrt L := calc
    _ ≤ (s⁻¹*(2*(n:ℝ)))*(2*L^2) := by gcongr; linarith
    _ = _ := by dsimp only [s]; field_simp [Real.sqrt_ne_zero'.mpr hL0]; norm_num
  have hb : ‖parsevalLogArcChange n‖ ≤ (1+s)*parsevalLogArcEnergy n +
      (s⁻¹*((n:ℝ)+1))*(∑ j ∈ J, ((j+1).totient:ℝ)⁻¹) := by
    apply (norm_sum_le ..).trans
    change _ ≤ (1+s)*(∑ j ∈ J, parsevalLogArcRowEnergy n j) + _
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    exact sum_le_sum fun j hj => by simpa only [div_eq_mul_inv] using parsevalLogArc_row_young n j hn hs
  exact hb.trans ((add_le_add hfirst hsecond).trans_eq (by change _=(2*V+4)*(n:ℝ)/Real.sqrt L; ring))

theorem parsevalLogArcChange_small (hψ : grhAllUniform) {ε:ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ‖parsevalLogArcChange n‖ ≤ ε*(n:ℝ) := by
  obtain ⟨C,hC,hp⟩ := nearRoot_prefix_of_uniform_psi hψ
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto terminalPrimeArcLog atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [terminalPrimeArcLog]; linarith) hlog
  have hs := (Real.tendsto_sqrt_atTop.comp hL).eventually_ge_atTop ((2*parsevalLogArcConstant C+4)/ε)
  filter_upwards [hs,hp,eventually_ge_atTop (4:ℕ)] with n h hp' hn
  have hL0 : 0<terminalPrimeArcLog n := by
    dsimp only [terminalPrimeArcLog]; linarith [Real.log_natCast_nonneg n]
  change (2*parsevalLogArcConstant C+4)/ε ≤ Real.sqrt (terminalPrimeArcLog n) at h
  apply (parsevalLogArcChange_bound_at hn hC hp').trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hL0)).mpr
  exact (mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp h) (Nat.cast_nonneg (α:=ℝ) n)).trans_eq (by ring)

end GoldbachPartial