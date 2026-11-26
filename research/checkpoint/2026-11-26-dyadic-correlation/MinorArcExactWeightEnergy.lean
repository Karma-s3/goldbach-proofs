import NaturalTubeDilation
import SmallCutoffExactWeightCentering

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

/-- A frequency outside the complete family of major arcs stays separated after every small dilation. -/
theorem minorArc_dilate_circle_separation {n Q d : ℕ} (hn : 0<n) (hd : 0<d) (hQ : d≤Q)
    (hsmall : (Q:ℝ)/n≤1/2) {t : ℝ} (ht : t∈Set.Icc 0 1) (hminor : t∉rationalArcSet Q n) :
    (Q:ℝ)/n≤‖(((d:ℝ)*t:ℝ):UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  generalize round ((d:ℝ)*t)=z
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hdt0 := mul_nonneg hd'.le ht.1
  have hdt1 := mul_le_mul_of_nonneg_left ht.2 hd'.le
  by_cases hz : z<0
  · have hneg : (z:ℝ)≤-1 := by exact_mod_cast (show z≤-1 by omega)
    exact hsmall.trans ((by linarith : (1:ℝ)/2≤d*t-z).trans (le_abs_self _))
  by_cases hz' : (d:ℤ)<z
  · have hbig : (d:ℝ)+1≤(z:ℝ) := by exact_mod_cast (show (d:ℤ)+1≤z by omega)
    exact hsmall.trans ((by linarith : (1:ℝ)/2≤-(d*t-z)).trans (neg_le_abs _))
  lift z to ℕ using (le_of_not_gt hz)
  have hzd : z≤d := by exact_mod_cast le_of_not_gt hz'
  let g := z.gcd d
  let a := z/g
  let q := d/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right z hd
  have hgd : g∣d := Nat.gcd_dvd_right z d
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd hd hgd) hg
  have hqd : q≤d := Nat.div_le_self _ _
  have ha : a≤q := Nat.div_le_div_right hzd
  have hc : a.Coprime q := Nat.coprime_div_gcd_div_gcd hg
  have ha' : (a:ℝ)*g=z := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left z d)
  have hq' : (q:ℝ)*g=d := by exact_mod_cast Nat.div_mul_cancel hgd
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq
  have hg0 : (0:ℝ)<g := by exact_mod_cast hg
  have hdist : (Q:ℝ)/((q:ℝ)*n) < |t-(a:ℝ)/q| := by
    apply lt_of_not_ge
    intro hc'
    exact hminor ⟨q,a,hq,hqd.trans hQ,ha,hc,hc'⟩
  have hx : t-(a:ℝ)/q=((d:ℝ)*t-z)/d := by
    have hprop : (a:ℝ)*d=(z:ℝ)*q := by rw [←hq',←ha'];ring
    field_simp
    linarith only [hprop]
  rw [hx,abs_div,abs_of_nonneg hd'.le] at hdist
  have hdiv : (Q:ℝ)/((d:ℝ)*n)≤(Q:ℝ)/((q:ℝ)*n) := by gcongr
  have h := (lt_div_iff₀ hd').mp (hdiv.trans_lt hdist)
  push_cast
  apply le_of_lt
  calc
    _ = ((Q:ℝ)/((d:ℝ)*n))*d := by field_simp
    _ < _ := h

private theorem localized_dilate_integral_le_tail {V : Set ℝ} (hVm : MeasurableSet V) (hV : V⊆Set.Icc 0 1)
    {d : ℕ} (hd : 0<d) {a : ℝ} (ha : 0<a) (hab' : a≤1/2)
    (hsep : ∀ t∈V,a≤‖(((d:ℝ)*t:ℝ):UnitAddCircle)‖) {f : ℝ→ℝ}
    (hf : Continuous f) (hpos : ∀ x,0≤f x) (hp : Function.Periodic f 1) :
    (∫ t in V, f ((d:ℝ)*t)) ≤ ∫ t in a..(1-a), f t := by
  classical
  let U := {x : ℝ | a≤‖(x:UnitAddCircle)‖}
  let g := U.indicator f
  have hc : Continuous (fun x : ℝ => ‖(x:UnitAddCircle)‖) := by fun_prop
  have hu : MeasurableSet U := (isClosed_le continuous_const hc).measurableSet
  have hgper : Function.Periodic g 1 := by
    intro x
    have h : (x+1∈U) ↔ x∈U := by
      change (a≤‖((x+1:ℝ):UnitAddCircle)‖) ↔ _
      simp [U]
    by_cases hx : x∈U
    · simp [g,Set.indicator_of_mem hx,Set.indicator_of_mem (h.mpr hx),hp x]
    · simp [g,Set.indicator_of_notMem hx,Set.indicator_of_notMem (fun h' => hx (h.mp h'))]
  have hint (x y : ℝ) : IntervalIntegrable g volume x y :=
    intervalIntegrable_iff.mpr ((hf.intervalIntegrable x y).def'.integrable.indicator hu)
  have hreal (t : ℝ) (ht : t∈V) : g ((d:ℝ)*t) = f ((d:ℝ)*t) :=
    Set.indicator_of_mem (hsep t ht) _
  have hpre : MeasurableSet ((fun t : ℝ => (d:ℝ)*t)⁻¹' U) := hu.preimage (by fun_prop)
  have hcomp : IntegrableOn (fun t : ℝ => g ((d:ℝ)*t)) (Set.Icc 0 1) := by
    have hbase : IntegrableOn (fun t : ℝ => f ((d:ℝ)*t)) (Set.Icc 0 1) :=
      (hf.comp (by fun_prop)).integrableOn_Icc
    exact hbase.indicator hpre
  have hset : Set.Ioc (0:ℝ) 1 ∩ U = Set.Icc a (1-a) := by
    ext x
    have hchar (hx : 0≤x) (hx' : x<1) : x∈U ↔ a≤x ∧ x≤1-a := by
      change (a≤‖(x:UnitAddCircle)‖) ↔ _
      rw [UnitAddCircle.norm_eq,abs_sub_round_eq_min,Int.fract_eq_self.mpr ⟨hx,hx'⟩,le_min_iff]
      constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁,by linarith⟩
    constructor
    · rintro ⟨⟨hx,hx'⟩,hu'⟩
      rcases hx'.lt_or_eq with hlt|rfl
      · exact (hchar hx.le hlt).mp hu'
      · have hn : ¬(1:ℝ)∈U := by
          change ¬a≤‖((1:ℝ):UnitAddCircle)‖
          rw [UnitAddCircle.norm_eq]
          simpa using not_le.mpr ha
        exact (hn hu').elim
    · rintro ⟨h₁,h₂⟩
      have hx := ha.trans_le h₁
      have hx' : x<1 := by linarith
      exact ⟨⟨hx,hx'.le⟩,(hchar hx.le hx').mpr ⟨h₁,h₂⟩⟩
  calc
    _ = ∫ t in V, g ((d:ℝ)*t) :=
      setIntegral_congr_fun hVm (fun t ht => (hreal t ht).symm)
    _ ≤ ∫ t in Set.Icc (0:ℝ) 1, g ((d:ℝ)*t) := by
      apply setIntegral_mono_set hcomp _ (Filter.Eventually.of_forall fun _ ht => hV ht)
      exact Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun x _ => hpos x) _)
    _ = ∫ t in (0:ℝ)..1, g ((d:ℝ)*t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0:ℝ)..1,g t := unit_interval_integral_dilate hgper hint hd
    _ = ∫ t in a..(1-a),f t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      change (∫ t in Set.Ioc (0:ℝ) 1,U.indicator f t)=_
      rw [setIntegral_indicator hu,hset,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith)]

theorem minorArc_divisorRow_energy {V : Set ℝ} (hVm : MeasurableSet V) (hV : V⊆Set.Icc 0 1)
    {n Q d : ℕ} (hn : 0<n) (hd : 0<d) (hdn : d≤n) (hdQ : d≤Q) (hsmall : (Q:ℝ)/n≤1/2)
    (hminor : V⊆(rationalArcSet Q n)ᶜ) :
    (∫ t in V, ‖positiveDivisorRow n d t‖^2) ≤ 8*(n:ℝ)/Q := by
  let m := n/d-1
  have hQ : 0<Q := hd.trans_le hdQ
  have ha : 0<(Q:ℝ)/n := by positivity
  have hp := wheelGeometricKernel_period m
  have hrow := localized_dilate_integral_le_tail hVm hV hd ha hsmall
    (fun t ht => minorArc_dilate_circle_separation hn hd hdQ hsmall (hV ht) (hminor ht))
    (f:=fun t => ‖dirichletGeometricKernel m t‖^2) (by unfold dirichletGeometricKernel E;fun_prop)
    (fun t => sq_nonneg _) (fun t => by dsimp only;rw [hp t])
  have he (t : ℝ) : ‖positiveDivisorRow n d t‖=‖dirichletGeometricKernel m ((d:ℝ)*t)‖ := by
    rw [positiveDivisorRow_eq hd hdn,norm_mul,show ‖E ((d:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
  simp_rw [he]
  exact hrow.trans ((geometricKernel_single_period_tail m ha hsmall).trans_eq (by field_simp))

/-- Leakage bound for all finite divisor rows supported on d≤P in the original minor arcs. -/
theorem minorArc_finiteDivisorWave_energy {V : Set ℝ} (hVm : MeasurableSet V) (hV : V⊆Set.Icc 0 1)
    {n Q P : ℕ} (hn : 0<n) (hPn : P≤n) (hPQ : P≤Q) (hsmall : (Q:ℝ)/n≤1/2)
    (hminor : V⊆(rationalArcSet Q n)ᶜ) (a : ℕ→ℂ) {K : ℝ}
    (ha : ∀ d∈Icc 1 P,‖a d‖≤K) :
    (∫ t in V, ‖smallDivisorWave n (Icc 1 P) a t‖^2) ≤ 8*(P:ℝ)^2*K^2*(n:ℝ)/Q := by
  let I := Icc 1 P
  have hcard : (#I:ℝ)=P := by dsimp [I];simp
  let b := fun d t => ‖positiveDivisorRow n d t‖
  have hpoint (t : ℝ) : ‖smallDivisorWave n I a t‖^2≤(P:ℝ)*K^2*(∑ d∈I,b d t^2) := by
    have ht : ‖smallDivisorWave n I a t‖≤K*(∑ d∈I,b d t) := by
      unfold smallDivisorWave;apply (norm_sum_le ..).trans;rw [mul_sum]
      apply sum_le_sum;intro d hd
      rw [norm_mul];exact mul_le_mul_of_nonneg_right (ha d hd) (norm_nonneg _)
    have hcs := sum_mul_sq_le_sq_mul_sq I (fun _ : ℕ => (1:ℝ)) (fun d => b d t)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hcard] at hcs
    have hsq := pow_le_pow_left₀ (norm_nonneg _) ht 2
    rw [mul_pow] at hsq
    exact hsq.trans ((mul_le_mul_of_nonneg_left hcs (sq_nonneg K)).trans_eq (by ring))
  have hrow d (hd : d∈I) := minorArc_divisorRow_energy hVm hV hn (mem_Icc.mp hd).1
    ((mem_Icc.mp hd).2.trans hPn) ((mem_Icc.mp hd).2.trans hPQ) hsmall hminor
  have hc (d : ℕ) : Continuous (fun t => b d t^2) := by unfold b positiveDivisorRow E;fun_prop
  have hI (d : ℕ) : IntegrableOn (fun t => b d t^2) V := (hc d).integrableOn_Icc.mono_set hV
  have hF : Continuous (fun t => ‖smallDivisorWave n I a t‖^2) := by unfold smallDivisorWave positiveDivisorRow E;fun_prop
  have hsum : Continuous (fun t => (P:ℝ)*K^2*∑ d∈I,b d t^2) :=
    continuous_const.mul (continuous_finsetSum I fun d _ => hc d)
  calc
    _ ≤ ∫ t in V,(P:ℝ)*K^2*∑ d∈I,b d t^2 := integral_mono (hF.integrableOn_Icc.mono_set hV)
      (hsum.integrableOn_Icc.mono_set hV) hpoint
    _ = (P:ℝ)*K^2*∑ d∈I,∫ t in V,b d t^2 := by
      rw [integral_const_mul,integral_finsetSum _ (fun d _ => hI d)]
    _ ≤ (P:ℝ)*K^2*∑ _d∈I,8*(n:ℝ)/Q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum hrow
    _ = _ := by simp only [sum_const,nsmul_eq_mul,hcard];ring

/-- The cutoff grows like the eighth root of the natural logarithm. -/
noncomputable def minorRamanujanCutoff (n : ℕ) := ⌊(Real.log (n:ℝ))^(1/8:ℝ)⌋₊

private theorem minor_log_square_lower {n : ℕ} (hn : 0<n) :
    (Real.log n)^2≤4*(medDeskQ n:ℝ) := by
  let k := Nat.log 2 (n+2)
  have hk : 1≤k := Nat.log_pos (by decide) (by omega)
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Nat.lt_pow_succ_log_self (by decide : 1<2) (n+2)
  have hpow : (n:ℝ)≤(2:ℝ)^(k+1) := by exact_mod_cast (show n≤2^(k+1) by dsimp [k];omega)
  have hlog := Real.log_le_log (by exact_mod_cast hn) hpow
  rw [Real.log_pow] at hlog;push_cast at hlog
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hprod := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤(k:ℝ)+1)
  have hlog' : Real.log n≤2*(k:ℝ) := by linarith only [hlog,hprod,hk']
  change _≤4*((k^2:ℕ):ℝ)
  push_cast
  have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog' 2
  nlinarith only [hsq]

theorem minorRamanujan_geometry_eventually :
    ∀ᶠ n : ℕ in atTop, let T := (Real.log n)^(1/8:ℝ)
      0<n ∧ 2≤T ∧ T^8=Real.log n ∧ T^32≤Real.sqrt n ∧
      (minorRamanujanCutoff n:ℝ)≤T ∧ minorRamanujanCutoff n≤medDeskQ n ∧
      minorRamanujanCutoff n≤n ∧ 0<medDeskQ n ∧ (medDeskQ n:ℝ)/n≤1/2 ∧
      T^16≤4*(medDeskQ n:ℝ) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hp := (isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0:ℝ)<1/2)).bound zero_lt_one
  filter_upwards [ht.eventually_ge_atTop 2,tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually hp,
      eventually_core_cutoffs,squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ)] with n ht hp hc hg hn
  let T := (Real.log n)^(1/8:ℝ)
  change 2≤T at ht
  have ht0 : 0<T := by linarith
  have hl := Real.log_natCast_nonneg n
  have ht8 : T^8=Real.log n := by
    dsimp [T];rw [←Real.rpow_natCast,←Real.rpow_mul hl];norm_num
  have ht32 : T^32≤Real.sqrt n := by
    rw [show T^32=(T^8)^4 by ring,ht8,Real.sqrt_eq_rpow]
    change ‖Real.log (n:ℝ)^(4:ℝ)‖≤_ at hp
    simpa only [show (4:ℝ)=((4:ℕ):ℝ) from rfl,Real.rpow_natCast,Real.norm_of_nonneg
      (pow_nonneg hl 4),Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),one_mul] using hp
  have hT16 : T^16≤4*(medDeskQ n:ℝ) := by rw [show T^16=(T^8)^2 by ring,ht8];exact minor_log_square_lower hn
  have hP : (minorRamanujanCutoff n:ℝ)≤T := Nat.floor_le ht0.le
  have hTQ : T≤medDeskQ n := by
    have hT3 : T^3≤T^16 := pow_le_pow_right₀ (by linarith only [ht]) (by decide)
    have ht2 : (2:ℝ)^2≤T^2 := pow_le_pow_left₀ (by norm_num) ht 2
    nlinarith only [hT3,hT16,mul_le_mul_of_nonneg_right ht2 ht0.le]
  have hPQ : minorRamanujanCutoff n≤medDeskQ n := by exact_mod_cast hP.trans hTQ
  have hB : 0<medDeskD n := hg.1
  have hN : 2*medDeskQ n*medDeskD n<n := hc.2.2.2
  have hqN : 2*medDeskQ n≤n := (Nat.le_mul_of_pos_right (2*medDeskQ n) hB).trans hN.le
  have hQ : 0<medDeskQ n := Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  refine ⟨hn,ht,ht8,ht32,hP,hPQ,by omega,hQ,?_,hT16⟩
  apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
  have hreal : 2*(medDeskQ n:ℝ)≤n := by exact_mod_cast hqN
  linarith

theorem minorArc_exactWeight_energy :
    ∀ᶠ n : ℕ in atTop,∀ V : Set ℝ, MeasurableSet V → V⊆Set.Icc 0 1 →
      V⊆(rationalArcSet (medDeskQ n) n)ᶜ →
      (∫ t in V,‖smallDivisorWave n (Icc 1 (minorRamanujanCutoff n))
        (fun d => (exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t‖^2) ≤
        8192*(n:ℝ)/((Real.log n)^(1/8:ℝ))^12 := by
  filter_upwards [minorRamanujan_geometry_eventually] with n h
  intro V hm hV hminor
  obtain ⟨hn,ht,h8,_,hP,hPQ,hPn,hQ,hw,hQ'⟩ := h
  let T := (Real.log (n:ℝ))^(1/8:ℝ)
  let P := minorRamanujanCutoff n
  let Q := medDeskQ n
  have ht0 : 0<T := by linarith only [ht]
  have hq0 : (0:ℝ)<Q := by exact_mod_cast hQ
  have hK : 8*(1+Real.log P)≤16*T := by
    have hp : Real.log P≤(P:ℝ) := Real.log_le_self (Nat.cast_nonneg _)
    linarith only [hP,hp,ht]
  have hh := minorArc_finiteDivisorWave_energy hm hV hn hPn hPQ hw hminor
    (fun d => (exactRamanujanWeight P d:ℂ)) (K:=16*T)
    (fun d _ => by rw [Complex.norm_real,Real.norm_eq_abs];exact (exactRamanujanWeight_abs_le_log P d).trans hK)
  apply hh.trans
  change 8*(P:ℝ)^2*(16*T)^2*(n:ℝ)/Q≤8192*(n:ℝ)/T^12
  apply (div_le_div_iff₀ hq0 (pow_pos ht0 12)).mpr
  calc
    _ ≤ (8*T^2*(16*T)^2*(n:ℝ))*T^12 := by gcongr
    _ = 2048*(n:ℝ)*T^16 := by ring
    _ ≤ 2048*(n:ℝ)*(4*(Q:ℝ)) := by gcongr
    _ = _ := by ring

end GoldbachPartial
