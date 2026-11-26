
import NonresonantSquareShortModes
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private def zeroPairBox (n:ℕ) :=
  ((Icc 1 n) ×ˢ (Icc 1 n)).filter (fun u=>farPairFrequency n u.1 u.2=0)

private theorem zeroPair_mem {n:ℕ}{u:ℕ×ℕ}(hu:u∈zeroPairBox n) :
    u.1∈Icc 1 n ∧ u.2∈Icc 1 n := mem_product.mp (mem_filter.mp hu).1

theorem zeroFrequency_divisor_convolution (n:ℕ) :
    (∑u∈zeroPairBox n,(u.1.divisors.card:ℝ)*u.2.divisors.card) ≤ (n:ℝ)*(1+Real.log n)^3 := by
  let I := zeroPairBox n
  let A (k:ℕ):ℝ := k.divisors.card
  have h₁ : (↑I:Set (ℕ×ℕ)).InjOn Prod.fst := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have h1 := (mem_filter.mp hab).2
    have h2 := (mem_filter.mp hcd).2
    change (a:ℤ)+b-n=0 at h1
    change (c:ℤ)+d-n=0 at h2
    change a=c at he
    exact Prod.ext he (by omega)
  have h₂ : (↑I:Set (ℕ×ℕ)).InjOn Prod.snd := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have h1 := (mem_filter.mp hab).2
    have h2 := (mem_filter.mp hcd).2
    change (a:ℤ)+b-n=0 at h1
    change (c:ℤ)+d-n=0 at h2
    change b=d at he
    exact Prod.ext (by omega) he
  have hproj (f:ℕ×ℕ→ℕ) (hf:(↑I:Set (ℕ×ℕ)).InjOn f) (hh:∀u∈I,f u∈Icc 1 n) :
      (∑u∈I,(A (f u))^2) ≤(n:ℝ)*(1+Real.log n)^3 := by
    apply le_trans _ (divisor_square_mean_bound n)
    apply sum_le_sum_of_injOn f hf
    · intro k hk
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hk
      exact hh u hu
    · intro u _; exact le_rfl
    · intro k _ _; exact sq_nonneg _
  have hl := hproj _ h₁ (fun u hu => (zeroPair_mem hu).1)
  have hr := hproj _ h₂ (fun u hu => (zeroPair_mem hu).2)
  have hh : (2:ℝ)*(∑u∈I,A u.1*A u.2) ≤
          (∑u∈I,(A u.1)^2)+(∑u∈I,(A u.2)^2) := by
    rw [mul_sum,←sum_add_distrib]
    exact sum_le_sum fun u _ => by nlinarith [sq_nonneg (A u.1-A u.2)]
  change ∑u∈I,A u.1*A u.2≤_
  linarith only [hl,hr,hh]

theorem nonresonantCoefficient_eq_common {n D q k:ℕ} (hk:¬q∣k) :
    nonresonantCoefficient n D q k=nonresonantCoefficient n D 0 k := by
  unfold nonresonantCoefficient
  congr 1
  ext d
  simp only [mem_filter,mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hl,hu⟩,_⟩,hd⟩
    exact ⟨⟨⟨hl,hu⟩,by simp;omega⟩,hd⟩
  · rintro ⟨⟨⟨hl,hu⟩,_⟩,hd⟩
    exact ⟨⟨⟨hl,hu⟩,fun h=>hk (h.trans hd)⟩,hd⟩

private def zeroBadCount (R Q k:ℕ) := ((Ico R Q).filter fun j=>j+1∣k).card
private theorem zeroBadCount_le {k:ℕ} (hk:0<k) (R Q:ℕ) : zeroBadCount R Q k ≤ k.divisors.card := by
  apply card_le_card_of_injOn (fun j=>j+1)
  · intro j hj;exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hj).2,hk.ne'⟩
  · intro i _ j _ h;change i+1=j+1 at h;omega

private theorem zeroPair_bad_card {k l:ℕ} (hk:0<k) (hl:0<l) (R Q:ℕ) :
    ((Ico R Q).filter (fun j=>j+1∣k ∨ j+1∣l)).card≤k.divisors.card+l.divisors.card := by
  rw [filter_or]
  exact (card_union_le _ _).trans (Nat.add_le_add (zeroBadCount_le hk R Q) (zeroBadCount_le hl R Q))

private theorem zero_divisor_fourth_root {k n:ℕ} (hkn:k≤n) :
    (k.divisors.card:ℝ) ≤ 4096*(n:ℝ)^(1/4:ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have h : (k.divisors.card:ℝ)^4 ≤ (2:ℝ)^48*(k:ℝ) := by exact_mod_cast divisor_count_fourth_le k
  apply h.trans
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  norm_num
  exact_mod_cast hkn

theorem zeroFrequency_common_weighted (n D R Q:ℕ) (w:ℕ→ℝ) (hw:∀j∈Ico R Q,|w j|≤1) :
    |∑j∈Ico R Q,w j*(nonresonantSquareModeCoefficient n D (j+1) 0-
          nonresonantSquareModeCoefficient n D 0 0)| ≤
      (16384*(n:ℝ)^(1/4:ℝ)*(Real.log n)^2)*((n:ℝ)*(1+Real.log n)^3) := by
  let B (q:ℕ) (u:ℕ×ℕ) := nonresonantCoefficient n D q u.1*nonresonantCoefficient n D q u.2
  let T (u:ℕ×ℕ) : ℝ := (u.1.divisors.card:ℝ)*u.2.divisors.card
  let I := zeroPairBox n
  let J := Ico R Q
  let C := 16384*(n:ℝ)^(1/4:ℝ)*(Real.log n)^2
  have hT (u:ℕ×ℕ) : 0≤T u := by dsimp [T];positivity
  have hB (q:ℕ) (u:ℕ×ℕ) (hu:u∈I) : |B q u|≤T u*(Real.log n)^2 := by
    obtain ⟨hk,hl⟩ := zeroPair_mem hu
    dsimp [B,T];rw [abs_mul]
    apply (mul_le_mul (nonresonantCoefficient_bound (mem_Icc.mp hk).1 n D q)
      (nonresonantCoefficient_bound (mem_Icc.mp hl).1 n D q) (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))).trans_eq
    ring
  have hpair (u:ℕ×ℕ) (hu:u∈I) :
      |∑j∈J,w j*(B (j+1) u-B 0 u)|≤C*T u := by
    obtain ⟨hk,hl⟩ := zeroPair_mem hu
    let bad (j:ℕ) := j+1∣u.1 ∨ j+1∣u.2
    have hrest (j:ℕ) (_hj:j∈J) (hne:w j*(B (j+1) u-B 0 u)≠0) : bad j := by
      by_contra hb
      change ¬(_ ∨ _) at hb
      obtain ⟨h₁,h₂⟩ := not_or.mp hb
      apply hne; unfold B
      rw [nonresonantCoefficient_eq_common h₁,nonresonantCoefficient_eq_common h₂,sub_self,mul_zero]
    rw [←sum_filter_of_ne hrest]
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _j∈J.filter bad,2*(T u*(Real.log n)^2) := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul]
        apply (mul_le_of_le_one_left (abs_nonneg _) (hw j (mem_filter.mp hj).1)).trans
        exact (abs_sub _ _).trans ((add_le_add (hB (j+1) u hu) (hB 0 u hu)).trans_eq (by ring))
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        have hc : ((J.filter bad).card:ℝ) ≤ (u.1.divisors.card:ℝ)+u.2.divisors.card := by
          exact_mod_cast zeroPair_bad_card (mem_Icc.mp hk).1 (mem_Icc.mp hl).1 R Q
        have hr := hc.trans (add_le_add (zero_divisor_fourth_root (mem_Icc.mp hk).2)
                                        (zero_divisor_fourth_root (mem_Icc.mp hl).2))
        exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans_eq (by dsimp [C];ring)
  change |∑j∈J,w j*((∑u∈I,B (j+1) u)-(∑u∈I,B 0 u))|≤_
  simp_rw [←sum_sub_distrib,mul_sum]
  rw [sum_comm]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum hpair).trans
  rw [←mul_sum]
  exact mul_le_mul_of_nonneg_left (zeroFrequency_divisor_convolution n) (by dsimp [C];positivity)

theorem zeroFrequency_mass_eq (n D R Q:ℕ) :
    nonresonantSquareModeMass n D R Q {0} =
      (((2/((3*Q:ℕ):ℝ)) * ∑j∈Ico R Q,
        (((j+1).totient:ℝ)/((j+1:ℕ):ℝ))*nonresonantSquareModeCoefficient n D (j+1) 0:ℝ):ℂ) := by
  unfold nonresonantSquareModeMass
  rw [mul_sum,Complex.ofReal_sum]
  apply sum_congr rfl
  intro j _
  have hz := unit_exp_ramanujan_eq_divisor 0 (j+1)
  simp [E,ZMod.card_units_eq_totient] at hz
  have h₀ : dyadicRamanujanDivisor 0 (j+1) = ((j+1).totient:ℤ) := by exact_mod_cast hz.symm
  simp only [sum_singleton,Int.natAbs_zero,h₀,Int.cast_natCast,Int.cast_zero,zero_mul,E,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,intervalIntegral.integral_const,sub_neg_eq_add,
    Complex.real_smul,mul_one]
  unfold naturalTubeRadius
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem zeroFrequency_mass_common_bound (n D R Q:ℕ) (hQ:0<Q) :
    ‖nonresonantSquareModeMass n D R Q {0} -
      ((volume.real (naturalTubeUnion R Q (3*Q))*nonresonantSquareModeCoefficient n D 0 0:ℝ):ℂ)‖ ≤
      (2/((3*Q:ℕ):ℝ))*(16384*(n:ℝ)^(1/4:ℝ)*(Real.log n)^2)*
        ((n:ℝ)*(1+Real.log n)^3) := by
  let w (j:ℕ) := ((j+1).totient:ℝ)/((j+1:ℕ):ℝ)
  have hw (j:ℕ) (_hj:j∈Ico R Q) : |w j|≤1 := by
    dsimp [w];rw [abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.totient_le (j+1)
  rw [zeroFrequency_mass_eq,naturalTubeUnion_realVolume_eq R Q (3*Q) (by omega),←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
  change |(2/((3*Q:ℕ):ℝ))*(∑j∈Ico R Q,w j*nonresonantSquareModeCoefficient n D (j+1) 0) -
    ((2/((3*Q:ℕ):ℝ))*(∑j∈Ico R Q,w j))*nonresonantSquareModeCoefficient n D 0 0|≤_
  rw [mul_assoc,←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤2/((3*Q:ℕ):ℝ)),sum_mul,
    ←sum_sub_distrib]
  simp_rw [←mul_sub]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (zeroFrequency_common_weighted n D R Q w hw) (by positivity)

theorem zeroFrequency_mass_common_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, ∀D R:ℕ,
      ‖nonresonantSquareModeMass n D R (naturalTubeScale n) {0} -
        ((volume.real (naturalTubeUnion R (naturalTubeScale n) (3*naturalTubeScale n))*
            nonresonantSquareModeCoefficient n D 0 0:ℝ):ℂ)‖ ≤ ε*(n:ℝ) := by
  let t := fun n:ℕ=>(n:ℝ)^(1/4:ℝ)
  have hl : Tendsto (fun n:ℕ=>(Real.log n)^5/t n) atTop (𝓝 0) := by
    simpa only [t,Function.comp_def,Real.rpow_ofNat] using
      ((isLittleO_log_rpow_rpow_atTop (5:ℝ) (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually_ge_atTop 1,
      hl.eventually_lt_const (by positivity : (0:ℝ)<ε/262144)] with n hn hlog hsmall
  intro D R
  let Q := naturalTubeScale n
  let T := t n
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hT : 0<T := Real.rpow_pos_of_pos hn0 _
  have hs1 : 1≤Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hq1 : 1≤Q := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by simpa using hs1)
  have hq1r : (1:ℝ)≤Q := by exact_mod_cast hq1
  have hQr : (0:ℝ)<Q := by linarith
  have hT2 : T^2=Real.sqrt n := by
    dsimp [T,t];rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le,Real.sqrt_eq_rpow];norm_num
  have hqs : T^2≤2*(Q:ℝ) := by
    rw [hT2]; have hh : Real.sqrt n<(Q:ℝ)+1 := Nat.lt_floor_add_one _;linarith
  have hrec : 2/(3*(Q:ℝ))≤2/T^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr;linarith only [hqs,hQr]
  change 1≤Real.log (n:ℝ) at hlog
  have hL : 1+Real.log n≤2*Real.log n := by linarith
  have hlg : 0≤Real.log n := by linarith
  have hbase := zeroFrequency_mass_common_bound n D R Q (by omega)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hbase
  apply hbase.trans
  change 2/(3*(Q:ℝ))*(16384*T*(Real.log n)^2)*((n:ℝ)*(1+Real.log n)^3) ≤ _
  calc
    _ ≤ (2/T^2)*(16384*T*(Real.log n)^2)*((n:ℝ)*(2*Real.log n)^3) := by gcongr
    _ = (262144*((Real.log n)^5/T))*(n:ℝ) := by field_simp;ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hn0.le
      have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<262144)).mp hsmall
      change (Real.log (n:ℝ))^5/T*262144<ε at h
      linarith only [h]
end GoldbachPartial
