import VerifiedMinorArcVaughanTypeII

namespace GoldbachPartial
open Finset ExtendedArcCoefficient
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

theorem rationalSample_small_integer (d q a : ℕ) (hd : 0<d) (hdq : 2*d≤q)
    (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (z : ℤ) :
    1/(2*(q:ℝ)) ≤ |(d:ℝ)*α-z| := by
  have hq : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hz : (d:ℤ)*a-z*q ≠ 0 := by
    intro he
    have hv : (q:ℤ) ∣ (d:ℤ)*a := ⟨z,by linarith only [he]⟩
    have hv' : q ∣ d*a := by exact_mod_cast hv
    have hh := Nat.le_of_dvd hd (hc.symm.dvd_of_dvd_mul_right hv')
    omega
  have h1 : (1:ℝ)≤|(d:ℝ)*a-z*q| := by
    exact_mod_cast (show (1:ℤ)≤|(d:ℤ)*a-z*q| by have hp:=abs_pos.mpr hz;omega)
  have hterm : |(q:ℝ)*α-a|≤1/(q:ℝ) := by
    calc _ = (q:ℝ)*|α-a/(q:ℝ)| := by
              rw [show (q:ℝ)*α-a=(q:ℝ)*(α-(a:ℝ)/q) by field_simp,abs_mul,abs_of_pos hq]
         _ ≤ (q:ℝ)*(1/(q:ℝ)^2) := mul_le_mul_of_nonneg_left ha hq.le
         _ = _ := by field_simp
  have hnear : (d:ℝ)*|(q:ℝ)*α-a|≤1/2 := by
    apply (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg d)).trans
    rw [mul_one_div,div_le_div_iff₀ hq (by norm_num : (0:ℝ)<2)]
    have hh : 2*(d:ℝ)≤q := by exact_mod_cast hdq
    linarith
  have htri : |(d:ℝ)*a-z*q|≤(d:ℝ)*|(q:ℝ)*α-a|+(q:ℝ)*|(d:ℝ)*α-z| := by
    calc _ = |(-((d:ℝ)*((q:ℝ)*α-a)))+(q:ℝ)*((d:ℝ)*α-z)| := by congr 1;ring
         _ ≤ _ := by simpa only [abs_neg,abs_mul,abs_of_pos hq,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)]
                      using abs_add_le (-((d:ℝ)*((q:ℝ)*α-a))) ((q:ℝ)*((d:ℝ)*α-z))
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [h1,hnear,htri]

theorem rationalSample_small_prefix (T d q a : ℕ) (hd : 0<d) (hdq : 2*d≤q)
    (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖∑j∈Icc 1 T,E ((j:ℝ)*((d:ℝ)*α))‖≤2*(q:ℝ) := by
  let t := (d:ℝ)*α
  have hq : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hsep : 1/(2*(q:ℝ))≤‖(t:UnitAddCircle)‖ := by
    rw [UnitAddCircle.norm_eq];exact rationalSample_small_integer d q a hd hdq hc ha _
  have hdist := (one_div_pos.mpr (by positivity : 0<2*(q:ℝ))).trans_le hsep
  rw [show Icc 1 T=Ico 1 (T+1) by ext j;simp,sum_Ico_eq_sum_range,Nat.add_sub_cancel]
  apply (cappedCircleReciprocal_geometric_row 1 T T t le_rfl).trans
  rw [cappedCircleReciprocal,ite_eq_right hdist.ne']
  apply (min_le_right ..).trans
  apply (div_le_iff₀ hdist).mpr
  have hh := (div_le_iff₀ (by positivity : 0<2*(q:ℝ))).mp hsep
  linarith only [hh]

private theorem minorShift (T : ℕ) (g : ℕ→ℂ) :
    (∑j∈Icc 1 T,g j)=∑ k∈range T,g (k+1) := by
  rw [show Icc 1 T=Ico 1 (T+1) by ext j;simp,sum_Ico_eq_sum_range]
  simp [add_comm]

theorem rationalSample_small_weighted_prefix (T d q a : ℕ) (hd : 0<d) (hdq : 2*d≤q)
    (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2)
    (w : ℕ→ℝ) (hw : Monotone w) (hpos : ∀j,0≤w j) :
    ‖∑j∈Icc 1 T,(w j:ℂ)*E ((j:ℝ)*((d:ℝ)*α))‖≤4*(q:ℝ)*w (T+1) := by
  let W (k : ℕ) := w (k+1)
  let F (k : ℕ) := E (((k+1:ℕ):ℝ)*((d:ℝ)*α))
  have hP (K : ℕ) : ‖∑k∈range K,F k‖≤2*(q:ℝ) := by
    rw [←minorShift K (fun j=>E ((j:ℝ)*((d:ℝ)*α)))]
    exact rationalSample_small_prefix K d q a hd hdq hc ha
  have hwW : Monotone W := fun _ _ h => hw (Nat.add_le_add_right h 1)
  rw [minorShift]
  have hp := sum_range_by_parts W F T
  change ‖∑k∈range T,(W k:ℂ)*F k‖≤_
  simp only [Complex.real_smul] at hp
  rw [hp]
  apply (norm_sub_le ..).trans
  have htop : ‖(W (T-1):ℂ)*∑k∈range T,F k‖≤W (T-1)*(2*(q:ℝ)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hpos _)]
    exact mul_le_mul_of_nonneg_left (hP T) (hpos _)
  have hdif (i : ℕ) : 0≤W (i+1)-W i := sub_nonneg.mpr (hwW (by omega))
  have ht : ‖∑i∈range (T-1),((W (i+1)-W i:ℝ):ℂ)*(∑j∈range (i+1),F j)‖≤
      (W (T-1)-W 0)*(2*(q:ℝ)) := by
    apply (norm_sum_le ..).trans
    rw [←sum_range_sub W,sum_mul]
    apply sum_le_sum;intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hdif i)]
    exact mul_le_mul_of_nonneg_left (hP (i+1)) (hdif i)
  have hle := mul_le_mul_of_nonneg_right (hwW (Nat.sub_le T 1)) (show (0:ℝ)≤2*q by positivity)
  have h0 := mul_nonneg (hpos 1) (show (0:ℝ)≤2*q by positivity)
  change 0≤W 0*(2*(q:ℝ)) at h0
  change _ ≤ 4*(q:ℝ)*W T
  linarith only [htop,ht,hle,h0]


noncomputable def vaughanAdditiveSum (X : ℕ) (f : ArithmeticFunction ℝ) (α : ℝ) : ℂ :=
  ∑k∈Icc 1 X,(f k:ℂ)*E ((k:ℝ)*α)

noncomputable def vaughanAdditiveBilinear (X : ℕ) (f g : ArithmeticFunction ℝ) (α : ℝ) : ℂ :=
  ∑d∈Icc 1 X,(f d:ℂ)*∑j∈Icc 1 (X/d),(g j:ℂ)*E ((j:ℝ)*((d:ℝ)*α))

theorem vaughan_additive_convolution (X : ℕ) (f g : ArithmeticFunction ℝ) (α : ℝ) :
    vaughanAdditiveSum X (f*g) α=vaughanAdditiveBilinear X f g α := by
  let F := fun p : ℕ×ℕ => (((f p.1)*(g p.2):ℝ):ℂ)*E ((p.2:ℝ)*((p.1:ℝ)*α))
  calc
    _ = ∑k∈Icc 1 X,∑p∈k.divisorsAntidiagonal,F p := by
      apply sum_congr rfl;intro k _
      rw [ArithmeticFunction.mul_apply,Complex.ofReal_sum,sum_mul]
      apply sum_congr rfl;intro p hp
      rw [←(Nat.mem_divisorsAntidiagonal.mp hp).1]
      dsimp only [F];push_cast;ring_nf
    _ = _ := by
      rw [vaughan_finite_hyperbola]
      dsimp only [vaughanAdditiveBilinear,F]
      apply sum_congr rfl;intro d _
      rw [mul_sum]
      apply sum_congr rfl;intro j _
      push_cast;ring

theorem vaughan_additive_identity (X U V : ℕ) (α : ℝ) :
    vaughanAdditiveSum X Λ α =
      vaughanAdditiveSum X (vaughanInitial V Λ) α +
      vaughanAdditiveBilinear X (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log α -
      vaughanAdditiveBilinear X (vaughanTypeICoefficient U V) (ζ : ArithmeticFunction ℝ) α +
      vaughanAdditiveBilinear X (vaughanTypeIICoefficient U) (vaughanTail V Λ) α := by
  have hid : Λ = vaughanInitial V Λ + vaughanInitial U (μ : ArithmeticFunction ℝ)*ArithmeticFunction.log -
      vaughanTypeICoefficient U V*(ζ : ArithmeticFunction ℝ)+vaughanTypeIICoefficient U*vaughanTail V Λ := by
    apply (vaughan_arithmetic_identity U V).trans
    dsimp only [vaughanTypeICoefficient,vaughanTypeIICoefficient];ring
  simp only [←vaughan_additive_convolution,vaughanAdditiveSum,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl;intro k _
  have hp := congrArg (fun f : ArithmeticFunction ℝ=>f k) hid
  change Λ k=_ at hp
  simp only [add_apply,sub_apply] at hp
  rw [hp];push_cast;ring

private theorem minor_natLog_mono : Monotone (fun n:ℕ=>Real.log (n:ℝ)) := by
  intro m n h
  by_cases hm : m=0
  · simp [hm];exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast h)

theorem vaughan_additive_log_small (X U q a : ℕ) (hU : 2*U≤q)
    (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖vaughanAdditiveBilinear X (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log α‖ ≤
      4*(q:ℝ)*Real.log (X+1:ℕ)*U := by
  let C := 4*(q:ℝ)*Real.log (X+1:ℕ)
  have hC : 0≤C := by dsimp [C];positivity
  apply (norm_sum_le ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (vaughan_mu_initial_l1 X U) hC)
  rw [mul_sum]
  apply sum_le_sum;intro d hd
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm C]
  by_cases h : d≤U
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply (rationalSample_small_weighted_prefix (X/d) d q a (mem_Icc.mp hd).1 (by omega) hc ha
      _ minor_natLog_mono Real.log_natCast_nonneg).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact minor_natLog_mono (Nat.add_le_add_right (Nat.div_le_self X d) 1)
  · change |if d≤U then _ else (0:ℝ)| * _≤|if d≤U then _ else (0:ℝ)| * C
    simp [h]

theorem vaughan_additive_zeta_small (X U V q a : ℕ) (hUV : 2*(U*V)≤q)
    (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖vaughanAdditiveBilinear X (vaughanTypeICoefficient U V) (ζ : ArithmeticFunction ℝ) α‖ ≤
      2*(q:ℝ)*((U:ℝ)*((Real.log 4+4)*V)) := by
  apply (norm_sum_le ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (vaughan_typeI_coefficient_l1 X U V) (by positivity : 0≤2*(q:ℝ)))
  rw [mul_sum]
  apply sum_le_sum;intro d hd;rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm (2*(q:ℝ))]
  by_cases h : d≤U*V
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply le_trans (le_of_eq ?_) (rationalSample_small_prefix (X/d) d q a (mem_Icc.mp hd).1 (by omega) hc ha)
    congr 1
    apply sum_congr rfl;intro j hj
    rw [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne (by have := (mem_Icc.mp hj).1;omega)]
    simp
  · rw [vaughanTypeICoefficient_support U V d (lt_of_not_ge h),abs_zero,zero_mul,zero_mul]

theorem vaughan_additive_initial_bound (X V : ℕ) (α : ℝ) :
    ‖vaughanAdditiveSum X (vaughanInitial V Λ) α‖≤(Real.log 4+4)*V := by
  apply (norm_sum_le ..).trans
  apply le_trans _ (vaughan_lambda_initial_l1 X V)
  apply sum_le_sum;intro k _
  rw [norm_mul,show ‖E ((k:ℝ)*α)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,Complex.norm_real,Real.norm_eq_abs]
  apply le_of_eq
  apply abs_of_nonneg
  change 0 ≤ (if k≤V then Λ k else 0)
  split_ifs <;> first | exact ArithmeticFunction.vonMangoldt_nonneg | exact le_rfl
end GoldbachPartial