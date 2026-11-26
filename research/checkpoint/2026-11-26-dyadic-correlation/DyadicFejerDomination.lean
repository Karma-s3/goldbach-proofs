import DyadicFejerDefinitions
import NaturalTubeDilation
import FejerMajorWindow

namespace GoldbachPartial
open Finset ExtendedArcCoefficient

theorem fejerWave_nonneg (M : ℕ) (x : ℝ) : 0 ≤ fejerWave M x := by
  unfold fejerWave
  positivity

theorem fejerWave_one (x : ℝ) : fejerWave 1 x=1 := by
  simp [fejerWave,dirichletGeometricKernel,E]

theorem fejerWave_le_envelope {Q j : ℕ} (hj : j≤Nat.log 2 Q) (x : ℝ) :
    fejerWave (2^j) x ≤ dyadicFejerEnvelope Q x :=
  single_le_sum (fun k _ => fejerWave_nonneg (2^k) x) (mem_range.mpr (Nat.lt_succ_of_le hj))

private theorem phaseKernel_round_reduce (n : ℕ) (x : ℝ) :
    dirichletGeometricKernel n (x-round x) = dirichletGeometricKernel n x := by
  have hp := wheelGeometricKernel_period n
  simpa only [mul_one] using hp.sub_int_mul_eq (x:=x) (round x)

theorem fejerWave_lower_near_integer {M : ℕ} (hM : 0<M) {x : ℝ}
    (hx : 6*(M:ℝ)*‖(x:UnitAddCircle)‖≤1) : (M:ℝ)/4 ≤ fejerWave M x := by
  let β := x-(round x:ℝ)
  have hp := Real.pi_pos
  have hR : M-1+1=M := by omega
  have hsmall : 6*(M:ℝ)*|β|≤1 := by simpa only [UnitAddCircle.norm_eq] using hx
  have hcos (k : ℕ) (hk : k∈range M) : 1/2≤(E ((k:ℝ)*β)).re := by
    have hkn : (k:ℝ)≤M := by exact_mod_cast (mem_range.mp hk).le
    have hb := mul_le_mul_of_nonneg_right hkn (abs_nonneg β)
    have harg : |2*Real.pi*((k:ℝ)*β)| ≤ Real.pi/3 := by
      simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k),abs_of_pos hp,
        abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith only [mul_le_mul_of_nonneg_left (show (k:ℝ)*|β|≤1/6 by linarith only [hsmall,hb]) hp.le]
    unfold E
    rw [Complex.exp_ofReal_mul_I_re,←Real.cos_abs,←Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hnorm : (M:ℝ)/2 ≤ ‖dirichletGeometricKernel (M-1) x‖ := by
    rw [←phaseKernel_round_reduce _ x]
    calc
      _ = ∑ k∈range M,(1/2:ℝ) := by simp; ring
      _ ≤ ∑ k∈range M,(E ((k:ℝ)*β)).re := sum_le_sum hcos
      _ = (dirichletGeometricKernel (M-1) β).re := by simp [dirichletGeometricKernel,hR]
      _ ≤ _ := Complex.re_le_norm _
  apply (le_div_iff₀ (by exact_mod_cast hM : (0:ℝ)<M)).mpr
  nlinarith only [pow_le_pow_left₀ (by positivity) hnorm 2]

theorem min_inverse_circle_norm_le_fejer_envelope (Q : ℕ) (x : ℝ) :
    min (Q:ℝ) (1/‖(x:UnitAddCircle)‖) ≤ 48*dyadicFejerEnvelope Q x := by
  let v := ‖(x:UnitAddCircle)‖
  let b := min (Q:ℝ) (1/v)
  have hv : 0≤v := norm_nonneg _
  have hb : 0≤b := le_min (Nat.cast_nonneg _) (by positivity)
  have h0 : 1≤dyadicFejerEnvelope Q x := by
    simpa only [pow_zero,fejerWave_one] using fejerWave_le_envelope (Q:=Q) (j:=0) (Nat.zero_le _) x
  change b≤_
  by_cases hbig : 6≤b
  · let m : ℕ := ⌊b/6⌋₊
    have hm : 1≤m := (Nat.one_le_floor_iff _).mpr (by linarith)
    have hfloor : (m:ℝ)≤b/6 := Nat.floor_le (by positivity)
    have hupper : b/6 < (m:ℝ)+1 := Nat.lt_floor_add_one _
    let j := Nat.log 2 m
    let M := 2^j
    have hM : 0<M := Nat.two_pow_pos _
    have hMm : M≤m := Nat.pow_log_le_self _ (by omega : m≠0)
    have hmQ : m≤Q := by
      have hBQ : b≤(Q:ℝ) := min_le_left _ _
      exact_mod_cast (show (m:ℝ)≤Q by linarith)
    have henv := fejerWave_le_envelope (Nat.log_mono_right hmQ) x
    have hbound : m+1≤M*2 := by
      have hh := Nat.lt_pow_succ_log_self (by decide : 1<2) m
      simpa only [pow_succ] using (show m+1≤2^(Nat.log 2 m+1) from hh)
    have hvpos : 0<v := by
      by_contra! h
      have he := le_antisymm h hv
      have hbi : b≤1/v := min_le_right _ _
      rw [he] at hbi
      norm_num at hbi
      linarith
    have hprod : b*v ≤ 1 := (le_div_iff₀ hvpos).mp (min_le_right _ _)
    have hMR : (M:ℝ)≤m := by exact_mod_cast hMm
    have hlocal : 6*(M:ℝ)*v≤1 := by
      have h := mul_le_mul_of_nonneg_right (show 6*(M:ℝ)≤b by linarith) hv
      linarith only [h,hprod]
    have hlow := fejerWave_lower_near_integer hM hlocal
    have hsz : (m:ℝ)+1≤(M:ℝ)*2 := by exact_mod_cast hbound
    change fejerWave M x≤_ at henv
    linarith only [hlow,henv,hsz,hupper]
  · linarith only [h0,lt_of_not_ge hbig]

theorem naturalTube_geometricKernel_le_fejer_envelope {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    {t : ℝ} (ht : t∈naturalTubeUnion R Q (3*Q)) (m : ℕ) :
    ‖dirichletGeometricKernel m ((d:ℝ)*t)‖ ≤ 48*dyadicFejerEnvelope Q ((d:ℝ)*t) := by
  let x := (d:ℝ)*t
  let β := x-(round x:ℝ)
  let v := ‖(x:UnitAddCircle)‖
  have hQn : 0<Q := by
    by_contra! h
    have h0 : Q=0 := by omega
    simp [h0,naturalTubeUnion,naturalTubeIndices] at ht
  have hQ : (0:ℝ)<Q := by exact_mod_cast hQn
  have hsep : (2/3:ℝ)/Q≤v := naturalTube_dilate_circle_separation hd hdR ht
  have hv : 0<v := (div_pos (by norm_num) hQ).trans_le hsep
  have hvb : |β|=v := UnitAddCircle.norm_eq.symm
  have hvhalf : v≤1/2 := by rw [←hvb]; exact abs_sub_round _
  have hn : ‖dirichletGeometricKernel m x‖=‖dirichletGeometricKernel m v‖ := by
    rw [←phaseKernel_round_reduce m x,←hvb]
    change ‖dirichletGeometricKernel m β‖=‖dirichletGeometricKernel m |β|‖
    by_cases h : 0≤β
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h),wheelGeometricKernel_neg_norm]
  have hk : ‖dirichletGeometricKernel m x‖ ≤ 1/(2*v) := by
    rw [hn]
    exact fejer_kernel_pointwise m hv hvhalf
  apply (le_min _ _).trans (min_inverse_circle_norm_le_fejer_envelope Q x)
  · apply hk.trans
    apply (div_le_iff₀ (by positivity)).mpr
    have hb := (div_le_iff₀ hQ).mp hsep
    linarith only [hb]
  · exact hk.trans (one_div_le_one_div_of_le hv (by linarith))

theorem naturalTube_shifted_geometric_le_fejer_envelope {R Q d : ℕ} (hd : 0<d) (hdR : d≤R)
    {t : ℝ} (ht : t∈naturalTubeUnion R Q (3*Q)) (m : ℕ) :
    ‖∑ j∈Icc 1 m,E ((j:ℝ)*((d:ℝ)*t))‖ ≤ 48*dyadicFejerEnvelope Q ((d:ℝ)*t) := by
  let x := (d:ℝ)*t
  rcases Nat.eq_zero_or_pos m with rfl|hm
  · simp only [Icc_eq_empty_of_lt (by decide : 0<1),sum_empty,norm_zero]
    exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => fejerWave_nonneg _ _)
  · have hset : Icc 1 m = Ico 1 (m+1) := by ext k; simp
    have hrow : (∑ j∈Icc 1 m,E ((j:ℝ)*x))=E x * dirichletGeometricKernel (m-1) x := by
      rw [hset,sum_Ico_eq_sum_range]
      unfold dirichletGeometricKernel
      simp only [Nat.add_sub_cancel,show m-1+1=m by omega,Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,phase_add]
    change ‖∑ j∈Icc 1 m,E ((j:ℝ)*x)‖ ≤ _
    rw [hrow,norm_mul,show ‖E x‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
    exact naturalTube_geometricKernel_le_fejer_envelope hd hdR ht _

end GoldbachPartial