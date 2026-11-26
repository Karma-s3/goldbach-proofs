import SignedPrimeArcBounds


/-! For a bounded sequence of prefixes, integrate its Abel transform over a window.
Parseval applied to the polynomial of prefixes gives a linear dependence on nρ. -/

namespace GoldbachPartial
open MeasureTheory Finset ExtendedArcCoefficient

noncomputable def finiteAbelWave (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ s, c k * E ((k:ℝ)*t)

private theorem abelParseval_nat_phase (k:ℕ) : E k=1 := by
  unfold E
  rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I k

private theorem abelParseval_conj (t : ℝ) : (starRingEnd ℂ) (E t) = E (-t) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

theorem finiteAbelWave_unit_energy (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ t in (-(1/2):ℝ)..(1/2), ‖finiteAbelWave s c t‖^2) = ∑ k ∈ s, ‖c k‖^2 := by
  have hper : Function.Periodic (finiteAbelWave s c) 1 := by
    intro t
    unfold finiteAbelWave
    simp_rw [mul_add,mul_one,phase_add,abelParseval_nat_phase,mul_one]
  have hper' : Function.Periodic (fun t => ‖finiteAbelWave s c t‖^2) 1 :=
    fun t => congrArg (fun z:ℂ => ‖z‖^2) (hper t)
  have hshift := hper'.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at hshift
  rw [hshift]
  let g (k j : ℕ) (t:ℝ) := (c k * (starRingEnd ℂ) (c j))*E ((((k:ℤ)-j):ℤ)*t)
  have hgc (k j : ℕ) : Continuous (g k j) := by dsimp [g,E]; fun_prop
  have hp (t:ℝ) : ((‖finiteAbelWave s c t‖^2 : ℝ):ℂ) = ∑ k ∈ s, ∑ j ∈ s, g k j t := by
    rw [Complex.ofReal_pow,←Complex.mul_conj']
    unfold finiteAbelWave
    rw [map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [g]
    rw [map_mul,abelParseval_conj]
    push_cast
    rw [show ((k:ℝ)-j)*t = (k:ℝ)*t + -((j:ℝ)*t) by ring,phase_add]
    ring
  have row (k:ℕ) (hk:k∈s) : (∫ t in (0:ℝ)..1, ∑ j ∈ s, g k j t) = ((‖c k‖^2:ℝ):ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hgc k j).intervalIntegrable _ _)]
    simp only [g,intervalIntegral.integral_const_mul,fourier_mode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [Complex.ofReal_pow,←Complex.mul_conj']
    · intro j hj hne
      simp [show (k:ℤ)-j ≠ 0 by omega]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum s (fun j _ => hgc k j)).intervalIntegrable _ _)]
  push_cast
  exact Finset.sum_congr rfl fun k hk => by simpa using row k hk

theorem finiteAbelWave_window_energy (s : Finset ℕ) (c : ℕ → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hh : ρ≤1/2) :
    (∫ t in -ρ..ρ, ‖finiteAbelWave s c t‖^2) ≤ ∑ k ∈ s, ‖c k‖^2 := by
  rw [←finiteAbelWave_unit_energy]
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hh
  · exact Filter.Eventually.of_forall fun t => sq_nonneg _
  · apply Continuous.intervalIntegrable
    unfold finiteAbelWave E
    fun_prop


private theorem abelParseval_chord (x : ℝ) : ‖E x - 1‖ ≤ 2*Real.pi*|x| := by
  have hlip : LipschitzWith 1 Real.sin :=
    lipschitzWith_of_nnNorm_deriv_le Real.differentiable_sin (by simpa using! Real.abs_cos_le_one)
  have hsin (u : ℝ) : |Real.sin u| ≤ |u| := by
    simpa [Real.dist_eq] using hlip.dist_le_mul u 0
  let y : ℝ := 2 * Real.pi * x
  change ‖Complex.exp ((y : ℂ) * Complex.I) - 1‖ ≤ _
  rw [mul_comm (y : ℂ), Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |(2 : ℝ)| * |y/2| := mul_le_mul_of_nonneg_left (hsin _) (abs_nonneg _)
    _ = _ := by simp [y, abs_div, abs_mul, abs_of_pos Real.pi_pos]; ring

theorem phase_sum_abel_window_of_prefix (c : ℕ → ℂ) (n : ℕ) {ρ D : ℝ}
    (hρ : 0 ≤ ρ) (hh : ρ ≤ 1/2)
    (hp : ∀ j≤n, ‖∑ k ∈ range (j+1), c k‖ ≤ D) :
    (∫ t in -ρ..ρ, ‖finiteAbelWave (range (n+1)) c t‖^2) ≤
      D^2*ρ*(4 + 8*Real.pi^2*(n:ℝ)*ρ) := by
  let A (k : ℕ) := ∑ j ∈ range (k+1), c j
  let T (t : ℝ) := finiteAbelWave (range n) A t
  have hT : Continuous T := by dsimp [T,finiteAbelWave,E]; fun_prop
  have hc : Continuous (finiteAbelWave (range (n+1)) c) := by unfold finiteAbelWave E; fun_prop
  have hD : 0≤D := (norm_nonneg _).trans (hp n le_rfl)
  have hdecomp (t : ℝ) : finiteAbelWave (range (n+1)) c t =
      E ((n:ℝ)*t)*A n - (E t-1)*T t := by
    let z (k:ℕ) := E ((k:ℝ)*t)
    have hz (k:ℕ) : z (k+1)-z k = (E t-1)*z k := by
      dsimp [z]
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,phase_add]
      ring
    have hw := Finset.sum_range_by_parts z c (n+1)
    simp only [Nat.add_sub_cancel,smul_eq_mul] at hw
    calc
      _ = ∑ k ∈ range (n+1), z k*c k := Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = _ := by
        rw [hw]
        congr 1
        change (∑ k ∈ range n, (z (k+1)-z k)*A k) = (E t-1)*∑ k ∈ range n, A k*z k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hz]; ring
  have hpt (t : ℝ) (ht : t∈Set.Icc (-ρ) ρ) :
      ‖finiteAbelWave (range (n+1)) c t‖^2 ≤ 2*D^2+(2*(2*Real.pi*ρ)^2)*‖T t‖^2 := by
    have h1 := norm_sub_le (E ((n:ℝ)*t)*A n) ((E t-1)*T t)
    rw [norm_mul,norm_mul,show ‖E ((n:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul] at h1
    have h2 : ‖E t-1‖ ≤ 2*Real.pi*ρ := (abelParseval_chord t).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity))
    rw [hdecomp]
    have h3 := (h1.trans (add_le_add (hp n le_rfl) (mul_le_mul_of_nonneg_right h2 (norm_nonneg (T t)))))
    have hx := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith only [hx,sq_nonneg (D-(2*Real.pi*ρ)*‖T t‖)]
  have hE : (∫ t in -ρ..ρ, ‖T t‖^2) ≤ n*D^2 := by
    apply (finiteAbelWave_window_energy (range n) A hρ hh).trans
    calc
      _ ≤ ∑ _k ∈ range n, D^2 := Finset.sum_le_sum fun k hk =>
        pow_le_pow_left₀ (norm_nonneg _) (hp k (Nat.le_of_lt (mem_range.mp hk))) 2
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ ∫ t in -ρ..ρ, 2*D^2+(2*(2*Real.pi*ρ)^2)*‖T t‖^2 := intervalIntegral.integral_mono_on
      (by linarith) ((hc.norm.pow 2).intervalIntegrable _ _)
      (intervalIntegrable_const.add (((hT.norm.pow 2).intervalIntegrable _ _).const_mul _)) hpt
    _ = (ρ- -ρ)*(2*D^2)+(2*(2*Real.pi*ρ)^2)*(∫ t in -ρ..ρ, ‖T t‖^2) := by
      rw [intervalIntegral.integral_add (f:=fun _ : ℝ => 2*D^2) (g:=fun t:ℝ => (2*(2*Real.pi*ρ)^2)*‖T t‖^2) intervalIntegrable_const (((hT.norm.pow 2).intervalIntegrable _ _).const_mul _),
        intervalIntegral.integral_const, smul_eq_mul,intervalIntegral.integral_const_mul]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hE (show 0≤2*(2*Real.pi*ρ)^2 by positivity)]

theorem centeredPrimeArcTransform_abel_window_of_prefix (q : ℕ) [NeZero q] (n : ℕ) {ρ D : ℝ}
    (hρ : 0≤ρ) (hh : ρ≤1/2)
    (hp : ∀ χ, ∀ j≤n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D)
    (χ : DirichletCharacter ℂ q) :
    (∫ t in -ρ..ρ, ‖centeredPrimeArcTransform q n t (∑ k ∈ range (n+1), E ((k:ℝ)*t)) χ‖^2) ≤
      D^2*ρ*(4+8*Real.pi^2*(n:ℝ)*ρ) := by
  simp_rw [centeredPrimeArcTransform_geometric_eq]
  apply phase_sum_abel_window_of_prefix _ n hρ hh
  intro j hj
  have h := centeredPrimeArcTransform_geometric_eq q j 0 χ
  simp [E] at h
  rw [←h]
  exact hp χ j hj

theorem primeArc_tube_abel_parseval_of_prefix (q : ℕ) [NeZero q] (n : ℕ) {ρ D : ℝ}
    (hρ : 0≤ρ) (hh : ρ≤1/2)
    (hp : ∀ χ, ∀ j≤n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    (∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy q a n t
      (∑ k ∈ range (n+1), E ((k:ℝ)*t))‖^2) ≤
        ρ*(q.totient:ℝ)*(D^2*(8+16*Real.pi^2*(n:ℝ)*ρ)+4*(Real.log q)^2) := by
  let M (t:ℝ) := ∑ k ∈ range (n+1), E ((k:ℝ)*t)
  have hc : Continuous M := by dsimp [M,E]; fun_prop
  have h := primeArcModelDiscrepancy_integrated q n M (by linarith : -ρ≤ρ) hc
    (centeredPrimeArcTransform_abel_window_of_prefix q n hρ hh hp)
  exact h.trans (le_of_eq (by ring))

end GoldbachPartial