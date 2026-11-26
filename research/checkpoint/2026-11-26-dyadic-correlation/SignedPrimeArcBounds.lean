import DyadicCorrelationReduction

/-!
Bounds for signed Goldbach integrals on families of rational arcs.
The circle phase is retained in `primeArcSignedChange`. A uniform bound for
centered prime character sums on prefixes controls replacement of the true
wave by its geometric model. All prefix hypotheses are explicit.
-/

namespace GoldbachPartial

open scoped BigOperators
open Finset ExtendedArcCoefficient

open Finset ExtendedArcCoefficient

private theorem abel_phase_chord (x : ℝ) : ‖E x - 1‖ ≤ 2 * Real.pi * |x| := by
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

theorem phase_sum_abel_of_prefix (c : ℕ → ℂ) (n : ℕ) (β D : ℝ)
    (h : ∀ j ≤ n, ‖∑ k ∈ range (j+1), c k‖ ≤ D) :
    ‖∑ k ∈ range (n+1), c k * E ((k : ℝ)*β)‖ ≤ D*(1+2*Real.pi*n*|β|) := by
  let z := fun k : ℕ => E ((k : ℝ)*β)
  have hunit (k : ℕ) : ‖z k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hstep (k : ℕ) : ‖z (k+1) - z k‖ ≤ 2*Real.pi*|β| := by
    have hz : z (k+1) - z k = z k*(E β-1) := by
      dsimp only [z]
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, phase_add]; ring
    rw [hz, norm_mul, hunit, one_mul]
    exact abel_phase_chord β
  have hb := Finset.sum_range_by_parts z c (n+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hb
  have hD : 0 ≤ D := (norm_nonneg _).trans (h n le_rfl)
  calc
    _ = ‖∑ k ∈ range (n+1), z k*c k‖ := by
      apply congrArg norm
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ ≤ ‖z n * ∑ k ∈ range (n+1), c k‖ +
        ‖∑ k ∈ range n, (z (k+1)-z k) * ∑ j ∈ range (k+1), c j‖ := by
      rw [hb]; apply norm_sub_le
    _ ≤ D + ∑ _k ∈ range n, (2*Real.pi*|β|)*D := by
      apply add_le_add
      · rw [norm_mul, hunit, one_mul]
        exact h n le_rfl
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul (hstep k) (h k (Nat.le_of_lt (mem_range.mp hk))) (norm_nonneg _)
          (by positivity)
    _ = _ := by simp [nsmul_eq_mul]; ring

open Classical in
noncomputable def primeArcAbelCoefficient (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (k : ℕ) : ℂ :=
  (weight k : ℂ)*star (χ (k : ZMod q)) - if χ=1 then 1 else 0

theorem centeredPrimeArcTransform_geometric_eq (q : ℕ) [NeZero q] (n : ℕ) (β : ℝ)
    (χ : DirichletCharacter ℂ q) :
    centeredPrimeArcTransform q n β (∑ k ∈ range (n+1), E ((k : ℝ)*β)) χ =
      ∑ k ∈ range (n+1), primeArcAbelCoefficient q χ k * E ((k : ℝ)*β) := by
  classical
  unfold centeredPrimeArcTransform weightedArcCharacterSum primeArcAbelCoefficient
  by_cases hc : χ=1
  · simp only [hc, ite_true, sub_mul, one_mul, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [ite_eq_right hc, sub_zero]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem centeredPrimeArcTransform_abel_of_prefix (q : ℕ) [NeZero q] (n : ℕ) (β D : ℝ)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ j ≤ n, ‖centeredPrimeArcTransform q j 0 ((j : ℂ)+1) χ‖ ≤ D) :
    ‖centeredPrimeArcTransform q n β (∑ k ∈ range (n+1), E ((k : ℝ)*β)) χ‖ ≤
      D*(1+2*Real.pi*n*|β|) := by
  rw [centeredPrimeArcTransform_geometric_eq]
  apply phase_sum_abel_of_prefix
  intro j hj
  have hp := centeredPrimeArcTransform_geometric_eq q j 0 χ
  simp [E] at hp
  rw [← hp]
  exact h j hj

section MultiscaleSignedArcs

open MeasureTheory

private theorem signed_square_young (f m z : ℂ) {s : ℝ} (hs : 0 < s) (hz : ‖z‖ ≤ 1) :
    ‖(f^2-m^2)*z‖ ≤ (1+s)*‖f-m‖^2 + s⁻¹*‖m‖^2 := by
  let d := f-m
  have he : f^2-m^2 = d*(d+2*m) := by dsimp [d]; ring
  have hb : ‖d+2*m‖ ≤ ‖d‖+2*‖m‖ := by simpa [norm_mul] using norm_add_le d (2*m)
  rw [he,norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) hz).trans
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left hb (norm_nonneg d)).trans ?_
  change ‖d‖ * (‖d‖+2*‖m‖) ≤ (1+s)*‖d‖^2+s⁻¹*‖m‖^2
  apply (mul_le_mul_iff_right₀ hs).mp
  conv_rhs => rw [mul_add, ← mul_assoc s s⁻¹, mul_inv_cancel₀ hs.ne', one_mul]
  nlinarith only [sq_nonneg (s*‖d‖-‖m‖)]

/-- The intervals may have different widths. Each row retains its phase. -/
theorem signed_squares_on_arcs {ι : Type*} (I : Finset ι)
    (l r : ι → ℝ) (F M P : ι → ℝ → ℂ) {s : ℝ} (hs : 0 < s)
    (hlr : ∀ i ∈ I, l i ≤ r i)
    (hF : ∀ i ∈ I, Continuous (F i)) (hM : ∀ i ∈ I, Continuous (M i))
    (hP : ∀ i ∈ I, Continuous (P i))
    (habs : ∀ i ∈ I, ∀ t ∈ Set.Icc (l i) (r i), ‖P i t‖ ≤ 1) :
    ‖∑ i ∈ I, ∫ t in l i..r i, ((F i t)^2 - (M i t)^2)*P i t‖ ≤
      (1+s)*(∑ i ∈ I, ∫ t in l i..r i, ‖F i t-M i t‖^2) +
      s⁻¹*(∑ i ∈ I, ∫ t in l i..r i, ‖M i t‖^2) := by
  refine (norm_sum_le ..).trans ?_
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hd : Continuous (fun t => ‖F i t-M i t‖^2) := ((hF i hi).sub (hM i hi)).norm.pow 2
  have hm : Continuous (fun t => ‖M i t‖^2) := (hM i hi).norm.pow 2
  have hp : Continuous (fun t => ((F i t)^2-(M i t)^2)*P i t) :=
    (((hF i hi).pow 2).sub ((hM i hi).pow 2)).mul (hP i hi)
  have hd' : Continuous (fun t => (1+s)*‖F i t-M i t‖^2) := continuous_const.mul hd
  have hm' : Continuous (fun t => s⁻¹*‖M i t‖^2) := continuous_const.mul hm
  have hv : Continuous (fun t => (1+s)*‖F i t-M i t‖^2+s⁻¹*‖M i t‖^2) := hd'.add hm'
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hd'.intervalIntegrable _ _)
      (hm'.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm (hlr i hi)).trans
  apply intervalIntegral.integral_mono_on (hlr i hi) (hp.norm.intervalIntegrable _ _) (hv.intervalIntegrable _ _)
  exact fun t ht => signed_square_young _ _ _ hs (habs i hi t ht)

theorem primeArcModelDiscrepancy_integrated (q : ℕ) [NeZero q] (n : ℕ)
    (M : ℝ → ℂ) {l r B : ℝ} (h : l ≤ r) (hM : Continuous M)
    (hB : ∀ χ, (∫ t in l..r, ‖centeredPrimeArcTransform q n t (M t) χ‖^2) ≤ B) :
    (∫ t in l..r, ∑ a, ‖primeArcModelDiscrepancy q a n t (M t)‖^2) ≤
      2*(q.totient:ℝ)*B + (r-l)*(q.totient:ℝ)*(2*(Real.log q)^2) := by
  classical
  let T := fun χ t => centeredPrimeArcTransform q n t (M t) χ
  let R := fun t => ∑ a, ‖dirichletArcErrorRow q (fun χ => T χ t) a‖^2
  have hT (χ) : Continuous (T χ) := by
    dsimp only [T,centeredPrimeArcTransform,weightedArcCharacterSum,E]
    split_ifs <;> fun_prop
  have hR : Continuous R := by dsimp [R,dirichletArcErrorRow]; fun_prop
  have hL : Continuous (fun t => ∑ a, ‖primeArcModelDiscrepancy q a n t (M t)‖^2) := by
    dsimp only [primeArcModelDiscrepancy,E]; fun_prop
  have hrow := dirichletArcErrorRow_integral_le q T l r B (fun χ => ((hT χ).norm.pow 2).intervalIntegrable _ _) hB
  have h2R : Continuous (fun t => 2*R t) := continuous_const.mul hR
  have hconst : Continuous (fun _ : ℝ => (q.totient:ℝ)*(2*(Real.log q)^2)) := continuous_const
  have htot : Continuous (fun t => 2*R t + (q.totient:ℝ)*(2*(Real.log q)^2)) := h2R.add hconst
  have mono : (∫ t in l..r, ∑ a, ‖primeArcModelDiscrepancy q a n t (M t)‖^2) ≤
      ∫ t in l..r, 2*R t + (q.totient:ℝ)*(2*(Real.log q)^2) := by
    apply intervalIntegral.integral_mono_on h (hL.intervalIntegrable _ _)
      (htot.intervalIntegrable _ _)
    intro t _
    simpa only [R,T,dirichletArcErrorRow_energy] using primeArcModelDiscrepancy_energy_le q n t (M t)
  rw [intervalIntegral.integral_add (h2R.intervalIntegrable _ _)
    intervalIntegrable_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at mono
  change (∫ t in l..r, R t) ≤ (q.totient:ℝ)*B at hrow
  simp only [smul_eq_mul] at mono
  nlinarith only [hrow,mono]

/-- Sum the true-prime square errors over any chosen denominators q = j+1 ≤ R.
The interval radius is uniform, which allows a prefix character estimate to be used directly. -/
theorem primeArc_uniform_tubes_energy (J : Finset ℕ) (n R : ℕ) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB0 : 0 ≤ B) (hJ : ∀ j ∈ J, j < R) (M : ℝ → ℂ) (hM : Continuous M)
    (hB : ∀ j ∈ J, ∀ χ, (∫ t in -ρ..ρ, ‖centeredPrimeArcTransform (j+1) n t (M t) χ‖^2) ≤ B) :
    (∑ j ∈ J, ∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy (j+1) a n t (M t)‖^2) ≤
      (R:ℝ)^2 * (2*B + 4*ρ*(Real.log R)^2) := by
  have hcard : J.card ≤ R := by
    have hj : J ⊆ Finset.range R := fun j hj => Finset.mem_range.mpr (hJ j hj)
    simpa using Finset.card_le_card hj
  have hbr : 0 ≤ 2*B + 4*ρ*(Real.log R)^2 := by positivity
  calc
    _ ≤ ∑ _j ∈ J, (R:ℝ)*(2*B+4*ρ*(Real.log R)^2) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hq : j+1 ≤ R := hJ j hj
      have hqr : ((j+1:ℕ):ℝ) ≤ R := by exact_mod_cast hq
      have ht : (((j+1).totient:ℕ):ℝ) ≤ R := by exact_mod_cast (Nat.totient_le _).trans hq
      have hlog : 0 ≤ Real.log ((j+1:ℕ):ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ j+1 by omega))
      have hl : Real.log ((j+1:ℕ):ℝ) ≤ Real.log R := Real.log_le_log (by positivity) hqr
      have hs := pow_le_pow_left₀ hlog hl 2
      refine (primeArcModelDiscrepancy_integrated (j+1) n M (by linarith : -ρ ≤ ρ) hM (hB j hj)).trans ?_
      calc
        _ = ((j+1).totient:ℝ) * (2*B + 4*ρ*(Real.log ((j+1:ℕ):ℝ))^2) := by ring
        _ ≤ _ := by gcongr
    _ = (J.card:ℝ)*((R:ℝ)*(2*B+4*ρ*(Real.log R)^2)) := by simp
    _ ≤ (R:ℝ)*((R:ℝ)*(2*B+4*ρ*(Real.log R)^2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring


/-- A prefix estimate supplies the full true-prime row energy with its explicit dependence
on the radius. This uses the actual prime logarithms, and includes nonunit prime residues. -/
theorem primeArc_tube_of_prefix (q : ℕ) [NeZero q] (n : ℕ) {ρ D : ℝ}
    (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hp : ∀ χ, ∀ j ≤ n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    (∫ t in -ρ..ρ, ∑ a, ‖primeArcModelDiscrepancy q a n t
      (∑ k ∈ range (n+1), E ((k:ℝ)*t))‖^2) ≤
      4*ρ*(q.totient:ℝ)*((D*(1+2*Real.pi*n*ρ))^2+(Real.log q)^2) := by
  let M := fun t : ℝ => ∑ k ∈ range (n+1), E ((k:ℝ)*t)
  let K := D*(1+2*Real.pi*n*ρ)
  have hc : Continuous M := by dsimp [M,E]; fun_prop
  have lr : -ρ ≤ ρ := by linarith
  have hb (χ : DirichletCharacter ℂ q) :
      (∫ t in -ρ..ρ, ‖centeredPrimeArcTransform q n t (M t) χ‖^2) ≤ (2*ρ)*K^2 := by
    have ht : Continuous (fun t => ‖centeredPrimeArcTransform q n t (M t) χ‖^2) := by
      classical
      dsimp only [centeredPrimeArcTransform,weightedArcCharacterSum,E]
      split_ifs <;> fun_prop
    calc
      _ ≤ ∫ _t in -ρ..ρ, K^2 := by
        apply intervalIntegral.integral_mono_on lr (ht.intervalIntegrable _ _) intervalIntegrable_const
        intro t ht
        apply pow_le_pow_left₀ (norm_nonneg _)
        have h := centeredPrimeArcTransform_abel_of_prefix q n t D χ (hp χ)
        refine h.trans ?_
        have hab : |t| ≤ ρ := abs_le.mpr ht
        dsimp only [K]
        gcongr
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  refine (primeArcModelDiscrepancy_integrated q n M lr hc hb).trans ?_
  dsimp only [K]
  exact le_of_eq (by ring)

/-- Sum across any finite band. Each denominator can use its own radius and prefix bound. -/
theorem primeArc_tubes_of_prefix (J : Finset ℕ) (n : ℕ) (ρ D : ℕ → ℝ)
    (hρ : ∀ j ∈ J, 0 ≤ ρ j) (hD : ∀ j ∈ J, 0 ≤ D j)
    (hp : ∀ j ∈ J, ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ D j) :
    (∑ j ∈ J, ∫ t in -(ρ j)..ρ j, ∑ a, ‖primeArcModelDiscrepancy (j+1) a n t
      (∑ k ∈ range (n+1), E ((k:ℝ)*t))‖^2) ≤
    ∑ j ∈ J, 4*(ρ j)*((j+1).totient:ℝ)*((D j*(1+2*Real.pi*n*ρ j))^2+(Real.log (j+1:ℕ))^2) := by
  exact Finset.sum_le_sum fun j hj => primeArc_tube_of_prefix (j+1) n (hρ j hj) (hD j hj) (hp j hj)


noncomputable def geometricPrimeArcModel (q : ℕ) [NeZero q] (n : ℕ) (t : ℝ) : ℂ :=
  unitGaussCoefficient q 1 * (∑ k ∈ range (n+1), E ((k:ℝ)*t)) / (q.totient:ℂ)

noncomputable def shiftedTruePrimeWave (q : ℕ) (a : (ZMod q)ˣ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (weight k:ℂ)*E ((k:ℝ)*(t+((a:ZMod q).val:ℝ)/q))

/-- Integrated error in the signed coefficient, with its original additive phase. -/
noncomputable def primeArcSignedChange (q : ℕ) [NeZero q] (n : ℕ) (ρ : ℝ) : ℂ :=
  ∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ,
    ((shiftedTruePrimeWave q a n t)^2 - (geometricPrimeArcModel q n t)^2) *
      E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))

theorem primeArc_signed_row_of_prefix (q : ℕ) [NeZero q] (n : ℕ) {ρ D s : ℝ}
    (hρ : 0 ≤ ρ) (hD : 0 ≤ D) (hs : 0 < s)
    (hp : ∀ χ, ∀ j ≤ n, ‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖ ≤ D) :
    ‖primeArcSignedChange q n ρ‖ ≤
      (1+s)*(4*ρ*(q.totient:ℝ)*((D*(1+2*Real.pi*n*ρ))^2+(Real.log q)^2)) +
      s⁻¹*((q.totient:ℝ)*∫ t in -ρ..ρ, ‖geometricPrimeArcModel q n t‖^2) := by
  classical
  let P := fun (a : (ZMod q)ˣ) (t : ℝ) => E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))
  have hf (a : (ZMod q)ˣ) : Continuous (shiftedTruePrimeWave q a n) := by
    unfold shiftedTruePrimeWave E; fun_prop
  have hm : Continuous (geometricPrimeArcModel q n) := by unfold geometricPrimeArcModel E; fun_prop
  have hh := signed_squares_on_arcs (Finset.univ : Finset (ZMod q)ˣ) (fun _ => -ρ) (fun _ => ρ)
    (fun a => shiftedTruePrimeWave q a n) (fun _ => geometricPrimeArcModel q n) P hs
    (fun _ _ => by linarith) (fun a _ => hf a) (fun _ _ => hm)
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
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (primeArc_tube_of_prefix q n hρ hD hp) (show 0 ≤ 1+s by positivity)) le_rfl)

theorem primeArc_signed_band_of_prefix (J : Finset ℕ) (n : ℕ) (ρ D : ℕ → ℝ) {s : ℝ}
    (hρ : ∀ j ∈ J, 0 ≤ ρ j) (hD : ∀ j ∈ J, 0 ≤ D j) (hs : 0 < s)
    (hp : ∀ j ∈ J, ∀ χ, ∀ k ≤ n, ‖centeredPrimeArcTransform (j+1) k 0 ((k:ℂ)+1) χ‖ ≤ D j) :
    ‖∑ j ∈ J, primeArcSignedChange (j+1) n (ρ j)‖ ≤
      (1+s)*(∑ j ∈ J, 4*(ρ j)*((j+1).totient:ℝ)*
        ((D j*(1+2*Real.pi*n*(ρ j)))^2+(Real.log (j+1:ℕ))^2)) +
      s⁻¹*(∑ j ∈ J, ((j+1).totient:ℝ)*∫ t in -(ρ j)..ρ j, ‖geometricPrimeArcModel (j+1) n t‖^2) := by
  apply (norm_sum_le ..).trans
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j hj => primeArc_signed_row_of_prefix (j+1) n (hρ j hj) (hD j hj) hs (hp j hj)

end MultiscaleSignedArcs

end GoldbachPartial
