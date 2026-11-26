import PinnedLargeMobiusBudget
import PinnedMajorGeometry
import GRHTruePrimePrefix
import Mathlib.NumberTheory.Chebyshev

/- The elementary rational-arc and summation bounds in this module are taken from
DFQDZZ/goldbach-proofs at e4ab24712555ae8c2c926adf19d368a9fb392c35,
L_goldbach_arc_major_floor.lean (Apache-2.0); the prime-character input below is GRH. -/
namespace Pinned316.GoldbachMajorArc.GRHError
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section
private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight (n : ℕ) :
    ∑ k ∈ range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
  rfl

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

/-- On each published arc the amplification factor for the center error is at most
1 + 2πQ/q, with the declared width Q/(qn). -/
theorem rational_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (cutoff n : ℝ) / ((q : ℝ) * n)) :
    ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ (cutoff n : ℝ) / q := by
    apply (le_div_iff₀ hq').mpr
    calc
      _ = |β| * ((q : ℝ) * n) := by ring
      _ ≤ _ := (le_div_iff₀ (mul_pos hq' hn')).mp hβ
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) :=
    (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) _ _)
  refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply add_le_add_right
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The model and the actual complex integrand have the same unit twist.
This bounds their pointwise difference everywhere on each declared arc. -/
theorem squared_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (cutoff n : ℝ) / ((q : ℝ) * n)) :
    let r : ℝ := (a : ℝ) / q
    let A := unitMean q a
    ‖integrand n (r + β) - (A * kernel n β) ^ 2 * phase (-(n : ℝ) * (r + β))‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) *
        (Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ)) := by
  intro r A
  have hsum : ‖primeSum n (r + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase]
  have hplus : ‖primeSum n (r + β) + A * kernel n β‖ ≤ Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ) := by
    refine (norm_add_le _ _).trans (add_le_add hsum ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  unfold integrand
  rw [← sub_mul, norm_mul, norm_phase, mul_one,
    show (primeSum n (r + β)) ^ 2 - (A * kernel n β) ^ 2 =
      (primeSum n (r + β) - A * kernel n β) * (primeSum n (r + β) + A * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul (rational_arc_error (a := a) hn hq hβ) hplus (norm_nonneg _)
    ((norm_nonneg _).trans (rational_arc_error (a := a) hn hq hβ))
private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

theorem integral_error_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ cutoff n)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width n q)..(width n q), modelError n q a β) ≤
      2 * (cutoff n : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width n q := by unfold width; positivity
  have hlength : width n q ≤ (cutoff n : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width n q)) (width n q)) :
      modelError n q a β ≤ B := by
    have hp' := squared_arc_error (a := a) hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * cutoff n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a) := by
    unfold modelError integrand primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width n q)..(width n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((cutoff n : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

private theorem totalArcError_nonneg (n : ℕ) : 0 ≤ totalArcError n := by
  refine sum_nonneg fun q _ => sum_nonneg fun a _ => ?_
  have hw : 0 ≤ width n q := by unfold width; positivity
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _
open GoldbachPartial
private theorem pinned_char_delta {q:ℕ} [NeZero q] (k b:ℕ) (hb:b<q) (hcop:b.Coprime q) :
    (∑χ:DirichletCharacter ℂ q, χ (b:ZMod q)*star (χ (k:ZMod q))) =
      if k%q=b then (q.totient:ℂ) else 0 := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩,rootsOfUnity.isCyclic ..⟩
  have heq : ((k:ZMod q)=(b:ZMod q)) ↔ k%q=b := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hb]
  by_cases h:IsUnit (k:ZMod q)
  · have hs (χ:DirichletCharacter ℂ q) : star (χ (k:ZMod q))=χ ((k:ZMod q)⁻¹) := by
      obtain ⟨u,hu⟩ := h
      rw [←hu,MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]
    have hcomm (χ:DirichletCharacter ℂ q) : χ (b:ZMod q)*χ ((k:ZMod q)⁻¹)=χ ((k:ZMod q)⁻¹)*χ (b:ZMod q) := mul_comm _ _
    simp_rw [hs,hcomm]
    simp only [DirichletCharacter.sum_char_inv_mul_char_eq ℂ h,heq]
  · have hn : k%q≠b := fun hh => h ((heq.mpr hh) ▸ (ZMod.isUnit_iff_coprime b q).mpr hcop)
    simp [hn,fun χ:DirichletCharacter ℂ q => χ.map_nonunit h]

theorem unitClass_error_of_true_character {q:ℕ} [NeZero q] (j b:ℕ)
    (hb:b<q) (hcop:b.Coprime q) {D:ℝ}
    (h : ∀χ,‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖≤D) :
    |classError (j+1) q b| ≤ D := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩,rootsOfUnity.isCyclic ..⟩
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hu : IsUnit (b:ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr hcop
  have hp : (∑χ:DirichletCharacter ℂ q,χ (b:ZMod q)*centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ)=
      (q.totient:ℂ)*(classMass (j+1) q b:ℂ)-((j:ℂ)+1) := by
    unfold centeredPrimeArcTransform weightedArcCharacterSum
    simp only [mul_zero,ExtendedArcCoefficient.E,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,mul_sub,sum_sub_distrib]
    congr 1
    · simp_rw [mul_sum]
      rw [sum_comm]
      have hr (k:ℕ) : (∑χ:DirichletCharacter ℂ q,χ (b:ZMod q)*((weight k:ℂ)*star (χ (k:ZMod q))))=
          (weight k:ℂ)*(if k%q=b then (q.totient:ℂ) else 0) := by
        rw [←pinned_char_delta k b hb hcop,mul_sum]
        exact sum_congr rfl fun χ _ => by ring
      simp_rw [hr]
      unfold classMass
      rw [Complex.ofReal_sum,sum_filter,mul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp [primeWeight,weight,mul_comm]
    · rw [sum_eq_single (1:DirichletCharacter ℂ q)]
      · simp [MulChar.one_apply hu]
      · intro χ _ hχ
        simp [hχ]
      · simp
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hv : (((q.totient:ℝ)*classError (j+1) q b:ℝ):ℂ)=(q.totient:ℂ)*(classMass (j+1) q b:ℂ)-((j:ℂ)+1) := by
    simp only [classError,ite_eq_left hcop,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_one]
    push_cast
    field_simp [show (q.totient:ℂ)≠0 by exact_mod_cast hφ.ne']
  have hbound : ‖(q.totient:ℂ)*(classMass (j+1) q b:ℂ)-((j:ℂ)+1)‖≤(q.totient:ℝ)*D := by
    rw [←hp]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑_χ:DirichletCharacter ℂ q,D := by
        apply sum_le_sum
        intro χ _
        rw [norm_mul]
        simpa using mul_le_mul (χ.norm_le_one _) (h χ) (norm_nonneg _) zero_le_one
      _ = _ := by simp [hcard,nsmul_eq_mul]
  rw [←hv,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hφ] at hbound
  exact (mul_le_mul_iff_right₀ hφ).mp hbound
private theorem nonunitClass_error (q j b:ℕ) (hq:0<q) (hc:¬b.Coprime q) :
    |classError (j+1) q b|≤Real.log q := by
  classical
  let s := (range (j+1)).filter (fun k => k%q=b)
  have hs : s.filter Nat.Prime ⊆ q.primeFactors := by
    intro p hp
    obtain ⟨hpr,hp'⟩ := mem_filter.mp hp
    have he := (mem_filter.mp hpr).2
    have hnc : ¬p.Coprime q := by
      intro hh
      apply hc
      rw [←he,Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm]
      exact hh.gcd_eq_one
    exact Nat.mem_primeFactors.mpr ⟨hp',hp'.dvd_iff_not_coprime.mpr hnc,hq.ne'⟩
  have hn : 0≤classMass (j+1) q b := sum_nonneg fun k _ => primeWeight_nonneg k
  rw [classError,ite_eq_right hc,sub_zero,abs_of_nonneg hn]
  calc
    _ = ∑p∈s.filter Nat.Prime,Real.log p := by simp only [classMass,s,sum_filter,primeWeight]
    _ ≤ ∑p∈q.primeFactors,Real.log p := sum_le_sum_of_subset_of_nonneg hs fun p _ _ => Real.log_natCast_nonneg p
    _ ≤ _ := by
      have hprod : 0<∏p∈q.primeFactors,p := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      have hlog := Real.log_le_log (by exact_mod_cast hprod : (0:ℝ)<((∏p∈q.primeFactors,p:ℕ):ℝ))
        (by exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q) : ((∏p∈q.primeFactors,p:ℕ):ℝ)≤q)
      rw [Nat.cast_prod,Real.log_prod _] at hlog
      · exact hlog
      · intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem prefixError_of_trueCharacter (q n a:ℕ) [NeZero q] {D:ℝ} (hD:0≤D)
    (hp:∀χ,∀j≤n,‖centeredPrimeArcTransform q j 0 ((j:ℂ)+1) χ‖≤D) :
    prefixError n ((a:ℝ)/q) (unitMean q a) ≤ q*(D+Real.log q) := by
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  apply (center_prefix_bound (NeZero.pos q) a m).trans
  calc
    _ ≤ ∑ _b∈range q,(D+Real.log q) := by
      apply sum_le_sum
      intro b hb
      cases m with
      | zero => simpa [classError,classMass] using add_nonneg hD (Real.log_natCast_nonneg q)
      | succ j =>
        have hj : j≤n := by have := mem_range.mp hm; omega
        by_cases hc:b.Coprime q
        · exact (unitClass_error_of_true_character j b (mem_range.mp hb) hc (fun χ=>hp χ j hj)).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg q))
        · exact (nonunitClass_error q j b (NeZero.pos q) hc).trans (le_add_of_nonneg_left hD)
    _ = _ := by simp [nsmul_eq_mul,mul_add]
/-- GRH controls all numerators of the pinned model, including unreduced fractions. -/

theorem totalArcError_bound_of_grh (hψ:grhAllUniform) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ n:ℕ in atTop, totalArcError n ≤ A*(Real.log n)^10*Real.sqrt n := by
  obtain ⟨C₀,hC₀,hpre⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  let C : ℝ := 4*((1+2*Real.pi)*(Real.log 4+2))
  let A : ℝ := C*16^4*(9*C₀+1)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨A,by dsimp only [A]; positivity,?_⟩
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hl.eventually_ge_atTop 1,GoldbachPartial.pinnedCutoff_eventually_separated] with n hn hL hsep
  change (1:ℝ)≤Real.log (n:ℝ) at hL
  have hnr : (2:ℝ)≤n := by exact_mod_cast hn
  have hnpos : (0:ℝ)<n := by linarith
  have hscale : Real.log (2*(n:ℝ)^2) ≤ 3*Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hnr]
  have hsc0 : 0≤Real.log (2*(n:ℝ)^2) := Real.log_nonneg (by nlinarith [sq_nonneg ((n:ℝ)-2)])
  have hcutn : cutoff n≤n := (Nat.le_self_pow (by decide:2≠0) _).trans (by omega : (cutoff n)^2≤n)
  let E : ℝ := (9*C₀+1)*Real.sqrt n*(Real.log n)^2
  have hE : 0≤E := by dsimp only [E]; positivity
  have hp (q a:ℕ) (hq:0<q) (hQ:q≤cutoff n) :
      prefixError n ((a:ℝ)/q) (unitMean q a)≤q*E := by
    let _ : NeZero q := ⟨hq.ne'⟩
    have hqn := hQ.trans hcutn
    have hD := hpre n hn q hqn
    apply (prefixError_of_trueCharacter q n a (by positivity) hD).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : Real.log q ≤ Real.log n := Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqn)
    have hs1 : 1≤Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
    have h2 : Real.log n ≤ Real.sqrt n*(Real.log n)^2 := calc
      _ ≤ (Real.log n)^2 := by nlinarith only [mul_nonneg (by linarith : 0≤Real.log n-1) (show 0≤Real.log n by linarith)]
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hs1
    calc
      _ ≤ C₀*Real.sqrt n*(3*Real.log n)^2+Real.sqrt n*(Real.log n)^2 :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsc0 hscale 2) (by positivity)) (h1.trans h2)
      _ = _ := by dsimp [E]; ring
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff n := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)).ne')
  have hQ' : (1:ℝ)≤cutoff n := by exact_mod_cast hQ1
  let B : ℝ := 2 * (cutoff n : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError n ≤ C * (cutoff n : ℝ) ^ 4 * E := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 (cutoff n), (((cutoff n : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C]; ring
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (cutoff n)) (cutoff_le_log_sq hn) 4
  apply htot.trans
  calc
    _ ≤ C*(16*(Real.log n)^2)^4*E := by gcongr
    _ = _ := by dsimp only [A,E]; ring

theorem totalArcError_sublinear_of_grh (hψ:grhAllUniform) :
    Tendsto (fun n:ℕ => totalArcError n/n) atTop (𝓝 0) := by
  obtain ⟨A,_hA,he⟩ := totalArcError_bound_of_grh hψ
  have ht : Tendsto (fun n:ℕ=>(Real.log n)^10/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (10:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hlim := ht.const_mul A
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (totalArcError_nonneg n) (Nat.cast_nonneg n)) _ hlim
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with n hnum hn
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  have hspos : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hdiv := div_le_div_of_nonneg_right hnum hnpos.le
  apply hdiv.trans_eq
  field_simp
  rw [Real.sq_sqrt hnpos.le]

theorem actual_major_floor_of_grh (hψ:grhAllUniform) {c:ℝ} (hc:c<9/8) :
    ∀ᶠ n:ℕ in atTop, Even n → c*(n:ℝ) ≤ (majorContribution n).re :=
  actual_floor_of_error_sublinear (totalArcError_sublinear_of_grh hψ) hc

end
end Pinned316.GoldbachMajorArc.GRHError

namespace GoldbachPartial
open MeasureTheory Filter Pinned316.GoldbachMajorArc
open scoped Topology
theorem pinned_dyadic_floor_of_largeMobius_budget_of_grh (D:ℕ→ℕ)
    (hψ:grhAllUniform)
    (hclose : ∀ᶠ n:ℕ in atTop,
      ‖(∫t in highNaturalPrimeTubes n,primeSquareKernel n t)-
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t)‖≤(n:ℝ)/32)
    (htail : ∀ᶠ n:ℕ in atTop,Even n→ -(n:ℝ) ≤
      primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n+
        (∫t in highNaturalPrimeTubes n,largeMobiusKernel n (D n) t).re) :
    ∃ N : ℕ, ∀ X n:ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      (1/16:ℝ)*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) :=
  pinned_dyadic_floor_of_largeMobius_budget D major_error (GRHError.totalArcError_sublinear_of_grh hψ) hclose htail
end GoldbachPartial