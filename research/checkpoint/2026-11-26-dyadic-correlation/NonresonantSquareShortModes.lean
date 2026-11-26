import TrueMixedFrequencies
import DivisorSquareMean
import FarShortPairModes
import NaturalTubeShortModes

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private def squareModeBox (n:ℕ) := Icc 1 n ×ˢ Icc 1 n

noncomputable def nonresonantSquareModeCoefficient (n D q:ℕ) (h:ℤ) : ℝ :=
  ∑u∈(squareModeBox n).filter (fun u=>farPairFrequency n u.1 u.2=h),
    nonresonantCoefficient n D q u.1*nonresonantCoefficient n D q u.2

theorem nonresonantSquareModeCoefficient_le (n D q:ℕ) (h:ℤ) :
    |nonresonantSquareModeCoefficient n D q h|≤ (n:ℝ)*(1+Real.log n)^3*(Real.log n)^2 := by
  let I := (squareModeBox n).filter (fun u=>farPairFrequency n u.1 u.2=h)
  let A (k:ℕ):ℝ := k.divisors.card
  have hm {u:ℕ×ℕ} (hu:u∈I) : u.1∈Icc 1 n ∧ u.2∈Icc 1 n := mem_product.mp (mem_filter.mp hu).1
  have h₁ : (↑I:Set (ℕ×ℕ)).InjOn Prod.fst := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have h1 := (mem_filter.mp hab).2
    have h2 := (mem_filter.mp hcd).2
    change (a:ℤ)+b-n=h at h1
    change (c:ℤ)+d-n=h at h2
    change a=c at he
    exact Prod.ext he (by omega)
  have h₂ : (↑I:Set (ℕ×ℕ)).InjOn Prod.snd := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have h1 := (mem_filter.mp hab).2
    have h2 := (mem_filter.mp hcd).2
    change (a:ℤ)+b-n=h at h1
    change (c:ℤ)+d-n=h at h2
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
  have hconv : (∑u∈I,A u.1*A u.2) ≤ (n:ℝ)*(1+Real.log n)^3 := by
    have hl := hproj _ h₁ (fun u hu => (hm hu).1)
    have hr := hproj _ h₂ (fun u hu => (hm hu).2)
    have hh : (2:ℝ)*(∑u∈I,A u.1*A u.2) ≤
          (∑u∈I,(A u.1)^2)+(∑u∈I,(A u.2)^2) := by
      rw [mul_sum,←sum_add_distrib]
      exact sum_le_sum fun u _ => by nlinarith [sq_nonneg (A u.1-A u.2)]
    linarith only [hl,hr,hh]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑u∈I,(A u.1*A u.2)*(Real.log n)^2 := by
      apply sum_le_sum
      intro u hu
      rw [abs_mul]
      refine (mul_le_mul (nonresonantCoefficient_bound (mem_Icc.mp (hm hu).1).1 n D q)
        (nonresonantCoefficient_bound (mem_Icc.mp (hm hu).2).1 n D q) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n))).trans_eq ?_
      dsimp only [A];ring
    _ ≤ _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hconv (sq_nonneg _)

noncomputable def nonresonantSquareModeMass (n D R Q:ℕ) (S:Finset ℤ) : ℂ :=
  ∑j∈Ico R Q, ∑h∈S,(nonresonantSquareModeCoefficient n D (j+1) h:ℂ)*
    (dyadicRamanujanDivisor h.natAbs (j+1):ℂ)*
    (∫β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),E ((h:ℝ)*β))

theorem nonresonantSquareKernel_expansion (n D q:ℕ) (t:ℝ) :
    (nonresonantMobiusWave n D q t)^2*E (-(n:ℝ)*t)=
      ∑h∈Icc (-(n:ℤ)) (n:ℤ),(nonresonantSquareModeCoefficient n D q h:ℂ)*E ((h:ℝ)*t) := by
  let B := squareModeBox n
  let f (u:ℕ×ℕ) := farPairFrequency n u.1 u.2
  let w (u:ℕ×ℕ):ℝ := nonresonantCoefficient n D q u.1*nonresonantCoefficient n D q u.2
  have hmap (u:ℕ×ℕ) (hu:u∈B) : f u∈Icc (-(n:ℤ)) (n:ℤ) := by
    obtain ⟨ha,hb⟩ := mem_product.mp hu
    obtain ⟨_,hau⟩ := mem_Icc.mp ha
    obtain ⟨_,hbu⟩ := mem_Icc.mp hb
    apply mem_Icc.mpr
    dsimp only [f,farPairFrequency];omega
  have heq : (nonresonantMobiusWave n D q t)^2*E (-(n:ℝ)*t) =
      ∑u∈B,(w u:ℂ)*E ((f u:ℝ)*t) := by
    rw [nonresonantWave_at_frequencies,sq,sum_mul_sum,sum_mul]
    change _=∑k∈Icc 1 n ×ˢ Icc 1 n,_
    rw [sum_product]
    apply sum_congr rfl
    intro k _
    rw [sum_mul]
    apply sum_congr rfl
    intro l _
    dsimp only [w,f,farPairFrequency]
    push_cast
    rw [show ((k:ℝ)+l-n)*t=k*t+l*t+(-(n:ℝ)*t) by ring,phase_add,phase_add]
    ring
  rw [heq,←sum_fiberwise_of_maps_to hmap (fun u=>(w u:ℂ)*E ((f u:ℝ)*t))]
  apply sum_congr rfl
  intro h _
  unfold nonresonantSquareModeCoefficient
  rw [Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro u hu
  rw [(mem_filter.mp hu).2]


private theorem squareMode_center_sum {q:ℕ} [NeZero q] (f:ℕ→ℂ) :
    (∑a:(ZMod q)ˣ,f (a:ZMod q).val) = ∑a∈(range q).filter (fun a=>a.Coprime q),f a := by
  apply sum_bij (fun (a:(ZMod q)ˣ) _ => (a:ZMod q).val)
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ he
    exact Units.ext (ZMod.val_injective q he)
  · intro a ha
    obtain ⟨har,hac⟩ := mem_filter.mp ha
    exact ⟨ZMod.unitOfCoprime a hac,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp har)⟩
  · intro _ _;rfl

theorem nonresonantSquareMass_all_modes (n D R Q:ℕ) :
    nonresonantSquareMass n D R Q =
      nonresonantSquareModeMass n D R Q (Icc (-(n:ℤ)) (n:ℤ)) := by
  unfold nonresonantSquareMass nonresonantSquareModeMass
  apply sum_congr rfl
  intro j _
  let q := j+1
  let ρ := naturalTubeRadius (3*Q) q
  let I := Icc (-(n:ℤ)) (n:ℤ)
  let W (h:ℤ) : ℂ := nonresonantSquareModeCoefficient n D q h
  let Z (a:ℕ) (h:ℤ) (β:ℝ) := E ((h:ℝ)*(β+(a:ℝ)/q))
  change (∑a∈(range q).filter (fun a=>a.Coprime q), ∫ β in -ρ..ρ,
    (nonresonantMobiusWave n D q (β+(a:ℝ)/q))^2*E (-(n:ℝ)*(β+(a:ℝ)/q)))=_
  simp_rw [nonresonantSquareKernel_expansion]
  change (∑a∈(range q).filter (fun a=>a.Coprime q),∫β in -ρ..ρ,∑h∈I,W h*Z a h β)=_
  have hi (a:ℕ)(h:ℤ) : IntervalIntegrable (fun β=>W h*Z a h β) volume (-ρ) ρ := by
    apply Continuous.intervalIntegrable; unfold Z E; fun_prop
  simp_rw [intervalIntegral.integral_finsetSum (fun h _ => hi _ h),intervalIntegral.integral_const_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  rw [←mul_sum,←squareMode_center_sum]
  have hs := signedModeRow_exact q h ρ
  simpa only [mul_assoc] using congrArg (fun z=> W h*z) hs

theorem nonresonantSquareMass_delete_short (n D R Q H:ℕ) (hH:H≤n) :
    nonresonantSquareMass n D R Q -
      nonresonantSquareModeMass n D R Q (Icc (-(n:ℤ)) (n:ℤ) \ shortNonzeroModes H) =
      nonresonantSquareModeMass n D R Q (shortNonzeroModes H) := by
  have hsub : shortNonzeroModes H ⊆ Icc (-(n:ℤ)) (n:ℤ) := by
    intro h hh
    obtain ⟨hl,hu⟩ := mem_Icc.mp (mem_erase.mp hh).2
    apply mem_Icc.mpr;omega
  rw [nonresonantSquareMass_all_modes,sub_eq_iff_eq_add]
  unfold nonresonantSquareModeMass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  exact (sum_sdiff hsub).symm.trans (add_comm _ _)

theorem nonresonantSquare_short_bound (n D R Q H:ℕ) :
    ‖nonresonantSquareModeMass n D R Q (shortNonzeroModes H)‖ ≤
      ((n:ℝ)*(1+Real.log n)^3*(Real.log n)^2)*
      ((4/((3*Q:ℕ):ℝ))*(H:ℝ)*(1+Real.log Q)^2) := by
  let A := (n:ℝ)*(1+Real.log n)^3*(Real.log n)^2
  have hA : 0≤A := by dsimp [A]; positivity
  have hrow (j:ℕ) :
      (∑h∈shortNonzeroModes H,|(dyadicRamanujanDivisor h.natAbs (j+1):ℝ)|)
      ≤ 2*((H:ℝ)*(j+1).divisors.card) := by
    rw [sum_shortNonzeroModes]
    simp only [Int.natAbs_neg,Int.natAbs_natCast,←two_mul,←mul_sum]
    exact mul_le_mul_of_nonneg_left (ramanujan_frequency_mass (j+1) H (Nat.succ_pos j)) (by norm_num)
  have ht : (∑j∈Ico R Q,((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) ≤ (1+Real.log Q)^2 :=
    (sum_le_sum_of_subset_of_nonneg (fun j hj=>mem_range.mpr (mem_Ico.mp hj).2)
        (fun _ _ _=>by positivity)).trans (signedFiber_divisor_harmonic Q)
  unfold nonresonantSquareModeMass
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑j∈Ico R Q,(A*(4/((3*Q:ℕ):ℝ))*(H:ℝ))*
        (((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) := by
      apply sum_le_sum
      intro j _
      let r := naturalTubeRadius (3*Q) (j+1)
      have hr : 0≤r := by dsimp [r,naturalTubeRadius];positivity
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑h∈shortNonzeroModes H,(A*(2*r))*|(dyadicRamanujanDivisor h.natAbs (j+1):ℝ)| := by
          apply sum_le_sum
          intro h _
          have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
            (f:=fun t:ℝ=>E ((h:ℝ)*t)) (C:=1) (fun _ _=>(Complex.norm_exp_ofReal_mul_I _).le)
          rw [abs_of_nonneg (by linarith : 0≤r- -r),one_mul] at hi
          rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_intCast]
          apply (mul_le_mul (mul_le_mul_of_nonneg_right (nonresonantSquareModeCoefficient_le n D (j+1) h)
              (abs_nonneg _)) hi (norm_nonneg _) (mul_nonneg hA (abs_nonneg _))).trans_eq
          ring
        _ ≤ _ := by
          rw [←mul_sum]
          apply (mul_le_mul_of_nonneg_left (hrow j) (mul_nonneg hA (by positivity))).trans_eq
          dsimp only [r,naturalTubeRadius]; simp only [div_eq_mul_inv,mul_inv_rev];ring
    _ ≤ _ := by
      rw [←mul_sum]
      exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by ring)

noncomputable def nonresonantShortCutoff (n:ℕ) : ℕ :=
  ⌊Real.sqrt n/(terminalPrimeArcLog n)^8⌋₊

noncomputable def nonresonantSquareRetained (n D R:ℕ) : ℂ :=
  nonresonantSquareModeMass n D R (naturalTubeScale n)
    (Icc (-(n:ℤ)) (n:ℤ) \ shortNonzeroModes (nonresonantShortCutoff n))

theorem nonresonantSquare_terminal_short_error (n D R:ℕ) (hn:1≤n) :
    ‖nonresonantSquareMass n D R (naturalTubeScale n) - nonresonantSquareRetained n D R‖ ≤
      (8/3)*(n:ℝ)/terminalPrimeArcLog n := by
  let L := terminalPrimeArcLog n
  let Q := naturalTubeScale n
  let H := nonresonantShortCutoff n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hs1 : 1≤Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hsn : Real.sqrt n≤(n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  have hq1 : 1≤Q := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by simpa using hs1)
  have hqr1 : (1:ℝ)≤Q := by exact_mod_cast hq1
  have hqr : (0:ℝ)<Q := by linarith
  have hqu : (Q:ℝ)≤Real.sqrt n := Nat.floor_le (Real.sqrt_nonneg _)
  have hqs : Real.sqrt n≤2*(Q:ℝ) := by
    have hh : Real.sqrt n<(Q:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have hH : (H:ℝ)≤Real.sqrt n/L^8 := Nat.floor_le (by positivity)
  have hHn : H≤n := by
    exact_mod_cast hH.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)).trans hsn)
  have hlog : Real.log n≤L := by dsimp only [L,terminalPrimeArcLog];linarith
  have hlogQ : 1+Real.log Q≤L := add_le_add_right (Real.log_le_log hqr (hqu.trans hsn)) 1
  change ‖nonresonantSquareMass n D R Q - nonresonantSquareModeMass n D R Q
    (Icc (-(n:ℤ)) (n:ℤ) \ shortNonzeroModes H)‖ ≤ _
  rw [nonresonantSquareMass_delete_short n D R Q H hHn]
  have hb := nonresonantSquare_short_bound n D R Q H
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hb
  apply hb.trans
  calc
    _ ≤ ((n:ℝ)*L^3*L^2)*((4/(3*(Q:ℝ)))*(2*(Q:ℝ)/L^8)*L^2) := by
      have hHQ := hH.trans (div_le_div_of_nonneg_right hqs (pow_nonneg hL.le 8))
      have hlog0 := Real.log_natCast_nonneg n
      have hlogQ0 := Real.log_natCast_nonneg Q
      gcongr
    _ = _ := by change _=(8/3)*(n:ℝ)/L;field_simp;ring

theorem nonresonantSquare_terminal_short_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀D R:ℕ,
      ‖nonresonantSquareMass n D R (naturalTubeScale n) - nonresonantSquareRetained n D R‖ ≤
        ε*(n:ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually_ge_atTop ((8/3)/ε)] with n hn hb
  intro D R
  apply (nonresonantSquare_terminal_short_error n D R hn).trans
  change (8/3)*(n:ℝ)/(1+Real.log n) ≤ _
  have hl := Real.log_natCast_nonneg n
  have hh : (8/3:ℝ)≤ ε*(1+Real.log n) := by
    change (8/3)/ε ≤ Real.log (n:ℝ) at hb
    have ht := (div_le_iff₀ hε).mp hb
    linarith
  apply (div_le_iff₀ (by linarith)).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) n)
end GoldbachPartial
