import VerifiedResidueCorrelationWindow

namespace GoldbachPartial
open Finset Filter

private theorem count_weight_nonneg (k : ℕ) : 0≤weight k := by
  unfold weight
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

theorem residue_window_corr_chebyshev (m : ℕ) :
    corr m ≤ Real.log 4 * m * Real.log m := by
  have htotal : (∑ k ∈ range (m+1), weight k) = Chebyshev.theta m := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_range,sum_filter]
    rfl
  have hcap (k : ℕ) : weight (m-k) ≤ Real.log m := by
    unfold weight
    split_ifs with hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast Nat.sub_le m k)
    · exact Real.log_natCast_nonneg m
  unfold corr
  calc
    _ ≤ ∑ k ∈ range (m+1), weight k*Real.log m :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hcap k) (count_weight_nonneg k)
    _ = Chebyshev.theta m*Real.log m := by rw [←sum_mul,htotal]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _))
      (Real.log_natCast_nonneg _)

theorem residue_window_class_card_bound (N H q r : ℕ) :
    q*((Ioc N (N+H)).filter (fun m => m%q=r)).card ≤ H+q := by
  let S := (Ioc N (N+H)).filter (fun m => m%q=r)
  let f := fun m : ℕ => (m-(N+1))/q
  have hcard : S.card ≤ H/q+1 := by
    rw [←card_range (H/q+1)]
    apply card_le_card_of_injOn f
    · intro m hm
      have hi := mem_Ioc.mp (mem_filter.mp hm).1
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
    · intro a ha b hb he
      have ha' := mem_Ioc.mp (mem_filter.mp ha).1
      have hb' := mem_Ioc.mp (mem_filter.mp hb).1
      have hm : a ≡ b [MOD q] := (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
      have hr : (a-(N+1)) ≡ (b-(N+1)) [MOD q] := by
        apply Nat.ModEq.add_left_cancel' (N+1)
        rwa [Nat.add_sub_of_le (by omega : N+1≤a),Nat.add_sub_of_le (by omega : N+1≤b)]
      have h₁ := Nat.mod_add_div (a-(N+1)) q
      have h₂ := Nat.mod_add_div (b-(N+1)) q
      change (a-(N+1))%q=(b-(N+1))%q at hr
      change (a-(N+1))/q=(b-(N+1))/q at he
      rw [hr,he] at h₁
      omega
  calc
    _ ≤ q*(H/q+1) := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm q (H/q)];exact Nat.add_le_add_right (Nat.div_mul_le_self ..) _

/-- Local density factor of the admissible ordered prime classes. -/
noncomputable def residueWindowDensity (q c : ℕ) : ℝ :=
  (q:ℝ)*(residueWindowAdmissible q c).card/(q.totient:ℝ)^2

noncomputable def residueLinearWitnesses (N H q t : ℕ) : Finset ℕ :=
  ((Ioc N (N+H)).filter (fun m => m%q=(2*t)%q)).filter
    (fun m => Even m ∧ residueWindowDensity q (2*t)*(m:ℝ)/80≤corr m)

theorem admissible_even_residue_primeCorr_count :
    ∀ᶠ X : ℕ in atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      residueWindowDensity q (2*t)*H / (40*Real.log 4*q*Real.log (5*(X:ℝ))) ≤
        (residueLinearWitnesses N H q t).card := by
  classical
  filter_upwards [admissible_residue_primeCorr_mass,eventually_ge_atTop (1:ℕ)] with X hf hX
  intro N H q t h1 h2 h3 h4 hq hqL hqh hqe
  let S := (Ioc N (N+H)).filter (fun m => m%q=(2*t)%q)
  let G := residueLinearWitnesses N H q t
  let V := residueWindowDensity q (2*t)
  let L := Real.log (5*(X:ℝ))
  let B := 5*Real.log 4*(X:ℝ)*L
  let C := V*(X:ℝ)/16
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  have hx0 : (0:ℝ)<X := zero_lt_one.trans_le hx
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hV : 0≤V := by dsimp only [V,residueWindowDensity]; positivity
  have hL : 0<L := Real.log_pos (by linarith only [hx])
  have hlog : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hC : 0≤C := by dsimp only [C]; positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  have hm := hf N H q (2*t) h1 h2 h3 h4 hq hqL
  have hmass : V*(X:ℝ)*H/(4*q) ≤ ∑ m ∈ S,corr m := by
    apply le_trans (le_of_eq ?_) hm
    dsimp only [V,residueWindowDensity]
    field_simp
  have hcard : (q:ℝ)*S.card≤2*H := by
    exact_mod_cast (residue_window_class_card_bound N H q _).trans (by omega : H+q≤2*H)
  have hcap (m : ℕ) (hm : m ∈ S) : corr m ≤ B := by
    have hmi := mem_Ioc.mp (mem_filter.mp hm).1
    have hm5 : (m:ℝ)≤5*X := by exact_mod_cast hmi.2.trans h2
    have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    calc
      _ ≤ Real.log 4*m*Real.log m := residue_window_corr_chebyshev m
      _ ≤ Real.log 4*(5*(X:ℝ))*L := by gcongr; exact Real.log_le_log hm0 hm5
      _ = _ := by dsimp only [B];ring
  have hpt (m : ℕ) (hm : m∈S) : corr m ≤ (if m∈G then B else 0)+C := by
    by_cases hgood : m∈G
    · rw [ite_eq_left hgood]
      exact (hcap _ hm).trans (le_add_of_nonneg_right hC)
    · rw [ite_eq_right hgood,zero_add]
      have hmi := mem_Ioc.mp (mem_filter.mp hm).1
      have hm5 : (m:ℝ)≤5*X := by exact_mod_cast hmi.2.trans h2
      have he : Even m := by
        apply Nat.even_iff.mpr
        have ht := congrArg (fun k : ℕ => k%2) (mem_filter.mp hm).2
        change (m%q)%2=((2*t)%q)%2 at ht
        rw [Nat.mod_mod_of_dvd _ hqe,Nat.mod_mod_of_dvd _ hqe] at ht
        simpa using ht
      have hbad : ¬ V*(m:ℝ)/80 ≤ corr m := fun h => hgood (mem_filter.mpr ⟨hm,he,h⟩)
      exact (le_of_lt (lt_of_not_ge hbad)).trans (by dsimp only [C]; nlinarith only [mul_le_mul_of_nonneg_left hm5 hV])
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib,←sum_filter] at hsum
  have hsG : S.filter (fun m => m∈G) = G := by
    ext m
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun h => (mem_filter.mp h).1)
  rw [hsG,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul] at hsum
  have hbadmass : (S.card:ℝ)*C ≤ V*(X:ℝ)*H/(8*q) := by
    apply (le_div_iff₀ (show (0:ℝ)<8*q by positivity)).mpr
    dsimp only [C]
    have h := mul_le_mul_of_nonneg_left hcard (show 0≤V*(X:ℝ)/2 by positivity)
    linear_combination h
  have hGmass : V*(X:ℝ)*H/(8*q) ≤ (G.card:ℝ)*B := by
    linarith only [hmass,hsum,hbadmass,
      show 2*(V*(X:ℝ)*H/(8*q))=V*(X:ℝ)*H/(4*q) by ring]
  change V*H/(40*Real.log 4*q*L)≤(G.card:ℝ)
  apply (div_le_iff₀ (by positivity)).mpr
  have hv := (div_le_iff₀ (show (0:ℝ)<8*q by positivity)).mp hGmass
  apply (mul_le_mul_iff_right₀ hx0).mp
  dsimp only [B] at hv
  linear_combination hv

noncomputable def residueAbsoluteWitnesses (N H q t : ℕ) : Finset ℕ :=
  ((Ioc N (N+H)).filter (fun m => m%q=(2*t)%q)).filter
    (fun m => Even m ∧ (m:ℝ)/80≤corr m)

/-- Transfer to an absolute linear floor from the exact local combinatorial
inequality, with no additional analytic assumption. -/
theorem even_residue_absolute_count_of_local_factor :
    ∀ᶠ X : ℕ in atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      q.totient^2 ≤ q*(residueWindowAdmissible q (2*t)).card →
      (H:ℝ)/(40*Real.log 4*q*Real.log (5*(X:ℝ))) ≤
        (residueAbsoluteWitnesses N H q t).card := by
  filter_upwards [admissible_even_residue_primeCorr_count,eventually_ge_atTop (1:ℕ)] with X h hX
  intro N H q t h1 h2 h3 h4 hq hqL hqh hqe hf
  let V := residueWindowDensity q (2*t)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hV : 1 ≤ V := by
    dsimp only [V,residueWindowDensity]
    apply (one_le_div (pow_pos hφ 2)).mpr
    exact_mod_cast hf
  have hsub : residueLinearWitnesses N H q t ⊆ residueAbsoluteWitnesses N H q t := by
    intro m hm
    obtain ⟨hS,he,hc⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hS,he,le_trans ?_ hc⟩
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact le_mul_of_one_le_left (by positivity) hV
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  have hlog : 0<Real.log (5*(X:ℝ)) := Real.log_pos (by linarith)
  have h4pos : 0<Real.log 4 := Real.log_pos (by norm_num)
  calc
    _ ≤ V*H/(40*Real.log 4*q*Real.log (5*(X:ℝ))) := by
      apply div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hV) (by positivity)
    _ ≤ _ := (h N H q t h1 h2 h3 h4 hq hqL hqh hqe).trans (by exact_mod_cast card_le_card hsub)

end GoldbachPartial