import VerifiedTrueMinorEnergy
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient

private noncomputable def clipW (N k : ℕ) : ℝ := if k≤N then weight k else 0
private noncomputable def deltaW (N k : ℕ) : ℝ :=
  clipW N k-(if 2≤k then clipW N (k-2) else 0)

private theorem big_multiple_weight {k:ℕ} (hk:3<k) (h3:3∣k) : weight k=0 := by
  have hn : ¬ k.Prime := by
    intro hp
    rcases (Nat.dvd_prime hp).mp h3 with h|h <;> omega
  simp [weight,hn]

private theorem delta_coeff_energy (N : ℕ) :
    (∑ k∈range (N+1), (weight k)^2) - (∑ k∈range 7, (weight k)^2) ≤
      ∑ k∈range (N+3),(deltaW N k)^2 := by
  classical
  let A := (range (N+1)).filter (fun p => 7≤p ∧ p.Prime)
  let f (p:ℕ) := if p%3=1 then p+2 else p
  have hprops (p : ℕ) (hp : p∈A) : 7≤p ∧ p≤N ∧ (p%3=1 ∨ p%3=2) := by
    obtain ⟨ha,hl,hh⟩ := mem_filter.mp hp
    have hu := mem_range.mp ha
    have h3 : ¬3∣p := by
      intro h3
      rcases (Nat.dvd_prime hh).mp h3 with h|h <;> omega
    omega
  have hfinj : Set.InjOn f A := by
    intro p hp s hs he
    have h := hprops p hp
    have g := hprops s hs
    simp only [f] at he
    split_ifs at he <;> omega
  have hmem : A.image f ⊆ range (N+3) := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    have h:=hprops p hp
    apply mem_range.mpr
    simp only [f]
    split <;> omega
  have hdelta (p : ℕ) (hp : p∈A) : (deltaW N (f p))^2=(weight p)^2 := by
    obtain ⟨hl,hu,hr⟩ := hprops p hp
    rcases hr with hr|hr
    · have hc : weight (p+2)=0 := big_multiple_weight (by omega) (by omega)
      simp [f,hr,deltaW,clipW,hc,hu]
    · have hc : weight (p-2)=0 := big_multiple_weight (by omega) (by omega)
      simp [f,hr,deltaW,clipW,hc,hu,show 2≤p by omega]
  have hmain : (∑p∈A,(weight p)^2) ≤ ∑ k∈range (N+3),(deltaW N k)^2 := by
    calc
      _ = ∑p∈A,(deltaW N (f p))^2 := sum_congr rfl (fun p hp => (hdelta p hp).symm)
      _ = ∑k∈A.image f,(deltaW N k)^2 := by rw [sum_image hfinj]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hmem (fun _ _ _=>sq_nonneg _)
  have hsplit : (∑k∈range (N+1),(weight k)^2) ≤ (∑k∈range 7,(weight k)^2) + ∑p∈A,(weight p)^2 := by
    have heq : (∑p∈range (N+1),(weight p)^2) =
        ∑p∈range (N+1), if p<7 then (weight p)^2 else if 7≤p ∧ p.Prime then (weight p)^2 else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Prime <;> by_cases h7 : p<7 <;> simp [hp,h7,show (7≤p)↔¬p<7 by omega,weight]
    rw [heq]
    have h7 : (∑p∈(range (N+1)).filter (fun p=>p<7),(weight p)^2) ≤ ∑p∈range 7,(weight p)^2 :=
      sum_le_sum_of_subset_of_nonneg (fun p hp=>mem_range.mpr (mem_filter.mp hp).2) (fun _ _ _=>sq_nonneg _)
    apply le_trans _ (add_le_add_left h7 _)
    dsimp only [A]
    rw [sum_filter,sum_filter]
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro p _
    by_cases h : p<7 <;> simp [h,show (7≤p)↔¬p<7 by omega]
  linarith


private theorem wave_delta (N : ℕ) (t : ℝ) :
    finiteAbelWave (range (N+3)) (fun k=>(deltaW N k:ℂ)) t =
      centralPrimeWave N t * (1-E (2*t)) := by
  have hclip : (∑k∈range (N+3),(clipW N k:ℂ)*E ((k:ℝ)*t)) = centralPrimeWave N t := by
    unfold centralPrimeWave
    have hsub : range (N+1)⊆range (N+3) := range_mono (by omega)
    rw [←sum_subset hsub (f:=fun k=>(clipW N k:ℂ)*E ((k:ℝ)*t)) (by
      intro k hk hh
      simp only [mem_range] at hh
      simp [clipW,show ¬k≤N by omega])]
    apply sum_congr rfl
    intro k hk
    simp [clipW,mem_range_succ_iff.mp hk]
  have hshift : (∑k∈range (N+3),((if 2≤k then clipW N (k-2) else 0:ℝ):ℂ)*E ((k:ℝ)*t)) =
      centralPrimeWave N t * E (2*t) := by
    rw [show N+3=2+(N+1) by omega,sum_range_add]
    have hlow : (∑k∈range 2,((if 2≤k then clipW N (k-2) else 0:ℝ):ℂ)*E ((k:ℝ)*t))=0 := by
      apply sum_eq_zero
      intro k hk
      simp [show ¬2≤k by have := mem_range.mp hk; omega]
    rw [hlow,zero_add]
    unfold centralPrimeWave
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    have h := mem_range_succ_iff.mp hk
    rw [ite_eq_left (by omega : 2≤2+k),show 2+k-2=k by omega]
    simp only [clipW,ite_eq_left h,Nat.cast_add,Nat.cast_ofNat,add_mul,phase_add]
    ring
  unfold finiteAbelWave deltaW
  simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib]
  rw [hclip,hshift]
  ring

theorem truePrime_shift_two_energy (N : ℕ) :
    (∑k∈range (N+1),(weight k)^2)-(∑k∈range 7,(weight k)^2) ≤
      ∫t in Set.Icc (0:ℝ) 1, ‖centralPrimeWave N t‖^2 * ‖1-E (2*t)‖^2 := by
  let G (t:ℝ) := finiteAbelWave (range (N+3)) (fun k=>(deltaW N k:ℂ)) t
  have hn (k:ℕ) : E k=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I)=(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast;ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  have hper : Function.Periodic G 1 := by
    intro t
    unfold G finiteAbelWave
    simp_rw [mul_add,mul_one,phase_add,hn,mul_one]
  have hfper : Function.Periodic (fun t=>‖G t‖^2) 1 := fun t=>congrArg (fun z:ℂ=>‖z‖^2) (hper t)
  have hs := hfper.intervalIntegral_add_eq (-(1/2):ℝ) 0
  norm_num at hs
  have he := finiteAbelWave_unit_energy (range (N+3)) (fun k=>(deltaW N k:ℂ))
  change (∫ t in (-(1/2):ℝ)..(1/2), ‖G t‖^2)=_ at he
  rw [hs] at he
  have hm (t:ℝ) : ‖G t‖^2=‖centralPrimeWave N t‖^2 * ‖1-E (2*t)‖^2 := by
    rw [show G t=_ from wave_delta N t,norm_mul,mul_pow]
  simp only [hm,Complex.norm_real,Real.norm_eq_abs,sq_abs] at he
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,he]
  exact delta_coeff_energy N

theorem truePrime_shift_two_energy_large :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)*Real.log n/64 ≤
      ∫t in Set.Icc (0:ℝ) 1, ‖centralPrimeWave n t‖^2 * ‖1-E (2*t)‖^2 := by
  let C := ∑k∈range 7,(weight k)^2
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [truePrime_full_energy_large,hln.eventually_ge_atTop (1:ℝ),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (64*C)] with n hn hlog hbig
  rw [truePrime_full_energy_sum] at hn
  change 1 ≤ Real.log (n:ℝ) at hlog
  change 64*C ≤ (n:ℝ) at hbig
  have h := truePrime_shift_two_energy n
  change (∑k∈range (n+1),(weight k)^2)-C ≤ _ at h
  nlinarith only [hn,h,hbig,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (sub_nonneg.mpr hlog)]


/-- The unsigned majorant for moving a Fourier coefficient from m to m+2
remains large after deleting any set having sufficiently small prime-wave energy. -/
theorem truePrime_shift_two_minor_transfer (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Icc 0 1) :
    (∫t in Set.Icc (0:ℝ) 1, ‖centralPrimeWave n t‖^2*‖1-E (2*t)‖^2) -
       4*(∫t in A,‖centralPrimeWave n t‖^2) ≤
       2*(∫t in Set.Icc (0:ℝ) 1 \ A, ‖centralPrimeWave n t‖^2*‖1-E (2*t)‖) := by
  let f (t:ℝ) := ‖centralPrimeWave n t‖^2
  let g (t:ℝ) := ‖1-E (2*t)‖
  have hfc : Continuous f := by unfold f centralPrimeWave E;fun_prop
  have hgc : Continuous g := by unfold g E;fun_prop
  have hfi := hfc.integrableOn_Icc (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hgi := (hfc.mul hgc).integrableOn_Icc (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have h2i := (hfc.mul (hgc.pow 2)).integrableOn_Icc (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hgb (t : ℝ) : g t≤2 := by
    have h := norm_sub_le (1:ℂ) (E (2*t))
    rw [norm_one,show ‖E (2*t)‖=1 from Complex.norm_exp_ofReal_mul_I _] at h
    dsimp only [g]
    linarith
  have h1 : (∫t in A, f t*(g t)^2) ≤ 4*∫t in A,f t := by
    rw [←integral_const_mul]
    apply integral_mono (h2i.mono_set hsub) ((hfi.mono_set hsub).const_mul 4)
    intro t
    have hv := pow_le_pow_left₀ (norm_nonneg _) (hgb t) 2
    change f t * g t^2 ≤ 4*f t
    nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg ‖centralPrimeWave n t‖)]
  have h2 : (∫t in Set.Icc (0:ℝ) 1 \ A, f t*(g t)^2) ≤
        2*∫t in Set.Icc (0:ℝ) 1 \ A,f t*g t := by
    rw [←integral_const_mul]
    apply integral_mono (h2i.mono_set Set.sdiff_subset) ((hgi.mono_set Set.sdiff_subset).const_mul 2)
    intro t
    change f t*g t^2≤2*(f t*g t)
    have hf : 0≤f t := sq_nonneg _
    have hg : 0≤g t := norm_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgb t) hg) hf]
  change IntegrableOn (fun t=>f t*(g t)^2) (Set.Icc (0:ℝ) 1) at h2i
  rw [setIntegral_sdiff hA h2i hsub] at h2
  change (∫t in Set.Icc (0:ℝ) 1, f t*(g t)^2) - 4*(∫t in A,f t) ≤ 2*(∫t in Set.Icc 0 1 \ A,f t*g t)
  linarith

open GoldbachMajorArc
open scoped Topology

theorem truePrime_shift_two_frozen_minor_large :
    ∀ᶠ n:ℕ in atTop, (n:ℝ)*Real.log n/256 ≤
      ∫t in Set.Icc (0:ℝ) 1 ∩ (arcs n)ᶜ, ‖centralPrimeWave n t‖^2*‖1-E (2*t)‖ := by
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hll : Tendsto (fun n:ℕ=>Real.log (Real.log n)/Real.log n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp hln)
  filter_upwards [eventually_ge_atTop (2:ℕ),cutoff_separated,truePrime_shift_two_energy_large,
    totalArcError_sublinear.eventually_lt_const zero_lt_one,
    hln.eventually_ge_atTop (1048576:ℝ),hll.eventually_lt_const (show 0<(1:ℝ)/1048576 by norm_num)] with n hn hs hf he hu hv
  let L:=Real.log (n:ℝ)
  change 1048576≤L at hu
  have hL : 0<L := by linarith
  have hN : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn' : 0<(n:ℝ) := by linarith
  have hQ : 0<cutoff n := by
    change 0<(Nat.log 2 (n+2))^2
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQ' : (0:ℝ)<cutoff n := by exact_mod_cast hQ
  have hlog := Real.log_le_log hQ' (GoldbachMajorArc.cutoff_le_log_sq hn)
  change Real.log (cutoff n)≤Real.log (16*L^2) at hlog
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Nat.cast_ofNat] at hlog
  have hl16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)
  change Real.log L/L<1/1048576 at hv
  have hlog' : 1+Real.log (cutoff n)≤L/32768 := by linarith only [hlog,hl16,(div_lt_iff₀ hL).mp hv,hu]
  have he' : totalArcError n≤(n:ℝ) := by simpa using ((div_lt_iff₀ hn').mp he).le
  have hm := truePrime_major_energy n hs
  have hAm : MeasurableSet (Set.Icc (0:ℝ) 1∩arcs n) := measurableSet_Icc.inter (measurable_rational_arcs _ _)
  have hf' := truePrime_shift_two_minor_transfer n hAm Set.inter_subset_left
  have hset : Set.Icc (0:ℝ) 1 ∩ (arcs n)ᶜ = Set.Icc 0 1 \ (Set.Icc 0 1∩arcs n) := by ext t;simp
  rw [hset]
  have hb := mul_le_mul (show 8*((n:ℝ)+1)≤16*(n:ℝ) by linarith) hlog'
    (show 0≤1+Real.log (cutoff n) by positivity) (by positivity : (0:ℝ)≤16*n)
  change (n:ℝ)*L/64≤_ at hf
  change (n:ℝ)*L/256≤_
  nlinarith only [hf,hf',hm,hb,he',mul_le_mul_of_nonneg_left hu hn'.le]
end GoldbachPartial