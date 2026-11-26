import VerifiedExactWeightedShortTube
import MinorArcExactWeightEnergy
import PinnedMajorGeometry
import PinnedLargeMobiusBudget
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology ArithmeticFunction.vonMangoldt

theorem clippedMajor_realVolume_le (n P:ℕ) (hn:0<n) :
    volume.real (Set.Icc (0:ℝ) 1 ∩ rationalArcSet P n)≤4*(P:ℝ)^2/(n:ℝ) := by
  let W (q a:ℕ):Set ℝ := Set.Icc 0 1 ∩ Set.Icc ((a:ℝ)/q-(P:ℝ)/((q:ℝ)*n)) ((a:ℝ)/q+(P:ℝ)/((q:ℝ)*n))
  let V (q:ℕ) := ⋃a∈range (q+1),W q a
  let U := ⋃q∈Icc 1 P,V q
  have hu : U⊆Set.Icc 0 1 := by
    rintro t ht
    obtain ⟨q,_,a,_,ht⟩ : ∃q∈Icc 1 P,∃a∈range (q+1),t∈W q a := by simpa [U,V] using ht
    exact ht.1
  have hs : Set.Icc (0:ℝ) 1 ∩ rationalArcSet P n ⊆ U := by
    intro t ht
    obtain ⟨q,a,hl,hr,ha,_hc,hw⟩ := ht.2
    rw [abs_le] at hw
    have he : t∈W q a := ⟨ht.1,by constructor <;> linarith only [hw.1,hw.2]⟩
    exact Set.mem_iUnion₂.mpr ⟨q,mem_Icc.mpr ⟨hl,hr⟩,Set.mem_iUnion₂.mpr ⟨a,mem_range.mpr (by omega),he⟩⟩
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hrow (q:ℕ) (hq:q∈Icc 1 P) : volume.real (V q)≤4*(P:ℝ)/n := by
    have hq1 : (1:ℝ)≤q := by exact_mod_cast (mem_Icc.mp hq).1
    have hq0 : (0:ℝ)<q := by linarith
    apply (measureReal_biUnion_finset_le (range (q+1)) (W q)).trans
    calc _ ≤ ∑_a∈range (q+1),2*((P:ℝ)/((q:ℝ)*n)) := by
           apply sum_le_sum;intro a _
           apply (measureReal_mono (Set.inter_subset_right (s:=Set.Icc 0 1)) measure_Icc_lt_top.ne).trans
           rw [Real.volume_real_Icc_of_le (by linarith [show 0≤(P:ℝ)/((q:ℝ)*n) by positivity])]
           apply le_of_eq;ring
         _ ≤ _ := by
           simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
           field_simp
           nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) (Nat.cast_nonneg (α:=ℝ) P)]
  apply (measureReal_mono hs (measure_ne_top_of_subset hu measure_Icc_lt_top.ne)).trans
  apply (measureReal_biUnion_finset_le (Icc 1 P) V).trans
  apply (sum_le_sum hrow).trans_eq
  simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul];ring

theorem exactCentered_minor_full_energy :
    ∀ᶠ n:ℕ in atTop,(∑k∈Icc 1 n,(exactCenteredMangoldt (minorRamanujanCutoff n) k)^2) ≤
      28*(n:ℝ)*terminalPrimeArcLog n := by
  filter_upwards [medDesk_projection_parameters,minorRamanujan_geometry_eventually,
    eventually_ge_atTop (1:ℕ)] with n h hg hn
  let P := minorRamanujanCutoff n
  have hPQ : P≤medDeskQ n := hg.2.2.2.2.2.1
  have hPn : P≤n := hPQ.trans h.2.1
  have hLog (m:ℕ) (hm:P≤m) : Real.log P≤Real.log m := by
    by_cases hP:P=0
    · simpa only [hP,Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg m
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hP) (by exact_mod_cast hm)
  have hB : 2*(P:ℝ)^2*(8*(1+Real.log P))^2≤Real.sqrt n := by
    apply le_trans _ h.2.2
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) P) (by exact_mod_cast hPQ : (P:ℝ)≤medDeskQ n) 2
    have hl : 8*(1+Real.log P)≤8*(1+Real.log (medDeskQ n)) := by linarith only [hLog _ hPQ]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) (pow_le_pow_left₀ (by positivity) hl 2)
      (sq_nonneg _) (by positivity)
  have hh := exactCentered_interval_energy P 0 n n (by omega)
  rw [zero_add] at hh
  have hψ : (∑k∈Ioc 0 n,Λ k)≤(Real.log 4+4)*(n:ℝ) := by
    simpa only [Chebyshev.psi,Nat.floor_natCast] using Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) n)
  have h4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hS : Real.sqrt n≤(n:ℝ) := by
    have h₁ : (1:ℝ)≤n := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  rw [show Icc 1 n=Ioc 0 n by ext k;simp only [mem_Icc,mem_Ioc];omega]
  apply hh.trans
  calc
    _ ≤ 2*Real.log n*((4+4)*(n:ℝ))+2*(4*(n:ℝ)*(1+Real.log n)+(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hψ.trans (mul_le_mul_of_nonneg_right (show Real.log 4+4≤4+4 by linarith only [h4]) (Nat.cast_nonneg _))) (by positivity)
      · apply mul_le_mul_of_nonneg_left (add_le_add _ (hB.trans hS)) (by norm_num)
        exact mul_le_mul_of_nonneg_left (add_le_add_right (hLog _ hPn) _) (by positivity)
    _ ≤ _ := by
      unfold terminalPrimeArcLog
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (Real.log_natCast_nonneg n),Nat.cast_nonneg (α:=ℝ) n]

theorem exactWeightedShortPolynomial_full_zero (n P H:ℕ) :
    (∫t in Set.Icc (0:ℝ) 1,exactWeightedShortPolynomial n P H t)=0 := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  unfold exactWeightedShortPolynomial
  rw [intervalIntegral.integral_finsetSum (fun h _=>by apply Continuous.intervalIntegrable;unfold E;fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul,fourier_mode]
  apply sum_eq_zero;intro h hh;simp [(mem_erase.mp hh).1]

theorem exactWeightedShortPolynomial_pointwise (n P H:ℕ) (t:ℝ) :
    ‖exactWeightedShortPolynomial n P H t‖≤(2*(H:ℝ))*(∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2) := by
  let B := ∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2
  unfold exactWeightedShortPolynomial
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑_h∈shortNonzeroModes H,B := by
         apply sum_le_sum;intro h _
         rw [norm_mul,show ‖E ((h:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,Complex.norm_real,Real.norm_eq_abs]
         exact exactWeightedModeCoefficient_energy n P h
       _ = _ := by rw [sum_shortNonzeroModes];simp only [sum_const,card_range,nsmul_eq_mul];dsimp [B];ring

theorem minorCutoff_short_on_major_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, ‖∫t in Set.Icc (0:ℝ) 1 ∩ rationalArcSet (medDeskQ n) n,
        exactWeightedShortPolynomial n (minorRamanujanCutoff n) (exactWeightedShortCutoff n) t‖≤ε*(n:ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun n:ℕ=>(Real.log n)^5/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (5:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [exactCentered_minor_full_energy,eventually_ge_atTop (2:ℕ),hlog.eventually_ge_atTop 1,
    hlim.eventually_lt_const (by positivity : (0:ℝ)<ε/114688)] with n he hn hu hsm
  let P := minorRamanujanCutoff n
  let L := terminalPrimeArcLog n
  let u := Real.log n
  let H := exactWeightedShortCutoff n
  let T := Real.sqrt n
  let A := Set.Icc (0:ℝ) 1 ∩ rationalArcSet (medDeskQ n) n
  change 1≤u at hu
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL2 : L≤2*u := by change 1+u≤_;linarith
  have hLG := Real.log_nonneg hL1
  have hT0 : 0≤T := Real.sqrt_nonneg _
  have hH : (H:ℝ)≤T := (Nat.floor_le (by positivity : 0≤T/(L^2*(1+Real.log L)))).trans
    (div_le_self (Real.sqrt_nonneg _) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1)
      (le_add_of_nonneg_right (Real.log_nonneg hL1))))
  have hb := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=A)
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Icc_lt_top)
    (fun t _=>exactWeightedShortPolynomial_pointwise n P H t)
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hT : 0<T := Real.sqrt_pos.mpr hn'
  have hs : T^2=(n:ℝ) := Real.sq_sqrt hn'.le
  have hcut : (medDeskQ n:ℝ)≤16*u^2 := Pinned316.GoldbachMajorArc.cutoff_le_log_sq hn
  have hv := clippedMajor_realVolume_le n (medDeskQ n) (by omega)
  apply hb.trans
  calc _ ≤ ((2*T)*(28*(n:ℝ)*(2*u)))*(4*(16*u^2)^2/(n:ℝ)) := by
         apply mul_le_mul _ _ measureReal_nonneg (by positivity)
         · apply mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num))
             (he.trans (mul_le_mul_of_nonneg_left hL2 (by positivity))) (sum_nonneg fun _ _=>sq_nonneg _) (by positivity)
         · apply hv.trans;gcongr
       _ = (114688*(u^5/T))*(n:ℝ) := by
         field_simp
         linear_combination (114688:ℝ)*hs
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ hn'.le
         have hh := (lt_div_iff₀ (by norm_num : (0:ℝ)<114688)).mp hsm
         change u^5/T*114688<ε at hh
         linarith only [hh]

noncomputable def exteriorMinorTubeDomain (n:ℕ) : Set ℝ :=
  Set.Icc 0 1 ∩ ((rationalArcSet (medDeskQ n) n)ᶜ \ highNaturalPrimeTubes n)

theorem exteriorMinorTube_integral_partition {n:ℕ} {f:ℝ→ℂ} (hf:Continuous f)
    (hV:highNaturalPrimeTubes n⊆Set.Icc 0 1)
    (hO:highNaturalPrimeTubes n⊆(rationalArcSet (medDeskQ n) n)ᶜ) :
    (∫t in exteriorMinorTubeDomain n,f t) =
      (∫t in Set.Icc (0:ℝ) 1,f t)-(∫t in Set.Icc (0:ℝ) 1 ∩ rationalArcSet (medDeskQ n) n,f t)-
      (∫t in highNaturalPrimeTubes n,f t) := by
  let I := Set.Icc (0:ℝ) 1
  let A := rationalArcSet (medDeskQ n) n
  let V := highNaturalPrimeTubes n
  have hU : exteriorMinorTubeDomain n=(I \ (I∩A)) \ V := by
    ext t
    change (_ ∧ (¬_ ∧ ¬_)) ↔ ((_ ∧ ¬(_ ∧ _)) ∧ ¬_)
    tauto
  have hV' : V⊆I \ (I∩A) := fun t ht=>⟨hV ht,fun hh=>hO ht hh.2⟩
  have hmV : MeasurableSet V := naturalTubeUnion_measurable ..
  have hmA : MeasurableSet (I∩A) := measurableSet_Icc.inter (measurable_rational_arcs _ _)
  have hfI : IntegrableOn f I := hf.integrableOn_Icc
  rw [hU]
  change (∫t in (I \ (I∩A)) \ V,f t) = ((∫t in I,f t)-(∫t in I∩A,f t))-(∫t in V,f t)
  rw [setIntegral_sdiff hmV (hfI.mono_set Set.sdiff_subset) hV',
    setIntegral_sdiff hmA hfI Set.inter_subset_left]

theorem exteriorMinorTube_fourier (n:ℕ) (h:ℤ) (hh:h≠0)
    (hV:highNaturalPrimeTubes n⊆Set.Icc 0 1)
    (hO:highNaturalPrimeTubes n⊆(rationalArcSet (medDeskQ n) n)ᶜ) :
    (∫t in exteriorMinorTubeDomain n,E ((h:ℝ)*t)) =
      -(∫t in Set.Icc (0:ℝ) 1 ∩ rationalArcSet (medDeskQ n) n,E ((h:ℝ)*t))-
      ∫t in highNaturalPrimeTubes n,E ((h:ℝ)*t) := by
  rw [exteriorMinorTube_integral_partition (by unfold E;fun_prop) hV hO]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),fourier_mode,
    ite_eq_right hh,zero_sub]

theorem exteriorMinorTube_short_integral_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,‖∫t in exteriorMinorTubeDomain n,
      exactWeightedShortPolynomial n (minorRamanujanCutoff n) (exactWeightedShortCutoff n) t‖≤ε*(n:ℝ) := by
  have hv := exactWeighted_high_short_small_of_energy minorRamanujanCutoff (C:=28) (by norm_num)
    exactCentered_minor_full_energy (show 0<ε/2 by positivity)
  filter_upwards [minorCutoff_short_on_major_small (show 0<ε/2 by positivity),hv,
    highNaturalPrimeTubes_geometry,highNaturalPrimeTubes_outside_pinned_major] with n hm hh hg ho
  rw [exactWeightedOffTarget_integral_delete n _ _ hg.1] at hh
  rw [exteriorMinorTube_integral_partition (by unfold exactWeightedShortPolynomial E;fun_prop) hg.1 ho,
    exactWeightedShortPolynomial_full_zero,zero_sub]
  apply (norm_sub_le ..).trans
  rw [norm_neg]
  exact (add_le_add hm hh).trans_eq (by ring)

theorem exteriorMinorTube_short_delete {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      ‖(∫t in exteriorMinorTubeDomain n,exactWeightedOffTarget n (minorRamanujanCutoff n) t)-
        (∫t in exteriorMinorTubeDomain n,exactWeightedFarOffTarget n (minorRamanujanCutoff n)
          (exactWeightedShortCutoff n) t)‖≤ε*(n:ℝ) := by
  filter_upwards [exteriorMinorTube_short_integral_small hε] with n hn
  have hU : exteriorMinorTubeDomain n⊆Set.Icc 0 1 := Set.inter_subset_left
  rw [exactWeightedOffTarget_integral_delete n _ _ hU]
  exact hn

theorem exteriorMinorTube_kernel_short_delete {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      ‖(∫t in exteriorMinorTubeDomain n,weightedMangoldtKernel n (minorRamanujanCutoff n)
           (fun d=>(exactRamanujanWeight (minorRamanujanCutoff n) d:ℂ)) t) -
        ((∫t in exteriorMinorTubeDomain n,exactWeightedFarOffTarget n (minorRamanujanCutoff n)
           (exactWeightedShortCutoff n) t) + ((volume.real (exteriorMinorTubeDomain n) *
           exactWeightedZeroMode n (minorRamanujanCutoff n):ℝ):ℂ))‖≤ε*(n:ℝ) := by
  filter_upwards [exteriorMinorTube_short_delete hε] with n hn
  have hU : exteriorMinorTubeDomain n⊆Set.Icc 0 1 := Set.inter_subset_left
  rw [exactWeighted_kernel_setIntegral n _ hU,add_sub_add_right_eq_sub]
  exact hn
end GoldbachPartial
