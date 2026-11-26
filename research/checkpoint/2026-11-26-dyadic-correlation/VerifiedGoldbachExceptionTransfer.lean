import VerifiedUniformPrimeMajorFloor
import VerifiedCommonWidthSiegelWalfisz
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Classical Topology

theorem fixedPrimeArcMode_decomposition {A : Set ℝ} (hA : MeasurableSet A) (hAI : A ⊆ Set.Icc 0 1)
    (N m : ℕ) (hm : m≤N) :
    (corr m : ℂ) = fixedPrimeArcMode A N (m:ℤ) +
      fixedPrimeArcMode (Set.Icc 0 1 \ A) N (m:ℤ) := by
  let f := fun t : ℝ => (centralPrimeWave N t)^2*E (-((m:ℤ):ℝ)*t)
  have hi : IntegrableOn f (Set.Icc (0:ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    unfold f centralPrimeWave E
    fun_prop
  change (corr m:ℂ) = (∫t in A,f t)+(∫t in Set.Icc 0 1 \ A,f t)
  rw [setIntegral_sdiff hA hi hAI,add_sub_cancel,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  simpa only [f,centralPrimeWave,Int.cast_natCast,corr] using (fixed_truncation_coefficient weight N m hm).symm

theorem uniformPrime_major_floor (b : ℕ) (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m≤N → N≤2*m → Even m →
      (m:ℝ)/12 ≤ (fixedPrimeArcMode (fixedUniformMajorArcs (uniformPrimeDenominator b N)
        (uniformPrimeWidth b N)) N (m:ℤ)).re :=
  uniformPrime_major_floor_of_approximation commonWidth_SW_wave b hb

noncomputable def dyadicGoldbachExceptions (X : ℕ) : Finset ℕ :=
  ((Ico X (2*X)).filter Even).filter (fun m => corr m < (m:ℝ)/36)

theorem goldbach_exception_bound_of_minor (b : ℕ) (hb : 0<b) (C : ℝ) (hC : 0<C)
    (hminor : ∀ᶠ N : ℕ in atTop, ∀ t∈uniformPrimeMinor b N,
      ‖centralPrimeWave N t‖ ≤ C*N/Real.log N) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop,
      ((dyadicGoldbachExceptions X).card:ℝ) ≤ K*X/Real.log X := by
  let δ : ℝ := 1/36
  have hδ : 0<δ := by norm_num [δ]
  let K := 2*Real.log 4*C^2/δ^2
  have h4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K,hK,?_⟩
  have ht : Tendsto (fun X : ℕ => 2*X) atTop atTop := tendsto_atTop.mpr (fun r =>
    (eventually_ge_atTop r).mono (fun X hX => by omega))
  filter_upwards [ht.eventually (uniformPrime_major_floor b hb),ht.eventually hminor,
    ht.eventually (uniformPrime_geometry b hb),eventually_ge_atTop (2:ℕ)] with X hs hu hg hX
  let N := 2*X
  let A := fixedUniformMajorArcs (uniformPrimeDenominator b N) (uniformPrimeWidth b N)
  let B := uniformPrimeMinor b N
  let S := Ico X N
  have hA : MeasurableSet A := fixedUniformMajorArcs_measurable _ _
  have hAI : A⊆Set.Icc 0 1 := fixedUniformMajorArcs_subset (by have h := hg.1;change 16≤uniformPrimeDenominator b N at h;omega) hg.2.1.le hg.2.2.1
  have hB : MeasurableSet B := measurableSet_Icc.diff hA
  have hsub : B⊆Set.Icc 0 1 := Set.sdiff_subset
  have hN : 2≤N := by dsimp [N];omega
  have hinc : dyadicGoldbachExceptions X ⊆ S.filter (fun m : ℕ => δ*N≤‖fixedPrimeArcMode B N (m:ℤ)‖) := by
    intro m hm
    obtain ⟨hm',hc⟩ := mem_filter.mp hm
    obtain ⟨hmS,he⟩ := mem_filter.mp hm'
    obtain ⟨hXm,hmN⟩ := mem_Ico.mp hmS
    have hNm : N≤2*m := by dsimp [N];omega
    have hmaj := hs m hmN.le hNm he
    have heq := congrArg Complex.re (fixedPrimeArcMode_decomposition hA hAI N m hmN.le)
    change corr m = (fixedPrimeArcMode A N (m:ℤ)).re+(fixedPrimeArcMode B N (m:ℤ)).re at heq
    change (m:ℝ)/12 ≤ (fixedPrimeArcMode A N (m:ℤ)).re at hmaj
    have hneg := Complex.re_le_norm (-fixedPrimeArcMode B N (m:ℤ))
    simp only [Complex.neg_re,norm_neg] at hneg
    have hNm' : (N:ℝ)≤2*(m:ℝ) := by exact_mod_cast hNm
    apply mem_filter.mpr ⟨hmS,?_⟩
    change (1/36:ℝ)*N≤_
    linarith only [hc,heq,hmaj,hneg,hNm']
  have hcard : ((dyadicGoldbachExceptions X).card:ℝ) ≤ _ := Nat.cast_le.mpr (card_le_card hinc)
  have hU := fixedPrimeArcMode_exceptional_natural B hB hsub N hN S C δ hδ hu
  apply (hcard.trans hU).trans
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl : 0<Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hLN : Real.log X ≤ Real.log N := Real.log_le_log hx (by exact_mod_cast (show X≤N by dsimp [N];omega))
  calc _ = K*X/Real.log N := by dsimp only [N,K];push_cast;ring
       _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hK.le hx.le) hl hLN

end GoldbachPartial