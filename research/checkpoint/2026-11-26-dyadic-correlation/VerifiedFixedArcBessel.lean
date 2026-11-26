import VerifiedTrueMinorEnergy
import TruePrimeCenteringChebyshev
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology Classical

/-- Lebesgue Fourier coefficient on a fixed measurable part of one period. -/
noncomputable def arcFourierCoefficient (B:Set ℝ)(f:ℝ→ℂ)(m:ℤ):ℂ:=
  ∫ t in B,f t*E (-(m:ℝ)*t)

private noncomputable def finiteIntegerWave (S:Finset ℤ)(c:ℤ→ℂ)(t:ℝ):ℂ:=
  ∑m∈S,c m*E ((m:ℝ)*t)

open private abelParseval_conj from AbelParsevalPrimeArc

private theorem finiteIntegerWave_full_energy (S:Finset ℤ)(c:ℤ→ℂ):
    (∫t in Set.Icc (0:ℝ) 1,‖finiteIntegerWave S c t‖^2)=∑m∈S,‖c m‖^2 := by
  let g (k j:ℤ)(t:ℝ):=(c k*(starRingEnd ℂ) (c j))*E (((k-j:ℤ):ℝ)*t)
  have hgc (k j:ℤ):Continuous (g k j):=by dsimp [g,E];fun_prop
  have hp (t:ℝ):((‖finiteIntegerWave S c t‖^2:ℝ):ℂ)=∑k∈S,∑j∈S,g k j t:=by
    rw [Complex.ofReal_pow,←Complex.mul_conj']
    unfold finiteIntegerWave
    rw [map_sum,sum_mul]
    apply sum_congr rfl;intro k _
    rw [mul_sum];apply sum_congr rfl;intro j _
    dsimp only [g]
    rw [map_mul,abelParseval_conj,Int.cast_sub,show ((k:ℝ)-j)*t=(k:ℝ)*t + -((j:ℝ)*t) by ring,phase_add]
    ring
  have hrow (k:ℤ)(hk:k∈S):(∫t in (0:ℝ)..1,∑j∈S,g k j t)=((‖c k‖^2:ℝ):ℂ):=by
    rw [intervalIntegral.integral_finsetSum (fun j _=>(hgc k j).intervalIntegrable _ _)]
    simp only [g,intervalIntegral.integral_const_mul,fourier_mode]
    rw [sum_eq_single_of_mem k hk]
    · simp [Complex.ofReal_pow,←Complex.mul_conj']
    · intro j _ hne;simp [show k-j≠0 by omega]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  apply Complex.ofReal_injective
  rw [←intervalIntegral.integral_ofReal]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun k _=>(continuous_finsetSum S (fun j _=>hgc k j)).intervalIntegrable _ _)]
  push_cast
  exact sum_congr rfl (fun k hk=>by simpa only [Complex.ofReal_pow] using hrow k hk)

private theorem finiteIntegerWave_test (B:Set ℝ)(hB:B⊆Set.Icc 0 1) (f:ℝ→ℂ)(hf:Continuous f)
    (S:Finset ℤ)(c:ℤ→ℂ) :
    (∫t in B,f t*(starRingEnd ℂ) (finiteIntegerWave S c t))=
      ∑m∈S,arcFourierCoefficient B f m*(starRingEnd ℂ) (c m) := by
  have h (t:ℝ): f t*(starRingEnd ℂ) (finiteIntegerWave S c t)=
      ∑m∈S,(f t*E (-(m:ℝ)*t))*(starRingEnd ℂ) (c m):= by
    unfold finiteIntegerWave
    rw [map_sum,mul_sum]
    apply sum_congr rfl;intro m _
    rw [map_mul,abelParseval_conj,neg_mul];ring
  simp_rw [h]
  rw [integral_finsetSum S (fun m _=>(show Continuous (fun t=>f t*E (-(m:ℝ)*t)*(starRingEnd ℂ) (c m)) by unfold E;fun_prop).integrableOn_Icc.mono_set hB)]
  apply sum_congr rfl;intro m _
  exact integral_mul_const _ _

theorem arcFourierCoefficient_bessel (B:Set ℝ) (hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (f:ℝ→ℂ)(hf:Continuous f)(S:Finset ℤ):
    (∑m∈S,‖arcFourierCoefficient B f m‖^2)≤∫t in B,‖f t‖^2 := by
  let c:=arcFourierCoefficient B f
  let P:=finiteIntegerWave S c
  let Z:=fun t=>f t*(starRingEnd ℂ) (P t)
  have hP:Continuous P := by
    change Continuous (fun t=>∑m∈S,c m*E ((m:ℝ)*t))
    unfold E;fun_prop
  have hZ:Continuous Z := by dsimp [Z];fun_prop
  have hF:Continuous (fun t=>‖f t‖^2):=hf.norm.pow _
  have hP₂:Continuous (fun t=>‖P t‖^2):=hP.norm.pow _
  have htest:(∫t in B,Z t) = ((∑m∈S,‖c m‖^2:ℝ):ℂ):=by
    calc _ = ∑m∈S,c m*(starRingEnd ℂ) (c m) := finiteIntegerWave_test B hBI f hf S c
         _ = _ := by push_cast;simp only [Complex.mul_conj']
  have hre:(∫t in B,(Z t).re)=∑m∈S,‖c m‖^2:=by
    rw [show (∫t in B,(Z t).re)=(∫t in B,Z t).re from integral_re (hZ.integrableOn_Icc.mono_set hBI),htest,Complex.ofReal_re]
  have hpB:(∫t in B,‖P t‖^2)≤∑m∈S,‖c m‖^2 :=
    (setIntegral_mono_set hP₂.integrableOn_Icc (Eventually.of_forall fun _=>sq_nonneg _) hBI.eventuallySubset).trans_eq
      (finiteIntegerWave_full_energy S c)
  have hpw (t:ℝ):2*(Z t).re≤‖f t‖^2+‖P t‖^2:=by
    have hh: (Z t).re≤‖f t‖*‖P t‖:=by simpa only [Z,norm_mul,Complex.norm_conj] using Complex.re_le_norm (Z t)
    nlinarith only [hh,sq_nonneg (‖f t‖-‖P t‖)]
  have hi:(∫t in B,2*(Z t).re)≤∫t in B,(‖f t‖^2+‖P t‖^2) := setIntegral_mono_on
    ((continuous_const.mul (Complex.continuous_re.comp hZ)).integrableOn_Icc.mono_set hBI)
    ((hF.add hP₂).integrableOn_Icc.mono_set hBI) hB (fun t _=>hpw t)
  rw [integral_const_mul,integral_add (hF.integrableOn_Icc.mono_set hBI) (hP₂.integrableOn_Icc.mono_set hBI),hre] at hi
  change (∑m∈S,‖c m‖^2)≤_
  linarith only [hi,hpB]


/-- The polynomial cutoff N and the Fourier integer m are independent. -/
noncomputable def fixedPrimeArcMode (B:Set ℝ)(N:ℕ)(m:ℤ):ℂ:=
  arcFourierCoefficient B (fun t=>(centralPrimeWave N t)^2) m

noncomputable def fixedPrimeArcSup (B:Set ℝ)(N:ℕ):ℝ:=
  sSup ((fun t=>‖centralPrimeWave N t‖) '' B)

private theorem fixedPrimeArc_energy_id (N:ℕ):
    (∫t in Set.Icc (0:ℝ) 1,‖centralPrimeWave N t‖^2)=∑p∈(range (N+1)).filter Nat.Prime,(Real.log p)^2 := by
  rw [truePrime_full_energy_sum,sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp:p.Prime <;> simp [weight,hp]

theorem fixedPrimeArcMode_bessel_bound (B:Set ℝ)(hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (N:ℕ)(S:Finset ℤ)(U:ℝ)(hU:∀t∈B,‖centralPrimeWave N t‖≤U) :
    (∑m∈S,‖fixedPrimeArcMode B N m‖^2)≤U^2*(∑p∈(range (N+1)).filter Nat.Prime,(Real.log p)^2) := by
  let F:=centralPrimeWave N
  have hc:Continuous F := by change Continuous (fun t=>centralPrimeWave N t);unfold centralPrimeWave E;fun_prop
  have hh:=arcFourierCoefficient_bessel B hB hBI (fun t=>(F t)^2) (hc.pow _) S
  apply hh.trans
  have hG:=setIntegral_mono_on
    (show IntegrableOn (fun t:ℝ=>‖(F t)^2‖^2) B from ((hc.pow 2).norm.pow 2).integrableOn_Icc.mono_set hBI)
    (show IntegrableOn (fun t:ℝ=>U^2*‖F t‖^2) B from (continuous_const.mul (hc.norm.pow 2)).integrableOn_Icc.mono_set hBI) hB
    (fun t ht=>by
      rw [norm_pow,pow_two (‖F t‖^2)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hU t ht) 2) (sq_nonneg _))
  apply hG.trans
  rw [integral_const_mul,←fixedPrimeArc_energy_id]
  exact mul_le_mul_of_nonneg_left (setIntegral_mono_set (hc.norm.pow 2).integrableOn_Icc
    (Eventually.of_forall fun _=>sq_nonneg _) hBI.eventuallySubset) (sq_nonneg _)

theorem fixedPrimeArcMode_bessel_sup (B:Set ℝ)(hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (N:ℕ)(S:Finset ℤ) :
    (∑m∈S,‖fixedPrimeArcMode B N m‖^2)≤(fixedPrimeArcSup B N)^2*
      ∑p∈(range (N+1)).filter Nat.Prime,(Real.log p)^2 := by
  have hc:Continuous (fun t=>‖centralPrimeWave N t‖):=by unfold centralPrimeWave E;fun_prop
  apply fixedPrimeArcMode_bessel_bound B hB hBI N S
  intro t ht
  apply le_csSup
  · exact (isCompact_Icc.image hc).bddAbove.mono (Set.image_mono hBI)
  · exact Set.mem_image_of_mem _ ht

theorem fixedPrimeArcMode_large_deviation (B:Set ℝ)(hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (N:ℕ)(S:Finset ℤ)(U T:ℝ)(hT:0≤T)(hU:∀t∈B,‖centralPrimeWave N t‖≤U):
    (((S.filter (fun m=>T≤‖fixedPrimeArcMode B N m‖)).card:ℝ))*T^2 ≤
      U^2*(Real.log 4*(N:ℝ)*Real.log N) := by
  let D:=S.filter (fun m=>T≤‖fixedPrimeArcMode B N m‖)
  have hD:((D.card:ℝ))*T^2≤∑m∈D,‖fixedPrimeArcMode B N m‖^2:=by
    rw [←nsmul_eq_mul,←sum_const]
    exact sum_le_sum (fun m hm=>pow_le_pow_left₀ hT (mem_filter.mp hm).2 2)
  apply (hD.trans (fixedPrimeArcMode_bessel_bound B hB hBI N D U hU)).trans
  rw [←fixedPrimeArc_energy_id]
  exact mul_le_mul_of_nonneg_left (centralPrimeWave_local_energy_chebyshev N Set.Subset.rfl) (sq_nonneg _)

theorem fixedPrimeArcMode_exceptional_count (B:Set ℝ)(hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (N:ℕ)(hN:2≤N)(S:Finset ℤ)(C δ:ℝ)(hδ:0<δ)
    (hU:∀t∈B,‖centralPrimeWave N t‖≤C*(N:ℝ)/Real.log N):
    ((S.filter (fun m=>δ*(N:ℝ)≤‖fixedPrimeArcMode B N m‖)).card:ℝ)≤
      Real.log 4*C^2*(N:ℝ)/(δ^2*Real.log N) := by
  have hNp:(0:ℝ)<N:=by exact_mod_cast (show 0<N by omega)
  have hL:0<Real.log (N:ℝ):=Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hb:=fixedPrimeArcMode_large_deviation B hB hBI N S _ (δ*(N:ℝ)) (by positivity) hU
  apply (le_div_iff₀ (by positivity)).mpr
  apply le_of_mul_le_mul_left (a:=((N:ℝ))^2) _ (sq_pos_of_pos hNp)
  apply le_of_mul_le_mul_left (a:=Real.log (N:ℝ)) _ hL
  have hpos:=mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.log (N:ℝ)))
  convert hpos using 1
  · ring
  · field_simp

theorem fixedPrimeArcMode_exceptional_natural (B:Set ℝ)(hB:MeasurableSet B)(hBI:B⊆Set.Icc 0 1)
    (N:ℕ)(hN:2≤N)(S:Finset ℕ)(C δ:ℝ)(hδ:0<δ)
    (hU:∀t∈B,‖centralPrimeWave N t‖≤C*(N:ℝ)/Real.log N):
    ((S.filter (fun m:ℕ=>δ*(N:ℝ)≤‖fixedPrimeArcMode B N (m:ℤ)‖)).card:ℝ)≤
      Real.log 4*C^2*(N:ℝ)/(δ^2*Real.log N) := by
  let f:ℕ→ℤ:=Int.ofNat
  have hh:=fixedPrimeArcMode_exceptional_count B hB hBI N hN (S.image f) C δ hδ hU
  rw [filter_image,card_image_of_injective _ Int.ofNat_injective] at hh
  exact hh

theorem fixedPrimeArcMode_exceptional_density_zero
    (B:ℕ→Set ℝ)(S:ℕ→Finset ℕ)(C δ:ℝ)(hδ:0<δ)
    (h:∀ᶠ N:ℕ in atTop,MeasurableSet (B N) ∧ B N⊆Set.Icc 0 1 ∧
      ∀t∈B N,‖centralPrimeWave N t‖≤C*(N:ℝ)/Real.log N):
    Tendsto (fun N:ℕ=>(((S N).filter (fun m:ℕ=>δ*(N:ℝ)≤‖fixedPrimeArcMode (B N) N (m:ℤ)‖)).card:ℝ)/(N:ℝ))
      atTop (𝓝 0) := by
  have hlt:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht:Tendsto (fun N:ℕ=>(Real.log 4*C^2/δ^2)/Real.log (N:ℝ)) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop hlt
  apply squeeze_zero' (Eventually.of_forall (fun n=>by positivity)) _ ht
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with N hh hn
  have hNp:(0:ℝ)<N:=by exact_mod_cast (show 0<N by omega)
  apply (div_le_div_of_nonneg_right (fixedPrimeArcMode_exceptional_natural (B N) hh.1 hh.2.1 N hn (S N) C δ hδ hh.2.2) hNp.le).trans_eq
  field_simp

end GoldbachPartial
