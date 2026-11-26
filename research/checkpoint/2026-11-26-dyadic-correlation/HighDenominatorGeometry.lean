import MidpointCorrelationReduction
import NaturalPrimeGapTubeUnion

namespace GoldbachPartial
open Finset Set Filter MeasureTheory
open scoped Topology

noncomputable def highNaturalPrimeTubes (n : ℕ) : Set ℝ :=
  naturalTubeUnion (terminalPrimeArcCutoff n) (naturalTubeScale n) (3*naturalTubeScale n)

noncomputable def remainingPrimeArcs (n : ℕ) : Set ℝ :=
  (((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n) \
    quarterEndpointStrips n) \ halfPeriodWings n

private theorem naturalTube_adjacent_disjoint {B R Q M : ℕ} (hr : R≤Q) (hs : 2*Q<M) :
    Disjoint (naturalTubeUnion B R M) (naturalTubeUnion R Q M) := by
  apply Set.disjoint_left.mpr
  intro t ht hu
  obtain ⟨i,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨j,hj,hu⟩ := Set.mem_iUnion₂.mp hu
  obtain ⟨hi',ha⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hj',hb⟩ := Finset.mem_sigma.mp hj
  obtain ⟨_,hiR⟩ := Finset.mem_Ico.mp hi'
  obtain ⟨hRj,hjQ⟩ := Finset.mem_Ico.mp hj'
  have hiQ : i ∈ naturalTubeIndices 0 Q := Finset.mem_sigma.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,hiR.trans_le hr⟩,ha⟩
  have hjQ' : j ∈ naturalTubeIndices 0 Q := Finset.mem_sigma.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,hjQ⟩,hb⟩
  have hne : i≠j := by intro he; subst j; omega
  exact Set.disjoint_left.mp (naturalTube_pairwise hs hiQ hjQ' hne) ht hu

private theorem broadCore_scale :
    ∀ᶠ n : ℕ in atTop, 4*(256*(medDeskD n:ℝ)*(medDeskQ n:ℝ))≤Real.sqrt n := by
  let t := fun n : ℕ => (n:ℝ)^(1/15:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/15)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_core_cutoffs,ht.eventually_ge_atTop 1024,eventually_ge_atTop (1:ℕ)] with n hc hT hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hQ : medDeskQ n ≤ medDeskC n := hc.1.trans hc.2.1
  have hQr : (medDeskQ n:ℝ) ≤ (n:ℝ)^(1/10:ℝ) :=
    (show (medDeskQ n:ℝ)≤medDeskC n by exact_mod_cast hQ).trans (Nat.floor_le (by positivity))
  have hBr : (medDeskD n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  calc
    _ = 1024*(medDeskD n:ℝ)*(medDeskQ n:ℝ) := by ring
    _ ≤ t n*(n:ℝ)^(1/3:ℝ)*(n:ℝ)^(1/10:ℝ) := by gcongr
    _ = _ := by
      dsimp [t]
      rw [← Real.rpow_add hn',← Real.rpow_add hn',Real.sqrt_eq_rpow]
      norm_num

theorem highNaturalPrimeTubes_geometry :
    ∀ᶠ n : ℕ in atTop, highNaturalPrimeTubes n ⊆ Icc 0 1 ∧
      highNaturalPrimeTubes n ⊆ remainingPrimeArcs n := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [naturalTube_eventual_budget,squareRootLogShell_geometry,broadCore_scale,
    quarterEndpointStrips_inside_wide_core,halfPeriodWings_geometry,hlog] with n h hcut hH hend hmid hlog
  let B := medDeskD n
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let H := 256*B*medDeskQ n
  have hn : 0<n := h.1
  have hQ : 0<Q := h.2.2.1
  have hqr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hBR : B≤R := hcut.2.1
  have hB : 0<B := hcut.1
  have hR : 0<R := hB.trans_le hBR
  have hRQ : R≤Q := by have h' : 2*R<Q := h.2.2.2.1; omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hm : (Q:ℝ) ≤ Real.sqrt n := Nat.floor_le (Real.sqrt_nonneg _)
  have hh : 4*(H:ℝ) ≤ Real.sqrt n := by simpa [H,B] using hH
  have h₁ : (Q:ℝ)*H/n ≤ 1/4 := by
    have he := mul_le_mul hm hh (by positivity) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hn'.le] at he
    apply (div_le_iff₀ hn').mpr
    linarith only [he]
  have h₂ : (R:ℝ)/(3*Q) ≤ 1/3 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    (by
      have h' : (R:ℝ)≤Q := by exact_mod_cast hRQ
      linarith only [h'])
  have hwideR := naturalTubeUnion_outside_core (n:=n) (B:=R) (R:=Q) (M:=3*Q) (H:=H) hn
    (by omega) (by push_cast; linarith only [h₁,h₂])
  have hwide : highNaturalPrimeTubes n ⊆ (coreArcBand n H 0 B)ᶜ := by
    intro t ht hh'
    obtain ⟨q,a,hq,hu,ha,hcop,hw⟩ := hh'
    exact hwideR ht ⟨q,a,hq,hu.trans hBR,ha,hcop,hw⟩
  have hsep := naturalTube_adjacent_disjoint (B:=B) (M:=3*Q) hRQ (by omega)
  change 2 ≤ Real.log (n:ℝ) at hlog
  have hL : 3 ≤ terminalPrimeArcLog n := by dsimp [terminalPrimeArcLog]; linarith
  have hL4 : (3:ℝ)≤(terminalPrimeArcLog n)^4 := by
    calc (3:ℝ) ≤ 3^4 := by norm_num
         _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL 4
  have hlow : logFourPrimeTubes n ⊆ naturalTubeUnion B R (3*Q) := by
    apply naturalTube_union_of_le
    intro j _
    have hj : (0:ℝ)<((j+1:ℕ):ℝ) := by positivity
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<((j+1:ℕ):ℝ)*(3*Q:ℕ)) 
    push_cast
    calc
      _ = ((j:ℝ)+1)*((Q:ℝ)*3) := by ring
      _ ≤ ((j:ℝ)+1)*(Real.sqrt n*(terminalPrimeArcLog n)^4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm hL4 (by norm_num) (Real.sqrt_nonneg _)) (by positivity)
      _ = _ := by ring
  refine ⟨naturalTubeUnion_inside_unit hR (by omega : 0<3*Q),?_⟩
  intro t ht
  refine ⟨⟨⟨?_,fun hl => Set.disjoint_left.mp hsep (hlow hl) ht⟩,
    fun he => hwide ht (hend he)⟩,fun he => hwide ht (hmid.2.2 he)⟩
  intro hc
  apply hwide ht
  obtain ⟨q,a,hq,hu,ha,hcop,hw⟩ := hc
  refine ⟨q,a,hq,hu,ha,hcop,hw.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hge : 1≤256*B := by omega
  exact_mod_cast (show medDeskQ n ≤ H by simpa [H] using Nat.mul_le_mul_right (medDeskQ n) hge)

end GoldbachPartial
