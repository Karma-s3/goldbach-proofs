import ExactWeightedKernelZeroMode
import SignedHighTubeModes
import FarShortPairModes
namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Topology

private def exactOffPairs (n:ℕ) := (Icc 1 n ×ˢ Icc 1 n).filter (fun u=>u.1+u.2≠n)
private def exactMode (n:ℕ) (u:ℕ×ℕ) : ℤ := farPairFrequency n u.1 u.2
private def modeFiber (n:ℕ) (h:ℤ) := (exactOffPairs n).filter (fun u=>exactMode n u=h)

noncomputable def exactWeightedModeCoefficient (n P:ℕ) (h:ℤ) : ℝ :=
  ∑u∈modeFiber n h,exactCenteredMangoldt P u.1*exactCenteredMangoldt P u.2

noncomputable def exactWeightedShortPolynomial (n P H:ℕ) (t:ℝ) : ℂ :=
  ∑h∈shortNonzeroModes H,(exactWeightedModeCoefficient n P h:ℂ)*E ((h:ℝ)*t)

noncomputable def exactWeightedFarOffTarget (n P H:ℕ) (t:ℝ) : ℂ :=
  ∑u∈(exactOffPairs n).filter (fun u=>exactMode n u∉shortNonzeroModes H),
    ((exactCenteredMangoldt P u.1*exactCenteredMangoldt P u.2:ℝ):ℂ)*E (((u.1:ℝ)+u.2-n)*t)

theorem exactWeightedOffTarget_split_short (n P H:ℕ) (t:ℝ) :
    exactWeightedOffTarget n P t=exactWeightedShortPolynomial n P H t+exactWeightedFarOffTarget n P H t := by
  let O := exactOffPairs n
  let S := shortNonzeroModes H
  let F := exactMode n
  let w (u:ℕ×ℕ):ℝ := exactCenteredMangoldt P u.1*exactCenteredMangoldt P u.2
  let z (u:ℕ×ℕ):ℂ := (w u:ℂ)*E (((u.1:ℝ)+u.2-n)*t)
  let B := O.filter (fun u=>F u∈S)
  have hm (u:ℕ×ℕ) (hu:u∈B) : F u∈S := (mem_filter.mp hu).2
  have he : (∑u∈B,z u)=exactWeightedShortPolynomial n P H t := by
    rw [←sum_fiberwise_of_maps_to hm z]
    apply sum_congr rfl
    intro h hh
    have hs : B.filter (fun u=>F u=h)=modeFiber n h := by
      ext u
      change (u∈(O.filter (fun u=>F u∈S)).filter (fun u=>F u=h)) ↔ u∈O.filter (fun u=>F u=h)
      simp only [mem_filter]
      constructor
      · exact fun h=>⟨h.1.1,h.2⟩
      · rintro ⟨hu,hf⟩;exact ⟨⟨hu,hf ▸ hh⟩,hf⟩
    rw [hs,exactWeightedModeCoefficient,Complex.ofReal_sum,sum_mul]
    apply sum_congr rfl
    intro u hu
    have hf := (mem_filter.mp hu).2
    change (u.1:ℤ)+u.2-n=h at hf
    dsimp only [z,w]
    rw [←hf];push_cast;rfl
  change (∑u∈O,z u)=_+∑u∈O.filter (fun u=>F u∉S),z u
  rw [←he]
  exact (sum_filter_add_sum_filter_not O (fun u=>F u∈S) z).symm

theorem exactWeightedModeCoefficient_energy (n P:ℕ) (h:ℤ) :
    |exactWeightedModeCoefficient n P h|≤∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2 := by
  let I := modeFiber n h
  let A := exactCenteredMangoldt P
  have hm {u:ℕ×ℕ} (hu:u∈I) : u.1∈Icc 1 n ∧ u.2∈Icc 1 n :=
    mem_product.mp (mem_filter.mp (mem_filter.mp hu).1).1
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
      (∑u∈I,(A (f u))^2) ≤∑k∈Icc 1 n,(A k)^2 := by
    apply sum_le_sum_of_injOn f hf
    · intro k hk;obtain ⟨u,hu,rfl⟩ := mem_image.mp hk;exact hh u hu
    · intro u _;exact le_rfl
    · intro k _ _;exact sq_nonneg _
  have hl := hproj _ h₁ (fun u hu => (hm hu).1)
  have hr := hproj _ h₂ (fun u hu => (hm hu).2)
  have hh : (2:ℝ)*(∑u∈I,|A u.1*A u.2|) ≤ (∑u∈I,(A u.1)^2)+(∑u∈I,(A u.2)^2) := by
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum;intro u _
    rw [abs_mul]
    nlinarith only [sq_nonneg (|A u.1| - |A u.2|),sq_abs (A u.1),sq_abs (A u.2)]
  apply (abs_sum_le_sum_abs ..).trans
  change ∑u∈I,|A u.1*A u.2|≤∑k∈Icc 1 n,(A k)^2
  linarith only [hl,hr,hh]

theorem exactWeightedShortPolynomial_integral_bound (n P H R Q M:ℕ)
    (hsep:2*Q<M) (hV:naturalTubeUnion R Q M⊆Set.Icc 0 1) (hcap:(H:ℝ)*(1+Real.log Q)≤M) :
    ‖∫t in naturalTubeUnion R Q M,exactWeightedShortPolynomial n P H t‖ ≤
    (∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2)*(((16+8*Real.pi)/(M:ℝ))*(H:ℝ)*(1+Real.log H)) := by
  let B := ∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2
  have hB : 0≤B := sum_nonneg fun _ _=>sq_nonneg _
  let c (h:ℤ) : ℂ := exactWeightedModeCoefficient n P h
  have hi (h:ℤ) : IntegrableOn (fun t:ℝ => c h*E ((h:ℝ)*t)) (naturalTubeUnion R Q M) := by
    have hh : Continuous (fun t:ℝ => c h*E ((h:ℝ)*t)) := by unfold E;fun_prop
    exact hh.integrableOn_Icc.mono_set hV
  change ‖∫t in naturalTubeUnion R Q M,∑h∈shortNonzeroModes H,c h*E ((h:ℝ)*t)‖≤_
  rw [integral_finsetSum _ (fun h _=>hi h)]
  simp_rw [integral_const_mul]
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑h∈shortNonzeroModes H,B*‖naturalTubeFourierMode R Q M h‖ := by
         apply sum_le_sum;intro h _
         rw [norm_mul];apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
         simpa only [c,Complex.norm_real,Real.norm_eq_abs] using exactWeightedModeCoefficient_energy n P h
       _ ≤ _ := by
         rw [←mul_sum];exact mul_le_mul_of_nonneg_left (signedTube_shortFourier_l1 R Q M H hsep hcap) hB

theorem exactWeightedOffTarget_integral_delete (n P H:ℕ) {V:Set ℝ} (hV:V⊆Set.Icc 0 1) :
    (∫t in V,exactWeightedOffTarget n P t)-(∫t in V,exactWeightedFarOffTarget n P H t)=
      ∫t in V,exactWeightedShortPolynomial n P H t := by
  simp_rw [exactWeightedOffTarget_split_short n P H]
  have hs : Continuous (exactWeightedShortPolynomial n P H) := by unfold exactWeightedShortPolynomial E;fun_prop
  have hf : Continuous (exactWeightedFarOffTarget n P H) := by unfold exactWeightedFarOffTarget E;fun_prop
  rw [integral_add (hs.integrableOn_Icc.mono_set hV) (hf.integrableOn_Icc.mono_set hV),add_sub_cancel_right]

noncomputable def exactWeightedShortCutoff (n:ℕ) : ℕ :=
  ⌊Real.sqrt n/((terminalPrimeArcLog n)^2*(1+Real.log (terminalPrimeArcLog n)))⌋₊

theorem exactWeighted_high_short_rate (C:ℝ) (hC:0≤C) :
    ∀ᶠ n:ℕ in atTop,∀P:ℕ,
      (∑k∈Icc 1 n,(exactCenteredMangoldt P k)^2)≤C*(n:ℝ)*terminalPrimeArcLog n →
      ‖(∫t in highNaturalPrimeTubes n,exactWeightedOffTarget n P t)-
        (∫t in highNaturalPrimeTubes n,exactWeightedFarOffTarget n P (exactWeightedShortCutoff n) t)‖ ≤
        ((32+16*Real.pi)*C)*(n:ℝ)/(1+Real.log (terminalPrimeArcLog n)) := by
  filter_upwards [highNaturalPrimeTubes_geometry,eventually_ge_atTop (1:ℕ)] with n hV hn
  intro P hP
  let L := terminalPrimeArcLog n
  let Q := naturalTubeScale n
  let H := exactWeightedShortCutoff n
  let J := 1+Real.log L
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hJ1 : 1≤J := le_add_of_nonneg_right (Real.log_nonneg hL1)
  have hJ : 0<J := by linarith
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hs1 : 1≤Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hsn : Real.sqrt n≤(n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  have hq1 : 1≤Q := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by simpa using hs1)
  have hqr1 : (1:ℝ)≤Q := by exact_mod_cast hq1
  have hqr : (0:ℝ)<Q := by linarith
  have hqs : Real.sqrt n≤2*(Q:ℝ) := by
    have hh : Real.sqrt n<(Q:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have hqrn : (Q:ℝ)≤n := (Nat.floor_le (Real.sqrt_nonneg _)).trans hsn
  have hlogQ : 1+Real.log Q≤L := add_le_add_right (Real.log_le_log hqr hqrn) 1
  have hH : (H:ℝ)≤Real.sqrt n/(L^2*J) := Nat.floor_le (by positivity)
  have hHt := (le_div_iff₀ (mul_pos (pow_pos hL 2) hJ)).mp hH
  have h1den : 1≤L^2*J := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hJ1
  have hHn : (H:ℝ)≤n := hH.trans ((div_le_self (Real.sqrt_nonneg _) h1den).trans hsn)
  have hlogH : 1+Real.log H≤L := by
    by_cases hp : H=0
    · simpa [hp] using hL1
    · exact add_le_add_right (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hp) hHn) 1
  have hHL : L≤L^2*J := (le_self_pow₀ hL1 (by decide:2≠0)).trans
    (le_mul_of_one_le_right (sq_nonneg _) hJ1)
  have hcap : (H:ℝ)*(1+Real.log Q)≤((3*Q:ℕ):ℝ) := by
    apply (mul_le_mul_of_nonneg_left (hlogQ.trans hHL) (Nat.cast_nonneg H)).trans
    exact hHt.trans (hqs.trans (by push_cast;linarith))
  have hb := exactWeightedShortPolynomial_integral_bound n P H (terminalPrimeArcCutoff n) Q (3*Q)
    (by omega) hV.1 hcap
  rw [exactWeightedOffTarget_integral_delete n P H hV.1]
  apply hb.trans
  have hH' := hH.trans (div_le_div_of_nonneg_right hqs (by positivity))
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ ≤ (C*(n:ℝ)*L)*(((16+8*Real.pi)/(3*(Q:ℝ)))*(2*(Q:ℝ)/(L^2*J))*L) := by
      have hc' : 0≤C*(n:ℝ)*L := by positivity
      gcongr
    _ ≤ ((32+16*Real.pi)*C)*(n:ℝ)/J := by
      have he : (C*(n:ℝ)*L)*(((16+8*Real.pi)/(3*(Q:ℝ)))*(2*(Q:ℝ)/(L^2*J))*L)=
          (((32+16*Real.pi)*C)*(n:ℝ)/J)/3 := by field_simp;ring
      rw [he];exact div_le_self (by positivity) (by norm_num)

theorem exactWeighted_high_short_small_of_energy (P:ℕ→ℕ) {C:ℝ} (hC:0≤C)
    (he:∀ᶠ n:ℕ in atTop,(∑k∈Icc 1 n,(exactCenteredMangoldt (P n) k)^2)≤C*(n:ℝ)*terminalPrimeArcLog n)
    {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      ‖(∫t in highNaturalPrimeTubes n,exactWeightedOffTarget n (P n) t)-
        (∫t in highNaturalPrimeTubes n,exactWeightedFarOffTarget n (P n) (exactWeightedShortCutoff n) t)‖ ≤ ε*(n:ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hL : Tendsto (fun n:ℕ=>terminalPrimeArcLog n) atTop atTop :=
    tendsto_atTop_mono (fun n=>show Real.log (n:ℝ)≤1+Real.log n by linarith) hlog
  have hJ := Real.tendsto_log_atTop.comp hL
  let A := (32+16*Real.pi)*C
  filter_upwards [he,exactWeighted_high_short_rate C hC,hJ.eventually_ge_atTop (A/ε)] with n hN hb hSe
  apply (hb (P n) hN).trans
  let J := 1+Real.log (terminalPrimeArcLog n)
  have hL1 : 1≤terminalPrimeArcLog n := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hJl := Real.log_nonneg hL1
  have hJp : 0<J := by dsimp [J];linarith
  have hAe : A/ε≤J := hSe.trans (by change Real.log (terminalPrimeArcLog n)≤1+Real.log (terminalPrimeArcLog n);linarith)
  have ha := (div_le_iff₀ hε).mp hAe
  change A*(n:ℝ)/J≤ε*n
  apply (div_le_iff₀ hJp).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (α:=ℝ) n)
end GoldbachPartial
