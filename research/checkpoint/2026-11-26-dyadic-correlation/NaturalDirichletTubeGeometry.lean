import NearRootShell
namespace GoldbachPartial
open Set Finset Filter MeasureTheory
open GoldbachDeepFourth (deepTube deepTube_cross deepTube_separation)
noncomputable section

abbrev naturalTubeScale (n : ℕ) : ℕ := ⌊Real.sqrt n⌋₊
abbrev naturalTubeRadius (M q : ℕ) : ℝ := 1/((q:ℝ)*M)
abbrev naturalTubeIndices (B R : ℕ) := (Finset.Ico B R).sigma intervalTubeNumerators
def naturalTubeUnion (B R M : ℕ) : Set ℝ :=
  ⋃ i ∈ naturalTubeIndices B R, deepTube (naturalTubeRadius M (i.1+1)) (i.1+1) i.2

theorem naturalTubeUnion_measurable (B R M : ℕ) : MeasurableSet (naturalTubeUnion B R M) :=
  (naturalTubeIndices B R).measurableSet_biUnion fun _ _ => measurableSet_Icc

private theorem tubes_separate {q r a b : ℕ} {u v : ℝ} (hq : 0<q) (hr : 0<r)
    (ha : a.Coprime q) (hb : b.Coprime r) (hne : (q,a)≠(r,b))
    (h : u+v < 1/((q:ℝ)*r)) : Disjoint (deepTube u q a) (deepTube v r b) := by
  have hs := deepTube_separation hq hr (deepTube_cross hq hr ha hb hne)
  refine Set.disjoint_left.mpr ?_
  rintro t ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
  have hc : |(a:ℝ)/q-b/r| ≤ u+v := abs_le.mpr ⟨by linarith,by linarith⟩
  exact (not_lt_of_ge (hs.trans hc)) h

theorem naturalTube_pair_disjoint {q r a b M : ℕ} (hq : 0<q) (hr : 0<r)
    (ha : a.Coprime q) (hb : b.Coprime r) (hne : (q,a) ≠ (r,b)) (h : q+r < M) :
    Disjoint (deepTube (naturalTubeRadius M q) q a) (deepTube (naturalTubeRadius M r) r b) := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  apply tubes_separate hq hr ha hb hne
  unfold naturalTubeRadius
  field_simp
  exact_mod_cast (by omega : r+q<M)

theorem naturalTube_pairwise {B R M : ℕ} (h : 2*R<M) :
    (↑(naturalTubeIndices B R) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i k =>
      Disjoint (deepTube (naturalTubeRadius M (i.1+1)) (i.1+1) i.2)
        (deepTube (naturalTubeRadius M (k.1+1)) (k.1+1) k.2)) := by
  rintro ⟨j,a⟩ hj ⟨k,b⟩ hk hne
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hj
  obtain ⟨hk,hb⟩ := Finset.mem_sigma.mp hk
  have hj' : j<R := (Finset.mem_Ico.mp hj).2
  have hk' : k<R := (Finset.mem_Ico.mp hk).2
  apply naturalTube_pair_disjoint (Nat.succ_pos j) (Nat.succ_pos k)
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 _ (by omega)
  intro he
  have ej : j=k := by have := congrArg Prod.fst he; simpa using this
  have ea : a=b := congrArg Prod.snd he
  exact hne (by subst k; subst b; rfl)

theorem naturalTubeUnion_inside_unit {B R M : ℕ} (hB : 0<B) (hM : 0<M) :
    naturalTubeUnion B R M ⊆ Icc 0 1 := by
  intro t ht
  obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hm,hcop⟩ := Finset.mem_filter.mp ha
  have hlo : B≤j := (Finset.mem_Ico.mp hj).1
  have haq : a<j+1 := Finset.mem_range.mp hm
  have ha' : 0<a := by
    by_contra! hz
    have h₀ : a=0 := by omega
    have h₁ : j+1=1 := by simpa [h₀] using hcop
    omega
  let q := j+1
  have hq : (0:ℝ)<q := by exact_mod_cast Nat.succ_pos j
  have hM' : (1:ℝ)≤M := by exact_mod_cast hM
  have hrad : naturalTubeRadius M q ≤ 1/(q:ℝ) :=
    one_div_le_one_div_of_le hq (by simpa using mul_le_mul_of_nonneg_left hM' hq.le)
  have hl : 1/(q:ℝ) ≤ (a:ℝ)/q := (div_le_div_iff_of_pos_right hq).mpr (by exact_mod_cast ha')
  have hu : (a:ℝ)/q+1/q ≤ 1 := by
    rw [← add_div,div_le_one hq]; exact_mod_cast (Nat.succ_le_of_lt haq)
  change t ∈ deepTube (naturalTubeRadius M q) q a at ht
  obtain ⟨h₁,h₂⟩ := ht
  exact ⟨by linarith,by linarith⟩

theorem naturalTubeUnion_outside_core {n B R M H : ℕ} (hn : 0<n) (hM : 0<M)
    (hg : (R:ℝ)*H/n + B/M < 1) :
    naturalTubeUnion B R M ⊆ (coreArcBand n H 0 B)ᶜ := by
  intro t ht hc
  obtain ⟨⟨j,a⟩,hi,ht⟩ := Set.mem_iUnion₂.mp ht
  obtain ⟨hj,ha⟩ := Finset.mem_sigma.mp hi
  let q := j+1
  have hq : 0<q := Nat.succ_pos j
  have hqB : B<q := Nat.lt_succ_of_le (Finset.mem_Ico.mp hj).1
  have hqR : q≤R := (Finset.mem_Ico.mp hj).2
  have ha' : a.Coprime q := (Finset.mem_filter.mp ha).2
  obtain ⟨r,b,hr,hrB,_,hb,hbw⟩ := hc
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hbnd : (q:ℝ)*H/n + r/M < 1 := lt_of_le_of_lt (by gcongr) hg
  have hsum : naturalTubeRadius M q + (H:ℝ)/(r*n) < 1/(q*r) := by
    unfold naturalTubeRadius
    calc _ = (((q:ℝ)*H/n + r/M)/(q*r)) := by field_simp; ring
         _ < _ := (div_lt_div_iff_of_pos_right (mul_pos hq' hr')).mpr hbnd
  have hdis := tubes_separate hq hr ha' hb (by intro he; have h := congrArg Prod.fst he; dsimp at h; omega) hsum
  apply Set.disjoint_left.mp hdis ht
  have ⟨hl,hu⟩ := abs_le.mp hbw
  exact ⟨by linarith,by linarith⟩

theorem naturalTube_eventual_budget :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := terminalPrimeArcCutoff n
      let M := naturalTubeScale n; let H := 256*B*medDeskQ n
      0<n ∧ 0<B ∧ 0<M ∧ 2*R<M ∧ (R:ℝ)*H/n+B/M<1 := by
  let t := fun n : ℕ => (n:ℝ)^(1/15:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/15)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_core_cutoffs,squareRootLogShell_geometry,eventually_ge_atTop (2:ℕ),
    ht.eventually_ge_atTop 256,hl.eventually_ge_atTop 1] with n hc hg hn ht' hl'
  let B := medDeskD n
  let R := terminalPrimeArcCutoff n
  let M := naturalTubeScale n
  let H := 256*B*medDeskQ n
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := Real.sqrt_nonneg (n:ℝ)
  have hB : 0<B := hg.1
  have hBR : B≤R := hg.2.1
  have hQ : medDeskQ n ≤ medDeskC n := hc.1.trans hc.2.1
  have hQr : (medDeskQ n:ℝ) ≤ (n:ℝ)^(1/10:ℝ) :=
    (show (medDeskQ n:ℝ)≤medDeskC n by exact_mod_cast hQ).trans (Nat.floor_le (by positivity))
  have hBr : (B:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hH : (H:ℝ) ≤ Real.sqrt n := by
    change ((256*B*medDeskQ n:ℕ):ℝ) ≤ _
    push_cast only [Nat.cast_mul,Nat.cast_ofNat]
    calc _ ≤ t n * (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/10:ℝ) := by gcongr
         _ = _ := by
           dsimp [t]
           rw [← Real.rpow_add hn',← Real.rpow_add hn',Real.sqrt_eq_rpow]
           norm_num
  have hMub : (M:ℝ) ≤ Real.sqrt n := Nat.floor_le hs
  have h4 : 4*R ≤ M := by
    apply Nat.le_floor
    push_cast
    let D := (1+Real.log (n:ℝ))^5
    have hD : (4:ℝ) ≤ D := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (show 2≤1+Real.log (n:ℝ) by linarith) 5
      dsimp [D]; norm_num at hh; linarith
    have hR : (R:ℝ) ≤ Real.sqrt n/D :=
      Nat.floor_le (div_nonneg hs (by linarith : 0≤D))
    calc 4*(R:ℝ) ≤ 4*(Real.sqrt n/D) := by gcongr
         _ = 4*Real.sqrt n/D := by ring
         _ ≤ Real.sqrt n := (div_le_iff₀ (by linarith : 0<D)).mpr (by
           simpa only [mul_comm] using mul_le_mul_of_nonneg_right hD hs)
  have hM : 0<M := by omega
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hR' : 4*(R:ℝ) ≤ Real.sqrt n := (show 4*(R:ℝ)≤M by exact_mod_cast h4).trans hMub
  have hsmall : (R:ℝ)*H/n ≤ 1/4 := by
    apply (div_le_iff₀ hn').mpr
    have hh := mul_le_mul hR' hH (Nat.cast_nonneg H) hs
    rw [Real.mul_self_sqrt hn'.le] at hh
    linarith only [hh]
  have hsmall' : (B:ℝ)/M ≤ 1/4 := by
    apply (div_le_iff₀ hM').mpr
    have hh : 4*B ≤ M := (Nat.mul_le_mul_left _ hBR).trans h4
    have hh' : 4*(B:ℝ)≤M := by exact_mod_cast hh
    linarith
  exact ⟨by omega,hB,hM,by omega,by linarith⟩

private theorem naturalDeepTube_mono {u v : ℝ} (q a : ℕ) (h : u≤v) :
    deepTube u q a ⊆ deepTube v q a :=
  Icc_subset_Icc (sub_le_sub_left h _) (add_le_add_right h _)

theorem naturalTube_pairwise_of_le {B R M : ℕ} (h : 2*R<M) (ρ : ℕ → ℝ)
    (hρ : ∀ j ∈ Finset.Ico B R, ρ (j+1) ≤ naturalTubeRadius M (j+1)) :
    (↑(naturalTubeIndices B R) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i k =>
      Disjoint (deepTube (ρ (i.1+1)) (i.1+1) i.2) (deepTube (ρ (k.1+1)) (k.1+1) k.2)) := by
  intro i hi k hk hne
  exact (naturalTube_pairwise h hi hk hne).mono
    (naturalDeepTube_mono _ _ (hρ _ (Finset.mem_sigma.mp hi).1))
    (naturalDeepTube_mono _ _ (hρ _ (Finset.mem_sigma.mp hk).1))

theorem naturalTube_union_of_le {B R M : ℕ} (ρ : ℕ → ℝ)
    (hρ : ∀ j ∈ Finset.Ico B R, ρ (j+1) ≤ naturalTubeRadius M (j+1)) :
    (⋃ i ∈ naturalTubeIndices B R, deepTube (ρ (i.1+1)) (i.1+1) i.2) ⊆ naturalTubeUnion B R M := by
  intro t ht
  obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp ht
  exact Set.mem_iUnion₂.mpr ⟨i,hi,naturalDeepTube_mono _ _ (hρ _ (Finset.mem_sigma.mp hi).1) hit⟩

theorem terminalNaturalTube_geometry :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := terminalPrimeArcCutoff n
      let M := naturalTubeScale n; let H := 256*B*medDeskQ n
      (↑(naturalTubeIndices B R) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i k =>
        Disjoint (deepTube (naturalTubeRadius M (i.1+1)) (i.1+1) i.2)
          (deepTube (naturalTubeRadius M (k.1+1)) (k.1+1) k.2)) ∧
      naturalTubeUnion B R M ⊆ Icc 0 1 ∧ naturalTubeUnion B R M ⊆ (coreArcBand n H 0 B)ᶜ := by
  filter_upwards [naturalTube_eventual_budget] with n h
  obtain ⟨hn,hB,hM,hsep,hcore⟩ := h
  exact ⟨naturalTube_pairwise hsep,naturalTubeUnion_inside_unit hB hM,naturalTubeUnion_outside_core hn hM hcore⟩
end
end GoldbachPartial

