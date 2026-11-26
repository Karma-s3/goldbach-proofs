import HalfPeriodWings
namespace GoldbachPartial
open Filter Set
open GoldbachDeepFourth (deepTube_cross deepTube_separation)

theorem logFourPrimeTubes_outside_wide_core :
    ∀ᶠ n : ℕ in atTop, logFourPrimeTubes n ⊆
      (coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n))ᶜ := by
  filter_upwards [terminalNaturalTube_geometry,naturalTube_eventual_budget,
    eventually_ge_atTop (1:ℕ)] with n hg hb hn
  apply Set.Subset.trans _ hg.2.2
  apply naturalTube_union_of_le
  intro j _
  have hM : (0:ℝ)<naturalTubeScale n := by exact_mod_cast hb.2.2.1
  have hM' : (naturalTubeScale n:ℝ) ≤ Real.sqrt n := Nat.floor_le (Real.sqrt_nonneg _)
  have hL : 1 ≤ terminalPrimeArcLog n := by
    have := Real.log_nonneg (show 1≤(n:ℝ) by exact_mod_cast hn)
    dsimp only [terminalPrimeArcLog]; linarith
  have hh : 1≤(terminalPrimeArcLog n)^4 := one_le_pow₀ hL
  have hj : (0:ℝ)<((j+1:ℕ):ℝ) := by positivity
  apply one_div_le_one_div_of_le (mul_pos hj hM)
  exact (mul_le_mul_of_nonneg_left hM' hj.le).trans
    (le_mul_of_one_le_right (mul_nonneg hj.le (Real.sqrt_nonneg _)) hh)

private theorem half_center_separation {n B Q : ℕ} {u t : ℝ} (hn : 0<n)
    (hu : 0≤u) (hsep : 2*(B:ℝ)*u+2*Q < n)
    (haway : (Q:ℝ)/n < |t-1/2|) (hclose : |t-1/2| ≤ u/n) :
    t ∉ coreArcBand n Q 0 B := by
  rintro ⟨q,a,hq,hqB,_,hcop,hwidth⟩
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  by_cases he : (2,1) = (q,a)
  · have hq₂ : 2=q := congrArg Prod.fst he
    have ha₁ : 1=a := congrArg Prod.snd he
    subst q; subst a
    have hr : (Q:ℝ)/(2*n) ≤ (Q:ℝ)/n :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn' (by linarith)
    norm_num at hwidth
    exact (not_lt_of_ge (hwidth.trans hr)) haway
  · have hd := deepTube_separation (q:=2) (r:=q) (a:=1) (b:=a) (by decide) hq
      (deepTube_cross (by decide) hq (by decide) hcop he)
    change 1/(2*(q:ℝ)) ≤ |1/2-(a:ℝ)/q| at hd
    have ha := abs_le.mp hwidth
    have hb := abs_le.mp hclose
    have hs : |1/2-(a:ℝ)/q| ≤ u/n+Q/(q*n) := abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩
    have hqr : (q:ℝ) ≤ B := by exact_mod_cast hqB
    have hnum : 2*(q:ℝ)*u+2*Q < n := lt_of_le_of_lt (by gcongr) hsep
    have hden : u/n+(Q:ℝ)/(q*n) < 1/(2*q) := by
      field_simp
      linarith only [hnum]
    exact (not_lt_of_ge (hd.trans hs)) hden

theorem halfPeriodWings_geometry :
    ∀ᶠ n : ℕ in atTop, halfPeriodWings n ⊆ Icc 0 1 ∧
      halfPeriodWings n ⊆ (((coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ logFourPrimeTubes n)
        \ quarterEndpointStrips n) ∧
      halfPeriodWings n ⊆ coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n) := by
  filter_upwards [eventually_core_cutoffs,squareRootLogShell_geometry,
    GoldbachDeepFourth.eventually_deep_fourth_budget,logFourPrimeTubes_outside_wide_core,
    eventually_ge_atTop (2:ℕ)] with n hc hg hmany ht hn
  let B := medDeskD n
  let Q := medDeskQ n
  let H := 256*B*Q
  let R := squareRootLogShellCutoff n
  let u := (n:ℝ)^(1/4:ℝ)
  let A := (Q:ℝ)/n
  let D := u/n
  have hB : 2 ≤ B := (by decide : 2≤192^4).trans hmany.2.1
  have hQ : Q≤B := hc.1.trans (hc.2.1.trans hc.2.2.1)
  have hQ1 : 1≤Q := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have hBR : B≤R := hg.2.1
  have hsep' : R*(H+B)<n := hg.2.2.2.2
  have hBH : B*(H+B)<n := lt_of_le_of_lt (Nat.mul_le_mul_right _ hBR) hsep'
  have hB' : (2:ℝ)≤B := by exact_mod_cast hB
  have hBH' : (B:ℝ)*(H+B)<n := by exact_mod_cast hBH
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0.le _
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) hn0.le
  have huH : 2*u ≤ (H:ℝ) := by
    have huB : u ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow_of_exponent_le hn'.le (by norm_num)
    have hh := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (B:ℝ)+1 at hh
    have h₂ : 2*(B+1)≤H := by
      have h := Nat.mul_le_mul_left (256*B) hQ1
      dsimp [H]
      omega
    have h₂' : 2*((B:ℝ)+1) ≤ H := by exact_mod_cast h₂
    linarith
  have hstrict : 2*(B:ℝ)*u+2*Q < n := by
    have h₁ := mul_le_mul_of_nonneg_left huH (Nat.cast_nonneg (α:=ℝ) B)
    have h₂ := mul_le_mul_of_nonneg_right hB' (Nat.cast_nonneg (α:=ℝ) B)
    have h₃ : (Q:ℝ) ≤ B := by exact_mod_cast hQ
    nlinarith only [h₁,h₂,h₃,hBH']
  have hD : D < 1/4 := by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [hstrict,mul_le_mul_of_nonneg_right hB' hu0,Nat.cast_nonneg (α:=ℝ) Q]
  have hwide : D ≤ (H:ℝ)/(2*n) := by
    dsimp only [D]
    apply (div_le_div_iff₀ hn0 (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right huH hn0.le]
  have hall {t : ℝ} (htw : t ∈ halfPeriodWings n) :
      t ∈ Icc 0 1 ∧ t ∉ coreArcBand n Q 0 B ∧
      t ∉ quarterEndpointStrips n ∧ t ∈ coreArcBand n H 0 B := by
    have habs : A < |t-1/2| ∧ |t-1/2| ≤ D := by
      rcases htw with h|h
      · change 1/2+A < t ∧ t ≤ 1/2+D at h
        rw [abs_of_nonneg (by linarith [h.1])]
        exact ⟨by linarith [h.1],by linarith [h.2]⟩
      · change 1/2-D ≤ t ∧ t < 1/2-A at h
        rw [abs_of_nonpos (by linarith [h.2])]
        exact ⟨by linarith [h.2],by linarith [h.1]⟩
    have hw := abs_le.mp habs.2
    refine ⟨⟨by linarith [hw.1],by linarith [hw.2]⟩,
      half_center_separation (by omega) hu0 hstrict habs.1 habs.2,?_,?_⟩
    · rintro (h|h)
      · change A<t ∧ t≤D at h
        linarith [hw.1,h.2]
      · change 1-D≤t ∧ t<1-A at h
        linarith [hw.2,h.1]
    · refine ⟨2,1,by decide,hB,by decide,by decide,?_⟩
      simpa only [Nat.cast_ofNat,Nat.cast_one] using habs.2.trans hwide
  refine ⟨fun _ h => (hall h).1,?_,fun _ h => (hall h).2.2.2⟩
  intro t h
  have hall' := hall h
  exact ⟨⟨hall'.2.1,fun hu => ht hu hall'.2.2.2⟩,hall'.2.2.1⟩

end GoldbachPartial
