import NearRootShell

namespace GoldbachPartial
open Filter Set

noncomputable def quarterEndpointStrips (n : ℕ) : Set ℝ :=
  let a := (medDeskQ n : ℝ)/n
  let b := (n:ℝ)^(1/4:ℝ)/n
  Ioc a b ∪ Ico (1-b) (1-a)

private theorem endpoint_reflect_core {n W B : ℕ} {s : ℝ}
    (hs : s ∈ coreArcBand n W 0 B) : 1-s ∈ coreArcBand n W 0 B := by
  obtain ⟨q,a,hq,hB,ha,hcop,hw⟩ := hs
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨q,q-a,hq,hB,Nat.sub_le ..,(Nat.coprime_self_sub_left ha).mpr hcop,?_⟩
  rw [Nat.cast_sub ha, show 1-s-((q:ℝ)-a)/q = -(s-(a:ℝ)/q) by field_simp; ring, abs_neg]
  exact hw

private theorem endpoint_gap {n B Q H : ℕ} (hn : 0<n) (hB : 0<B) (hsep : B*H+Q<n)
    {t : ℝ} (ht : t ∈ Ioc ((Q:ℝ)/n) ((H:ℝ)/n)) :
    t ∈ Icc 0 1 ∧ t ∉ coreArcBand n Q 0 B ∧ t ∈ coreArcBand n H 0 B := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hn'.le).trans ht.1.le
  have hHb : H ≤ B*H := by simpa using Nat.mul_le_mul_right H hB
  have ht1 : t ≤ 1 := ht.2.trans ((div_le_one hn').mpr (by exact_mod_cast (show H≤n by omega)))
  refine ⟨⟨ht0,ht1⟩,?_,⟨1,0,by decide,hB,by decide,by decide,?_⟩⟩
  · rintro ⟨q,a,hq,hqB,_,hcop,hw⟩
    by_cases ha : a=0
    · subst a
      have he : q=1 := by simpa using hcop
      subst q
      have hh : t ≤ (Q:ℝ)/n := by simpa [abs_of_nonneg ht0] using hw
      exact (not_lt_of_ge hh) ht.1
    · have hq' : (0:ℝ)<q := by exact_mod_cast hq
      have ha' : (1:ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
      have hmul := mul_le_mul_of_nonneg_right (abs_le.mp hw).1 (mul_nonneg hq'.le hn'.le)
      have hlo : (a:ℝ)*n ≤ Q+t*n*q := by
        field_simp [hq'.ne',hn'.ne'] at hmul
        linarith only [hmul]
      have hup := (le_div_iff₀ hn').mp ht.2
      have h₁ := mul_le_mul_of_nonneg_right hup hq'.le
      have h₂ := mul_le_mul_of_nonneg_left (show (q:ℝ)≤B by exact_mod_cast hqB) (Nat.cast_nonneg H)
      have h₃ := mul_le_mul_of_nonneg_right ha' hn'.le
      have hs : (B:ℝ)*H+Q<n := by exact_mod_cast hsep
      nlinarith only [hlo,h₁,h₂,h₃,hs]
  · simpa [abs_of_nonneg ht0] using ht.2

/-- The intervals are nonempty. Each lies inside the integration interval and
in the remaining complement after both the frozen core and the near-root tubes. -/
theorem quarterEndpointStrips_geometry :
    ∀ᶠ n : ℕ in atTop,
      (medDeskQ n : ℝ)/n < (n:ℝ)^(1/4:ℝ)/n ∧
      quarterEndpointStrips n ⊆ Icc 0 1 ∧
      quarterEndpointStrips n ⊆ (coreArcBand n (medDeskQ n) 0 (medDeskD n))ᶜ \ nearRootTubes n := by
  filter_upwards [eventually_core_cutoffs,squareRootLogShell_geometry,
    nearRootTubes_geometry,eventually_ge_atTop (2:ℕ)] with n hc hg ht hn
  let B := medDeskD n
  let Q := medDeskQ n
  let H := 256*B*Q
  let R := squareRootLogShellCutoff n
  let u := (n:ℝ)^(1/4:ℝ)
  obtain ⟨hb,hr,_,_,hsp⟩ := hg
  have hsep' : R*(H+B)<n := hsp
  have hQ : Q≤B := hc.1.trans (hc.2.1.trans hc.2.2.1)
  have hR : 1 ≤ R := hb.trans_le hr
  have hsep : B*H+Q<n := by
    have hm := Nat.mul_le_mul_right H hr
    have hm' := Nat.mul_le_mul_right B hR
    nlinarith only [hm,hm',hQ,hsep']
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hQ1 : 1≤Q := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have huH : u ≤ (H:ℝ) := by
    have huB : u ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow_of_exponent_le hn'.le (by norm_num)
    have hh := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (B:ℝ)+1 at hh
    have htwo : B+1 ≤ H := by
      have h := Nat.mul_le_mul_left (256*B) hQ1
      dsimp [H]
      omega
    have htwo' : (B:ℝ)+1 ≤ H := by exact_mod_cast htwo
    exact huB.trans (hh.le.trans htwo')
  have hQu : (Q:ℝ)<u := by
    have hQC : Q ≤ medDeskC n := hc.1.trans hc.2.1
    have hh : (Q:ℝ) ≤ medDeskC n := by exact_mod_cast hQC
    exact (hh.trans (Nat.floor_le (by positivity))).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hn' (by norm_num : (1/10:ℝ)<1/4))
  have hgap {t : ℝ} (h : t ∈ Ioc ((Q:ℝ)/n) (u/n)) :
      t ∈ Icc 0 1 ∧ t ∉ coreArcBand n Q 0 B ∧ t ∈ coreArcBand n H 0 B :=
    endpoint_gap (by omega) hb hsep ⟨h.1,h.2.trans (div_le_div_of_nonneg_right huH hn0.le)⟩
  have hboth {t : ℝ} (h : t ∈ quarterEndpointStrips n) :
      t ∈ Icc 0 1 ∧ t ∉ coreArcBand n Q 0 B ∧ t ∈ coreArcBand n H 0 B := by
    rcases h with h|h
    · exact hgap h
    · change 1-u/n ≤ t ∧ t < 1-(Q:ℝ)/n at h
      obtain ⟨hw,hs,hg⟩ := hgap (t:=1-t) ⟨by linarith [h.2],by linarith [h.1]⟩
      have hi := endpoint_reflect_core hg
      rw [sub_sub_cancel] at hi
      exact ⟨⟨by linarith [hw.2],by linarith [hw.1]⟩,fun hm => hs (endpoint_reflect_core hm),hi⟩
  refine ⟨(div_lt_div_iff_of_pos_right hn0).mpr hQu,fun _ h => (hboth h).1,?_⟩
  intro t h
  have hw := hboth h
  exact ⟨hw.2.1,fun hmem => ht.2.1 hmem hw.2.2⟩
end GoldbachPartial
