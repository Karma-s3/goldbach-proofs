import QuarterEndpointGeometry
import NaturalDirichletTubeGeometry

namespace GoldbachPartial
open Filter Set
open GoldbachDeepFourth (deepTube)
noncomputable section

theorem quarterEndpointStrips_inside_wide_core :
    ∀ᶠ n : ℕ in atTop, quarterEndpointStrips n ⊆
      coreArcBand n (256*medDeskD n*medDeskQ n) 0 (medDeskD n) := by
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (2:ℕ)] with n hg hn
  let B := medDeskD n
  let H := 256*B*medDeskQ n
  let u := (n:ℝ)^(1/4:ℝ)
  have hB : 0<B := hg.1
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hQ1 : 1 ≤ medDeskQ n := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have huH : u ≤ (H:ℝ) := by
    have huB : u ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow_of_exponent_le hn'.le (by norm_num)
    have hh := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (B:ℝ)+1 at hh
    have h₂ : B+1≤H := by
      have h := Nat.mul_le_mul_left (256*B) hQ1
      dsimp [H]
      omega
    exact huB.trans (hh.le.trans (by exact_mod_cast h₂))
  have hu := div_le_div_of_nonneg_right huH hn0.le
  have hQ0 : 0 ≤ (medDeskQ n:ℝ)/n := div_nonneg (Nat.cast_nonneg _) hn0.le
  intro t ht
  rcases ht with h|h
  · change (medDeskQ n:ℝ)/n < t ∧ t ≤ u/n at h
    refine ⟨1,0,by decide,hB,by decide,by decide,?_⟩
    simpa [H,B,abs_of_nonneg (hQ0.trans h.1.le)] using h.2.trans hu
  · change 1-u/n ≤ t ∧ t < 1-(medDeskQ n:ℝ)/n at h
    refine ⟨1,1,by decide,hB,by decide,by decide,?_⟩
    have hw : |t-1| ≤ (H:ℝ)/n := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    simpa [H,B] using hw

def naturalSubTubeUnion (B R : ℕ) (ρ : ℕ → ℝ) : Set ℝ :=
  ⋃ i ∈ naturalTubeIndices B R, deepTube (ρ (i.1+1)) (i.1+1) i.2

theorem terminal_subnatural_geometry :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := terminalPrimeArcCutoff n
      let M := naturalTubeScale n
      ∀ ρ : ℕ → ℝ, (∀ j ∈ Finset.Ico B R, ρ (j+1) ≤ naturalTubeRadius M (j+1)) →
        (↑(naturalTubeIndices B R) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i k =>
          Disjoint (deepTube (ρ (i.1+1)) (i.1+1) i.2) (deepTube (ρ (k.1+1)) (k.1+1) k.2)) ∧
        naturalSubTubeUnion B R ρ ⊆ Icc 0 1 ∧
        naturalSubTubeUnion B R ρ ⊆ (coreArcBand n (medDeskQ n) 0 B)ᶜ ∧
        Disjoint (naturalSubTubeUnion B R ρ) (quarterEndpointStrips n) := by
  filter_upwards [naturalTube_eventual_budget,terminalNaturalTube_geometry,
    quarterEndpointStrips_inside_wide_core] with n hb hg he
  obtain ⟨_,hB,_,hsep,_⟩ := hb
  dsimp only
  intro ρ hρ
  have hsub := naturalTube_union_of_le ρ hρ
  have hw := hsub.trans hg.2.2
  refine ⟨naturalTube_pairwise_of_le hsep ρ hρ,hsub.trans hg.2.1,?_,
    disjoint_left.mpr (fun _ ht ht' => hw ht (he ht'))⟩
  intro t ht hh
  apply hw ht
  obtain ⟨q,a,hq,hb,ha,hcop,hr⟩ := hh
  refine ⟨q,a,hq,hb,ha,hcop,hr.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show medDeskQ n ≤ 256*medDeskD n*medDeskQ n by
    have h₁ : 1 ≤ 256*medDeskD n := by omega
    simpa using Nat.mul_le_mul_right (medDeskQ n) h₁)

abbrev logFourDirichletRadius (n q : ℕ) : ℝ :=
  1/((q:ℝ)*Real.sqrt n*(terminalPrimeArcLog n)^4)

theorem logFourDirichletShell_geometry :
    ∀ᶠ n : ℕ in atTop, let B := medDeskD n; let R := terminalPrimeArcCutoff n
      let ρ := logFourDirichletRadius n
      (↑(naturalTubeIndices B R) : Set (Σ _ : ℕ, ℕ)).Pairwise (fun i k =>
        Disjoint (deepTube (ρ (i.1+1)) (i.1+1) i.2) (deepTube (ρ (k.1+1)) (k.1+1) k.2)) ∧
      naturalSubTubeUnion B R ρ ⊆ Icc 0 1 ∧
      naturalSubTubeUnion B R ρ ⊆ (coreArcBand n (medDeskQ n) 0 B)ᶜ ∧
      Disjoint (naturalSubTubeUnion B R ρ) (quarterEndpointStrips n) := by
  filter_upwards [terminal_subnatural_geometry,naturalTube_eventual_budget,
    eventually_ge_atTop (1:ℕ)] with n hg hb hn
  apply hg
  intro j _
  have hM : (0:ℝ)<naturalTubeScale n := by exact_mod_cast hb.2.2.1
  have hM' : (naturalTubeScale n:ℝ) ≤ Real.sqrt n := Nat.floor_le (Real.sqrt_nonneg _)
  have hL : 1 ≤ terminalPrimeArcLog n := by
    have := Real.log_nonneg (show 1≤(n:ℝ) by exact_mod_cast hn)
    dsimp only [terminalPrimeArcLog]; linarith
  have hL' : 1 ≤ (terminalPrimeArcLog n)^4 := one_le_pow₀ hL
  have hj : (0:ℝ) < ((j+1:ℕ):ℝ) := by positivity
  apply one_div_le_one_div_of_le (mul_pos hj hM)
  calc ((j+1:ℕ):ℝ)*naturalTubeScale n ≤ ((j+1:ℕ):ℝ)*Real.sqrt n :=
         mul_le_mul_of_nonneg_left hM' hj.le
       _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hj.le (Real.sqrt_nonneg _)) hL'
end
end GoldbachPartial

