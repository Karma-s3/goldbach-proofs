import CenteredDistantPrimeMass

namespace GoldbachPartial
open Finset Filter MeasureTheory

private theorem totient_even_at_most_half (m : ℕ) : (2*m).totient≤m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m=0
    · simp [hm]
    by_cases he : Even m
    · rw [Nat.totient_two_mul_of_even he]
      obtain ⟨j,hj⟩ := he
      have hjm : m=2*j := by omega
      have hh := ih j (by omega)
      rw [hjm];omega
    · rw [Nat.totient_two_mul_of_odd (Nat.not_even_iff_odd.mp he)]
      exact Nat.totient_le _

theorem high_natural_volume_le_half {R Q : ℕ} (hR : 0<R) (hQ : 0<Q) :
    volume.real (naturalTubeUnion R Q (3*Q)) ≤ 1/2 := by
  let f := fun j : ℕ => ((j+1).totient:ℝ)/((j+1:ℕ):ℝ)
  have h1 (j : ℕ) : f j≤1 := by
    apply (div_le_one (by positivity)).mpr;exact_mod_cast Nat.totient_le (j+1)
  have h2 (i : ℕ) : f (2*i+1)≤1/2 := by
    have he : 2*i+1+1=2*(i+1) := by omega
    dsimp only [f];rw [he]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<2)).mpr
    rw [one_mul]
    exact_mod_cast (show (2*(i+1)).totient*2≤2*(i+1) by linarith only [totient_even_at_most_half (i+1)])
  have hp (i : ℕ) : (∑ j∈Ico 1 (2*i+1),f j) ≤ (3/2:ℝ)*i := by
    induction i with
    | zero => norm_num
    | succ i ih =>
      rw [show 2*(i+1)+1=(2*i+1)+1+1 by omega,sum_Ico_succ_top (by omega),sum_Ico_succ_top (by omega)]
      push_cast
      linarith only [ih,h2 i,h1 (2*i+1+1)]
  have hsub : Ico R Q⊆Ico 1 (2*(Q/2)+1) := by
    intro j hj
    obtain ⟨hl,hu⟩ := mem_Ico.mp hj
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hmax := (sum_le_sum_of_subset_of_nonneg (f:=f) hsub (fun j _ _ => by dsimp [f];positivity)).trans (hp (Q/2))
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hh : (2:ℝ)*((Q/2:ℕ):ℝ)≤Q := by exact_mod_cast (show 2*(Q/2)≤Q by omega)
  rw [naturalTubeUnion_realVolume_eq R Q (3*Q) (by omega)]
  change 2/((3*Q:ℕ):ℝ)*(∑j∈Ico R Q,f j)≤_
  push_cast
  field_simp
  linarith only [hmax,hh]

theorem high_tube_volume_eventually_half :
    ∀ᶠ n : ℕ in atTop, volume.real (highNaturalPrimeTubes n)≤1/2 := by
  filter_upwards [squareRootLogShell_geometry,eventually_ge_atTop (1:ℕ)] with n hg hn
  have hQ : 0<naturalTubeScale n := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr (by exact_mod_cast hn : (1:ℝ)≤n))
  exact high_natural_volume_le_half (hg.1.trans_le hg.2.1) hQ

end GoldbachPartial