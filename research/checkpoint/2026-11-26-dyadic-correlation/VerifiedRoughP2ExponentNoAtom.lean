import VerifiedRoughP2BandExcision
namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

/-- For a fixed interior exponent, a two-sided neighborhood of the exponent
has arbitrarily small weighted mass, uniformly in every sufficiently large
even target and every roughness cutoff z with z^11≥n. -/
theorem roughP2_two_sided_excision {a ε : ℝ} (ha : 0<a) (ha' : a<1/2) (hε : 0<ε) :
    ∃ h : ℝ, 0<h ∧ 0<a-h ∧ a+h<1/2 ∧ ∀ᶠ n : ℕ in atTop, Even n → ∀ z : ℕ, n≤z^11 →
      roughP2BandLogMass n z (movingPrimeBand n (a-h) (a+h)) ≤ ε*n*((n:ℝ)/n.totient) := by
  obtain ⟨B,haB,hB,K,hK,hKa,hKB⟩ := brunBand_select ha ha'
  have hKr : 0<(K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have hcut : 1/(K:ℝ)<a := hKa.trans_le (min_le_left ..)
  let T := ε/(8*(K:ℝ))
  have hT : 0<T := by dsimp [T];positivity
  have h4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  let h := min ((a-1/(K:ℝ))/2) (min ((B-a)/2) (a*T/(64*Real.log 4)))
  have hh : 0<h := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hleft : h≤(a-1/(K:ℝ))/2 := min_le_left .. 
  have hright : h≤(B-a)/2 := (min_le_right ..).trans (min_le_left ..)
  have hcost : h≤a*T/(64*Real.log 4) := (min_le_right ..).trans (min_le_right ..)
  have hhalf : a/2≤a-h := by linarith only [hleft,(one_div_pos.mpr hKr).le]
  have ha1 : 0<a-h := by linarith
  have ha2 : a-h<a+h := by linarith
  have hentry : 1/(K:ℝ)≤a-h := by linarith
  have hmax : a+h≤B := by linarith
  have hcost' := (le_div_iff₀ (by positivity : (0:ℝ)<64*Real.log 4)).mp hcost
  have hratio : 8*Real.log 4*(((a+h)-(a-h))/(a-h)) ≤ T := by
    rw [←mul_div_assoc,div_le_iff₀ ha1]
    nlinarith only [hcost',mul_le_mul_of_nonneg_left hhalf hT.le,mul_pos ha hT]
  refine ⟨h,hh,ha1,hmax.trans_lt hB,?_⟩
  filter_upwards [movingPrimeBand_weight_upper (a-h) (a+h) ha1 ha2,brunBandLevel_geometry (show 0<K by omega),
    brunBandLevel_gap hK hentry,brunBand_prefix_budget hK hKB (show 0<ε/4 by linarith),
    eventually_ge_atTop (2:ℕ)] with n hsum hg hg' hbud hn
  intro he z hz
  let y := brunBandLevel K n
  let w := movingPrimeCutoff n (a+h)
  let R := movingPrimeBand n (a-h) (a+h)
  have hR (r : ℕ) (hr : r∈R) : r.Prime ∧ y<r ∧ r≤w := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hr
    exact ⟨hp,hg'.1.trans_lt (mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2⟩
  obtain ⟨hd,hw⟩ := hbud (a+h) hmax
  have hg' := roughP2BandLogMass_budget n z (brunBandIndex K n) w (2*K) R he hn (hg'.2 z hz) hg.2.2 hR
    (ε/4) T (by linarith) hT.le (hsum.trans hratio) hd hw
  apply hg'.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp only [T]
  push_cast
  field_simp
  nlinarith only [mul_pos hKr hε]

theorem roughP2BandLogMass_mono (n z : ℕ) {R S : Finset ℕ} (h : R⊆S) :
    roughP2BandLogMass n z R ≤ roughP2BandLogMass n z S := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hC,r,hr,hd⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hC,r,h hr,hd⟩
  · intro p _ _
    exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _)

/-- A possibly target-dependent shrinking exponent band cannot carry a
positive proportion of the singularly normalized two-logarithm weight. -/
theorem roughP2_moving_exponent_no_atom {a : ℝ} (ha : 0<a) (ha' : a<1/2)
    (lo hi : ℕ→ℝ) (hlo : Tendsto lo atTop (𝓝 a)) (hhi : Tendsto hi atTop (𝓝 a)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, Even n → ∀ z:ℕ, n≤z^11 →
      roughP2BandLogMass n z (movingPrimeBand n (lo n) (hi n)) ≤ ε*n*((n:ℝ)/n.totient) := by
  intro ε hε
  obtain ⟨h,hh,_,_,hbound⟩ := roughP2_two_sided_excision ha ha' hε
  filter_upwards [hbound,hlo.eventually_const_lt (show a-h<a by linarith),
    hhi.eventually_lt_const (show a<a+h by linarith),eventually_ge_atTop (1:ℕ)] with n hs hlow hhigh hn
  intro he z hz
  apply le_trans _ (hs he z hz)
  apply roughP2BandLogMass_mono
  have hmono {u v:ℝ} (hu:u≤v) : movingPrimeCutoff n u≤movingPrimeCutoff n v :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hu)
  intro r hr
  obtain ⟨hi',hp⟩ := mem_filter.mp hr
  have hr' := mem_Ioc.mp hi'
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hmono hlow.le).trans_lt hr'.1,hr'.2.trans (hmono hhigh.le)⟩,hp⟩

end GoldbachPartial