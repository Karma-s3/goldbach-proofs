import VerifiedRoughP2BandBudget
import VerifiedBrunBandPowerLevel
import VerifiedRoughP2WeightedTransfer
namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

/-- At any exponent strictly between zero and one half, there is a nonempty
fixed interval of exponents whose prime factors account for at most ε times
the natural singular scale. Both the target and the rough cutoff are uniform. -/
theorem roughP2_power_band_removable {a ε : ℝ} (ha : 0<a) (ha' : a<1/2) (hε : 0<ε) :
    ∃ b : ℝ, a<b ∧ b<1/2 ∧ ∀ᶠ n : ℕ in atTop, Even n → ∀ z : ℕ, n≤z^11 →
      roughP2BandLogMass n z (movingPrimeBand n a b) ≤ ε*n*((n:ℝ)/n.totient) := by
  obtain ⟨B,haB,hB,K,hK,hKa,hKB⟩ := brunBand_select ha ha'
  have hKr : 0<(K:ℝ) := by exact_mod_cast (by omega : 0<K)
  let T := ε/(8*(K:ℝ))
  have hT : 0<T := by dsimp [T];positivity
  obtain ⟨b,hab,hbB,hmass⟩ := movingPrimeBand_arbitrarily_small ha haB hT
  refine ⟨b,hab,hbB.trans hB,?_⟩
  filter_upwards [hmass,brunBandLevel_geometry (show 0<K by omega),
    brunBandLevel_gap hK (hKa.le.trans (min_le_left ..)),brunBand_prefix_budget hK hKB (show 0<ε/4 by linarith),
    eventually_ge_atTop (2:ℕ)] with n hsum hg hg' hbud hn
  intro he z hz
  let y := brunBandLevel K n
  let w := movingPrimeCutoff n b
  let R := movingPrimeBand n a b
  have hR (r : ℕ) (hr : r∈R) : r.Prime ∧ y<r ∧ r≤w := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hr
    exact ⟨hp,hg'.1.trans_lt (mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2⟩
  obtain ⟨hd,hw⟩ := hbud b hbB.le
  have hh := roughP2BandLogMass_budget n z (brunBandIndex K n) w (2*K) R he hn (hg'.2 z hz) hg.2.2 hR
    (ε/4) T (by linarith) hT.le hsum hd hw
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp only [T]
  push_cast
  field_simp
  nlinarith only [mul_pos hKr hε]

theorem roughP2_sum_after_excision (n z : ℕ) (R : Finset ℕ) :
    (∑p∈reflectedP2Set n z \ roughP2MeetingBand n z R,Real.log p*Real.log (n-p:ℕ))+
      roughP2BandLogMass n z R = reflectedP2LogMass n z := by
  have hsub : roughP2MeetingBand n z R ⊆ reflectedP2Set n z := filter_subset ..
  exact sum_sdiff hsub

/-- A Chen-size count still leaves positive doubly weighted mass after
removing every candidate meeting a suitable prescribed band of prime sizes. -/
theorem roughP2_mass_outside_band_of_count (z : ℕ→ℕ) {a c : ℝ} (ha : 0<a) (ha' : a<1/2)
    (hc : 0<c) (hz : ∀ᶠ n:ℕ in atTop,n≤(z n)^11)
    (hcount : ∀ᶠ n:ℕ in atTop, Even n → c*((n:ℝ)/n.totient)*n/(Real.log n)^2 ≤ ((reflectedP2Set n (z n)).card:ℝ)) :
    ∃ b : ℝ, a<b ∧ b<1/2 ∧ ∀ᶠ n:ℕ in atTop, Even n →
      (c/16)*((n:ℝ)/n.totient)*n ≤
        ∑p∈reflectedP2Set n (z n) \ roughP2MeetingBand n (z n) (movingPrimeBand n a b),Real.log p*Real.log (n-p:ℕ) := by
  obtain ⟨b,hab,hb,hs⟩ := roughP2_power_band_removable ha ha' (show 0<c/16 by linarith)
  refine ⟨b,hab,hb,?_⟩
  filter_upwards [hs,hz,reflectedP2_weighted_mass_of_count z hc hcount] with n hs hz hm
  intro he
  have hsmall := hs he (z n) hz
  have heq := roughP2_sum_after_excision n (z n) (movingPrimeBand n a b)
  linarith only [hsmall,heq,hm he]

end GoldbachPartial