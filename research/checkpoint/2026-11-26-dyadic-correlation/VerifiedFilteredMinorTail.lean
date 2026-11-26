import VerifiedInteriorTailReduction
import NonresonantSquareShortModes

namespace GoldbachPartial
open Filter Pinned316.GoldbachMajorArc

/-- The high-arc square retains frequency zero and all sufficiently distant
frequencies. The true mixed term retains only its interior frequencies. -/
noncomputable def filteredMinorArcTail (n : ℕ) : ℝ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  primeArcMass ((arcs n)ᶜ \ highNaturalPrimeTubes n) n +
    (nonresonantSquareRetained n R R + trueMixedFrequencyBand n R R Q (mixedInteriorFrequencies n)).re

theorem filteredMinorArcTail_approx {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |corr n-(majorContribution n).re-filteredMinorArcTail n| ≤ ε*(n:ℝ) := by
  filter_upwards [corr_sub_major_interior_eventually_small (ε:=ε/2) (by positivity),
    nonresonantSquare_terminal_short_small (ε:=ε/2) (by positivity)] with n hi hs
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  have hd := (Complex.abs_re_le_norm (nonresonantSquareMass n R R Q - nonresonantSquareRetained n R R)).trans (hs R R)
  rw [Complex.sub_re] at hd
  have hid : interiorMobiusTail n-filteredMinorArcTail n =
      (nonresonantSquareMass n R R Q).re-(nonresonantSquareRetained n R R).re := by
    unfold interiorMobiusTail filteredMinorArcTail
    simp only [Complex.add_re];ring
  rw [←hid] at hd
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp hi).1,(abs_le.mp hd).1],
    by linarith only [(abs_le.mp hi).2,(abs_le.mp hd).2]⟩

/-- Any slope below 1/8 would follow from the indicated pointwise signed lower
bound on the remaining expression. -/
theorem dyadic_floor_of_filtered_minor_tail {c : ℝ} (hc : c<1/8)
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ) ≤ filteredMinorArcTail n) :
    ∃ N : ℕ, ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  let δ : ℝ := (1/8-c)/2
  have hd : 0<δ := by dsimp [δ];linarith
  have hM := GoldbachMajorArc.verified_major_floor_below_nine_eighths (9/8-δ) (by linarith)
  have hh : ∀ᶠ n : ℕ in atTop,Even n → c*n≤corr n := by
    filter_upwards [hM,htail,filteredMinorArcTail_approx hd] with n hm ht he
    intro hn
    have hi := (abs_le.mp he).1
    have hδ : c = 9/8-δ-1-δ := by dsimp [δ];ring
    rw [hδ]
    have hm' : (9/8-δ)*(n:ℝ)≤(majorContribution n).re := hm hn
    linarith only [hm',ht hn,hi]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  exact ⟨N,fun X n hX hXn _ he => hN n (hX.trans hXn) he⟩

theorem frozen_floor_of_filtered_minor_tail
    (htail : ∀ᶠ n : ℕ in atTop, Even n → -(n:ℝ) ≤ filteredMinorArcTail n) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N≤X → X≤n → n<2*X → Even n →
      let w : ℕ→ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0
      c*(n:ℝ)≤Finset.sum (Finset.range (n+1)) (fun p => w p*w (n-p)) := by
  obtain ⟨N,hN⟩ := dyadic_floor_of_filtered_minor_tail (c:=1/16) (by norm_num) htail
  exact ⟨1/16,N,by norm_num,hN⟩

end GoldbachPartial