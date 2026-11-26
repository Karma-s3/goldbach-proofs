import VerifiedRoughP2SingularUpper

namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

/-- Only endpoints below √n cause a loss when a rough P₂ count is turned into
a lower bound for its two logarithmic weights. -/
theorem reflectedP2_count_log_comparison (n z : ℕ) (hn : 0<n) :
    ((reflectedP2Set n z).card:ℝ)*(Real.log n)^2 ≤
      4*reflectedP2LogMass n z+2*(n.sqrt+1:ℕ)*(Real.log n)^2 := by
  let C := reflectedP2Set n z
  let G := C.filter (fun p => n≤p^2 ∧ n≤(n-p)^2)
  let U := C.filter (fun p => ¬(n≤p^2 ∧ n≤(n-p)^2))
  let I := range (n.sqrt+1)
  let T := C.filter (fun p => n-p∈I)
  let L := Real.log n
  let F := fun p : ℕ => Real.log p*Real.log (n-p:ℕ)
  have hcard : G.card+U.card=C.card := card_filter_add_card_filter_not _
  have hsmall {k : ℕ} (hk : k^2<n) : k∈I := mem_range_succ_iff.mpr (Nat.le_sqrt'.mpr hk.le)
  have hU : U⊆I∪T := by
    intro p hp
    obtain ⟨hpC,hp'⟩ := mem_filter.mp hp
    by_cases hh : n≤p^2
    · exact mem_union_right _ (mem_filter.mpr ⟨hpC,hsmall (lt_of_not_ge (fun h => hp' ⟨hh,h⟩))⟩)
    · exact mem_union_left _ (hsmall (lt_of_not_ge hh))
  have hpn {p : ℕ} (hp : p∈T) : p≤n := mem_range_succ_iff.mp (mem_filter.mp (mem_filter.mp hp).1).1
  have hT : T.card≤I.card := card_le_card_of_injOn (fun p=>n-p) (fun p hp => (mem_filter.mp hp).2)
    (by intro p hp q hq hh;dsimp at hh;have := hpn hp;have := hpn hq;omega)
  have hUcard : U.card≤2*(n.sqrt+1) := by
    have h := (card_le_card hU).trans (card_union_le ..)
    have hI : I.card=n.sqrt+1 := card_range _
    omega
  have hlog {k : ℕ} (h : n≤k^2) : L≤2*Real.log k := by
    have hh := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast hn) (by exact_mod_cast h : (n:ℝ)≤(k:ℝ)^2)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hsum : (G.card:ℝ)*L^2≤4*reflectedP2LogMass n z := by
    calc _ = ∑_p∈G,L^2 := by simp
         _ ≤ ∑p∈G,4*F p := by
           apply sum_le_sum
           intro p hp
           obtain ⟨_,h1,h2⟩ := mem_filter.mp hp
           have hh := mul_le_mul (hlog h1) (hlog h2) (Real.log_natCast_nonneg n)
             (show 0≤2*Real.log (p:ℝ) by positivity)
           dsimp only [F]
           linarith only [hh]
         _ ≤ ∑p∈C,4*F p := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
             (fun p _ _=>by dsimp [F];positivity)
         _ = _ := (mul_sum ..).symm
  have hU' : (U.card:ℝ) ≤ 2*(n.sqrt+1:ℕ) := by exact_mod_cast hUcard
  have hc' : (G.card:ℝ)+U.card=C.card := by exact_mod_cast hcard
  change (C.card:ℝ)*L^2≤_
  linarith only [hsum,mul_le_mul_of_nonneg_right hU' (sq_nonneg L),
    congrArg (·*L^2) hc']

theorem reflectedP2_weighted_mass_of_count (z : ℕ→ℕ) {c : ℝ} (hc : 0<c)
    (hcount : ∀ᶠ n:ℕ in atTop, Even n → c*((n:ℝ)/n.totient)*n/(Real.log n)^2 ≤ ((reflectedP2Set n (z n)).card:ℝ)) :
    ∀ᶠ n:ℕ in atTop, Even n → (c/8)*((n:ℝ)/n.totient)*n ≤ reflectedP2LogMass n (z n) := by
  have hroot : ∀ᶠ n:ℕ in atTop,(n.sqrt:ℝ)≤Real.sqrt n := Eventually.of_forall (fun n =>
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n))
  filter_upwards [hcount,reflectedP2_cutoff_small Nat.sqrt hroot (c/4) (by linarith),eventually_ge_atTop (2:ℕ)] with n hH hE hn
  intro he
  have hn0 : 0<n := by omega
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn0
  have hlog : 0<Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hR : 1≤(n:ℝ)/n.totient := (one_le_div (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr (by exact_mod_cast Nat.totient_le n)
  have hr : 1≤n.sqrt := Nat.le_sqrt'.mpr (by omega)
  have hs : 2*((n.sqrt+1:ℕ):ℝ)≤4*(n.sqrt:ℝ) := by exact_mod_cast (show 2*(n.sqrt+1)≤4*n.sqrt by omega)
  have hh := (div_le_iff₀ (sq_pos_of_pos hlog)).mp (hH he)
  have hw := reflectedP2_count_log_comparison n (z n) hn0
  have hmul := mul_le_mul_of_nonneg_left hR (mul_nonneg hc.le hn'.le)
  linarith only [hh,hw,hE,hmul,mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.log (n:ℝ)))]

/-- A fixed fractional saving in the signed rough P₂ mass, together with a
Chen-size lower count, suffices for the original pointwise binary floor. -/
theorem dyadic_floor_of_roughP2_count_and_bias (z : ℕ→ℕ) {c η : ℝ} (hc : 0<c) (hη : 0<η)
    (hcount : ∀ᶠ n:ℕ in atTop, Even n → c*((n:ℝ)/n.totient)*n/(Real.log n)^2 ≤ ((reflectedP2Set n (z n)).card:ℝ))
    (hbias : ∀ᶠ n:ℕ in atTop, Even n → reflectedP2ParityMass n (z n) ≤ (1-η)*reflectedP2LogMass n (z n)) :
    ∃ (c' : ℝ) (N : ℕ),0<c' ∧ ∀ X n:ℕ,N≤X → X≤n → n<2*X → Even n → c'*n≤corr n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((reflectedP2_weighted_mass_of_count z hc hcount).and hbias)
  refine ⟨η*c/16,max N 1,by positivity,?_⟩
  intro X n hX hn _ he
  have hN' := (le_max_left ..).trans (hX.trans hn)
  have hn0 : 0<n := (le_max_right N 1).trans (hX.trans hn)
  have hm := (hN n hN').1 he
  have hs := (hN n hN').2 he
  have hR : 1≤(n:ℝ)/n.totient := (one_le_div (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr (by exact_mod_cast Nat.totient_le n)
  have hbase : (c/8)*(n:ℝ) ≤ reflectedP2LogMass n (z n) := by
    apply le_trans _ hm
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hR) (Nat.cast_nonneg _)
  have hcorr := (reflectedP2_parity_cutoff n (z n)).1
  linarith only [hcorr,hs,mul_le_mul_of_nonneg_left hbase hη.le]

end GoldbachPartial