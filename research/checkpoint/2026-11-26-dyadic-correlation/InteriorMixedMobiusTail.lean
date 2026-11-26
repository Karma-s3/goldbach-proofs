import TrueMixedFrequencies
import DivisorCountFourth
import NearEndDivisorProduct

namespace GoldbachPartial
open Finset MeasureTheory Filter ExtendedArcCoefficient
open scoped Topology

noncomputable def mixedEndCutoff (n : ℕ) : ℕ := ⌊(n:ℝ)/(1+Real.log n)^26⌋₊

noncomputable def mixedEndFrequencies (n J : ℕ) : Finset ℕ :=
  Icc 1 J ∪ Ico (n-J) n

noncomputable def mixedInteriorFrequencies (n : ℕ) : Finset ℕ :=
  Icc 1 n \ (mixedEndFrequencies n (mixedEndCutoff n) ∪ {n})

private theorem endpoint_geometry :
    ∀ᶠ n : ℕ in atTop,let R := terminalPrimeArcCutoff n; let Q := naturalTubeScale n;let L := 1+Real.log (n:ℝ)
      0<Q ∧ ((Q:ℝ)≤n) ∧ Real.sqrt n≤2*(Q:ℝ) ∧ mixedEndCutoff n<n ∧
      (∀ D : ℕ, ∀ j∈Ico R Q,∀ β : ℝ,‖resonantMobiusWave n D n (j+1) β‖≤Real.sqrt n*L^7) := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hl,eventually_ge_atTop (1:ℕ)] with n hnlog hn
  let L := 1+Real.log n
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  change 1≤Real.log (n:ℝ) at hnlog
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hL2 : 2≤L := by dsimp [L]; linarith
  have hL : 0<L := by linarith
  have hQ : 0<Q := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hn')
  have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hfloor : Real.sqrt n<(Q:ℝ)+1 := Nat.lt_floor_add_one _
  have hroot : Real.sqrt n≤(n:ℝ) := by
    rw [Real.sqrt_eq_rpow];simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ)≤1)
  have hj : mixedEndCutoff n<n := by
    apply Nat.lt_of_not_ge
    intro h
    have hh : (n:ℝ)≤(mixedEndCutoff n:ℝ) := by exact_mod_cast h
    have hJ : (mixedEndCutoff n:ℝ)≤(n:ℝ)/L^26 := Nat.floor_le (by positivity)
    have hdiv := div_lt_self hn0 (one_lt_pow₀ (by linarith only [hL2] : 1<L) (by decide : 26≠0))
    exact (not_le.mpr hdiv) (hh.trans hJ)
  refine ⟨hQ,(Nat.floor_le (Real.sqrt_nonneg _)).trans hroot,by linarith only [hfloor,hQr],hj,?_⟩
  intro D j hmem β
  have hfloorR : Real.sqrt n/L^5<(R:ℝ)+1 := Nat.lt_floor_add_one _
  have hRj : (R:ℝ)+1≤((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (mem_Ico.mp hmem).1
  have hjr := (div_le_iff₀ (by positivity : 0<L^5)).mp (hfloorR.le.trans hRj)
  have hlog : Real.log n≤L := by dsimp [L];linarith
  apply (resonantMobiusWave_bound n D n (j+1) (by omega) β).trans
  apply (div_le_iff₀ (by positivity)).mpr
  change (n:ℝ)*Real.log n*L ≤ _
  calc
    _ ≤ (n:ℝ)*L*L := by gcongr
    _ = (Real.sqrt n*L^2)*Real.sqrt n := by nlinarith only [congrArg (fun x:ℝ => L^2*x) (Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n))]
    _ ≤ (Real.sqrt n*L^2)*(((j+1:ℕ):ℝ)*L^5) := mul_le_mul_of_nonneg_left hjr (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 900000 in
theorem trueMixedEndBand_eventually_bound :
    ∀ᶠ n : ℕ in atTop,∀ D : ℕ,
      ‖trueMixedFrequencyBand n D (terminalPrimeArcCutoff n) (naturalTubeScale n)
        (mixedEndFrequencies n (mixedEndCutoff n))‖ ≤ 6*(n:ℝ)/(1+Real.log n) := by
  filter_upwards [endpoint_geometry] with n hg
  intro D
  let L := 1+Real.log n
  let J := mixedEndCutoff n
  let Q := naturalTubeScale n
  let R := terminalPrimeArcCutoff n
  let B := Real.sqrt n*L^7
  obtain ⟨hQ,hQn,hroot,hJ,hT⟩ := hg
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hL1 : 1≤L := by dsimp [L];linarith [Real.log_natCast_nonneg n]
  have hL : 0<L := by linarith
  have hlog : Real.log n≤L := by dsimp [L];linarith
  have hlogQ : 1+Real.log Q≤L := add_le_add_right (Real.log_le_log hQ' hQn) _
  have he := trueMixedFrequencyBand_nearEnd_bound D R Q hJ (B:=B) (by dsimp[B];positivity) (hT D)
  have hcoeff : 4/(3*(Q:ℝ))*Real.log n*B*(1+Real.log Q) ≤ 3*L^9 := by
    dsimp only [B]
    change Real.sqrt n≤2*(Q:ℝ) at hroot
    calc
      _ ≤ 4/(3*(Q:ℝ))*L*((2*(Q:ℝ))*L^7)*L := by gcongr
      _ ≤ _ := by
        field_simp
        nlinarith only [mul_nonneg hQ'.le (pow_nonneg hL.le 9)]
  have hJbound : (J:ℝ)≤(n:ℝ)/L^26 := Nat.floor_le (by positivity)
  have hsqrt : Real.sqrt (J:ℝ)≤Real.sqrt n/L^13 := by
    have h := Real.sqrt_le_sqrt hJbound
    rw [Real.sqrt_div (by positivity),show L^26=(L^13)^2 by ring,Real.sqrt_sq (by positivity)] at h
    exact h
  apply he.trans
  calc
    _ ≤ (3*L^9)*(2*Real.sqrt n*Real.sqrt J*L^3) := by
      apply mul_le_mul_of_nonneg_right hcoeff
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (pow_nonneg hL.le 3)
    _ ≤ (3*L^9)*(2*Real.sqrt n*(Real.sqrt n/L^13)*L^3) := by gcongr
    _ = 6*(n:ℝ)/L := by field_simp;nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)]

theorem mixedZeroMode_eventually_bound :
    ∀ᶠ n : ℕ in atTop,∀ D : ℕ,
      ‖trueMixedFrequencyBand n D (terminalPrimeArcCutoff n) (naturalTubeScale n) {n}‖ ≤
        8192*(n:ℝ)/(1+Real.log n) := by
  let t := fun n : ℕ => (n:ℝ)^(1/64:ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/64)).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n/t n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/64)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [endpoint_geometry,eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop 4,
    hl.eventually (gt_mem_nhds zero_lt_one)] with n hg hn ht4 hl1
  intro D
  let L := 1+Real.log n
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let T := t n
  have hT4 : 4≤T := ht4
  have hT : 0<T := by linarith
  have hL : 0<L := by dsimp [L];positivity
  have hlog : Real.log n≤L := by dsimp [L];linarith
  have hL2T : L≤2*T := by
    change Real.log n/T<1 at hl1
    dsimp only [L]
    linarith [(div_lt_iff₀ hT).mp hl1]
  have hpow (k : ℕ) : T^k=(n:ℝ)^((1/64:ℝ)*k) := by
    dsimp only [T,t]; rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤(n:ℝ))]
  have h32 : T^32=Real.sqrt n := by rw [hpow,Real.sqrt_eq_rpow];norm_num
  have h64 : T^64=(n:ℝ) := by rw [hpow];norm_num
  have hτ : (n.divisors.card:ℝ)≤4096*T^16 := by
    apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by positivity)
    calc
      _ ≤ (2:ℝ)^48*(n:ℝ) := by exact_mod_cast divisor_count_fourth_le n
      _ = _ := by rw [←h64];ring
  have hL9 : L^9≤T^16 := calc
    _ ≤ (2*T)^9 := by gcongr
    _ ≤ T^7*T^9 := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (by norm_num : (2:ℝ)^9≤4^7).trans (pow_le_pow_left₀ (by norm_num) hT4 7)
    _ = _ := by ring
  obtain ⟨hQ,_,_,_,hTrow⟩ := hg
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have he := trueMixedFrequencyBand_zero_bound hn D R Q (B:=Real.sqrt n*L^7) (by positivity) (hTrow D)
  apply he.trans
  change _≤8192*(n:ℝ)/L
  apply (le_div_iff₀ hL).mpr
  calc
    _ = (4/3:ℝ)*(n.divisors.card:ℝ)*Real.sqrt n*Real.log n*L^8 := by field_simp
    _ ≤ (4/3:ℝ)*(n.divisors.card:ℝ)*Real.sqrt n*L^9 := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (show 0≤(4/3:ℝ)*(n.divisors.card:ℝ)*Real.sqrt n by positivity))
        (pow_nonneg hL.le 8)
      exact h.trans_eq (by ring)
    _ ≤ (4/3:ℝ)*(4096*T^16)*(T^32)*T^16 := by rw [h32];gcongr
    _ ≤ 8192*(n:ℝ) := by rw [←h64];nlinarith only [pow_nonneg hT.le 64]


/-- The frequencies discarded from the *true* mixed term consist of both end intervals
and the single zero phase k=n. The estimate is uniform over the large-divisor cutoff. -/
theorem trueMixedRemoved_eventually_bound :
    ∀ᶠ n : ℕ in atTop,∀ D : ℕ,let R := terminalPrimeArcCutoff n;let Q := naturalTubeScale n
      ‖trueMixedFrequencyBand n D R Q (Icc 1 n)-trueMixedFrequencyBand n D R Q (mixedInteriorFrequencies n)‖≤
        8198*(n:ℝ)/(1+Real.log n) := by
  filter_upwards [trueMixedEndBand_eventually_bound,mixedZeroMode_eventually_bound,endpoint_geometry,
    eventually_ge_atTop (1:ℕ)] with n hEnds hZero hg hn
  intro D
  let J := mixedEndCutoff n
  let I := mixedEndFrequencies n J
  let F := trueMixedFrequencyBand n D (terminalPrimeArcCutoff n) (naturalTubeScale n)
  have hJ : J<n := hg.2.2.2.1
  have hI : I⊆Icc 1 n := by
    intro k hk
    rcases mem_union.mp hk with hh|hh
    · obtain ⟨a,b⟩ := mem_Icc.mp hh;exact mem_Icc.mpr ⟨a,b.trans hJ.le⟩
    · obtain ⟨a,b⟩ := mem_Ico.mp hh
      change n-J≤k at a
      exact mem_Icc.mpr ⟨by omega,b.le⟩
  have hnI : n∉I := by
    intro h
    rcases mem_union.mp h with h|h
    · exact hJ.not_ge (mem_Icc.mp h).2
    · exact (lt_irrefl n) (mem_Ico.mp h).2
  have hu : I∪{n}⊆Icc 1 n := by
    apply union_subset hI
    exact singleton_subset_iff.mpr (mem_Icc.mpr ⟨hn,le_rfl⟩)
  have hs : F (Icc 1 n)-F (mixedInteriorFrequencies n)= F I+F {n} := by
    unfold F trueMixedFrequencyBand
    change _- (∑ k∈(Icc 1 n)\(I∪{n}),_) = _
    have he := sum_sdiff hu (f:=fun k => ∑ j∈Ico (terminalPrimeArcCutoff n) (naturalTubeScale n),
      trueMixedFrequencyRow n D (j+1) k (naturalTubeRadius (3*naturalTubeScale n) (j+1)))
    rw [sum_union (disjoint_singleton_right.mpr hnI)] at he
    linear_combination -he
  change ‖F (Icc 1 n)-F (mixedInteriorFrequencies n)‖≤_
  rw [hs]
  exact (norm_add_le ..).trans ((add_le_add (hEnds D) (hZero D)).trans_eq (by ring))

noncomputable def interiorMobiusTail (n : ℕ) : ℝ :=
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  primeArcMass ((Pinned316.GoldbachMajorArc.arcs n)ᶜ \ highNaturalPrimeTubes n) n +
    (nonresonantSquareMass n R R Q+trueMixedFrequencyBand n R R Q (mixedInteriorFrequencies n)).re

theorem interiorMobiusTail_minus_mixed :
    ∀ᶠ n : ℕ in atTop,|interiorMobiusTail n-mixedMobiusTail n| ≤ 8198*(n:ℝ)/(1+Real.log n) := by
  filter_upwards [trueMixedRemoved_eventually_bound] with n h
  let R := terminalPrimeArcCutoff n
  let Q := naturalTubeScale n
  let A := trueMixedFrequencyBand n R R Q (Icc 1 n)
  let B := trueMixedFrequencyBand n R R Q (mixedInteriorFrequencies n)
  have he : |(A-B).re|≤8198*(n:ℝ)/(1+Real.log n) := (Complex.abs_re_le_norm _).trans (h R)
  unfold interiorMobiusTail mixedMobiusTail
  dsimp only
  rw [trueMixedFrequencyBand_complete]
  simp only [Complex.add_re]
  change |(_+(_+B.re))-(_+(_+A.re))|≤_
  rw [show ∀ a b x y:ℝ,(a+(b+x))-(a+(b+y))=x-y from fun _ _ _ _ => by ring,abs_sub_comm]
  exact he

theorem interiorMobiusTail_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,|interiorMobiusTail n-mixedMobiusTail n|≤ ε*n := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (8198/ε)
  filter_upwards [interiorMobiusTail_minus_mixed,hl] with n h hn
  apply h.trans
  change 8198/ε≤Real.log (n:ℝ) at hn
  apply (div_le_iff₀ (by positivity : 0<1+Real.log (n:ℝ))).mpr
  have hz := (div_le_iff₀ hε).mp hn
  nlinarith only [mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (α:=ℝ) n),mul_nonneg hε.le (Nat.cast_nonneg (α:=ℝ) n)]

end GoldbachPartial