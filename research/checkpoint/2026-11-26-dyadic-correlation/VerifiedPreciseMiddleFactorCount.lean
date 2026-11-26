import VerifiedPreciseBrunBounds
import VerifiedMiddleFactorCount
namespace GoldbachPartial
open Finset Filter
open scoped Classical
open private middle_survivor_model_floor from VerifiedMiddleFactorCount

theorem middle_excess_mass_strict {n y w B M : ℕ} (hw : 1≤w) (hwn : w≤n/4) (hB : n<w^(B+1)) :
    (M:ℝ) * fixedTargetExcessFactorMass n y (B+M-1) ≤ fixedTargetMarkedPrimeMass n y (middleBrunPrimes n y w) := by
  let T := ((fixedTargetBrunPrimeSurvivors n y).filter (fun k => Squarefree (n-k))).filter
    (fun k => ¬ ArithmeticFunction.cardFactors (n-k) ≤ B+M-1)
  let R := middleBrunPrimes n y w
  let S := fixedTargetBrunPrimeSurvivors n y
  rw [fixedTargetMarkedPrimeMass_by_complement]
  change (M:ℝ)*(∑ k∈T,Real.log k) ≤ ∑k∈S, ((R.filter (fun r => r∣n-k)).card:ℝ)*Real.log k
  rw [mul_sum]
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg
    (show T ⊆ S from (filter_subset ..).trans (filter_subset ..))
    (fun k _ _ => mul_nonneg (Nat.cast_nonneg (α:=ℝ) (R.filter (fun r => r∣n-k)).card) (Real.log_natCast_nonneg k)))
  apply sum_le_sum
  intro k hk
  obtain ⟨hh,hnf⟩ := mem_filter.mp hk
  obtain ⟨hs,hsf⟩ := mem_filter.mp hh
  have h := rough_middle_factor_count hs hsf hw hwn hB
  change ArithmeticFunction.cardFactors (n-k) ≤ B + (R.filter (fun r => r∣n-k)).card at h
  apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
  exact_mod_cast (show M ≤ (R.filter (fun r => r∣n-k)).card by omega)


theorem precise_factor_lower {n y w B M : ℕ} (hw : 1≤w) (hwn : w≤n/4)
    (hB : n<w^(B+1)) (hM : 1≤M) {P E A : ℝ} (hP : 0≤P)
    (hA : 1/1024+A ≤ (99/100:ℝ)*M)
    (hlow : (99/100:ℝ)*P-E ≤ fixedTargetBrunSurvivorMass n y)
    (hmarked : fixedTargetMarkedPrimeMass n y (middleBrunPrimes n y w) ≤ P*A+E)
    (herror : 4096*((M:ℝ)+1)*E ≤ P) (hsquare : 4096*(M:ℝ)*fixedTargetNonsquarefreeMass n y ≤ P) :
    P/(2048*M) ≤ ∑ k ∈ fixedTargetBoundedFactorPrimes n y (B+M-1), Real.log k := by
  let G := ∑ k ∈ fixedTargetBoundedFactorPrimes n y (B+M-1), Real.log k
  let F := fixedTargetExcessFactorMass n y (B+M-1)
  let S := fixedTargetNonsquarefreeMass n y
  have h := (middle_excess_mass_strict hw hwn hB (M:=M) (y:=y)).trans hmarked
  have hsplit := fixedTarget_boundedFactor_partition n y (B+M-1)
  have htotal := fixedTarget_squarefree_partition n y
  have hg : (99/100:ℝ)*P-E ≤ G+F+S := by rw [hsplit,htotal];exact hlow
  have hp := mul_le_mul_of_nonneg_right hA hP
  have hs := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) M)
  change (M:ℝ)*F ≤ _ at h
  change 4096*(M:ℝ)*S ≤ P at hsquare
  change P/(2048*M) ≤ G
  have hpos : (0:ℝ)<M := by exact_mod_cast hM
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2048) hpos)).mpr
  linarith only [hs,h,herror,hsquare,hp]


theorem precise_power_sieve_count (y w : ℕ → ℕ) (B M K : ℕ) (hM : 1≤M)
    (A : ℝ) (hA : 1/1024+A ≤ (99/100:ℝ)*M)
    (ht : Tendsto y atTop atTop)
    (hgeo : ∀ᶠ n : ℕ in atTop, 2≤y n ∧ y n≤w n ∧ w n≤n/4 ∧ n<(w n)^(B+1) ∧ n≤(y n)^K)
    (hsieve : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, Even n →
      let P := ((n/2-n/4:ℕ):ℝ) * ∏p∈fixedTargetBrunPrimes n (y n),(1-brunEulerWeight p)
      (99/100:ℝ)*P-ε*n/Real.log n≤fixedTargetBrunSurvivorMass n (y n) ∧
      fixedTargetMarkedPrimeMass n (y n) (middleBrunPrimes n (y n) (w n)) ≤
        P*A+ε*n/Real.log n) :
    ∀ᶠ n : ℕ in atTop, Even n →
      let S := fixedTargetBoundedFactorPrimes n (y n) (B+M-1)
      (n:ℝ)/(4194304*(M:ℝ)*Real.log n) ≤ ∑ k∈S,Real.log k ∧
      (n:ℝ)/(4194304*(M:ℝ)*(Real.log n)^2) ≤ (S.card:ℝ) := by
  let ε := 1/(8388608*((M:ℝ)+1))
  have hε : 0<ε := by dsimp [ε];positivity
  have hsq := rough_nonsquarefree_power_small y K ht
    (hgeo.mono (fun n h => ⟨h.2.1.trans h.2.2.1,h.2.2.2.2⟩)) hε
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hgeo,hsieve ε hε,hsq,eventually_ge_atTop (20:ℕ),hl.eventually_ge_atTop 1] with n hg hh hs hn hl'
  intro hev
  obtain ⟨hy,hyw,hwn,hbig,_⟩ := hg
  let P := ((n/2-n/4:ℕ):ℝ)*∏p∈fixedTargetBrunPrimes n (y n),(1-brunEulerWeight p)
  let L := Real.log (n:ℝ)
  have hL : 1≤L := hl'
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  have hw : 1≤w n := by omega
  have hP : (n:ℝ)/(2048*L) ≤ P := middle_survivor_model_floor n (y n) hn hev hy (hyw.trans hwn) hL
  have hval : 4096*((M:ℝ)+1)*(ε*(n:ℝ)/L) = (n:ℝ)/(2048*L) := by dsimp [ε];field_simp;ring
  have hbase : 4096*((M:ℝ)+1)*(ε*n/L) ≤ P := hval.le.trans hP
  have hbase' : 4096*(M:ℝ)*fixedTargetNonsquarefreeMass n (y n) ≤ P := by
    exact (mul_le_mul (by linarith : 4096*(M:ℝ)≤4096*((M:ℝ)+1)) hs
      (sum_nonneg fun k _ => Real.log_natCast_nonneg k) (by positivity)).trans hbase
  have hraw := precise_factor_lower hw hwn hbig hM ((by positivity : 0 ≤ (n:ℝ)/(2048*L)).trans hP)
    hA (hh hev).1 (hh hev).2 hbase hbase'
  let S := fixedTargetBoundedFactorPrimes n (y n) (B+M-1)
  have hg : (n:ℝ)/(4194304*(M:ℝ)*L) ≤ ∑k∈S,Real.log k := by
    refine le_trans ?_ ((div_le_div_of_nonneg_right hP (by positivity)).trans hraw)
    apply le_of_eq;field_simp;ring
  refine ⟨hg,?_⟩
  have hcard : (∑k∈S,Real.log k) ≤ (S.card:ℝ)*L := by
    calc _ ≤ ∑ _k∈S,L := by
            apply sum_le_sum
            intro k hk
            obtain ⟨_,hk',hp,-⟩ := (boundedFactorPrimes_iff n (y n) (B+M-1) k).mp hk
            exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show k≤n by omega))
         _ = _ := by simp
  change (n:ℝ)/(4194304*(M:ℝ)*L^2) ≤ _
  apply (div_le_iff₀ (by positivity)).mpr
  exact ((div_le_iff₀ (by positivity)).mp (hg.trans hcard)).trans_eq (by ring)

end GoldbachPartial