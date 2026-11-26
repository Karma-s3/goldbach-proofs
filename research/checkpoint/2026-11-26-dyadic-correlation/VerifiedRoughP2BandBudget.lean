import VerifiedRoughP2MarkedPrefix
import VerifiedMovingPrimeBands
namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology

noncomputable def roughP2MeetingBand (n z : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (reflectedP2Set n z).filter (fun p=>∃ r∈R,r∣n-p)

noncomputable def roughP2BandLogMass (n z : ℕ) (R : Finset ℕ) : ℝ :=
  ∑p∈roughP2MeetingBand n z R,Real.log p*Real.log (n-p:ℕ)

theorem roughP2BandLogMass_le_marked (n z : ℕ) (R : Finset ℕ) :
    roughP2BandLogMass n z R ≤ roughP2MarkedLogMass n z R := by
  let C := reflectedP2Set n z
  let F := fun p : ℕ => Real.log p*Real.log (n-p:ℕ)
  change (∑p∈C.filter (fun p=>∃r∈R,r∣n-p),F p) ≤ ∑r∈R,∑p∈C.filter (fun p=>r∣n-p),F p
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro p _
  have hnon : 0≤F p := by dsimp [F];positivity
  by_cases h : ∃r∈R,r∣n-p
  · rw [ite_eq_left h]
    obtain ⟨r,hr,hd⟩ := h
    exact (show F p = (if r∣n-p then F p else 0) by rw [ite_eq_left hd]).le.trans
      (single_le_sum (f:=fun r=>if r∣n-p then F p else 0) (fun i _=>by split <;> positivity) hr)
  · rw [ite_eq_right h]
    exact sum_nonneg (fun i _=>by split <;> positivity)

theorem roughP2BandLogMass_budget (n z J w K : ℕ) (R : Finset ℕ) (he : Even n) (hn : 2≤n)
    (hz : brunBlockBoundary J<z) (hscale : n≤(brunBlockBoundary J)^K)
    (hR : ∀r∈R,r.Prime ∧ brunBlockBoundary J<r ∧ r≤w)
    (ε T : ℝ) (hε : 0<ε) (hT : 0≤T)
    (hweights : (∑r∈R,brunEulerWeight r)≤T)
    (herr : (∑d∈Icc 1 (w*(brunBlockBoundary J)^29),brunPrimePrefixMaxError n d) ≤ ε*n/Real.log n)
    (hw : (w:ℝ)*(Real.log n)^2≤ε*n) :
    roughP2BandLogMass n z R ≤ ((8/7:ℝ)*K*T+2*ε)*n*((n:ℝ)/n.totient) := by
  let y := brunBlockBoundary J
  let u := (n:ℝ)/n.totient
  let L := Real.log n
  let l := Real.log ((y:ℝ)+1)
  have hn0 : 0<n := by omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn0
  have hu : 1≤u := (one_le_div (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr (by exact_mod_cast Nat.totient_le n)
  have hu0 := zero_le_one.trans hu
  have hy : 2≤y := brunBlockBoundary_mono (Nat.zero_le J)
  have hy' : 0<(y:ℝ) := by exact_mod_cast (by omega : 0<y)
  have hl : 0<l := Real.log_pos (by linarith only [hy'])
  have hLp : 0<L := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlog := Real.log_le_log hn' (by exact_mod_cast hscale : (n:ℝ)≤(y:ℝ)^K)
  rw [Real.log_pow] at hlog
  have hlk : L/l≤K := by
    apply (div_le_iff₀ hl).mpr
    exact hlog.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hy' (by linarith : (y:ℝ)≤(y:ℝ)+1)) (Nat.cast_nonneg _))
  let P := ∏p∈fixedTargetBrunPrimes n y,(1-brunEulerWeight p)
  have hprod : P≤u/l := fixedTarget_brunEuler_singular_upper n y hn0 (by omega)
  have hwt0 : 0≤∑r∈R,brunEulerWeight r := by
    apply sum_nonneg
    intro r hr
    unfold brunEulerWeight
    exact one_div_nonneg.mpr (by have h := (by exact_mod_cast (hR r hr).1.one_le : (1:ℝ)≤r);linarith)
  have hmain :
      L*((8/7:ℝ)*n*P*(∑r∈R,brunEulerWeight r)) ≤ (8/7:ℝ)*K*T*n*u := by
    calc _ ≤ L*((8/7:ℝ)*n*(u/l)*T) := mul_le_mul_of_nonneg_left
                (mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hweights hwt0 (by positivity)) hLp.le
         _ = ((8/7:ℝ)*n*u*T)*(L/l) := by ring
         _ ≤ ((8/7:ℝ)*n*u*T)*K := mul_le_mul_of_nonneg_left hlk (by positivity)
         _ = _ := by ring
  have he1 := mul_le_mul_of_nonneg_left herr hLp.le
  have he2 : L*(ε*n/L)=ε*n := by field_simp
  have hu1 := le_mul_of_one_le_right (mul_nonneg hε.le hn'.le) hu
  apply (roughP2BandLogMass_le_marked n z R).trans ((roughP2MarkedLogMass_upper n z J w R he hz hR).trans _)
  change L*((8/7:ℝ)*n*P*(∑r∈R,brunEulerWeight r)+_) + _ ≤ _
  linarith only [hmain,he1,he2,hw,hu1]

end GoldbachPartial