import ResonantSmoothRankin
import ResonantCoprimeCoefficients
import SignedPrimeArcBounds
import PrimeArcModelBounds

namespace GoldbachPartial
open Finset Filter ExtendedArcCoefficient
open scoped Topology

theorem resonant_totient_ratio_le_rootEuler (q:ℕ) (hq:0<q) : (q:ℝ)/q.totient≤smoothRootEuler q := by
  have h := smoothReciprocal_hasSum q hq
  have g := smoothRoot_hasSum q
  rw [←h.tsum_eq,←g.tsum_eq]
  apply h.summable.tsum_le_tsum _ g.summable
  intro m
  have hn : 0< (m.val:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero m.property.1
  have h1 : (1:ℝ)≤m.val := by exact_mod_cast Nat.pos_of_ne_zero m.property.1
  apply inv_anti₀ (Real.sqrt_pos.mpr hn)
  nlinarith [Real.sq_sqrt hn.le,Real.sqrt_nonneg (m.val:ℝ),mul_nonneg (show 0≤(m.val:ℝ)-1 by linarith) hn.le]

private theorem resonant_grid_sum {M : Type*} [AddCommMonoid M] (q n:ℕ) (hq:0<q)
    (F:ℕ→ℕ→M) :
    (∑ k∈range (n+1), if k≠0 ∧ q∣k then F (k/q) k else 0) =
      ∑ j∈Icc 1 (n/q), F j (q*j) := by
  classical
  rw [←sum_filter]
  symm
  apply sum_bij (fun j _ => q*j)
  · intro j hj
    obtain ⟨hpos,hmax⟩ := mem_Icc.mp hj
    have hk := (Nat.le_div_iff_mul_le hq).mp hmax
    refine mem_filter.mpr ⟨mem_range.mpr (by rw [Nat.mul_comm]; omega), (Nat.mul_pos hq hpos).ne',dvd_mul_right ..⟩
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hq hij
  · intro k hk
    obtain ⟨hr,hk,j,rfl⟩ := mem_filter.mp hk
    have hpos : 0<j := by by_contra! h; simp [show j=0 by omega] at hk
    have hmax := mem_range.mp hr
    exact ⟨j,mem_Icc.mpr ⟨hpos,(Nat.le_div_iff_mul_le hq).mpr (by rw [Nat.mul_comm]; omega)⟩,rfl⟩
  · intro j _
    simp [Nat.mul_div_cancel_left _ hq]

set_option maxHeartbeats 700000 in
theorem resonantMobiusWave_geometric_of_prefix {n d q:ℕ} (hd:d<q) (β:ℝ) {D:ℝ}
    (hp:∀j≤n/q, |(∑k∈Icc 1 j,resonantReducedCoefficient q k)-
       (ArithmeticFunction.moebius q:ℝ)/q.totient*((q*j:ℕ):ℝ)| ≤ D) :
    ‖resonantMobiusWave n d n q β-
       (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*dirichletGeometricKernel n β‖ ≤
      (D+(q:ℝ)/q.totient)*(1+2*Real.pi*n*|β|) := by
  classical
  have hq : 0<q := by omega
  let A : ℝ := (ArithmeticFunction.moebius q:ℝ)/q.totient
  let c (k:ℕ) : ℝ := if k≠0 ∧ q∣k then resonantReducedCoefficient q (k/q) else 0
  have hμ : |(ArithmeticFunction.moebius q:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hA : |A|≤1/(q.totient:ℝ) := by
    rw [show |A|=|(ArithmeticFunction.moebius q:ℝ)|/(q.totient:ℝ) by simp [A,abs_div]]
    exact div_le_div_of_nonneg_right hμ (Nat.cast_nonneg _)
  have hpre (i:ℕ) (hi:i≤n) : ‖∑k∈range (i+1),((c k-A:ℝ):ℂ)‖ ≤D+(q:ℝ)/q.totient := by
    rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    change |(∑k∈range (i+1),if k≠0 ∧ q∣k then resonantReducedCoefficient q (k/q) else 0) - ((i+1:ℕ):ℝ)*A| ≤ _
    rw [resonant_grid_sum q i hq (fun j _=>resonantReducedCoefficient q j)]
    have h1 := hp (i/q) (Nat.div_le_div_right hi)
    have hr : ((i+1:ℕ):ℝ)=((q*(i/q):ℕ):ℝ)+(i%q+1:ℕ) := by
      exact_mod_cast (show i+1=q*(i/q)+(i%q+1) by have := Nat.mod_add_div i q; omega)
    have hrem : ((i%q+1:ℕ):ℝ)≤q := by exact_mod_cast Nat.mod_lt i hq
    rw [hr, show (∑ k∈Icc 1 (i/q),resonantReducedCoefficient q k)-
      (((q*(i/q):ℕ):ℝ)+(i%q+1:ℕ))*A =
      ((∑ k∈Icc 1 (i/q),resonantReducedCoefficient q k)-A*((q*(i/q):ℕ):ℝ))-
      A*((i%q+1:ℕ):ℝ) by ring]
    apply (abs_sub _ _).trans
    rw [abs_mul A,abs_of_nonneg (a:=((i%q+1:ℕ):ℝ)) (Nat.cast_nonneg _)]
    apply add_le_add h1
    calc
      _ ≤ (1/(q.totient:ℝ))*q := mul_le_mul hA hrem (by positivity) (by positivity)
      _ = _ := by ring
  have he := phase_sum_abel_of_prefix (fun k=>((c k-A:ℝ):ℂ)) n β (D+(q:ℝ)/q.totient) hpre
  have heq : (∑k∈range (n+1),((c k-A:ℝ):ℂ)*E ((k:ℝ)*β)) =
      resonantMobiusWave n d n q β-(A:ℂ)*dirichletGeometricKernel n β := by
    simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib]
    rw [resonantMobiusWave_reduced hd]
    apply congrArg₂ HSub.hSub
    · have h (k:ℕ) : (c k:ℂ)*E ((k:ℝ)*β)=if k≠0 ∧ q∣k then (resonantReducedCoefficient q (k/q):ℂ)*E ((k:ℝ)*β) else 0 := by
        by_cases h:k≠0 ∧ q∣k <;> simp [c,h]
      simp_rw [h]
      exact resonant_grid_sum q n hq (fun j k=>(resonantReducedCoefficient q j:ℂ)*E ((k:ℝ)*β))
    · rw [dirichletGeometricKernel,mul_sum]
  rwa [heq] at he

end GoldbachPartial