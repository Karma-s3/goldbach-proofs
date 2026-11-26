import VerifiedMinorArcVaughanTypeI
import QuarterEndpointWing
import MangoldtPrimePrefix

namespace GoldbachPartial
open Finset ExtendedArcCoefficient
open scoped ArithmeticFunction.vonMangoldt

theorem minorArc_dyadic_sum {A : Type*} [AddCommMonoid A] (k : ℕ) (f : ℕ→A) :
    (∑m∈Ico 1 (2^k),f m) = ∑i∈range k,∑m∈range (2^i),f (2^i+m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,←ih,←sum_Ico_consecutive f (Nat.two_pow_pos k) (by rw [pow_succ];omega : 2^k≤2^(k+1))]
    congr 1
    rw [sum_Ico_eq_sum_range,show 2^(k+1)-2^k=2^k by rw [pow_succ];omega]

theorem vaughan_additive_typeII_blocks (X U V : ℕ) (α : ℝ) :
    vaughanAdditiveBilinear X (vaughanTypeIICoefficient U) (vaughanTail V Λ) α =
      ∑i∈range (Nat.log 2 X+1),∑j∈range (Nat.log 2 X+1),
        vaughanMinorArcTypeIIBlock X U V (2^i) (2^j) α := by
  let k := Nat.log 2 X+1
  let Z := 2^k
  have hZ : X<Z := Nat.lt_pow_succ_log_self (by decide : 1<2) X
  let f := fun d j : ℕ => (if V<j then vaughanActualRight j else 0)*
    (if d*j≤X then E (((d*j:ℕ):ℝ)*α) else 0)
  have hinner (d : ℕ) (hd : 0<d) :
      (∑j∈Icc 1 (X/d),((vaughanTail V Λ j):ℂ)*E ((j:ℝ)*((d:ℝ)*α))) =
        ∑j∈Ico 1 Z,f d j := by
    have hsub : Icc 1 (X/d)⊆Ico 1 Z := fun j hj=>mem_Ico.mpr
      ⟨(mem_Icc.mp hj).1,((mem_Icc.mp hj).2.trans (Nat.div_le_self ..)).trans_lt hZ⟩
    apply Eq.trans _ (sum_subset hsub ?_)
    · apply sum_congr rfl;intro j hj
      have h := (Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp hj).2
      dsimp only [f,vaughanActualRight]
      rw [ite_eq_left (show d*j≤X by simpa [Nat.mul_comm] using h),vaughanTail_apply]
      push_cast
      by_cases hV : V<j
      · simp [hV];ring_nf;simp
      · simp [hV]
    · intro j hj hno
      have h : ¬d*j≤X := fun hl=>hno (mem_Icc.mpr ⟨(mem_Ico.mp hj).1,(Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hl)⟩)
      simp [f,h]
  have hpad : vaughanAdditiveBilinear X (vaughanTypeIICoefficient U) (vaughanTail V Λ) α =
      ∑d∈Ico 1 Z,vaughanActualLeft U d*∑j∈Ico 1 Z,f d j := by
    have hsub : Icc 1 X⊆Ico 1 Z := fun d hd=>mem_Ico.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans_lt hZ⟩
    apply Eq.trans _ (sum_subset hsub ?_)
    · apply sum_congr rfl;intro d hd
      rw [←hinner d (mem_Icc.mp hd).1]
      rfl
    · intro d hd hno
      have hbig : X<d := by by_contra! h;exact hno (mem_Icc.mpr ⟨(mem_Ico.mp hd).1,h⟩)
      rw [sum_eq_zero (fun j hj=>?_ : ∀j∈_,f d j=0),mul_zero]
      have hj0 := (mem_Ico.mp hj).1
      have h := hbig.trans_le (Nat.le_mul_of_pos_right d hj0)
      simp [f,h.not_ge]
  rw [hpad,minorArc_dyadic_sum k]
  apply sum_congr rfl;intro i _
  have hh (d:ℕ) : (∑j∈Ico 1 Z,f d j)=∑t∈range k,∑j∈range (2^t),f d (2^t+j) := minorArc_dyadic_sum k _
  simp_rw [hh,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl;intro j _
  dsimp only [vaughanMinorArcTypeIIBlock,f]
  simp_rw [mul_sum]


theorem vaughanMinorArcTypeIIBlock_zero {X U V M N : ℕ} (α : ℝ)
    (hz : 2*M≤U ∨ 2*N≤V ∨ X<M*N) : vaughanMinorArcTypeIIBlock X U V M N α=0 := by
  apply sum_eq_zero
  intro m hm
  have hm' := mem_range.mp hm
  rcases hz with h|h|h
  · change ((vaughanTypeIICoefficient U (M+m):ℝ):ℂ)*_=0
    rw [vaughanTypeIICoefficient_support U (M+m) (by omega)];simp
  · apply mul_eq_zero_of_right
    apply sum_eq_zero;intro i hi
    rw [ite_eq_right (by have := mem_range.mp hi;omega : ¬V<N+i),zero_mul]
  · apply mul_eq_zero_of_right
    apply sum_eq_zero;intro i _
    have hn := h.trans_le (Nat.mul_le_mul (Nat.le_add_right M m) (Nat.le_add_right N i))
    rw [ite_eq_right hn.not_ge,mul_zero]

theorem vaughan_additive_typeII_of_block_cap (X U V : ℕ) (hX : 0<X) (α C : ℝ) (hC : 0≤C)
    (hb : ∀ M N:ℕ,0<M→0<N→M≤X→N≤X→U≤2*M→V≤2*N→M*N≤X→
      ‖vaughanMinorArcTypeIIBlock X U V M N α‖^2≤C^2) :
    ‖vaughanAdditiveBilinear X (vaughanTypeIICoefficient U) (vaughanTail V Λ) α‖ ≤
      ((Nat.log 2 X+1:ℕ):ℝ)^2*C := by
  let I := range (Nat.log 2 X+1)
  have hg {i:ℕ} (hi:i∈I) : 2^i≤X := (Nat.pow_le_pow_right (by decide : 0<2) (show i≤Nat.log 2 X from Nat.le_of_lt_succ (mem_range.mp hi))).trans (Nat.pow_log_le_self _ hX.ne')
  have hcell (i:ℕ) (hi:i∈I) (j:ℕ) (hj:j∈I) : ‖vaughanMinorArcTypeIIBlock X U V (2^i) (2^j) α‖≤C := by
    by_cases h : 2*(2^i)≤U ∨ 2*(2^j)≤V ∨ X<(2^i)*(2^j)
    · rw [vaughanMinorArcTypeIIBlock_zero α h,norm_zero];exact hC
    · push Not at h
      exact (sq_le_sq₀ (norm_nonneg _) hC).mp (hb _ _ (Nat.two_pow_pos i) (Nat.two_pow_pos j)
        (hg hi) (hg hj) h.1.le h.2.1.le h.2.2)
  rw [vaughan_additive_typeII_blocks]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑i∈I,∑j∈I,C := sum_le_sum (fun i hi=>(norm_sum_le ..).trans (sum_le_sum (hcell i hi)))
    _ = _ := by simp [I,pow_two];ring

theorem centralPrimeWave_additiveLambda_error (X : ℕ) (α : ℝ) :
    ‖centralPrimeWave X α-vaughanAdditiveSum X Λ α‖≤2*Real.sqrt X*Real.log X := by
  have heq : vaughanAdditiveSum X Λ α=∑k∈range (X+1),(Λ k:ℂ)*E ((k:ℝ)*α) := by
    apply sum_subset
    · exact fun k hk=>mem_range_succ_iff.mpr (mem_Icc.mp hk).2
    · intro k hk hno
      have h : k=0 := by have := mem_range_succ_iff.mp hk;by_contra! h';exact hno (mem_Icc.mpr ⟨by omega,this⟩)
      simp [h]
  rw [heq,centralPrimeWave,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply le_trans _ (primePowerError_le X)
  apply sum_le_sum;intro k _
  rw [←sub_mul,norm_mul,show ‖E ((k:ℝ)*α)‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]

end GoldbachPartial