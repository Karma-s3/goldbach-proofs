import VerifiedRationalSampleRows
import VerifiedActualVaughanConductor

namespace GoldbachPartial
open Finset ExtendedArcCoefficient

private theorem rationalSample_schur (N : ℕ) (v : ℕ→ℝ) (D : ℕ→ℕ→ℝ) (C : ℝ)
    (hD : ∀i j,0≤D i j) (hrow : ∀i∈range N,(∑j∈range N,D i j)≤C)
    (hcol : ∀j∈range N,(∑i∈range N,D i j)≤C) :
    (∑i∈range N,∑j∈range N,v i*v j*D i j) ≤ (∑i∈range N,v i^2)*C := by
  let S := range N
  have hpt (i j : ℕ) : 2*(v i*v j*D i j) ≤ v i^2*D i j+v j^2*D i j := by
    nlinarith only [mul_nonneg (sq_nonneg (v i-v j)) (hD i j)]
  have hr : (∑i∈S,∑j∈S,v i^2*D i j)≤(∑i∈S,v i^2)*C := by
    simp only [←mul_sum,sum_mul]
    exact sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _))
  have hl : (∑i∈S,∑j∈S,v j^2*D i j)≤(∑i∈S,v i^2)*C := by
    rw [sum_comm]
    simp only [←mul_sum,sum_mul]
    exact sum_le_sum (fun j hj=>mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg _))
  have hh := sum_le_sum (s:=S) (fun i _=>sum_le_sum (s:=S) (fun j _=>hpt i j))
  simp only [←mul_sum,sum_add_distrib] at hh
  simp only [←mul_sum] at hr
  change (∑i∈S,∑j∈S,v i*v j*D i j)≤(∑i∈S,v i^2)*C
  linarith only [hh,hr,hl]

theorem rationalSample_bilinear_gram (M N : ℕ) (a b : ℕ→ℂ) (A : ℕ→ℕ→ℂ)
    (D : ℕ→ℕ→ℝ) (C : ℝ) (hD : ∀i j,0≤D i j)
    (hk : ∀i∈range N,∀j∈range N,‖∑m∈range M,A m i*(starRingEnd ℂ) (A m j)‖≤D i j)
    (hrow : ∀i∈range N,(∑j∈range N,D i j)≤C) (hcol : ∀j∈range N,(∑i∈range N,D i j)≤C) :
    ‖∑m∈range M,a m*∑i∈range N,b i*A m i‖^2 ≤
      (∑m∈range M,‖a m‖^2)*((∑i∈range N,‖b i‖^2)*C) := by
  let Y := fun m:ℕ=>∑i∈range N,b i*A m i
  let K := fun i j:ℕ=>∑m∈range M,A m i*(starRingEnd ℂ) (A m j)
  have hsq (m:ℕ) : ((‖Y m‖^2:ℝ):ℂ) =
      ∑i∈range N,∑j∈range N,(b i*(starRingEnd ℂ) (b j))*(A m i*(starRingEnd ℂ) (A m j)) := by
    rw [Complex.ofReal_pow,←Complex.mul_conj']
    dsimp only [Y]
    rw [map_sum,sum_mul]
    apply sum_congr rfl;intro i _
    rw [mul_sum];apply sum_congr rfl;intro j _;rw [map_mul];ring
  have he : ((∑m∈range M,‖Y m‖^2:ℝ):ℂ) =
      ∑i∈range N,∑j∈range N,(b i*(starRingEnd ℂ) (b j))*K i j := by
    rw [Complex.ofReal_sum]
    simp_rw [hsq]
    rw [sum_comm]
    apply sum_congr rfl;intro i _;rw [sum_comm]
    apply sum_congr rfl;intro j _;rw [←mul_sum]
  have hE : (∑m∈range M,‖Y m‖^2) ≤ (∑i∈range N,‖b i‖^2)*C := by
    have hn : ‖((∑m∈range M,‖Y m‖^2:ℝ):ℂ)‖=(∑m∈range M,‖Y m‖^2) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun _ _=>sq_nonneg _))]
    rw [←hn,he]
    apply (norm_sum_le ..).trans
    apply le_trans _ (rationalSample_schur N (fun i=>‖b i‖) D C hD hrow hcol)
    apply sum_le_sum;intro i hi
    apply (norm_sum_le ..).trans
    apply sum_le_sum;intro j hj
    rw [norm_mul,norm_mul,RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hk i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hnorm : ‖∑m∈range M,a m*Y m‖ ≤ ∑m∈range M,‖a m‖*‖Y m‖ := by
    simpa only [norm_mul] using norm_sum_le (range M) (fun m=>a m*Y m)
  exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (sum_mul_sq_le_sq_mul_sq (range M) (fun m=>‖a m‖) (fun m=>‖Y m‖))).trans
      (mul_le_mul_of_nonneg_left hE (sum_nonneg (fun _ _=>sq_nonneg _)))


private theorem bilinearPhase_conj (t : ℝ) : (starRingEnd ℂ) (E t)=E (-t) := by
  unfold E
  rw [←Complex.exp_conj];congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast;ring

theorem cappedCircleReciprocal_neg (M x : ℝ) : cappedCircleReciprocal M (-x)=cappedCircleReciprocal M x := by
  simp [cappedCircleReciprocal]

/-- Shifted rectangles with an arbitrary prefix cutoff in each column. -/
theorem rationalSample_bilinear_prefix (M N q a₀ a : ℕ) (x : ℝ) (l : ℕ→ℕ)
    (u v : ℕ→ℂ) (hq : 0<q) (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖∑m∈range M,u m*∑i∈range N,v i*(if m<l i then
        E (((a₀+m:ℕ):ℝ)*(x+(i:ℝ))*α) else 0)‖^2 ≤
      (∑m∈range M,‖u m‖^2)*((∑i∈range N,‖v i‖^2)*
        (((N:ℝ)/q+1)*(6*(M:ℝ)+8*(q:ℝ)*(1+Real.log (q+2:ℕ))))) := by
  let D := fun i j:ℕ=>cappedCircleReciprocal M (((i:ℝ)-j)*α)
  let C := ((N:ℝ)/q+1)*(6*(M:ℝ)+8*(q:ℝ)*(1+Real.log (q+2:ℕ)))
  have hcol (j:ℕ) : (∑i∈range N,D i j)≤C := by
    apply le_trans (le_of_eq ?_) (rationalSample_range N q a hq hc ha (Nat.cast_nonneg M) (-((j:ℝ)*α)))
    apply sum_congr rfl;intro i _;dsimp only [D];congr 1;ring
  have hsym (i j:ℕ) : D i j=D j i := by
    dsimp only [D]
    rw [show ((i:ℝ)-j)*α = -(((j:ℝ)-i)*α) by ring,cappedCircleReciprocal_neg]
  apply rationalSample_bilinear_gram M N u v _ D C
  · exact fun i j=>cappedCircleReciprocal_nonneg (Nat.cast_nonneg _) _
  · intro i _ j _
    let L := min M (min (l i) (l j))
    have hL : L≤M := min_le_left .. 
    let A := fun m:ℕ=>if m<l i ∧ m<l j then E (((a₀+m:ℕ):ℝ)*(((i:ℝ)-j)*α)) else 0
    have hfe : ((range M).filter (fun m=>m<l i ∧ m<l j))=range L := by
      ext m;simp [L,lt_min_iff]
    have he : (∑m∈range M,A m) = ∑m∈range L,E (((a₀+m:ℕ):ℝ)*(((i:ℝ)-j)*α)) := by
      dsimp only [A];rw [←sum_filter,hfe]
    apply le_trans (le_of_eq ?_) (cappedCircleReciprocal_geometric_row a₀ L M _ (by exact_mod_cast hL))
    congr 1
    apply Eq.trans _ he
    apply sum_congr rfl;intro m _
    dsimp only [A]
    by_cases h1 : m<l i <;> by_cases h2 : m<l j <;> simp [h1,h2,bilinearPhase_conj,←phase_add]
    congr 1;ring
  · intro i _
    calc (∑j∈range N,D i j) = ∑j∈range N,D j i := sum_congr rfl (fun j _=>hsym i j)
         _ ≤ _ := hcol i
  · exact fun j _=>hcol j


/-- In a shifted dyadic box this imposes the actual hyperbolic Vaughan cutoff. -/
theorem rationalSample_vaughan_rectangle (X M N q a₀ b₀ a : ℕ) (hb₀ : 0<b₀)
    (u v : ℕ→ℂ) (hq : 0<q) (hc : a.Coprime q) {α : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖∑m∈range M,u (a₀+m)*∑i∈range N,v (b₀+i)*
      (if (a₀+m)*(b₀+i)≤X then E ((((a₀+m)*(b₀+i):ℕ):ℝ)*α) else 0)‖^2 ≤
      (∑m∈range M,‖u (a₀+m)‖^2)*((∑i∈range N,‖v (b₀+i)‖^2)*
        (((N:ℝ)/q+1)*(6*(M:ℝ)+8*(q:ℝ)*(1+Real.log (q+2:ℕ))))) := by
  let l := fun i:ℕ=>X/(b₀+i)+1-a₀
  have hf (m i:ℕ) : m<l i ↔ (a₀+m)*(b₀+i)≤X := by
    dsimp only [l]
    rw [←Nat.le_div_iff_mul_le (by omega : 0<b₀+i)]
    omega
  apply le_trans (le_of_eq ?_) (rationalSample_bilinear_prefix M N q a₀ a b₀ l
    (fun m=>u (a₀+m)) (fun i=>v (b₀+i)) hq hc ha)
  simp_rw [hf,Nat.cast_mul,Nat.cast_add]


/-- Actual type-II coefficients, including the cutoff on the Mangoldt factor. -/
noncomputable def vaughanMinorArcTypeIIBlock (X U V M N : ℕ) (α : ℝ) : ℂ :=
  ∑m∈range M,vaughanActualLeft U (M+m)*∑i∈range N,
    (if V<N+i then vaughanActualRight (N+i) else 0)*
    (if (M+m)*(N+i)≤X then E ((((M+m)*(N+i):ℕ):ℝ)*α) else 0)

theorem vaughanMinorArcTypeIIBlock_sq (X U V M N q a : ℕ) (hM : 0<M) (hN : 0<N)
    (hMX : M≤X) (hNX : N≤X) (hq : 0<q) (hc : a.Coprime q) {α : ℝ}
    (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    ‖vaughanMinorArcTypeIIBlock X U V M N α‖^2 ≤
      (8*(1+Real.log X)^3*(2*M)) *
        ((2*(Real.log 4+4)*(1+Real.log X)*(2*N)) *
          (((N:ℝ)/q+1)*(6*(M:ℝ)+8*(q:ℝ)*(1+Real.log (q+2:ℕ))))) := by
  let v := fun j : ℕ=>if V<j then vaughanActualRight j else 0
  have shift (B : ℕ) (f : ℕ→ℝ) : (∑k∈range B,f (B+k)) = ∑j∈Ico B (2*B),f j := by
    rw [sum_Ico_eq_sum_range,show 2*B-B=B by omega]
  have hs (B : ℕ) (hb : 0<B) : Ico B (2*B) ⊆ Icc 1 (2*B) :=
    fun j hj=>mem_Icc.mpr ⟨hb.trans_le (mem_Ico.mp hj).1,(mem_Ico.mp hj).2.le⟩
  have hux := (vaughan_actual_square_bounds_double X (2*M) U (by omega) (by omega) _ (hs M hM)).1
  have hvx := (vaughan_actual_square_bounds_double X (2*N) U (by omega) (by omega) _ (hs N hN)).2
  have hu : (∑m∈range M,‖vaughanActualLeft U (M+m)‖^2) ≤ 8*(1+Real.log X)^3*(2*M) := by
    rw [shift M (fun j=>‖vaughanActualLeft U j‖^2)]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hux
  have hv : (∑i∈range N,‖v (N+i)‖^2) ≤ 2*(Real.log 4+4)*(1+Real.log X)*(2*N) := by
    rw [shift N (fun j=>‖v j‖^2)]
    apply le_trans _ (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hvx)
    apply sum_le_sum;intro j _
    dsimp only [v];split_ifs
    · exact le_rfl
    · simp
  have hL := Real.log_natCast_nonneg X
  have hqL := Real.log_natCast_nonneg (q+2)
  apply (rationalSample_vaughan_rectangle X M N q M N a hN (vaughanActualLeft U) v hq hc ha).trans
  gcongr

end GoldbachPartial