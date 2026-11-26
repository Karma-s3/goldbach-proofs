import VerifiedFareyLargeSieve
namespace GoldbachPartial
open Finset Filter
open scoped Classical

private theorem binary_lt_step (v t W:ℕ) (ht:t<W) :
    (if v<t then (1:ℂ) else 0) = (if v/2<t/2 then 1 else 0)+
      ∑b∈range W,if v=2*b ∧ t=2*b+1 then (1:ℂ) else 0 := by
  let h:=t/2
  have hh:h<W := (Nat.div_le_self t 2).trans_lt ht
  have he : (∑b∈range W,if v=2*b ∧ t=2*b+1 then (1:ℂ) else 0)=
      (if v=2*h ∧ t=2*h+1 then (1:ℂ) else 0) := by
    apply sum_eq_single_of_mem h (mem_range.mpr hh)
    intro b _ hb
    rw [ite_eq_right (by dsimp [h] at hb;omega)]
  rw [he]
  dsimp only [h]
  split_ifs <;> norm_num
  all_goals omega

theorem binary_lt_rectangles (v t L:ℕ) (hv:v<2^L) (ht:t<2^L) :
    (if v<t then (1:ℂ) else 0) =
      ∑j∈range L,∑b∈range (2^L),if v/2^j=2*b ∧ t/2^j=2*b+1 then (1:ℂ) else 0 := by
  let W:=2^L
  have step (j:ℕ) :
      (if v/2^j<t/2^j then (1:ℂ) else 0) = (if v/2^(j+1)<t/2^(j+1) then 1 else 0)+
        ∑b∈range W,if v/2^j=2*b ∧ t/2^j=2*b+1 then (1:ℂ) else 0 := by
    have h := binary_lt_step (v/2^j) (t/2^j) W ((Nat.div_le_self t _).trans_lt ht)
    simpa only [pow_succ,Nat.div_div_eq_div_mul] using h
  have iter (i:ℕ) : (if v<t then (1:ℂ) else 0) = (if v/2^i<t/2^i then 1 else 0)+
      ∑j∈range i,∑b∈range W,if v/2^j=2*b ∧ t/2^j=2*b+1 then (1:ℂ) else 0 := by
    induction i with
    | zero => simp
    | succ i h =>
      rw [h,step i,sum_range_succ]
      abel
  simpa only [Nat.div_eq_of_lt hv,Nat.div_eq_of_lt ht,lt_self_iff_false,ite_false,zero_add] using iter L

def vaughanDyadicRows (M:Finset ℕ) (cut:ℕ→ℕ) (j b:ℕ) : Finset ℕ :=
  M.filter (fun m=>cut m/2^j=2*b+1)
def vaughanDyadicCols (N:Finset ℕ) (j b:ℕ) : Finset ℕ :=
  N.filter (fun n=>n/2^j=2*b)

/-- The strict row cutoff is exactly a disjoint union of dyadic rectangles. -/
theorem vaughan_triangle_rectangles (M N:Finset ℕ) (cut:ℕ→ℕ) (L:ℕ)
    (hm:∀m∈M,cut m<2^L) (hn:∀n∈N,n<2^L) (a b:ℕ→ℂ) :
    (∑m∈M,∑n∈N.filter (fun n=>n<cut m),a m*b n) =
    ∑j∈range L,∑r∈range (2^L),(∑m∈vaughanDyadicRows M cut j r,a m)*(∑n∈vaughanDyadicCols N j r,b n) := by
  let W:=2^L
  let g (m n j r:ℕ):ℂ := if n/2^j=2*r ∧ cut m/2^j=2*r+1 then a m*b n else 0
  have he {m n:ℕ} (hm':m∈M) (hn':n∈N) :
      (if n<cut m then a m*b n else 0)=∑j∈range L,∑r∈range W,g m n j r := by
    have hh:=congrArg (fun z:ℂ=>z*(a m*b n)) (binary_lt_rectangles n (cut m) L (hn n hn') (hm m hm'))
    simp only [ite_mul,one_mul,zero_mul,sum_mul] at hh
    exact hh
  have hr (j r:ℕ) :
      (∑m∈M,∑n∈N,g m n j r)=(∑m∈vaughanDyadicRows M cut j r,a m)*(∑n∈vaughanDyadicCols N j r,b n) := by
    simp only [vaughanDyadicRows,vaughanDyadicCols,sum_filter,sum_mul,mul_sum]
    rw [sum_comm (s:=N) (t:=M)]
    apply sum_congr rfl;intro m _
    apply sum_congr rfl;intro n _
    by_cases h:n/2^j=2*r <;> by_cases h':cut m/2^j=2*r+1 <;> simp [g,h,h']
  calc _ = ∑m∈M,∑n∈N,∑j∈range L,∑r∈range W,g m n j r := by
         apply sum_congr rfl;intro m hm'
         rw [sum_filter]
         exact sum_congr rfl (fun n hn'=>he hm' hn')
       _ = ∑j∈range L,∑r∈range W,∑m∈M,∑n∈N,g m n j r := by
         simp_rw [sum_comm (s:=N) (t:=range L),sum_comm (s:=M) (t:=range L),
           sum_comm (s:=N) (t:=range W),sum_comm (s:=M) (t:=range W)]
       _ = _ := sum_congr rfl fun j _=>sum_congr rfl fun r _=>hr j r

private theorem binary_fiber_mass (S:Finset ℕ) (label:ℕ→ℕ) (W e:ℕ) (f:ℕ→ℝ) (hf:∀k∈S,0≤f k) :
    (∑r∈range W,∑k∈S.filter (fun k=>label k=2*r+e),f k)≤∑k∈S,f k := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum;intro k hk
  by_cases h:∃r∈range W,label k=2*r+e
  · obtain ⟨r,hr,he⟩:=h
    rw [sum_eq_single_of_mem r hr,ite_eq_left he]
    intro t _ ht;exact ite_eq_right (by omega)
  · rw [sum_eq_zero (fun r hr=>ite_eq_right (fun h' => h ⟨r,hr,h'⟩))]
    exact hf k hk

/-- Transfer of a uniform rectangular estimate to any single row cutoff. The loss equals
the number of binary levels, without a factor for the number of rectangles at a level. -/
theorem vaughan_triangle_of_rectangles {ι:Type*} (H:Finset ι) (w:ι→ℝ) (hw:∀i∈H,0≤w i)
    (M N:Finset ℕ) (cut:ℕ→ℕ) (L:ℕ) (hm:∀m∈M,cut m<2^L) (hn:∀n∈N,n<2^L)
    (a b:ι→ℕ→ℂ) (x y:ℕ→ℝ) (hx:∀m∈M,0≤x m) (hy:∀n∈N,0≤y n)
    (hrect:∀ A⊆M,∀ B⊆N,(∑i∈H,w i*‖(∑m∈A,a i m)*(∑n∈B,b i n)‖)≤
      Real.sqrt (∑m∈A,x m)*Real.sqrt (∑n∈B,y n)) :
    (∑i∈H,w i*‖∑m∈M,∑n∈N.filter (fun n=>n<cut m),a i m*b i n‖) ≤
      (L:ℝ)*(Real.sqrt (∑m∈M,x m)*Real.sqrt (∑n∈N,y n)) := by
  let W:=2^L
  let U (j r:ℕ):=vaughanDyadicRows M cut j r
  let V (j r:ℕ):=vaughanDyadicCols N j r
  let F (j r:ℕ)(i:ι):=(∑m∈U j r,a i m)*(∑n∈V j r,b i n)
  have hU (j r:ℕ): U j r⊆M:=filter_subset .. 
  have hV (j r:ℕ): V j r⊆N:=filter_subset ..
  have hpoint (i:ι) :
      ‖∑m∈M,∑n∈N.filter (fun n=>n<cut m),a i m*b i n‖≤∑j∈range L,∑r∈range W,‖F j r i‖ := by
    rw [vaughan_triangle_rectangles M N cut L hm hn]
    exact (norm_sum_le _ _).trans (sum_le_sum (fun j _=>norm_sum_le _ _))
  have hrow (j:ℕ) :
      (∑r∈range W,∑i∈H,w i*‖F j r i‖)≤Real.sqrt (∑m∈M,x m)*Real.sqrt (∑n∈N,y n) := by
    apply (sum_le_sum (fun r _=>hrect (U j r) (hU j r) (V j r) (hV j r))).trans
    apply (Real.sum_sqrt_mul_sqrt_le (range W) (fun r=>sum_nonneg (fun m h=>hx m (hU j r h)))
      (fun r=>sum_nonneg (fun n h=>hy n (hV j r h)))).trans
    have h₁:=binary_fiber_mass M (fun m=>cut m/2^j) W 1 x hx
    have h₂:=binary_fiber_mass N (fun n=>n/2^j) W 0 y hy
    simp only [add_zero] at h₂
    exact mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc _ ≤ ∑i∈H,w i*(∑j∈range L,∑r∈range W,‖F j r i‖) := sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (hpoint i) (hw i hi))
       _ = ∑j∈range L,∑r∈range W,∑i∈H,w i*‖F j r i‖ := by
         simp_rw [mul_sum,sum_comm (s:=H) (t:=range L),sum_comm (s:=H) (t:=range W)]
       _ ≤ ∑_j∈range L,Real.sqrt (∑m∈M,x m)*Real.sqrt (∑n∈N,y n) := sum_le_sum (fun j _=>hrow j)
       _ = _ := by simp

noncomputable def vaughanProductWave {q:ℕ} (A B:Finset ℕ) (a b:ℕ→ℂ)
    (X:ℕ) (χ:DirichletCharacter ℂ q):ℂ :=
  ∑m∈A,∑n∈B.filter (fun n=>m*n≤X),a m*b n*χ ((m*n:ℕ):ZMod q)

/-- A pointwise-in-X hyperbolic Type II large sieve for genuine primitive characters,
with a single binary-logarithmic loss. -/
theorem primitive_hyperbolic_large_sieve (R M N X:ℕ) (J A B:Finset ℕ) (a b:ℕ→ℂ)
    (hJ:∀j∈J,j<R) (hm:∀m∈A,1≤m ∧ m≤M) (hn:∀n∈B,n≤N) :
    (∑j∈J,(((j+1:ℕ):ℝ)/(j+1).totient)*
      ∑χ∈sievePrimitiveCharacters (j+1),‖vaughanProductWave A B a b X χ‖) ≤
      (((Nat.log 2 (N+1)+1:ℕ):ℝ))*
      (Real.sqrt ((((R:ℝ)^2+(1+4*Real.pi^2)*((M:ℝ)+1)))*(∑m∈A,‖a m‖^2))*
       Real.sqrt ((((R:ℝ)^2+(1+4*Real.pi^2)*((N:ℝ)+1)))*(∑n∈B,‖b n‖^2))) := by
  let L:=Nat.log 2 (N+1)+1
  let cut (m:ℕ):=min (X/m) N +1
  let T (j:ℕ):=sievePrimitiveCharacters (j+1)
  let H:=J.sigma T
  let cM:ℝ:=(R:ℝ)^2+(1+4*Real.pi^2)*((M:ℝ)+1)
  let cN:ℝ:=(R:ℝ)^2+(1+4*Real.pi^2)*((N:ℝ)+1)
  let w (i:Σj:ℕ,DirichletCharacter ℂ (j+1)):ℝ:=((i.1+1:ℕ):ℝ)/(i.1+1).totient
  let f (i:Σj:ℕ,DirichletCharacter ℂ (j+1))(m:ℕ):ℂ:=a m*i.2 (m:ZMod (i.1+1))
  let g (i:Σj:ℕ,DirichletCharacter ℂ (j+1))(n:ℕ):ℂ:=b n*i.2 (n:ZMod (i.1+1))
  have hL:N+1<2^L:=Nat.lt_pow_succ_log_self (by decide) _
  have hcut (m:ℕ) : cut m<2^L := (Nat.add_le_add_right (min_le_right ..) 1).trans_lt hL
  have hrect (A':Finset ℕ) (hA:A'⊆A) (B':Finset ℕ) (hB:B'⊆B) :
      (∑i∈H,w i*‖(∑m∈A',f i m)*(∑n∈B',g i n)‖) ≤
        Real.sqrt (∑m∈A',cM*‖a m‖^2)*Real.sqrt (∑n∈B',cN*‖b n‖^2) := by
    rw [←mul_sum,←mul_sum]
    have h:=primitive_bilinear_large_sieve R M N J A' B' a b hJ (fun m h=>(hm m (hA h)).2) (fun n h=>hn n (hB h))
    change (∑i∈J.sigma T,_)≤_
    rw [sum_sigma]
    simpa only [mul_sum,w,f,g,T,sieveCharacterWave] using h
  have ht:=vaughan_triangle_of_rectangles H w (fun i _=>by dsimp [w];positivity) A B cut L
    (fun m _=>hcut m) (fun n h=>(hn n h).trans_lt (by omega)) f g
    (fun m=>cM*‖a m‖^2) (fun n=>cN*‖b n‖^2)
    (fun m _=>by dsimp [cM];positivity) (fun n _=>by dsimp [cN];positivity) hrect
  have heq (i:Σj:ℕ,DirichletCharacter ℂ (j+1)) :
      (∑m∈A,∑n∈B.filter (fun n=>n<cut m),f i m*g i n)=vaughanProductWave A B a b X i.2 := by
    unfold vaughanProductWave
    apply sum_congr rfl
    intro m hA
    have hs : B.filter (fun n=>n<cut m)=B.filter (fun n=>m*n≤X) := by
      ext n
      simp only [mem_filter]
      constructor
      · rintro ⟨hr,h⟩
        have hdiv : n≤X/m := (Nat.le_of_lt_succ h).trans (min_le_left ..)
        exact ⟨hr,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (hm m hA).1).mp hdiv⟩
      · rintro ⟨hr,h⟩
        exact ⟨hr,Nat.lt_succ_of_le (le_min ((Nat.le_div_iff_mul_le (hm m hA).1).mpr (by simpa [Nat.mul_comm] using h)) (hn n hr))⟩
    rw [hs]
    apply sum_congr rfl;intro n _
    dsimp [f,g];rw [Nat.cast_mul,map_mul];ring
  simp_rw [heq] at ht
  rw [show H=J.sigma T from rfl,sum_sigma] at ht
  simpa only [mul_sum,w,T,cM,cN,L] using ht

end GoldbachPartial
