import VerifiedHyperbolicLargeSieve

namespace GoldbachPartial
open Finset Filter
open scoped Classical

private theorem typeII_sqrt_block {Q Y:ℕ} {A E:ℝ} (hY:1≤Y) (hA:0≤A) (hE:0≤E) (he:E≤A*Y) :
    Real.sqrt (((((2*Q:ℕ):ℝ))^2+(1+4*Real.pi^2)*((Y:ℝ)+1))*E) ≤
      16*Real.sqrt A*((Q:ℝ)*Real.sqrt Y+(Y:ℝ)) := by
  let y:=Real.sqrt (Y:ℝ)
  have hy:0≤y := Real.sqrt_nonneg _
  have hY':(1:ℝ)≤Y := by exact_mod_cast hY
  have hyy : y^2=(Y:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp : Real.pi^2≤16 := by nlinarith only [mul_nonneg (sub_nonneg.mpr Real.pi_le_four) (show 0≤4+Real.pi by positivity)]
  have hh : ((((2*Q:ℕ):ℝ))^2+(1+4*Real.pi^2)*((Y:ℝ)+1))≤(16*((Q:ℝ)+y))^2 := by
    push_cast
    nlinarith only [hyy,hY',mul_nonneg (sub_nonneg.mpr hp) (show 0≤(Y:ℝ)+1 by positivity),sq_nonneg (Q:ℝ),mul_nonneg (Nat.cast_nonneg (α:=ℝ) Q) hy]
  calc _ ≤ Real.sqrt ((16*((Q:ℝ)+y))^2*(A*(Y:ℝ))) :=
         Real.sqrt_le_sqrt (mul_le_mul hh he hE (sq_nonneg _))
       _ = _ := by
         rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity),Real.sqrt_mul hA]
         change 16*((Q:ℝ)+y)*(Real.sqrt A*y)=16*Real.sqrt A*((Q:ℝ)*y+Y)
         linear_combination 16*Real.sqrt A*hyy

private theorem typeII_numeric_block {X Q U V M N:ℕ} (hQ:1≤Q) (hU:1≤U) (hV:1≤V)
    (hM:U≤M) (hN:V≤N) (hMN:M*N≤4*X) :
    (((Q:ℝ)*Real.sqrt M+M)*((Q:ℝ)*Real.sqrt N+N))/(Q:ℝ) ≤
      4*((X:ℝ)/Q+(X:ℝ)/Real.sqrt U+(X:ℝ)/Real.sqrt V+(Q:ℝ)*Real.sqrt X) := by
  let m:=Real.sqrt (M:ℝ)
  let n:=Real.sqrt (N:ℝ)
  let u:=Real.sqrt (U:ℝ)
  let v:=Real.sqrt (V:ℝ)
  let x:=Real.sqrt (X:ℝ)
  have hq : (0:ℝ)<Q := by exact_mod_cast hQ
  have hu : 0<u := Real.sqrt_pos.mpr (by exact_mod_cast hU)
  have hv : 0<v := Real.sqrt_pos.mpr (by exact_mod_cast hV)
  have hmn : (M:ℝ)*N≤4*(X:ℝ) := by exact_mod_cast hMN
  have hm : 0≤m := Real.sqrt_nonneg _
  have hn : 0≤n := Real.sqrt_nonneg _
  have hx : 0≤x := Real.sqrt_nonneg _
  have hmm:m^2=(M:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  have hnn:n^2=(N:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  have hxx:x^2=(X:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  have hmu : u≤m := Real.sqrt_le_sqrt (by exact_mod_cast hM)
  have hnv : v≤n := Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hs : m*n≤2*x := by
    have hp:=Real.sqrt_le_sqrt hmn
    rw [Real.sqrt_mul (Nat.cast_nonneg _) ,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
      show Real.sqrt 4=2 by exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)] at hp
    exact hp
  have h₁ : m*(N:ℝ)≤4*((X:ℝ)/u) := by
    rw [←mul_div_assoc,le_div_iff₀ hu]
    have hpp:=mul_le_mul_of_nonneg_left hmu (mul_nonneg hm (Nat.cast_nonneg (α:=ℝ) N))
    nlinarith only [hpp,hmn,congrArg (fun t:ℝ=>t*N) hmm]
  have h₂ : (M:ℝ)*n≤4*((X:ℝ)/v) := by
    rw [←mul_div_assoc,le_div_iff₀ hv]
    have hpp:=mul_le_mul_of_nonneg_left hnv (mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) hn)
    nlinarith only [hpp,hmn,congrArg (fun t:ℝ=>M*t) hnn]
  have h₃ : (M:ℝ)*N/Q≤4*((X:ℝ)/Q) := by rw [←mul_div_assoc];exact div_le_div_of_nonneg_right hmn hq.le
  change ((Q*m+M)*(Q*n+N))/(Q:ℝ)≤4*((X:ℝ)/Q+(X:ℝ)/u+(X:ℝ)/v+Q*x)
  have hid : ((Q*m+M)*(Q*n+N))/(Q:ℝ)=Q*(m*n)+m*N+M*n+M*N/Q := by field_simp;ring
  rw [hid]
  nlinarith only [h₁,h₂,h₃,mul_le_mul_of_nonneg_left hs hq.le,mul_nonneg hq.le hx]

def vaughanFactorBand (U X i:ℕ):Finset ℕ := (Ioc U X).filter (fun m=>Nat.log 2 m=i)

private theorem sum_vaughanFactorBand {F:Type*} [AddCommMonoid F] (U X:ℕ)(f:ℕ→F) :
    (∑m∈Ioc U X,f m)=∑i∈range (Nat.log 2 X+1),∑m∈vaughanFactorBand U X i,f m := by
  apply (sum_fiberwise_of_maps_to ?_ _).symm
  intro m hm
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Ioc.mp hm).2))

theorem vaughan_factor_band_split {q:ℕ} (X U V:ℕ) (a b:ℕ→ℂ) (χ:DirichletCharacter ℂ q) :
    vaughanProductWave (Ioc U X) (Ioc V X) a b X χ =
      ∑i∈range (Nat.log 2 X+1),∑j∈range (Nat.log 2 X+1),
        vaughanProductWave (vaughanFactorBand U X i) (vaughanFactorBand V X j) a b X χ := by
  unfold vaughanProductWave
  simp_rw [sum_filter]
  rw [sum_vaughanFactorBand U X]
  apply sum_congr rfl
  intro i _
  simp_rw [sum_vaughanFactorBand V X,sum_comm (s:=vaughanFactorBand U X i) (t:=range (Nat.log 2 X+1))]

noncomputable def vaughanTypeIIScale (X Q U V:ℕ):ℝ :=
  (X:ℝ)/Q+(X:ℝ)/Real.sqrt U+(X:ℝ)/Real.sqrt V+(Q:ℝ)*Real.sqrt X

private theorem typeII_band_caps {U X i m:ℕ} (hm:m∈vaughanFactorBand U X i) :
    1≤m ∧ m≤min X (2^(i+1)) ∧ U≤m ∧ min X (2^(i+1))≤2*m := by
  obtain ⟨h,hi⟩:=mem_filter.mp hm
  obtain ⟨hu,hx⟩:=mem_Ioc.mp h
  have h1:=Nat.lt_pow_succ_log_self (b:=2) (by decide) m
  have h2:=Nat.pow_log_le_self 2 (show m≠0 by omega)
  rw [hi] at h1 h2
  refine ⟨by omega,le_min hx h1.le,hu.le,?_⟩
  exact (min_le_right ..).trans (by rw [pow_succ];omega)

private theorem typeII_empty_wave {q X:ℕ}(S T:Finset ℕ)(a b:ℕ→ℂ)(χ:DirichletCharacter ℂ q)
    (hne:¬∃m∈S,∃n∈T,m*n≤X) : vaughanProductWave S T a b X χ=0 := by
  apply sum_eq_zero
  intro m hm
  have he : T.filter (fun n=>m*n≤X)=∅ := filter_eq_empty_iff.mpr (fun n hn hh=>hne ⟨m,hm,n,hn,hh⟩)
  simp [he]

private theorem typeII_block_bound (X Q U V i j:ℕ)(a b:ℕ→ℂ)(A B:ℝ)
    (hQ:1≤Q)(hU:1≤U)(hV:1≤V)(ha:0≤A)(hb:0≤B)
    (hA:∀Y≤X,∀S:Finset ℕ,S⊆Icc 1 Y→(∑m∈S,‖a m‖^2)≤A*Y)
    (hB:∀Y≤X,∀S:Finset ℕ,S⊆Icc 1 Y→(∑m∈S,‖b m‖^2)≤B*Y) :
    (∑r∈Ico Q (2*Q), (((r+1:ℕ):ℝ)/(r+1).totient)*
      ∑χ∈sievePrimitiveCharacters (r+1),
      ‖vaughanProductWave (vaughanFactorBand U X i) (vaughanFactorBand V X j) a b X χ‖) ≤
    (((Nat.log 2 (X+1)+1:ℕ):ℝ))*1024*Real.sqrt A*Real.sqrt B*
      ((Q:ℝ)*vaughanTypeIIScale X Q U V) := by
  let S:=vaughanFactorBand U X i
  let T:=vaughanFactorBand V X j
  let M:=min X (2^(i+1))
  let N:=min X (2^(j+1))
  change (∑r∈Ico Q (2*Q),_*∑χ∈sievePrimitiveCharacters (r+1),‖vaughanProductWave S T a b X χ‖)≤_
  by_cases he:∃m∈S,∃n∈T,m*n≤X
  · obtain ⟨m,hm,n,hn,hx⟩:=he
    have hc:=typeII_band_caps hm
    have hd:=typeII_band_caps hn
    have hM:U≤M:=hc.2.2.1.trans hc.2.1
    have hN:V≤N:=hd.2.2.1.trans hd.2.1
    have hMN:M*N≤4*X:= by
      calc
        M*N ≤ (2*m)*(2*n) := Nat.mul_le_mul hc.2.2.2 hd.2.2.2
        _ = 4*(m*n) := by ring
        _ ≤ 4*X := Nat.mul_le_mul_left 4 hx
    have hs:S⊆Icc 1 M:=fun k hk=>mem_Icc.mpr ⟨(typeII_band_caps hk).1,(typeII_band_caps hk).2.1⟩
    have ht:T⊆Icc 1 N:=fun k hk=>mem_Icc.mpr ⟨(typeII_band_caps hk).1,(typeII_band_caps hk).2.1⟩
    have em:=typeII_sqrt_block (Q:=Q) (hU.trans hM) ha (by positivity) (hA M (min_le_left ..) S hs)
    have en:=typeII_sqrt_block (Q:=Q) (hV.trans hN) hb (by positivity) (hB N (min_le_left ..) T ht)
    have hbnd:=primitive_hyperbolic_large_sieve (2*Q) M N X (Ico Q (2*Q)) S T a b
      (fun r hr=>(mem_Ico.mp hr).2) (fun k hk=>mem_Icc.mp (hs hk)) (fun k hk=>(mem_Icc.mp (ht hk)).2)
    have hl : ((Nat.log 2 (N+1)+1:ℕ):ℝ)≤((Nat.log 2 (X+1)+1:ℕ):ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right (min_le_left ..) 1)) 1
    have hnume:=typeII_numeric_block hQ hU hV hM hN hMN
    have hq:(0:ℝ)<Q:=by exact_mod_cast hQ
    have hh: (Q*Real.sqrt M+M)*(Q*Real.sqrt N+N) ≤4*vaughanTypeIIScale X Q U V*(Q:ℝ) := (div_le_iff₀ hq).mp hnume
    apply hbnd.trans
    calc _ ≤ (((Nat.log 2 (X+1)+1:ℕ):ℝ))*((16*Real.sqrt A*((Q:ℝ)*Real.sqrt M+M))*(16*Real.sqrt B*((Q:ℝ)*Real.sqrt N+N))) :=
          mul_le_mul hl (mul_le_mul em en (Real.sqrt_nonneg _) (by positivity)) (by positivity) (by positivity)
         _ = (↑(Nat.log 2 (X+1)+1):ℝ)*256*Real.sqrt A*Real.sqrt B*((Q*Real.sqrt M+M)*(Q*Real.sqrt N+N)) := by ring
         _ ≤ _ := by
          have hr:=mul_le_mul_of_nonneg_left hh (show 0≤(↑(Nat.log 2 (X+1)+1):ℝ)*256*Real.sqrt A*Real.sqrt B by positivity)
          convert hr using 1; ring
  · simp_rw [typeII_empty_wave S T a b _ he,norm_zero,sum_const_zero,mul_zero,sum_const_zero]
    unfold vaughanTypeIIScale
    positivity


theorem vaughan_typeII_dyadic_mean (X Q U V:ℕ)(a b:ℕ→ℂ)(A B:ℝ)
    (hQ:1≤Q)(hU:1≤U)(hV:1≤V)(ha:0≤A)(hb:0≤B)
    (hA:∀Y≤X,∀S:Finset ℕ,S⊆Icc 1 Y→(∑m∈S,‖a m‖^2)≤A*Y)
    (hB:∀Y≤X,∀S:Finset ℕ,S⊆Icc 1 Y→(∑m∈S,‖b m‖^2)≤B*Y) :
    (∑r∈Ico Q (2*Q), (1/((r+1).totient:ℝ))*
      ∑χ∈sievePrimitiveCharacters (r+1),
      ‖vaughanProductWave (Ioc U X) (Ioc V X) a b X χ‖) ≤
    (((Nat.log 2 X+1:ℕ):ℝ))^2*(((Nat.log 2 (X+1)+1:ℕ):ℝ))*1024*
      Real.sqrt A*Real.sqrt B*vaughanTypeIIScale X Q U V := by
  let I:=range (Nat.log 2 X+1)
  let J:=Ico Q (2*Q)
  let w (r:ℕ):ℝ:=((r+1:ℕ):ℝ)/(r+1).totient
  let C:ℝ:=(((Nat.log 2 (X+1)+1:ℕ):ℝ))*1024*Real.sqrt A*Real.sqrt B*
      ((Q:ℝ)*vaughanTypeIIScale X Q U V)
  let wave {r:ℕ} (χ:DirichletCharacter ℂ (r+1))(i j:ℕ):ℂ:=
    vaughanProductWave (vaughanFactorBand U X i) (vaughanFactorBand V X j) a b X χ
  let F (r:ℕ):ℝ:=∑χ∈sievePrimitiveCharacters (r+1),‖vaughanProductWave (Ioc U X) (Ioc V X) a b X χ‖
  have hw (r:ℕ):0≤w r:=by dsimp [w];positivity
  have hbnd (i j:ℕ) : (∑r∈J,w r*∑χ∈sievePrimitiveCharacters (r+1),‖wave χ i j‖)≤C :=
    typeII_block_bound X Q U V i j a b A B hQ hU hV ha hb hA hB
  have hf (r:ℕ) : F r≤∑i∈I,∑j∈I,∑χ∈sievePrimitiveCharacters (r+1),‖wave χ i j‖ := by
    calc F r≤∑χ∈sievePrimitiveCharacters (r+1),∑i∈I,∑j∈I,‖wave χ i j‖ := by
           apply sum_le_sum
           intro χ _
           rw [vaughan_factor_band_split]
           exact (norm_sum_le ..).trans (sum_le_sum (fun i _=>norm_sum_le ..))
         _ = _ := by simp_rw [sum_comm (s:=sievePrimitiveCharacters (r+1)) (t:=I)]
  have hq:(0:ℝ)<Q := by exact_mod_cast hQ
  apply (le_of_mul_le_mul_left (a:=(Q:ℝ)) · hq)
  change (Q:ℝ)*(∑r∈J, (1/((r+1).totient:ℝ))* F r)≤_
  calc _ ≤ ∑r∈J,w r*F r := by
         rw [mul_sum];apply sum_le_sum
         intro r hr
         have hqr:(Q:ℝ)≤((r+1:ℕ):ℝ):=by exact_mod_cast (mem_Ico.mp hr).1.trans (Nat.le_succ r)
         have hF : 0≤F r:=sum_nonneg (fun _ _=>norm_nonneg _)
         calc _ = ((Q:ℝ)/(r+1).totient)*F r := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hqr (Nat.cast_nonneg _)) hF
       _ ≤ ∑r∈J,∑i∈I,∑j∈I,w r*∑χ∈sievePrimitiveCharacters (r+1),‖wave χ i j‖ := by
         apply sum_le_sum;intro r _
         simpa only [mul_sum] using mul_le_mul_of_nonneg_left (hf r) (hw r)
       _ = ∑i∈I,∑j∈I,∑r∈J,w r*∑χ∈sievePrimitiveCharacters (r+1),‖wave χ i j‖ := by
         simp_rw [sum_comm (s:=J) (t:=I)]
       _ ≤ ∑i∈I,∑j∈I,C := sum_le_sum (fun i _=>sum_le_sum (fun j _=>hbnd i j))
       _ = _ := by simp [I,C];ring

end GoldbachPartial
