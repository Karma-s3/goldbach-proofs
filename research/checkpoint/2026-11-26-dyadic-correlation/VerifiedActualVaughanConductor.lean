import VerifiedDyadicTypeIISieve
import VerifiedVaughanNumericBounds
import VerifiedPrimeMeanBlocks

namespace GoldbachPartial
open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

noncomputable def vaughanActualLeft (U m : ℕ) : ℂ := (vaughanTypeIICoefficient U m:ℝ)
noncomputable def vaughanActualRight (j : ℕ) : ℂ := (Λ j:ℝ)

theorem vaughan_product_wave_eq_typeII {q : ℕ} (χ : DirichletCharacter ℂ q) (X U V : ℕ) :
    vaughanProductWave (Ioc U X) (Ioc V X) (vaughanActualLeft U) vaughanActualRight X χ =
      vaughanCharacterBilinear χ X (vaughanTypeIICoefficient U) (vaughanTail V Λ) := by
  let f (m : ℕ) := ((vaughanTypeIICoefficient U m:ℂ)*χ (m:ZMod q)) *
        (∑j∈Ioc V (X/m),(Λ j:ℂ)*χ (j:ZMod q))
  rw [vaughan_character_typeII_active]
  change _ = ∑m∈Ioc U (X/(V+1)),f m
  calc
    _ = ∑m∈Ioc U X,f m := by
      apply sum_congr rfl
      intro m hm
      have hmpos : 0<m := by have := (mem_Ioc.mp hm).1;omega
      have he : (Ioc V X).filter (fun j=>m*j≤X) = Ioc V (X/m) := by
        ext j
        simp only [mem_filter,mem_Ioc]
        constructor
        · rintro ⟨⟨hv,_⟩,hprod⟩
          exact ⟨hv,(Nat.le_div_iff_mul_le hmpos).mpr (by simpa only [Nat.mul_comm] using hprod)⟩
        · rintro ⟨hv,hj⟩
          exact ⟨⟨hv,hj.trans (Nat.div_le_self ..)⟩, by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hj⟩
      dsimp only [f]
      rw [he,mul_sum]
      apply sum_congr rfl
      intro j _
      rw [Nat.cast_mul,map_mul]
      dsimp only [vaughanActualLeft,vaughanActualRight]
      ring
    _ = _ := by
      symm
      apply sum_subset
      · intro m hm
        obtain ⟨hl,hu⟩ := mem_Ioc.mp hm
        exact mem_Ioc.mpr ⟨hl,hu.trans (Nat.div_le_self ..)⟩
      · intro m hm hbad
        have hml := (mem_Ioc.mp hm).1
        have hmp : 0<m := by omega
        have hbig : X/(V+1)<m := by by_contra! h;exact hbad (mem_Ioc.mpr ⟨hml,h⟩)
        have hquo : ¬V<X/m := by
          intro hv
          have hmn := (Nat.le_div_iff_mul_le hmp).mp hv
          exact hbig.not_ge ((Nat.le_div_iff_mul_le (Nat.succ_pos V)).mpr (by simpa only [Nat.mul_comm] using hmn))
        dsimp only [f]
        rw [Ioc_eq_empty hquo,sum_empty,mul_zero]

private theorem actual_natLog_mono {Y Z : ℕ} (h : Y≤Z) : Real.log Y≤Real.log Z := by
  by_cases hy : Y=0
  · simp [hy,Real.log_natCast_nonneg]
  exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hy) (by exact_mod_cast h)

theorem vaughan_actual_square_bounds (X Y U : ℕ) (hY : Y≤X) (S : Finset ℕ) (hS : S⊆Icc 1 Y) :
    (∑m∈S,‖vaughanActualLeft U m‖^2)≤(1+Real.log X)^3*(Y:ℝ) ∧
      (∑j∈S,‖vaughanActualRight j‖^2)≤((Real.log 4+4)*(1+Real.log X))*(Y:ℝ) := by
  have hlog := actual_natLog_mono hY
  have h0 := Real.log_natCast_nonneg Y
  have hR (j : ℕ) (hj : j∈S) : Λ j=vaughanTail 0 Λ j := by
    rw [vaughanTail_apply,ite_eq_left (show 0<j from (mem_Icc.mp (hS hj)).1)]
  constructor
  · simp only [vaughanActualLeft,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply (vaughan_typeII_left_square_le U Y S hS).trans
    rw [mul_comm (Y:ℝ)]
    gcongr
  · simp only [vaughanActualRight,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [sum_congr rfl (fun j hj=>congrArg (fun t : ℝ=>t^2) (hR j hj))]
    apply (vaughan_typeII_right_square_le 0 Y S hS).trans
    rw [mul_right_comm]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith

private theorem actual_log_twice (X : ℕ) (hX : 1≤X) :
    Real.log (2*X:ℕ) ≤ 1+Real.log X := by
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (by exact_mod_cast (show X≠0 by omega))]
  linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

theorem vaughan_actual_square_bounds_double (X Y U : ℕ) (hX : 1≤X) (hY : Y≤2*X)
    (S : Finset ℕ) (hS : S⊆Icc 1 Y) :
    (∑m∈S,‖vaughanActualLeft U m‖^2)≤(8*(1+Real.log X)^3)*(Y:ℝ) ∧
      (∑j∈S,‖vaughanActualRight j‖^2)≤(2*(Real.log 4+4)*(1+Real.log X))*(Y:ℝ) := by
  have hh := vaughan_actual_square_bounds (2*X) Y U hY S hS
  have hlog := actual_log_twice X hX
  have h1 : 1+Real.log (2*X:ℕ)≤2*(1+Real.log X) := by linarith only [hlog,Real.log_natCast_nonneg X]
  constructor
  · apply hh.1.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply (pow_le_pow_left₀ (show 0≤1+Real.log (2*X:ℕ) by positivity) h1 3).trans_eq
    ring
  · apply hh.2.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply (mul_le_mul_of_nonneg_left h1 (show 0≤Real.log 4+4 by positivity)).trans_eq
    ring

private theorem actual_natlog_two_bound (X Y : ℕ) (hX : 1≤X) (hY : Y≤2*X) :
    ((Nat.log 2 Y+1:ℕ):ℝ) ≤ 3*(1+Real.log X) := by
  have hy := Real.natLog_le_logb Y 2
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h2
  simp only [Nat.cast_ofNat,Real.logb] at hy
  have hy' : (Nat.log 2 Y:ℝ)≤2*Real.log Y := by
    apply hy.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr _)
    nlinarith only [mul_nonneg (Real.log_natCast_nonneg Y) (show 0≤2*Real.log 2-1 by linarith)]
  push_cast
  linarith only [hy',(actual_natLog_mono hY).trans (actual_log_twice X hX),Real.log_natCast_nonneg X]

theorem vaughan_actual_dyadic_typeII_bound (X Q H P : ℕ) (hX : 2≤X) (hH : 1≤H)
    (hP : 0<P) (hPQ : P≤Q) (hHP : H<2*P) (D : Finset ℕ)
    (hD : ∀q∈D,P<q ∧ q≤2*P) :
    vaughanTypeIIConductorMass X H H D ≤
      165888*(1+Real.log X)^5*((X:ℝ)/H+(X:ℝ)/Real.sqrt H+(Q:ℝ)*Real.sqrt X) := by
  let L := 1+Real.log X
  let κ := Real.log 4+4
  let A := L^3
  let B := κ*L
  have hL : 1≤L := by dsimp only [L];linarith only [Real.log_natCast_nonneg X]
  have hLp := zero_lt_one.trans_le hL
  have hκ : 0≤κ := by dsimp only [κ];positivity
  have ha : 0≤A := pow_nonneg hLp.le _
  have hb : 0≤B := mul_nonneg hκ hLp.le
  have hmean := vaughan_typeII_dyadic_mean X P H H (vaughanActualLeft H) vaughanActualRight A B hP hH hH ha hb
    (fun Y hY S hS=>(vaughan_actual_square_bounds X Y H hY S hS).1)
    (fun Y hY S hS=>(vaughan_actual_square_bounds X Y H hY S hS).2)
  let f := fun q : ℕ => (1/(q.totient:ℝ))*(∑χ∈sievePrimitiveCharacters q,
    ‖vaughanCharacterBilinear χ X (vaughanTypeIICoefficient H) (vaughanTail H Λ)‖)
  have hsum : vaughanTypeIIConductorMass X H H D ≤ ∑ r∈Ico P (2*P),f (r+1) := by
    rw [sum_Ico_add' f P (2*P) 1]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨h₁,h₂⟩ := hD q hq
      exact mem_Ico.mpr ⟨h₁,by omega⟩
    · intro q _ _
      positivity
  simp_rw [vaughan_product_wave_eq_typeII] at hmean
  apply (hsum.trans hmean).trans
  have hb1 := actual_natlog_two_bound X X (by omega) (by omega)
  have hb2 := actual_natlog_two_bound X (X+1) (by omega) (by omega)
  change _≤3*L at hb1 hb2
  have hroot : Real.sqrt A*Real.sqrt B≤3*L^2 := by
    rw [←Real.sqrt_mul ha]
    have hak : κ≤9 := by dsimp only [κ];linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    have heq : A*B≤(3*L^2)^2 := by
      change L^3*(κ*L)≤_
      calc
        _ = κ*L^4 := by ring
        _ ≤ 9*L^4 := mul_le_mul_of_nonneg_right hak (by positivity)
        _ = _ := by ring
    exact (Real.sqrt_le_sqrt heq).trans_eq (Real.sqrt_sq (by positivity))
  let T := (X:ℝ)/H+(X:ℝ)/Real.sqrt H+(Q:ℝ)*Real.sqrt X
  have hT : 0≤T := by dsimp only [T];positivity
  have hscale : vaughanTypeIIScale X P H H ≤ 2*T := by
    have hhr : 0<(H:ℝ) := by exact_mod_cast hH
    have hpr : 0<(P:ℝ) := by exact_mod_cast hP
    have hhrp : (H:ℝ) ≤ 2*P := by exact_mod_cast hHP.le
    have hratio : (X:ℝ)/P ≤ 2*((X:ℝ)/H) := by
      rw [show 2*((X:ℝ)/H)=(2*X)/H by ring]
      apply (div_le_div_iff₀ hpr hhr).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hhrp (Nat.cast_nonneg (α:=ℝ) X)]
    have hq := mul_le_mul_of_nonneg_right (by exact_mod_cast hPQ : (P:ℝ)≤Q) (Real.sqrt_nonneg (X:ℝ))
    dsimp only [vaughanTypeIIScale,T]
    linarith only [hratio,hq,show 0≤(Q:ℝ)*Real.sqrt X by positivity]
  calc
    _ = ((((Nat.log 2 X+1:ℕ):ℝ))^2*(((Nat.log 2 (X+1)+1:ℕ):ℝ))*1024)*
        (Real.sqrt A*Real.sqrt B)*vaughanTypeIIScale X P H H := by ring
    _ ≤ (((3*L)^2*(3*L)*1024)*(3*L^2))*(2*T) := by
      have hpos : 0≤vaughanTypeIIScale X P H H := by dsimp only [vaughanTypeIIScale];positivity
      gcongr
    _ = 165888*L^5*T := by ring

theorem vaughan_actual_conductor_bound :
    ∃ C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ X Q H P : ℕ, 2≤X → 1≤Q → Q≤X → 1≤H →
      0<P → P≤Q → H<2*P → ∀ D : Finset ℕ, D⊆Ioc H Q → (∀q∈D,P<q ∧ q≤2*P) →
        vaughanTypeIIConductorMass X H H D ≤ C*(1+Real.log X)^b*
          ((X:ℝ)/H+(X:ℝ)/Real.sqrt H+Q*Real.sqrt X) :=
  ⟨165888,by norm_num,5,fun X Q H P hX _ _ hH hP hPQ hHP D _ hD =>
    vaughan_actual_dyadic_typeII_bound X Q H P hX hH hP hPQ hHP D hD⟩

end GoldbachPartial