import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import VerifiedMedDeskProgression

namespace GoldbachPartial
open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

noncomputable def vaughanInitial (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤U then f n else 0,by simp⟩

noncomputable def vaughanTail (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f-vaughanInitial U f

theorem vaughanTail_apply (U k : ℕ) (f : ArithmeticFunction ℝ) :
    vaughanTail U f k = if U<k then f k else 0 := by
  change f k-(if k≤U then f k else 0)=_
  by_cases h : k≤U
  · rw [ite_eq_left h,ite_eq_right h.not_gt,sub_self]
  · rw [ite_eq_right h,ite_eq_left (lt_of_not_ge h),sub_zero]

/-- Vaughan's exact identity as Dirichlet convolution. Here zeta is the constant-one
function on positive integers; the ring unit is the delta mass at one. -/
theorem vaughan_arithmetic_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      vaughanInitial V Λ + (vaughanInitial U (μ : ArithmeticFunction ℝ))*ArithmeticFunction.log -
      ((vaughanInitial U (μ : ArithmeticFunction ℝ))*(ζ : ArithmeticFunction ℝ))*vaughanInitial V Λ +
      (vaughanTail U (μ : ArithmeticFunction ℝ)*(ζ : ArithmeticFunction ℝ))*vaughanTail V Λ := by
  have hid : ((μ : ArithmeticFunction ℝ)*(ζ : ArithmeticFunction ℝ))=1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  calc
    Λ = vaughanInitial V Λ + ((μ : ArithmeticFunction ℝ)*(ζ : ArithmeticFunction ℝ)) *
          (Λ-vaughanInitial V Λ) := by rw [hid,one_mul];abel
    _ = _ := by rw [←ArithmeticFunction.zeta_mul_vonMangoldt];unfold vaughanTail;ring

/-- Finite hyperbola identity with no diagonal or endpoint loss. -/
theorem vaughan_finite_hyperbola {R : Type*} [AddCommMonoid R] (N : ℕ) (F : ℕ×ℕ→R) :
    (∑ k∈Icc 1 N,∑ x∈k.divisorsAntidiagonal,F x) =
      ∑ m∈Icc 1 N,∑ j∈Icc 1 (N/m),F (m,j) := by
  let K := Icc 1 N
  let P := (K ×ˢ K).filter (fun x=>x.1*x.2≤N)
  have hmaps (x : ℕ×ℕ) (hx : x∈P) : x.1*x.2∈K := by
    obtain ⟨hw,hle⟩ := mem_filter.mp hx
    obtain ⟨h1,h2⟩ := mem_product.mp hw
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp h1).1 (mem_Icc.mp h2).1,hle⟩
  have hf (k : ℕ) (hk : k∈K) :
      P.filter (fun x=>x.1*x.2=k)=k.divisorsAntidiagonal := by
    ext x
    obtain ⟨hk1,hkN⟩ := mem_Icc.mp hk
    constructor
    · intro hh
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
    · intro hh
      obtain ⟨hxy,_⟩ := Nat.mem_divisorsAntidiagonal.mp hh
      have h1 : 0<x.1 := Nat.pos_of_dvd_of_pos (hxy ▸ dvd_mul_right x.1 x.2) hk1
      have h2 : 0<x.2 := Nat.pos_of_dvd_of_pos (hxy ▸ dvd_mul_left x.2 x.1) hk1
      have h1N := (Nat.le_of_dvd hk1 (hxy ▸ dvd_mul_right x.1 x.2)).trans hkN
      have h2N := (Nat.le_of_dvd hk1 (hxy ▸ dvd_mul_left x.2 x.1)).trans hkN
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨h1,h1N⟩,mem_Icc.mpr ⟨h2,h2N⟩⟩,hxy.le.trans hkN⟩,hxy⟩
  calc
    _ = ∑ k∈K,∑ x∈P.filter (fun x=>x.1*x.2=k),F x :=
      sum_congr rfl (fun k hk=>by rw [hf k hk])
    _ = ∑ x∈P,F x := sum_fiberwise_of_maps_to hmaps F
    _ = ∑ m∈K,∑ j∈K,if m*j≤N then F (m,j) else 0 := by rw [sum_filter,sum_product]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      have hm0 : 0<m := (mem_Icc.mp hm).1
      rw [←sum_filter]
      apply sum_congr _ (fun _ _=>rfl)
      ext j
      simp only [K,mem_filter,mem_Icc]
      constructor
      · rintro ⟨⟨hj,_⟩,hmj⟩
        exact ⟨hj,(Nat.le_div_iff_mul_le hm0).mpr (by simpa only [Nat.mul_comm] using hmj)⟩
      · rintro ⟨hj,hjmax⟩
        exact ⟨⟨hj,hjmax.trans (Nat.div_le_self ..)⟩,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hjmax⟩

noncomputable def vaughanCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ k∈Icc 1 N,(f k:ℂ)*χ (k:ZMod q)

noncomputable def vaughanCharacterBilinear {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ m∈Icc 1 N,((f m:ℂ)*χ (m:ZMod q))*(∑ j∈Icc 1 (N/m),(g j:ℂ)*χ (j:ZMod q))

theorem vaughan_character_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (f g : ArithmeticFunction ℝ) :
    vaughanCharacterSum χ N (f*g)=vaughanCharacterBilinear χ N f g := by
  let F := fun x : ℕ×ℕ => ((f x.1:ℂ)*χ (x.1:ZMod q))*((g x.2:ℂ)*χ (x.2:ZMod q))
  calc
    _ = ∑ k∈Icc 1 N,∑x∈k.divisorsAntidiagonal,F x := by
      apply sum_congr rfl
      intro k _
      rw [ArithmeticFunction.mul_apply,Complex.ofReal_sum,sum_mul]
      apply sum_congr rfl
      intro x hx
      have hxy := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [←hxy,Nat.cast_mul,map_mul,Complex.ofReal_mul]
      dsimp only [F]
      ring
    _ = _ := by
      rw [vaughan_finite_hyperbola]
      unfold vaughanCharacterBilinear
      apply sum_congr rfl
      intro m _
      rw [mul_sum]

noncomputable def vaughanTypeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  vaughanInitial U (μ : ArithmeticFunction ℝ) * vaughanInitial V Λ
noncomputable def vaughanTypeIICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  vaughanTail U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

/-- A short Mangoldt prefix, two Type I terms, and one Type II term, for each character. -/
theorem vaughan_character_sum_identity {q : ℕ} (χ : DirichletCharacter ℂ q) (N U V : ℕ) :
    vaughanCharacterSum χ N Λ =
      vaughanCharacterSum χ N (vaughanInitial V Λ) +
      vaughanCharacterBilinear χ N (vaughanInitial U (μ : ArithmeticFunction ℝ)) ArithmeticFunction.log -
      vaughanCharacterBilinear χ N (vaughanTypeICoefficient U V) (ζ : ArithmeticFunction ℝ) +
      vaughanCharacterBilinear χ N (vaughanTypeIICoefficient U) (vaughanTail V Λ) := by
  have hid : Λ = vaughanInitial V Λ + vaughanInitial U (μ : ArithmeticFunction ℝ)*ArithmeticFunction.log -
      vaughanTypeICoefficient U V*(ζ : ArithmeticFunction ℝ)+vaughanTypeIICoefficient U*vaughanTail V Λ := by
    apply (vaughan_arithmetic_identity U V).trans
    dsimp only [vaughanTypeICoefficient,vaughanTypeIICoefficient]
    ring
  simp only [←vaughan_character_convolution,vaughanCharacterSum,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  have hp := congrArg (fun f : ArithmeticFunction ℝ => f k) hid
  change Λ k = _ at hp
  simp only [add_apply,sub_apply] at hp
  rw [hp]
  push_cast
  ring

theorem vaughanTypeICoefficient_support (U V m : ℕ) (hm : U*V<m) :
    vaughanTypeICoefficient U V m=0 := by
  rw [vaughanTypeICoefficient,ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro x hx
  have hxy := (Nat.mem_divisorsAntidiagonal.mp hx).1
  change (if x.1≤U then _ else 0)*(if x.2≤V then _ else 0)=0
  by_cases h₁ : x.1≤U
  · have h₂ : ¬x.2≤V := fun h => hm.not_ge (hxy ▸ Nat.mul_le_mul h₁ h)
    rw [ite_eq_right h₂,mul_zero]
  · rw [ite_eq_right h₁,zero_mul]

theorem vaughanTypeIICoefficient_divisors (U m : ℕ) :
    vaughanTypeIICoefficient U m = ∑ d∈m.divisors.filter (fun d=>U<d),(μ d:ℝ) := by
  rw [vaughanTypeIICoefficient,ArithmeticFunction.coe_mul_zeta_apply,sum_filter]
  apply sum_congr rfl
  intro d _
  exact vaughanTail_apply U d (μ : ArithmeticFunction ℝ)

theorem vaughanTypeIICoefficient_support (U m : ℕ) (hm : m≤U) :
    vaughanTypeIICoefficient U m=0 := by
  rw [vaughanTypeIICoefficient_divisors]
  apply sum_eq_zero
  intro d hd
  obtain ⟨hd',hgt⟩ := mem_filter.mp hd
  exact False.elim (hgt.not_ge ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd').2) (Nat.dvd_of_mem_divisors hd')).trans hm))

theorem vaughanTypeIICoefficient_abs_le (U m : ℕ) :
    |vaughanTypeIICoefficient U m|≤(m.divisors.card:ℝ) := by
  rw [vaughanTypeIICoefficient_divisors]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _d∈m.divisors.filter (fun d=>U<d),(1:ℝ) := by
      apply sum_le_sum
      intro d _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul,mul_one]
      exact_mod_cast card_le_card (filter_subset _ _)

theorem vaughanTypeICoefficient_abs_le (U V m : ℕ) :
    |vaughanTypeICoefficient U V m| ≤ Real.log m := by
  rw [vaughanTypeICoefficient,ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ x∈m.divisorsAntidiagonal,Λ x.2 := by
      apply sum_le_sum
      intro x _
      change |(if x.1≤U then (μ x.1:ℝ) else 0)*(if x.2≤V then Λ x.2 else 0)| ≤ _
      by_cases h₁ : x.1≤U
      · by_cases h₂ : x.2≤V
        · rw [ite_eq_left h₁,ite_eq_left h₂,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
            (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=x.1)))
        · rw [ite_eq_right h₂,mul_zero,abs_zero]
          exact ArithmeticFunction.vonMangoldt_nonneg
      · rw [ite_eq_right h₁,zero_mul,abs_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ d∈m.divisors,Λ d := Nat.sum_divisorsAntidiagonal' (fun _ j=>Λ j)
    _ = _ := ArithmeticFunction.vonMangoldt_sum

theorem vaughan_character_typeII_active {q : ℕ} (χ : DirichletCharacter ℂ q) (N U V : ℕ) :
    vaughanCharacterBilinear χ N (vaughanTypeIICoefficient U) (vaughanTail V Λ) =
      ∑ m∈Ioc U (N/(V+1)),((vaughanTypeIICoefficient U m:ℂ)*χ (m:ZMod q)) *
        (∑j∈Ioc V (N/m),(Λ j:ℂ)*χ (j:ZMod q)) := by
  let f := fun m : ℕ => ((vaughanTypeIICoefficient U m:ℂ)*χ (m:ZMod q)) *
        (∑j∈Ioc V (N/m),(Λ j:ℂ)*χ (j:ZMod q))
  have hinner (m : ℕ) : (∑j∈Icc 1 (N/m),(vaughanTail V Λ j:ℂ)*χ (j:ZMod q)) =
      ∑j∈Ioc V (N/m),(Λ j:ℂ)*χ (j:ZMod q) := by
    have hset : Ioc V (N/m)=(Icc 1 (N/m)).filter (fun j=>V<j) := by
      ext j
      simp only [mem_Ioc,mem_filter,mem_Icc]
      omega
    rw [hset,sum_filter]
    apply sum_congr rfl
    intro j _
    rw [vaughanTail_apply]
    by_cases hj : V<j <;> simp [hj]
  unfold vaughanCharacterBilinear
  simp_rw [hinner]
  change ∑m∈Icc 1 N,f m = ∑m∈Ioc U (N/(V+1)),f m
  symm
  apply sum_subset
  · intro m hm
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hm
    exact mem_Icc.mpr ⟨by omega,hu.trans (Nat.div_le_self ..)⟩
  · intro m hm hno
    have hmpos := (mem_Icc.mp hm).1
    dsimp only [f]
    by_cases hU : m≤U
    · rw [vaughanTypeIICoefficient_support U m hU]
      simp
    · have hbig : N/(V+1)<m := by
        by_contra! hh
        exact hno (mem_Ioc.mpr ⟨by omega,hh⟩)
      have hquot : N/m≤V := by
        by_contra! hV
        have hmn := (Nat.le_div_iff_mul_le hmpos).mp hV
        exact hbig.not_ge ((Nat.le_div_iff_mul_le (Nat.succ_pos V)).mpr (by simpa only [Nat.mul_comm] using hmn))
      rw [Ioc_eq_empty (by omega : ¬V<N/m),sum_empty,mul_zero]

end GoldbachPartial