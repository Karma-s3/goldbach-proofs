import DyadicCorrelationReduction
import Mathlib.NumberTheory.LSeries.Nonvanishing
namespace GoldbachPartial
open Finset ExtendedArcCoefficient
open scoped Classical
noncomputable def sieveCharacterWave {q:ℕ} (S:Finset ℕ) (a:ℕ→ℂ)
    (χ:DirichletCharacter ℂ q):ℂ := ∑m∈S,a m*χ (m:ZMod q)

noncomputable def sieveFareyWave (q:ℕ) [NeZero q] (S:Finset ℕ) (a:ℕ→ℂ)
    (u:(ZMod q)ˣ):ℂ := ∑m∈S,a m*E ((m:ℝ)*((u:ZMod q).val:ℝ)/(q:ℝ))

private theorem unit_sum_cast (q:ℕ) [NeZero q] (f:ZMod q→ℂ)
    (hf:∀x,¬IsUnit x→f x=0) :
    (∑x:ZMod q,f x)=∑u:(ZMod q)ˣ,f (u:ZMod q) := by
  classical
  symm
  apply sum_bij_ne_zero (fun (u:(ZMod q)ˣ) _ _=>(u:ZMod q))
  · simp
  · intro u hu hfu v hv hfv he;exact Units.ext he
  · intro x _ hfx
    have hx:IsUnit x := by by_contra h;exact hfx (hf x h)
    exact ⟨hx.unit,mem_univ _,by simpa only [hx.unit_spec] using hfx,hx.unit_spec⟩
  · simp

private theorem std_phase_nat_unit (q:ℕ) [NeZero q] (m:ℕ) (u:(ZMod q)ˣ) :
    ZMod.stdAddChar ((m:ZMod q)*(u:ZMod q))=E ((m:ℝ)*((u:ZMod q).val:ℝ)/(q:ℝ)) := by
  let b:ℕ:=(u:ZMod q).val
  have hh : ((↑((m:ℤ)*(b:ℤ)):ZMod q))=(m:ZMod q)*(u:ZMod q) := by simp only [b,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [←hh,ZMod.stdAddChar_coe]
  unfold E
  push_cast
  congr 1
  dsimp only [b]
  ring

theorem primitive_sieve_gauss_identity (q:ℕ) [NeZero q] (S:Finset ℕ) (a:ℕ→ℂ)
    (χ:DirichletCharacter ℂ q) (hχ:χ.IsPrimitive) :
    sieveCharacterWave S a χ*gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑u:(ZMod q)ˣ,sieveFareyWave q S a u*χ⁻¹ (u:ZMod q) := by
  have h (m:ℕ) : χ (m:ZMod q)*gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑u:(ZMod q)ˣ, E ((m:ℝ)*((u:ZMod q).val:ℝ)/q)*χ⁻¹ (u:ZMod q) := by
    have hG:=gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (m:ZMod q)
    rw [inv_inv] at hG
    rw [←hG]
    unfold gaussSum
    rw [unit_sum_cast q _ (fun x hx=>by rw [MulChar.map_nonunit _ hx,zero_mul])]
    apply sum_congr rfl;intro u _
    rw [AddChar.mulShift_apply,std_phase_nat_unit,mul_comm]
  unfold sieveCharacterWave sieveFareyWave
  rw [sum_mul]
  simp_rw [mul_assoc,h,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl;intro u _
  rw [sum_mul]
  apply sum_congr rfl;intro m _;ring

noncomputable def sievePrimitiveCharacters (q:ℕ) : Finset (DirichletCharacter ℂ q) :=
  univ.filter (fun χ=>χ.IsPrimitive)

theorem primitive_sieve_row_le_additive (q:ℕ) [NeZero q] (S:Finset ℕ) (a:ℕ→ℂ) :
    ((q:ℝ)/q.totient)*(∑χ∈sievePrimitiveCharacters q,‖sieveCharacterWave S a χ‖^2) ≤
      ∑u:(ZMod q)ˣ,‖sieveFareyWave q S a u‖^2 := by
  let X:=sievePrimitiveCharacters q
  let F (χ:DirichletCharacter ℂ q):ℝ := ‖∑u:(ZMod q)ˣ,sieveFareyWave q S a u*χ (u:ZMod q)‖^2
  have hrow (χ:DirichletCharacter ℂ q) (hχ:χ∈X) : (q:ℝ)*‖sieveCharacterWave S a χ‖^2=F χ⁻¹ := by
    have hprim := (mem_filter.mp hχ).2
    have hh := congrArg (fun z:ℂ=>‖z‖^2) (primitive_sieve_gauss_identity q S a χ hprim)
    rw [norm_mul,mul_pow,DirichletCharacter.norm_gaussSum_stdAddChar hprim.inv,Real.sq_sqrt (Nat.cast_nonneg _)] at hh
    simpa only [mul_comm (q:ℝ),F] using hh
  have hsum : (q:ℝ)*(∑χ∈X,‖sieveCharacterWave S a χ‖^2)≤(q.totient:ℝ)*∑u:(ZMod q)ˣ,‖sieveFareyWave q S a u‖^2 := by
    rw [mul_sum]
    calc _ = ∑χ∈X,F χ⁻¹ := sum_congr rfl hrow
         _ ≤ ∑χ:DirichletCharacter ℂ q,F χ⁻¹ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>sq_nonneg _)
         _ = ∑χ:DirichletCharacter ℂ q,F χ := Equiv.sum_comp (Equiv.inv _) F
         _ = _ := dirichlet_analysis_energy q _
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [div_mul_eq_mul_div,div_le_iff₀ hφ]
  simpa only [mul_comm (q.totient:ℝ)] using hsum

theorem primitive_sieve_family_le_additive (J S:Finset ℕ) (a:ℕ→ℂ) :
    (∑j∈J,(((j+1:ℕ):ℝ)/(j+1).totient)*
      ∑χ∈sievePrimitiveCharacters (j+1),‖sieveCharacterWave S a χ‖^2) ≤
      ∑j∈J,∑u:(ZMod (j+1))ˣ,‖sieveFareyWave (j+1) S a u‖^2 :=
  sum_le_sum fun j _=>primitive_sieve_row_le_additive (j+1) S a

/-- The bilinear Vaughan form summed over primitive characters. Both second moments
on the right are evaluated at actual reduced additive frequencies. -/
theorem vaughan_bilinear_le_farey (J M N:Finset ℕ) (a b:ℕ→ℂ) :
    (∑j∈J,(((j+1:ℕ):ℝ)/(j+1).totient)*
      ∑χ∈sievePrimitiveCharacters (j+1),‖sieveCharacterWave M a χ*sieveCharacterWave N b χ‖) ≤
      Real.sqrt (∑j∈J,∑u:(ZMod (j+1))ˣ,‖sieveFareyWave (j+1) M a u‖^2)*
      Real.sqrt (∑j∈J,∑u:(ZMod (j+1))ˣ,‖sieveFareyWave (j+1) N b u‖^2) := by
  let W (j:ℕ):ℝ:=((j+1:ℕ):ℝ)/(j+1).totient
  let T (j:ℕ):=sievePrimitiveCharacters (j+1)
  let A (i:Σj:ℕ,DirichletCharacter ℂ (j+1)):=Real.sqrt (W i.1)*‖sieveCharacterWave M a i.2‖
  let B (i:Σj:ℕ,DirichletCharacter ℂ (j+1)):=Real.sqrt (W i.1)*‖sieveCharacterWave N b i.2‖
  let H:=J.sigma T
  have hw (j:ℕ) : 0≤W j := by dsimp [W];positivity
  have hab : (∑j∈J,W j*∑χ∈T j,‖sieveCharacterWave M a χ*sieveCharacterWave N b χ‖)=∑i∈H,A i*B i := by
    rw [show H=J.sigma T from rfl,sum_sigma]
    apply sum_congr rfl;intro j _
    rw [mul_sum]
    apply sum_congr rfl;intro χ _
    dsimp only [A,B];rw [norm_mul]
    linear_combination -(‖sieveCharacterWave M a χ‖*‖sieveCharacterWave N b χ‖)*(Real.sq_sqrt (hw j))
  have hm (S:Finset ℕ) (c:ℕ→ℂ) :
      (∑i∈H,(Real.sqrt (W i.1)*‖sieveCharacterWave S c i.2‖)^2)≤
        ∑j∈J,∑u:(ZMod (j+1))ˣ,‖sieveFareyWave (j+1) S c u‖^2 := by
    apply le_trans _ (primitive_sieve_family_le_additive J S c)
    rw [show H=J.sigma T from rfl,sum_sigma]
    apply le_of_eq;apply sum_congr rfl;intro j _
    rw [mul_sum];apply sum_congr rfl;intro χ _
    dsimp only;rw [mul_pow,Real.sq_sqrt (hw j)]
  change (∑j∈J,W j*∑χ∈T j,‖sieveCharacterWave M a χ*sieveCharacterWave N b χ‖)≤_
  rw [hab]
  apply (Real.sum_mul_le_sqrt_mul_sqrt H A B).trans
  exact mul_le_mul (Real.sqrt_le_sqrt (hm M a)) (Real.sqrt_le_sqrt (hm N b))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end GoldbachPartial
