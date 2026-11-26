import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GoldbachPartial
open Finset

/-- Number of residues for which both summands are units. -/
noncomputable def admissibleZCount (q c : ℕ) : ℕ :=
  Nat.card {a : ZMod q // IsUnit a ∧ IsUnit ((c : ZMod q)-a)}

open Classical in
private theorem admissible_units_card (q : ℕ) [NeZero q] :
    (univ.filter (fun a : ZMod q => IsUnit a)).card=q.totient := by
  classical
  let e : {x : ZMod q // IsUnit x} ≃ (ZMod q)ˣ :=
    { toFun := fun x => x.2.unit
      invFun := fun u => ⟨u,u.isUnit⟩
      left_inv := fun x => Subtype.ext x.2.unit_spec
      right_inv := fun u => Units.ext u.isUnit.unit_spec }
  rw [←Fintype.card_subtype,Fintype.card_congr e,ZMod.card_units_eq_totient]

open Classical in
theorem admissibleZCount_inclusion_lower (q c : ℕ) [NeZero q] :
    2*q.totient≤admissibleZCount q c+q := by
  classical
  let U := univ.filter (fun a : ZMod q => IsUnit a)
  let V := univ.filter (fun a : ZMod q => IsUnit ((c:ZMod q)-a))
  have hU : U.card=q.totient := admissible_units_card q
  have hVU : V.card=U.card := by
    apply card_bij (fun a _ => (c:ZMod q)-a)
    · intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩
    · intro a _ b _ h
      exact sub_right_inj.mp h
    · intro a ha
      refine ⟨(c:ZMod q)-a,mem_filter.mpr ⟨mem_univ _,?_⟩,sub_sub_cancel _ _⟩
      rw [sub_sub_cancel];exact (mem_filter.mp ha).2
  have hI : (U∩V).card=admissibleZCount q c := by
    unfold admissibleZCount
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext a
    simp [U,V]
  have hle := card_le_univ (U∪V)
  rw [ZMod.card] at hle
  have hsum := card_inter_add_card_union U V
  omega

/-- The odd prime-power local density lower bound. -/
theorem admissibleZCount_odd_power (p k c : ℕ) (hp : p.Prime) (hodd : 2<p) :
    1-1/((p:ℝ)-1)^2≤((p^(k+1):ℕ):ℝ)*(admissibleZCount (p^(k+1)) c:ℝ)/
      ((p^(k+1)).totient:ℝ)^2 := by
  have : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := admissibleZCount_inclusion_lower (p^(k+1)) c
  rw [Nat.totient_prime_pow_succ hp] at h ⊢
  have hp2 : (2:ℝ)<p := by exact_mod_cast hodd
  have hp0 : (0:ℝ)<p := by linarith
  have hP : (0:ℝ)<(p:ℝ)-1 := by linarith
  have hx : (0:ℝ)<(p:ℝ)^k := pow_pos hp0 _
  let K := (admissibleZCount (p^(k+1)) c:ℝ)
  have hr : 2*((p:ℝ)^k*((p:ℝ)-1))≤K+(p:ℝ)^(k+1) := by
    have hh : (((p-1:ℕ):ℝ))=(p:ℝ)-1 := by rw [Nat.cast_sub hp.one_le,Nat.cast_one]
    rw [←hh];dsimp only [K];exact_mod_cast h
  have hb : (p:ℝ)^k*((p:ℝ)-2)≤K := by rw [pow_succ] at hr;linarith only [hr]
  push_cast [Nat.cast_sub hp.one_le]
  change 1-1/((p:ℝ)-1)^2≤(p:ℝ)^(k+1)*K/((p:ℝ)^k*((p:ℝ)-1))^2
  calc
    _ = (p:ℝ)^(k+1)*((p:ℝ)^k*((p:ℝ)-2))/((p:ℝ)^k*((p:ℝ)-1))^2 := by
      rw [pow_succ];field_simp;ring
    _ ≤ _ := by gcongr

/-- For an even target every unit modulo a positive power of two has a unit complement. -/
theorem admissibleZCount_two_power_eq (k t : ℕ) :
    admissibleZCount (2^(k+1)) (2*t)=(2^(k+1)).totient := by
  classical
  let q := 2^(k+1)
  have : NeZero q := ⟨by dsimp [q];positivity⟩
  have hd : 2∣q := by dsimp [q];rw [pow_succ];exact dvd_mul_left .. 
  let π := ZMod.castHom hd (ZMod 2)
  have hu (x : ZMod q) : IsUnit x ↔ π x≠0 := by
    rw [←ZMod.natCast_zmod_val x,map_natCast]
    change IsUnit (x.val:ZMod (2^(k+1))) ↔ (x.val:ZMod 2)≠0
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (Nat.succ_pos k)]
    exact not_congr (ZMod.natCast_eq_zero_iff x.val 2).symm
  have hsame (a : ZMod q) (ha : IsUnit a) : IsUnit ((↑(2*t):ZMod q)-a) := by
    rw [hu,map_sub,map_natCast]
    have hz : ((2*t:ℕ):ZMod 2)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (dvd_mul_right ..)
    rw [hz,zero_sub,neg_ne_zero];exact (hu a).mp ha
  change admissibleZCount q (2*t)=q.totient
  unfold admissibleZCount
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←admissible_units_card]
  congr 1
  ext a
  simp only [mem_filter,mem_univ,true_and]
  exact ⟨And.left,fun h => ⟨h,hsame a h⟩⟩

theorem admissibleZCount_two_power (k t : ℕ) :
    2≤((2^(k+1):ℕ):ℝ)*(admissibleZCount (2^(k+1)) (2*t):ℝ)/
      ((2^(k+1)).totient:ℝ)^2 := by
  rw [admissibleZCount_two_power_eq,Nat.totient_prime_pow_succ Nat.prime_two]
  norm_num
  rw [pow_succ];field_simp
  norm_num

end GoldbachPartial
