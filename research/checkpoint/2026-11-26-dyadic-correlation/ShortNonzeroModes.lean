import PrimeArcModelBounds

namespace GoldbachPartial
open Finset

def shortNonzeroModes (H : ℕ) : Finset ℤ := (Icc (-(H:ℤ)) H).erase 0

theorem sum_shortNonzeroModes {A : Type*} [AddCommMonoid A] (H:ℕ) (f:ℤ→A) :
    ∑ h ∈ shortNonzeroModes H, f h =
      ∑ k ∈ range H, (f ((k+1:ℕ):ℤ)+f (-((k+1:ℕ):ℤ))) := by
  classical
  let p (k:ℕ) : ℤ := (k+1:ℕ)
  let m (k:ℕ) : ℤ := -((k+1:ℕ):ℤ)
  have he : shortNonzeroModes H = (range H).image p ∪ (range H).image m := by
    ext h
    simp only [shortNonzeroModes,mem_erase,mem_Icc,mem_union,mem_image,mem_range]
    dsimp only [p,m]
    constructor
    · intro hh
      by_cases h0 : 0<h
      · exact Or.inl ⟨h.toNat-1,by omega,by omega⟩
      · exact Or.inr ⟨(-h).toNat-1,by omega,by omega⟩
    · rintro (⟨k,hk,rfl⟩|⟨k,hk,rfl⟩) <;> omega
  have hd : Disjoint ((range H).image p) ((range H).image m) := by
    apply Finset.disjoint_left.mpr
    intro h ha hb
    obtain ⟨k,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,hj⟩ := mem_image.mp hb
    dsimp only [p,m] at hj
    omega
  rw [he,sum_union hd,sum_image (by intro a _ b _ h; dsimp [p] at h; omega),
    sum_image (by intro a _ b _ h; dsimp [m] at h; omega),sum_add_distrib]

end GoldbachPartial