import VerifiedBlockBonferroni
namespace GoldbachPartial
open Finset

private theorem sum_powerset_disjoint_union {α : Type*} [DecidableEq α] (A B : Finset α)
    (h : Disjoint A B) (f : Finset α→ℝ) :
    (∑s∈(A∪B).powerset,f s)=∑a∈A.powerset,∑b∈B.powerset,f (a∪b) := by
  rw [←sum_product']
  apply sum_bij (fun s _ => (s∩A,s∩B))
  · intro s hs
    exact mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,mem_powerset.mpr inter_subset_right⟩
  · intro s hs t ht he
    have hu : ∀ {u}, u⊆A∪B → (u∩A)∪(u∩B)=u := by
      intro u hu
      ext p
      simp only [mem_union,mem_inter]
      have ha (hp : p∈u) := mem_union.mp (hu hp)
      tauto
    rw [←hu (mem_powerset.mp hs),←hu (mem_powerset.mp ht)]
    exact congrArg₂ (·∪·) (congrArg Prod.fst he) (congrArg Prod.snd he)
  · rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have ha' := mem_powerset.mp ha
    have hb' := mem_powerset.mp hb
    refine ⟨a∪b,mem_powerset.mpr (union_subset_union ha' hb'),Prod.ext ?_ ?_⟩
    · change (a∪b)∩A=a
      ext p
      simp only [mem_inter,mem_union]
      have h₁ (hh:p∈a) := ha' hh
      have h₂ (hh:p∈b) : p∉A := fun hA => disjoint_left.mp h hA (hb' hh)
      tauto
    · change (a∪b)∩B=b
      ext p
      simp only [mem_inter,mem_union]
      have h₁ (hh:p∈b) := hb' hh
      have h₂ (hh:p∈a) : p∉B := fun hB => disjoint_left.mp h (ha' hh) hB
      tauto
  · intro s hs
    congr 1
    ext p
    simp only [mem_union,mem_inter]
    have hh (hp:p∈s) := mem_union.mp (mem_powerset.mp hs hp)
    tauto

theorem block_powerset_factorization {κ α : Type*} [DecidableEq κ] [DecidableEq α]
    (J : Finset κ) (B : κ → Finset α) (hdisj : ∀ i∈J,∀ j∈J,i≠j → Disjoint (B i) (B j))
    (f : κ→Finset α→ℝ) :
    (∑s∈(J.biUnion B).powerset,∏j∈J,f j (s∩B j))=∏j∈J,∑t∈(B j).powerset,f j t := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    have hJ := fun j hj k hk hne => hdisj j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hne
    have hd : Disjoint (B i) (J.biUnion B) := by
      apply disjoint_left.mpr
      intro p hp hu
      obtain ⟨j,hj,hm⟩ := mem_biUnion.mp hu
      exact disjoint_left.mp (hdisj i (mem_insert_self ..) j (mem_insert_of_mem hj) (fun he => hi (he ▸ hj))) hp hm
    rw [biUnion_insert,sum_powerset_disjoint_union (B i) (J.biUnion B) hd,prod_insert hi,←ih hJ,sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    have ha' := mem_powerset.mp ha
    have hb' := mem_powerset.mp hb
    have he : (a∪b)∩B i=a := by
      ext p
      simp only [mem_inter,mem_union]
      have h₁ (h:p∈a) := ha' h
      have h₂ (h:p∈b) : p∉B i := fun hm => disjoint_left.mp hd hm (hb' h)
      tauto
    rw [prod_insert hi,he]
    congr 1
    apply prod_congr rfl
    intro j hj
    congr 1
    ext p
    simp only [mem_inter,mem_union]
    have h₁ (h:p∈B j) : p∈J.biUnion B := mem_biUnion.mpr ⟨j,hj,h⟩
    have h₂ (h:p∈a) : p∉J.biUnion B := fun hm => disjoint_left.mp hd (ha' h) hm
    tauto
end GoldbachPartial