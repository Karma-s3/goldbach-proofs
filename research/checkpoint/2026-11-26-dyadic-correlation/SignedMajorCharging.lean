import FejerMajorWindow

namespace GoldbachPartial
open Finset
noncomputable section

/-- In a decreasing denominator weight, erasing one negative local factor
charges a negative term to a positive parent. -/
theorem powerset_signed_charging (S : Finset ℕ) (c W : ℕ → ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hW : ∀ d, 0≤W d)
    (hmono : ∀ i j : ℕ, 0 < i → i ≤ j → W j≤W i) :
    (1-∑ p ∈ S, max 0 (-c p))*
      (∑ t ∈ S.powerset, max 0 ((∏ p ∈ t,c p)*W (∏ p ∈ t,p))) ≤
      ∑ t ∈ S.powerset, (∏ p ∈ t,c p)*W (∏ p ∈ t,p) := by
  classical
  let F := fun t : Finset ℕ => (∏ p ∈ t,c p)*W (∏ p ∈ t,p)
  let E := fun t => max 0 (F t)
  let O := fun t => max 0 (-F t)
  let b := fun p => max 0 (-c p)
  let g := fun (t : Finset ℕ) p => if p∈t then b p*E (t.erase p) else 0
  have hE (t) : 0≤E t := le_max_left .. 
  have hb (p) : 0≤b p := le_max_left ..
  have hg (t p) : 0≤g t p := by
    dsimp only [g]
    split
    · exact mul_nonneg (hb _) (hE _)
    · exact le_rfl
  have hcharge (t : Finset ℕ) (ht : t∈S.powerset) : O t ≤ ∑ p ∈ S,g t p := by
    by_cases H : 0≤F t
    · have he : O t=0 := max_eq_left (by linarith)
      rw [he]; exact sum_nonneg (fun p _ => hg t p)
    have hFlt : F t < 0 := lt_of_not_ge H
    have hn : ∃ p∈t, c p < 0 := by
      by_contra! h
      exact H (mul_nonneg (prod_nonneg h) (hW _))
    obtain ⟨p,hp,hc⟩ := hn
    let u := t.erase p
    let z := ∏ r∈u,c r
    let d := ∏ r∈u,r
    have hcp : c p*z=∏ r∈t,c r := mul_prod_erase t c hp
    have hdp : p*d=∏ r∈t,r := mul_prod_erase t id hp
    have hpos : 0 < z := by
      by_contra! h
      apply H
      dsimp only [F]; rw [←hcp]
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hc.le h) (hW _)
    have hd : 0 < d := prod_pos fun q hq => hS q (mem_powerset.mp ht (mem_of_mem_erase hq))
    have hp0 := hS p (mem_powerset.mp ht hp)
    have hmon := hmono d (p*d) hd (Nat.le_mul_of_pos_left d hp0)
    have hu : E u = z*W d := max_eq_right (mul_nonneg hpos.le (hW _))
    calc O t = (-c p)*z*W (p*d) := by
           dsimp only [O]; rw [max_eq_right (by linarith : 0 ≤ -F t)]
           dsimp only [F]; rw [←hcp,←hdp]; ring
         _ ≤ (-c p)*z*W d := mul_le_mul_of_nonneg_left hmon (mul_nonneg (by linarith) hpos.le)
         _ = g t p := by
           dsimp only [g]; rw [ite_eq_left hp]
           change _ = b p * E u
           rw [hu,show b p= -c p from max_eq_right (by linarith)]; ring
         _ ≤ _ := single_le_sum (fun p _ => hg t p) (mem_powerset.mp ht hp)
  have hfiber (p : ℕ) (hp:p∈S) : (∑ t ∈ S.powerset,g t p) ≤ b p*∑ t ∈ S.powerset,E t := by
    let D := S.erase p
    have hD : p∉D := by simp [D] 
    have hno (t : Finset ℕ) (ht:t∈D.powerset) : p∉t := fun h => hD (mem_powerset.mp ht h)
    have hzero : (∑ t ∈ D.powerset, g t p)=0 :=
      sum_eq_zero (fun t ht => ite_eq_right (hno t ht))
    have hrow : (∑ t ∈ D.powerset,g (insert p t) p)=∑ t ∈ D.powerset,b p*E t := by
      apply sum_congr rfl; intro t ht
      simp [g,erase_insert (hno t ht)]
    calc _ = ∑ t ∈ D.powerset,b p*E t := by
           conv_lhs => rw [←insert_erase hp]
           rw [sum_powerset_insert hD,hzero,zero_add,hrow]
         _ = b p*∑ t ∈ D.powerset,E t := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (sum_le_sum_of_subset_of_nonneg (powerset_mono.mpr (erase_subset p S)) (fun t _ _ => hE t)) (hb p)
  have hO : (∑ t ∈ S.powerset,O t) ≤ (∑ p ∈ S,b p)*(∑ t ∈ S.powerset,E t) := by
    calc _ ≤ ∑ t ∈ S.powerset, ∑ p ∈ S,g t p := sum_le_sum hcharge
         _ = ∑ p ∈ S, ∑ t ∈ S.powerset,g t p := sum_comm
         _ ≤ ∑ p ∈ S,b p*(∑ t ∈ S.powerset,E t) := sum_le_sum hfiber
         _ = _ := (sum_mul ..).symm
  have heq : (∑ t ∈ S.powerset,F t)=(∑ t ∈ S.powerset,E t)-(∑ t ∈ S.powerset,O t) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl; intro t _
    dsimp only [E,O]
    rcases le_total (0:ℝ) (F t) with h|h
    · rw [max_eq_right h,max_eq_left (by linarith)]; ring
    · rw [max_eq_left h,max_eq_right (by linarith)]; ring
  change (1-∑ p ∈ S,b p)*(∑ t ∈ S.powerset,E t) ≤ ∑ t ∈ S.powerset,F t
  rw [heq]
  linarith only [hO]

private theorem major_reciprocal_partial (m : ℕ) :
    (∑ j ∈ range m, 1 / ((j:ℝ)+1)^2) ≤ 7/4 := by
  have tail (v : ℕ) :
      (∑ j ∈ range v, 1 / ((j:ℝ)+3)^2) ≤ 1/2 - 1/((v:ℝ)+2) := by
    induction v with
    | zero => norm_num
    | succ v ih =>
      rw [sum_range_succ]
      push_cast
      have h3 : (v:ℝ)+3 ≠ 0 := by positivity
      have h2 : (v:ℝ)+2 ≠ 0 := by positivity
      have step : 1/((v:ℝ)+3)^2 ≤ 1/((v:ℝ)+2) - 1/((v:ℝ)+3) := by
        field_simp
        nlinarith only [show (0:ℝ) ≤ v by positivity]
      rw [show (v:ℝ)+1+2=(v:ℝ)+3 by ring]
      linarith only [ih,step]
  rcases m with _|m
  · norm_num
  rcases m with _|m
  · norm_num
  rw [show m+1+1=2+m by omega, sum_range_add]
  norm_num [sum_range_succ]
  have he (j:ℕ) : 2+(j:ℝ)+1=(j:ℝ)+3 := by ring
  simp_rw [he, ←one_div]
  linarith only [tail m, show (0:ℝ) ≤ 1/((m:ℝ)+2) by positivity]

theorem major_odd_prime_cost (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    (∑ p ∈ P, 1/((p:ℝ)-1)^2) ≤ 7/16 := by
  let j := fun p : ℕ => p/2-1
  let M := P.sup id + 1
  have rep (p:ℕ) (hp:p∈P) : p=2*(j p+1)+1 := by
    have ho := (hP p hp).1.odd_of_ne_two (by have := (hP p hp).2; omega)
    obtain ⟨k,hk⟩ := ho
    dsimp [j]; have := (hP p hp).2; omega
  have weight_eq (p:ℕ) (hp:p∈P) :
      1/((p:ℝ)-1)^2 = (1/4:ℝ)*(1/(((j p):ℝ)+1)^2) := by
    have h : (p:ℝ)=2*(((j p):ℝ)+1)+1 := by exact_mod_cast rep p hp
    rw [show (p:ℝ)-1 = 2*(((j p):ℝ)+1) by linarith only [h]]
    have hpos : ((j p:ℕ):ℝ)+1 ≠ 0 := by positivity
    field_simp
    norm_num
  have hs : (∑ p ∈ P, 1/((p:ℝ)-1)^2) ≤ ∑ i ∈ range M, (1/4:ℝ)*(1/((i:ℝ)+1)^2) := by
    apply sum_le_sum_of_injOn j
    · intro p hp q hq he
      have hap := rep p hp; have haq := rep q hq
      omega
    · intro i hi
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
      apply mem_range.mpr
      have hh : p ≤ P.sup id := le_sup (f:=id) hp
      have h := rep p hp
      dsimp only [M]; omega
    · intro p hp
      exact (weight_eq p hp).le
    · intros; positivity
  rw [←mul_sum] at hs
  linarith only [hs,major_reciprocal_partial M]

/-- Local signed coefficient in the model of the pinned main-arc proof. -/
def majorPrimeLocal (p n : ℕ) : ℝ :=
  if p ∣ n then 1/((p:ℝ)-1) else -(1/((p:ℝ)-1)^2)

theorem signed_major_prime_floor {n : ℕ} (hn : Even n) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (h2 : 2∈P) (W : ℕ → ℝ)
    (hw : ∀ q, 0 ≤ W q) (hm : ∀ i j : ℕ, 0 < i → i ≤ j → W j ≤ W i) :
    (9/16:ℝ)*(W 1+W 2) ≤
    ∑ t ∈ P.powerset, (∏ p ∈ t,majorPrimeLocal p n)*W (∏ p ∈ t,p) := by
  classical
  let c := fun p => majorPrimeLocal p n
  let B := P.filter (fun p => ¬ p∣n)
  have hd : 2∣n := even_iff_two_dvd.mp hn
  have hB (p:ℕ) (hp:p∈B) : p.Prime ∧ 2 < p := by
    obtain ⟨h,h'⟩ := mem_filter.mp hp
    have hp' := hP p h
    exact ⟨hp',lt_of_le_of_ne hp'.two_le (fun e => h' (e ▸ hd))⟩
  have cost_eq : (∑ p ∈ P,max 0 (-c p)) = ∑ p ∈ B,1/((p:ℝ)-1)^2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    have ha : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    by_cases h : p∣n
    · have hv : 0 ≤ 1/((p:ℝ)-1) := by positivity
      simp only [c,majorPrimeLocal,ite_eq_left h,ite_eq_right (not_not_intro h)]
      exact max_eq_left (neg_nonpos.mpr hv)
    · have hv : 0 ≤ 1/((p:ℝ)-1)^2 := by positivity
      simp only [c,majorPrimeLocal,ite_eq_right h,ite_eq_left h,neg_neg]
      exact max_eq_right hv
  have hcost : (∑ p ∈ P,max 0 (-c p)) ≤ 7/16 := cost_eq.trans_le (major_odd_prime_cost B hB)
  let E := fun t:Finset ℕ => max 0 ((∏ p ∈ t,c p)*W (∏ p ∈ t,p))
  have hE (t) : 0 ≤ E t := le_max_left ..
  have hc2 : c 2 = 1 := by norm_num [c,majorPrimeLocal,hd]
  have hsub : ({∅,{2}}:Finset (Finset ℕ)) ⊆ P.powerset := by
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl
    · simp
    · simpa using h2
  have hmass : W 1+W 2 ≤ ∑ t ∈ P.powerset,E t := by
    have he := sum_le_sum_of_subset_of_nonneg (f:=E) hsub (fun t _ _ => hE t)
    simpa [E,hc2,max_eq_right (hw _)] using he
  have hcharge := powerset_signed_charging P c W (fun p hp => (hP p hp).pos) hw hm
  calc _ ≤ (9/16:ℝ)*∑ t ∈ P.powerset,E t := by linarith only [hmass]
       _ ≤ (1-∑ p ∈ P,max 0 (-c p))*(∑ t ∈ P.powerset,E t) :=
         mul_le_mul_of_nonneg_right (by linarith only [hcost]) (sum_nonneg fun t _ => hE t)
       _ ≤ _ := hcharge

end
end GoldbachPartial
