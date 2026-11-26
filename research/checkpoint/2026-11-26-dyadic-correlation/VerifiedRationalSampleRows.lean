import DyadicFejerDomination


namespace GoldbachPartial
open Finset
open scoped Classical

/-- The truncated reciprocal of torus distance takes the cap at an integer. -/
noncomputable def cappedCircleReciprocal (M x : ℝ) : ℝ :=
  if ‖(x:UnitAddCircle)‖=0 then M else min M (1/‖(x:UnitAddCircle)‖)

theorem cappedCircleReciprocal_nonneg {M : ℝ} (hM : 0≤M) (x : ℝ) :
    0≤cappedCircleReciprocal M x := by
  unfold cappedCircleReciprocal
  split_ifs
  · exact hM
  · exact le_min hM (by positivity)

private noncomputable def rationalSampleLabel (q a : ℕ) (x α : ℝ) (h : ℕ) : ℤ :=
  round ((q:ℝ)*x) + (a:ℤ)*h - (q:ℤ)*round (x+(h:ℝ)*α)

private theorem rationalSampleLabel_injective (q a : ℕ) (hc : a.Coprime q) (x α : ℝ) :
    Set.InjOn (rationalSampleLabel q a x α) (↑(range q)) := by
  intro u hu v hv e
  have hd : (a:ℤ)*u ≡ (a:ℤ)*v [ZMOD (q:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨round (x+(v:ℝ)*α)-round (x+(u:ℝ)*α),?_⟩
    unfold rationalSampleLabel at e
    linear_combination -e
  have hnat : a*u ≡ a*v [MOD q] := Int.natCast_modEq_iff.mp (by push_cast; exact hd)
  exact (hnat.cancel_left_of_coprime hc.symm).eq_of_lt_of_lt (mem_range.mp hu) (mem_range.mp hv)

private theorem rationalSampleLabel_bound (q a : ℕ) (hq : 0<q) {α : ℝ}
    (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (x : ℝ) {h : ℕ} (hh : h<q) :
    |(rationalSampleLabel q a x α h:ℝ)| ≤ (q:ℝ)*‖((x+(h:ℝ)*α:ℝ):UnitAddCircle)‖+3/2 := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hhr : (h:ℝ)≤q := by exact_mod_cast hh.le
  let y := x+(h:ℝ)*α
  have hterm : |(h:ℝ)*(q:ℝ)*(α-(a:ℝ)/q)|≤1 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(h:ℝ)*q)]
    apply (mul_le_mul_of_nonneg_left ha (by positivity : 0≤(h:ℝ)*q)).trans
    rw [mul_one_div,div_le_one (by positivity : 0<(q:ℝ)^2)]
    apply (mul_le_mul_of_nonneg_right hhr hqr.le).trans_eq
    ring
  have he : (rationalSampleLabel q a x α h:ℝ) =
      (q:ℝ)*(y-round y)+((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x)-((h:ℝ)*q*(α-(a:ℝ)/q)) := by
    dsimp only [rationalSampleLabel,y];push_cast
    field_simp;ring
  rw [he,UnitAddCircle.norm_eq]
  have h1 := abs_sub_le ((q:ℝ)*(y-round y)+((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x)) 0 ((h:ℝ)*q*(α-(a:ℝ)/q))
  simp only [sub_zero,zero_sub,abs_neg] at h1
  have h2 := abs_add_le ((q:ℝ)*(y-round y)) ((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x)
  rw [abs_mul,abs_of_pos hqr,abs_sub_comm ((round ((q:ℝ)*x):ℝ))] at h2
  change _ ≤ (q:ℝ)*|y-round y|+3/2
  linarith only [h1,h2,hterm,abs_sub_round ((q:ℝ)*x)]

private theorem rationalSample_harmonic (R : ℕ) :
    (∑ j ∈ range R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    by_cases h : R=0
    · subst R; norm_num
    · have hR : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(R:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hR)
      rw [Real.log_div hp.ne' hR.ne',inv_div] at hl
      have he : 1-(R:ℝ)/(R+1) = ((R:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]

theorem rationalSample_block (q a : ℕ) (hq : 0<q) (hc : a.Coprime q) {α M : ℝ}
    (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (hM : 0≤M) (x : ℝ) :
    (∑h∈range q,cappedCircleReciprocal M (x+(h:ℝ)*α)) ≤
      6*M+8*(q:ℝ)*(1+Real.log (q+2:ℕ)) := by
  let u := rationalSampleLabel q a x α
  let i : ℕ→ℕ×ℕ := fun h => (if u h<0 then 0 else 1, (u h).natAbs)
  let B := range 2 ×ˢ range (q+2)
  let F := fun j:ℕ => (if j<3 then M else 0) + 4*(q:ℝ)/((j:ℝ)+1)
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hF (j : ℕ) : 0≤F j := by dsimp [F];split_ifs <;> positivity
  have heq (z : ℤ) : (z.natAbs:ℝ)=|(z:ℝ)| := by
    cases z with
    | ofNat k => simp
    | negSucc k =>
      simp [Int.cast_negSucc]
      rw [abs_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) k;linarith : -1 + -(k:ℝ)≤0)]
      ring
  have hbound (h:ℕ) (hh:h∈range q) : ((u h).natAbs:ℝ) ≤
      (q:ℝ)*‖((x+(h:ℝ)*α:ℝ):UnitAddCircle)‖+3/2 := by
    rw [heq];exact rationalSampleLabel_bound q a hq ha x (mem_range.mp hh)
  have him (h:ℕ) (hh:h∈range q) : i h∈B := by
    apply mem_product.mpr
    refine ⟨?_,mem_range.mpr ?_⟩
    · dsimp [i];split_ifs <;> decide
    · have hdist : ‖((x+(h:ℝ)*α:ℝ):UnitAddCircle)‖≤1/2 := by rw [UnitAddCircle.norm_eq];exact abs_sub_round _
      have he := (hbound h hh).trans (add_le_add_left (mul_le_mul_of_nonneg_left hdist hqr.le) _)
      have hu : ((u h).natAbs:ℝ)<(q:ℝ)+2 := by linarith
      exact_mod_cast hu
  have hin : Set.InjOn i (↑(range q)) := by
    intro h hh k hk eq
    have hnat : (u h).natAbs=(u k).natAbs := congrArg Prod.snd eq
    have hsign : (if u h<0 then (0:ℕ) else 1)=(if u k<0 then 0 else 1) := congrArg Prod.fst eq
    apply rationalSampleLabel_injective q a hc x α hh hk
    obtain e | e := Int.natAbs_eq_natAbs_iff.mp hnat
    · exact e
    · change u h=u k
      split_ifs at hsign <;> omega
  have hpt (h:ℕ) (hh:h∈range q) : cappedCircleReciprocal M (x+(h:ℝ)*α) ≤ F (i h).2 := by
    let v := ‖((x+(h:ℝ)*α:ℝ):UnitAddCircle)‖
    let j := (u h).natAbs
    have hb : (j:ℝ)≤(q:ℝ)*v+3/2 := hbound h hh
    have hqp : 0≤4*(q:ℝ)/((j:ℝ)+1) := by positivity
    change (if v=0 then M else min M (1/v)) ≤ (if j<3 then M else 0)+4*(q:ℝ)/((j:ℝ)+1)
    by_cases hj : j<3
    · rw [ite_eq_left hj]
      split_ifs
      · linarith
      · exact (min_le_left ..).trans (le_add_of_nonneg_right hqp)
    · rw [ite_eq_right hj,zero_add]
      have hj' : (3:ℝ)≤j := by exact_mod_cast (Nat.le_of_not_gt hj)
      have hv : 0<v := by by_contra! hn; nlinarith only [hb,hj',mul_nonpos_of_nonneg_of_nonpos hqr.le hn]
      rw [ite_eq_right hv.ne']
      apply (min_le_right ..).trans
      apply (div_le_div_iff₀ hv (by positivity : 0<(j:ℝ)+1)).mpr
      linarith only [hb,hj']
  have hsum : (∑h∈range q,cappedCircleReciprocal M (x+(h:ℝ)*α)) ≤ ∑z∈B,F z.2 := by
    apply sum_le_sum_of_injOn i
    · exact hin
    · intro z hz;obtain ⟨h,hh,rfl⟩ := mem_image.mp hz;exact him h hh
    · exact hpt
    · intro z _ _;exact hF z.2
  have hminor : (∑j∈range (q+2),if j<3 then M else 0) ≤ 3*M := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have hcard : ((range (q+2)).filter (fun j=>j<3)).card≤3 := by
      apply (card_le_card (show (range (q+2)).filter (fun j=>j<3) ⊆ range 3 from
        fun j hj=>mem_range.mpr (mem_filter.mp hj).2)).trans_eq
      simp
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have hmajor : (∑j∈range (q+2),4*(q:ℝ)/((j:ℝ)+1)) ≤ 4*(q:ℝ)*(1+Real.log (q+2:ℕ)) := by
    simp only [div_eq_mul_inv,←mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Nat.cast_add,Nat.cast_one] using rationalSample_harmonic (q+2)
  apply hsum.trans
  change (∑z∈range 2×ˢrange (q+2),F z.2)≤_
  rw [sum_product' (range 2) (range (q+2)) (fun _ j=>F j),sum_const,nsmul_eq_mul,card_range]
  dsimp only [F];rw [sum_add_distrib]
  push_cast at hmajor ⊢
  linarith only [hminor,hmajor]


/-- Any shifted interval; the height loss occurs only once per block of q samples. -/
theorem rationalSample_range (H q a : ℕ) (hq : 0<q) (hc : a.Coprime q) {α M : ℝ}
    (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (hM : 0≤M) (x : ℝ) :
    (∑h∈range H,cappedCircleReciprocal M (x+(h:ℝ)*α)) ≤
      ((H:ℝ)/q+1)*(6*M+8*(q:ℝ)*(1+Real.log (q+2:ℕ))) := by
  let F := fun h:ℕ=>cappedCircleReciprocal M (x+(h:ℝ)*α)
  let S := range (H/q+1) ×ˢ range q
  let f := fun h : ℕ=>(h/q,h%q)
  have h1 : (∑h∈range H,F h) ≤ ∑z∈S,F (q*z.1+z.2) := by
    apply sum_le_sum_of_injOn f
    · intro h _ k _ he
      have hdiv : h/q=k/q := congrArg Prod.fst he
      have hmod : h%q=k%q := congrArg Prod.snd he
      calc h = h%q+q*(h/q) := (Nat.mod_add_div h q).symm
           _ = k := by rw [hdiv,hmod,Nat.mod_add_div]
    · intro z hz
      obtain ⟨h,hh,rfl⟩ := mem_image.mp hz
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hh).le)),mem_range.mpr (Nat.mod_lt _ hq)⟩
    · intro h _;dsimp [f];rw [Nat.div_add_mod]
    · intro z _ _;exact cappedCircleReciprocal_nonneg hM _
  let K := 6*M+8*(q:ℝ)*(1+Real.log (q+2:ℕ))
  have hK : 0≤K := by
    have hl := Real.log_natCast_nonneg (q+2)
    dsimp only [K];positivity
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hn : ((H/q:ℕ):ℝ)≤(H:ℝ)/q := by
    apply (le_div_iff₀ hqR).mpr;exact_mod_cast Nat.div_mul_le_self H q
  apply h1.trans
  rw [show (∑z∈S,F (q*z.1+z.2))=∑j∈range (H/q+1),∑h∈range q,F (q*j+h) from sum_product' (range (H/q+1)) (range q) (fun j h=>F (q*j+h))]
  apply (sum_le_sum (g:=fun _=>K) (fun j _=>?_)).trans
  · rw [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hK
  · have he := rationalSample_block q a hq hc ha hM (x+(q:ℝ)*j*α)
    convert he using 1
    apply sum_congr rfl
    intro k _
    dsimp only [F]
    congr 1
    push_cast;ring


open ExtendedArcCoefficient

theorem cappedCircleReciprocal_geometric_row (b T : ℕ) (M t : ℝ) (hT : (T:ℝ)≤M) :
    ‖∑k∈range T,E (((b+k:ℕ):ℝ)*t)‖ ≤ cappedCircleReciprocal M t := by
  have hphase : (∑k∈range T,E (((b+k:ℕ):ℝ)*t)) = E ((b:ℝ)*t)*(∑k∈range T,E ((k:ℝ)*t)) := by
    simp_rw [Nat.cast_add,add_mul,phase_add,mul_sum]
  rw [hphase,norm_mul,show ‖E ((b:ℝ)*t)‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
  have hcap : ‖∑k∈range T,E ((k:ℝ)*t)‖≤M := by
    apply (norm_sum_le ..).trans
    simpa only [show ∀s:ℝ,‖E s‖=1 from fun _=>Complex.norm_exp_ofReal_mul_I _,sum_const,card_range,nsmul_eq_mul,mul_one] using hT
  unfold cappedCircleReciprocal
  split_ifs with hz
  · exact hcap
  apply le_min hcap
  cases T with
  | zero => simp
  | succ m =>
    let v := ‖(t:UnitAddCircle)‖
    have hp : 0<v := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hy : |t-(round t:ℝ)|=v := UnitAddCircle.norm_eq.symm
    have hh : v≤1/2 := hy ▸ abs_sub_round _
    have hperiod := (wheelGeometricKernel_period m).sub_int_mul_eq (x:=t) (round t)
    simp only [mul_one] at hperiod
    have hred : ‖dirichletGeometricKernel m t‖=‖dirichletGeometricKernel m v‖ := by
      rw [←hperiod,←hy]
      by_cases hh : 0≤t-(round t:ℝ)
      · rw [abs_of_nonneg hh]
      · rw [abs_of_neg (lt_of_not_ge hh),wheelGeometricKernel_neg_norm]
    change ‖dirichletGeometricKernel m t‖≤1/v
    rw [hred]
    exact (fejer_kernel_pointwise m hp hh).trans (one_div_le_one_div_of_le hp (by linarith))

theorem rationalSample_geometric_rows (H q a : ℕ) (hq : 0<q) (hc : a.Coprime q)
    {α M : ℝ} (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (hM : 0≤M) (x : ℝ)
    (b T : ℕ→ℕ) (hT : ∀h∈range H,(T h:ℝ)≤M) :
    (∑h∈range H,‖∑k∈range (T h),E (((b h+k:ℕ):ℝ)*(x+(h:ℝ)*α))‖) ≤
      ((H:ℝ)/q+1)*(6*M+8*(q:ℝ)*(1+Real.log (q+2:ℕ))) := by
  exact (sum_le_sum (fun h hh=>cappedCircleReciprocal_geometric_row (b h) (T h) M _ (hT h hh))).trans
    (rationalSample_range H q a hq hc ha hM x)

theorem rationalSample_min_Icc (H q a : ℕ) (hq : 0<q) (hc : a.Coprime q) {α M : ℝ}
    (ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2) (hM : 0≤M) :
    (∑h∈Icc 1 H,min M (1/‖(((h:ℝ)*α:ℝ):UnitAddCircle)‖)) ≤
      ((H:ℝ)/q+1)*(6*M+8*(q:ℝ)*(1+Real.log (q+2:ℕ))) := by
  rw [show Icc 1 H=Ico 1 (H+1) by ext k;simp,sum_Ico_eq_sum_range,Nat.add_sub_cancel]
  apply le_trans _ (rationalSample_range H q a hq hc ha hM α)
  apply sum_le_sum
  intro h _
  rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
  unfold cappedCircleReciprocal
  split_ifs
  · exact min_le_left .. 
  · exact le_rfl

end GoldbachPartial