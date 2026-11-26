import GRHWindowCertificate
import PinnedUpstream316

namespace GoldbachPartial
open Finset Filter Set OAI.LargePrimeGaps
open scoped Classical Topology

theorem grh_induction_pinned : grhInductionInput := by
  intro q _ χ N
  have hh:=primeCharacterPrefix_primitive_difference (N:ℝ) (Nat.pos_of_ne_zero (NeZero.ne q)) χ
  have hI:Finset.Ioc 0 N=Finset.Icc 1 N:=by ext k;simp only [Finset.mem_Ioc,Finset.mem_Icc];omega
  simpa only [primeCharacterPrefix,Nat.floor_natCast,hI,mul_comm] using hh

noncomputable abbrev localDirichletL {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q):ℂ→ℂ :=
  DirichletCharacter.LFunction χ

theorem grh_zero_window_finite_of_line (hline:grhStripInput (@localDirichletL)):
    grhFiniteInput (@localDirichletL) := by
  intro q _ χ t T
  let S:=grhZeros (@localDirichletL) χ t T
  let v:ℝ→ℂ:=fun b=>(1/2:ℂ)+(b:ℂ)*Complex.I
  let K:=v '' Set.Icc (t-T) (t+T)
  have hc:IsCompact K:=isCompact_Icc.image (show Continuous v by dsimp [v];fun_prop)
  have hsub:S⊆K:=by
    intro z hz
    have hr:=hline q χ z hz.1 hz.2.1 hz.2.2.2
    have hb:=abs_le.mp hz.2.2.1
    refine ⟨z.im,⟨by linarith only [hb.1],by linarith only [hb.2]⟩,?_⟩
    apply Complex.ext <;> simp [v,hr]
  by_contra! hi
  obtain ⟨w,hw,ha⟩:=Set.Infinite.exists_accPt_of_subset_isCompact (s:=S) hi hc hsub
  obtain ⟨b,_,hb⟩:=hw
  have hwr:w.re=1/2:=by rw [←hb];simp [v]
  have hne:w≠1:=by intro h;rw [h,Complex.one_re] at hwr;norm_num at hwr
  have hd:DifferentiableOn ℂ (localDirichletL χ) ({1}ᶜ:Set ℂ):=fun z hz=>
    (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have han:AnalyticAt ℂ (localDirichletL χ) w := hd.analyticAt (isOpen_compl_singleton.mem_nhds hne)
  have hfr:=accPt_iff_frequently_nhdsNE.mp ha
  have hzfr:∃ᶠ z in 𝓝[≠] w,localDirichletL χ z=0:=hfr.mono (fun z hz=>hz.2.2.2)
  obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp (han.frequently_zero_iff_eventually_zero.mp hzfr)
  let e:=min (r/2) (1/4)
  have he:0<e:=lt_min (by linarith) (by norm_num)
  have he1:e≤1/4:=min_le_right .. 
  have her:e<r:=(min_le_left ..).trans_lt (by linarith)
  let z:=w+(e:ℂ)
  have hzdist:dist z w<r:=by simpa [z,dist_eq_norm,abs_of_pos he] using her
  have hrz:z.re=w.re+e:=by simp [z]
  have hfoo:=hline q χ z (by linarith) (by linarith) (hball hzdist)
  linarith
theorem grh_all_of_line_and_global_formula
    (mult : {q:ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℕ)
    (hline:grhStripInput (@localDirichletL))
    (hcount:grhZeroCountInput (@localDirichletL) mult)
    (hformula:grhExplicitInput (@localDirichletL) mult) : grhAllUniform :=
  uniform_all_psi_of_primitive
    (uniform_primitive_psi_of_GRH_inputs (@localDirichletL) mult
      hline (grh_zero_window_finite_of_line hline) hcount hformula) grh_induction_pinned

end GoldbachPartial
