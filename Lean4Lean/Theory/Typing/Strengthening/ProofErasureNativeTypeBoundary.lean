import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSpineReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEndpointBoundary

/-! # Declaration-type congruence must recover recursive annotations

A declaration with type (x : D) -> (x x -> Prop), for D = D -> Prop,
turns a common comparison of diagonal arguments into a demand to compare
self-application loops in its native result types. The prefix applications
are non-proofs. Their input comparison has no primitive computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_diagonal
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
variable [Params]

/-- A positive function-valued observer of a recursive argument's self-application.
The outer application is not erased as a proof, even though x x is a proposition. -/
def nativeLoopObserverType (D : VExpr) : VExpr :=
  .forallE D (.forallE RecursiveDomain.selfBody (.sort .zero))

/-- Native declaration-type congruence already requires comparison of every
annotation ordinarily convertible to this recursive Pi domain, when the displayed
observer declaration is present. The source certificate uses only constant
reflexivity and common lambda checking, at any chosen source relation. -/
theorem JointNativePrefixTypeComparison.recursive_annotations
    (HN : JointNativePrefixTypeComparison Source Target)
    (hstep : ErasedScopedPrimitiveDescent Target)
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars) (hdecl : ci.type.instL ls = nativeLoopObserverType D)
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    JointCompare Target (proofEraseCtx Γ) true (proofErase Γ D) (proofErase Γ D') := by
  have hD := Hrec.hasType.1
  have hD' := HD.hasType.2
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  have hb' : env.HasType univs (D' :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx := Hrec.symm.defeq Hdiag.hasType.1
  have hy := Hrec.symm.defeq Hdiag.hasType.2
  have EX := erase_diagonal hΓ hD hb
  have EY := erase_diagonal hΓ hD' hb'
  have hconst : env.HasType univs Γ (.const c ls) (nativeLoopObserverType D) := by
    rw [← hdecl]
    exact HasType.const hc hw hl
  have hmx : env.HasType univs Γ (.app (.const c ls) (RecursiveDomain.diagonal D))
      (.forallE (RecursiveDomain.omegaTerm D) (.sort .zero)) := by
    simpa [nativeLoopObserverType, RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar, VExpr.liftN_zero] using hconst.app hx
  have hmy : env.HasType univs Γ (.app (.const c ls) (RecursiveDomain.diagonal D'))
      (.forallE (RecursiveDomain.omegaTerm D') (.sort .zero)) := by
    simpa [nativeLoopObserverType, RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar, VExpr.liftN_zero] using hconst.app hy
  have hnx := not_isProof_function_to_sort hΓ hmx
  have hny := not_isProof_function_to_sort hΓ hmy
  have WX : InstForallsC env univs Γ (ci.type.instL ls) [RecursiveDomain.diagonal D]
      (.forallE (RecursiveDomain.omegaTerm D) (.sort .zero)) := by
    rw [hdecl]
    simpa [nativeLoopObserverType, RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar, VExpr.liftN_zero] using
      (InstForallsC.cons (B := .forallE RecursiveDomain.selfBody (.sort .zero)) hx .nil)
  have WY : InstForallsC env univs Γ (ci.type.instL ls) [RecursiveDomain.diagonal D']
      (.forallE (RecursiveDomain.omegaTerm D') (.sort .zero)) := by
    rw [hdecl]
    simpa [nativeLoopObserverType, RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar, VExpr.liftN_zero] using
      (InstForallsC.cons (B := .forallE RecursiveDomain.selfBody (.sort .zero)) hy .nil)
  have HC : JointCompare Source (proofEraseCtx Γ) false
      (proofErase Γ (.app (.const c ls) (RecursiveDomain.diagonal D)))
      (proofErase Γ (.app (.const c ls) (RecursiveDomain.diagonal D'))) := by
    change JointCompare Source (proofEraseCtx Γ) false
      (proofErase Γ (VExpr.mkApps (.const c ls) [RecursiveDomain.diagonal D]))
      (proofErase Γ (VExpr.mkApps (.const c ls) [RecursiveDomain.diagonal D']))
    rw [proofErase_const_spine hΓ (args := [RecursiveDomain.diagonal D]) hmx hnx,
      proofErase_const_spine hΓ (args := [RecursiveDomain.diagonal D']) hmy hny]
    simp only [List.map_cons, List.map_nil, ProofShape.mkApps, EX, EY]
    exact .app (.leaf .refl) (.lamCommon (.leaf .refl))
  have HC := HN hΓ hc hw hl WX WY hnx hny HC
  have hloopx : env.HasType univs Γ (RecursiveDomain.omegaTerm D) (.sort .zero) :=
    Hdiag.hasType.1.app hx
  have hloopy : env.HasType univs Γ (RecursiveDomain.omegaTerm D') (.sort .zero) :=
    Hdiag.hasType.2.app hy
  have hPX := HasType.forallE hloopx (HasType.sort (l := .zero) (by trivial))
  have hPY := HasType.forallE hloopy (HasType.sort (l := .zero) (by trivial))
  have EL : proofErase Γ (RecursiveDomain.omegaTerm D) = selfLoop (proofErase Γ D) := by
    rw [show proofErase Γ (RecursiveDomain.omegaTerm D) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hloopx), EX]
    rfl
  have ER : proofErase Γ (RecursiveDomain.omegaTerm D') = selfLoop (proofErase Γ D') := by
    rw [show proofErase Γ (RecursiveDomain.omegaTerm D') = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hloopy), EY]
    rfl
  have HC := proofErase_joint_types_inferred hstep hΓ hPX hPY HC
  rw [show proofErase Γ (.forallE (RecursiveDomain.omegaTerm D) (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPX),
    show proofErase Γ (.forallE (RecursiveDomain.omegaTerm D') (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPY)] at HC
  obtain ⟨A, B, R, HC⟩ := HC.forallE_domain_exposure hhead
  obtain ⟨_, _, HE, RD⟩ := R.forallE_domain_inv hhead
  cases HE
  have HC := JointCheck.compute (ScopedCompute.refl (Step := Target)) RD HC
  rw [EL, ER] at HC
  exact JointCompare.selfLoop_annotations hhead HC

omit [Params] in
/-- The repaired ordinary core cannot satisfy native declaration-type congruence
in the presence of this recursive observer. The target annotation is a reflexive
canonical-Eq cast with a free proof major. This refutes the certificate law,
not strengthening, and the source relation may even have no primitive steps. -/
theorem JointNativePrefixTypeComparison.not_core_of_recursive_pi
    {env : VEnv} (henv : env.WF) (U : Nat) (hquot : QuotRegistered env) :
    letI := henv.params U
    ∀ {Source Γ c ci ls A B u v i}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.constants c = some ci →
      (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
      ci.type.instL ls = nativeLoopObserverType (.forallE A B) →
      env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ¬ JointNativePrefixTypeComparison Source (fun _ => ErasedQuotCore.Step hquot) := by
  letI := henv.params U
  intro Source Γ c ci ls A B u v i heq hu hΓ hc hw hl hdecl hX hq Hrec HN
  have hs := ErasedQuotCore.sound hquot
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedQuotCore.Step hquot) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  have hhead : ∀ {Δ : List ProofShape} {a b},
      (fun _ => ErasedQuotCore.Step hquot) Δ a b → PrimitiveHead a :=
    fun H => erased_iota_primitive_head H
  have HD := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  have HC := HN.recursive_annotations hstep @hhead hΓ hc hw hl hdecl Hrec HD.symm
  have HC := proofErase_joint_types_inferred hstep hΓ Hrec.hasType.1 HD.hasType.1 HC
  rw [show proofErase Γ (.forallE A B) =
    .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ Hrec.hasType.1)] at HC
  obtain ⟨A', B', R⟩ := HC.forallE_exposure @hhead
  exact ErasedQuotCore.cast_no_pi henv U hquot heq hu hΓ hX hq Hrec.hasType.1 R

/-- The particular native-result shapes used by the obstruction compare at
joint stage one: the reflexive cast computes out of the loop annotations.
This repairs this witness without asserting native type congruence in general. -/
theorem ErasedQuotCore.cast_native_observer_results_stage_one
    (hquot : QuotRegistered env) (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (he : env.HasType univs Γ e X) :
    JointCompare (ErasedJointStage (ErasedQuotCore.definitions hquot) 1) (proofEraseCtx Γ) false
      (.forallE (selfLoop (proofErase Γ e)) (.sort .zero))
      (.forallE (selfLoop (proofErase Γ (typeCast u X X q e))) (.sort .zero)) := by
  have R := ErasedQuotCore.reflexive_cast_joint_stage_one hquot heq hu hΓ hX hq he
  exact .compute .refl (.forallE (.app (.lam R .refl) (.lam R .refl)) .refl) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
