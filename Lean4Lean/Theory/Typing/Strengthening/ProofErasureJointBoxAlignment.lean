import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotRepair
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # A nonempty parameter-dependent record alignment test

For an existing registered Box with constructor (A : Type) -> A -> Box A,
the retained field recipe is exactly its parameter. Neutral parameters therefore
satisfy the general record alignment criterion, including eta-different types
without a joint computational join. Registration is an explicit hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf types_equal native_typed normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]
namespace BoxCarrierAlignment

private theorem projection_recipe
    (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (HT : ProjTele env univs family info [] doms result)
    (hj : info.nparams + 0 < doms.length) :
    projectionType family info doms 0 hj [param] major = param := by
  have hlen : doms.length = 2 := by have := HT.numFields; omega
  cases doms with
  | nil => cases hlen
  | cons A ds =>
    cases ds with
    | nil => cases hlen
    | cons B ds =>
      have hnil : ds = [] := by simpa using hlen
      subst ds
      have HE := hshape.symm.trans HT.shape
      change VExpr.forallE _ _ = .forallE A (.forallE B result) at HE
      have HA := (VExpr.forallE.inj HE).1
      have HB := (VExpr.forallE.inj (VExpr.forallE.inj HE).2).1
      subst A
      subst B
      have hC : OnCtx [VExpr.sort (.succ .zero)] (env.IsType univs) :=
        ⟨trivial, _, HasType.sort (by trivial)⟩
      have hv : env.HasType univs [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
      have EV : proofErase [VExpr.sort (.succ .zero)] (.bvar 0) = .bvar 0 :=
        if_neg (not_isProof_of_sort hC hv)
      simp [projectionType, projectionArgs, hp, EV, ProofShape.instOuter,
        ProofShape.subst, ProofShape.Subst.ofList]

private theorem neutral_fields
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1)))) :
    NeutralRecordFields Step Δ family info [] [mkApps (.bvar i) args] := by
  intro ps' doms result RP HT j hj major hjf hproof
  have hj0 : j = 0 := by omega
  subst j
  cases RP with
  | cons R RT =>
    cases RT
    obtain ⟨args', rfl, _⟩ := R.bvar_spine hhead
    exact ⟨i, args', projection_recipe hp hf hshape HT hj⟩

/-- Every joint Box guard at a neutral parameter transfers to any new raw
parameter, including nested field checking and intervening carrier reductions.
This uses the actual one-field constructor recipe; endpoint typings at the new
Box type remain necessary for sound application. -/
theorem guard_reindex
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (H : JointCarrierGuard Step Δ (.app (.const family []) (mkApps (.bvar i) args)) a b) :
    JointCarrierGuard Step Δ (.app (.const family []) target) a b :=
  H.record_reindex_neutral_fields (target := [target]) hhead hinert hi (by simp [hp])
    (neutral_fields hhead hp hf hshape)

private def nativeType (family : Name) : VExpr := .app (.const family []) native
private def assignedType (family : Name) : VExpr := .app (.const family []) assigned
private def nativeShape (family : Name) : ProofShape := .app (.const family []) nativeRaw
private def assignedShape (family : Name) : ProofShape := .app (.const family []) assignedRaw

private theorem family_typed
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env.HasType univs Γ (.const family []) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .const hc (by simp) rfl

private theorem typed_eq
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env.IsDefEq univs (context Γ) (assignedType family) (nativeType family) (.sort (.succ .zero)) :=
  .appDF (family_typed hc) types_equal

private theorem erase_types
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (context Γ) (nativeType family) = nativeShape family ∧
      proofErase (context Γ) (assignedType family) = assignedShape family := by
  have hC := context_wf hΓ
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EC : proofErase (context Γ) (.const family []) = .const family [] :=
    if_neg (not_isProof_function_to_sort hC (family_typed hc))
  constructor
  · change proofErase (context Γ) (.app _ _) = _
    rw [show proofErase (context Γ) (.app (.const family []) native) = .app _ _ from
      if_neg (not_isProof_of_sort hC (typed_eq hc).hasType.2), EC, EN]
    rfl
  · change proofErase (context Γ) (.app _ _) = _
    rw [show proofErase (context Γ) (.app (.const family []) assigned) = .app _ _ from
      if_neg (not_isProof_of_sort hC (typed_eq hc).hasType.1), EC, EA]
    rfl

private theorem normal_types
    {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out) (Δ) :
    NormalSyntax (Step Δ) (nativeShape family) ∧ NormalSyntax (Step Δ) (assignedShape family) := by
  have hconst : NormalSyntax (Step Δ) (.const family []) :=
    ⟨fun _ H => hinert (args := []) H, trivial⟩
  obtain ⟨HN, HA⟩ := normal_forms (Step := Step) hhead Δ
  exact ⟨⟨(fun _ H => hinert (args := [nativeRaw]) H), (fun _ _ H => nomatch H), hconst, HN⟩,
    ⟨(fun _ H => hinert (args := [assignedRaw]) H), (fun _ _ H => nomatch H), hconst, HA⟩⟩

/-- For an existing registered one-field Box, eta-different neutral parameters
produce equal typed nonempty record carriers with no repaired-joint-union join.
Their full carrier guards are equivalent at every finite repaired joint stage.
This assumes the displayed registration; it does not construct an extension. -/
theorem typed_alignment_without_join
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' T U, OnCtx Γ' (env.IsType univs) ∧ env.IsDefEq univs Γ' T U (.sort (.succ .zero)) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion (ErasedQuotCore.definitions hq)) (proofEraseCtx Γ') (proofErase Γ' T) shared ∧
        ScopedCompute (ErasedJointUnion (ErasedQuotCore.definitions hq)) (proofEraseCtx Γ') (proofErase Γ' U) shared) ∧
      ∀ stage a b, JointCarrierGuard (ErasedJointStage (ErasedQuotCore.definitions hq) stage) (proofEraseCtx Γ')
          (proofErase Γ' T) a b ↔
        JointCarrierGuard (ErasedJointStage (ErasedQuotCore.definitions hq) stage) (proofEraseCtx Γ')
          (proofErase Γ' U) a b := by
  let D := ErasedQuotCore.definitions hq
  have hinert {Δ args out} : ¬ ErasedJointUnion D Δ (mkApps (.const family []) args) out :=
    fun H => erased_joint_union_no_rigid heq (henv.projectionRigid hi)
      (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _)
  obtain ⟨EN, EA⟩ := erase_types hc hΓ
  refine ⟨context Γ, assignedType family, nativeType family, context_wf hΓ, typed_eq hc, ?_, ?_⟩
  · rintro ⟨shared, RA, RN⟩
    rw [EA] at RA
    rw [EN] at RN
    have HA := scoped_normal_fixed RA (fun Δ =>
      (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) hinert Δ).2)
    have HN := scoped_normal_fixed RN (fun Δ =>
      (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) hinert Δ).1)
    cases HA.symm.trans HN
  · intro stage a b
    rw [EA, EN]
    have hinert' {Δ args out} : ¬ ErasedJointStage D stage Δ (mkApps (.const family []) args) out :=
      fun H => hinert ⟨stage, H⟩
    constructor
    · intro H
      exact guard_reindex (i := 1) (args := [.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))])
        (erased_joint_stage_head stage) hinert' hi hp hf hshape H
    · intro H
      exact guard_reindex (i := 1) (args := [.bvar 2])
        (erased_joint_stage_head stage) hinert' hi hp hf hshape H

end BoxCarrierAlignment
end Lean4Lean.VEnv.Strengthening
