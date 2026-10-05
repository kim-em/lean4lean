import Lean4Lean.Theory.Typing.AnchoredNativeLambdaBackwards
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
import Lean4Lean.Theory.Typing.AnchoredFunctionAnchor

/-! Open two original lambda typings at one demanded row. Their natural
codomains can differ. Actual source certificates cross the original outer
conversions before the shared finite row is selected. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure NativePairedLambdaRow (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (A leftBodyType rightBodyType : VExpr)
    (leftType rightType : VExpr) (key : Key n) (output : Atom n) (support : Profile (n + 1)) where
  prototypeDomain : VExpr
  prototypeBody : VExpr
  domain : Profile n
  rows : List (Key n × Profile n)
  member : (AtomData.pi prototypeDomain prototypeBody domain rows : Atom (n + 1)) ∈ support.atoms
  result : Profile n
  typed : (Profile.singleton output).HasType result
  row : (key, result) ∈ rows
  display : PiWitness env U registry (relations env U registry n) target
    ((VExpr.forallE A rightBodyType).subst σ) ((VExpr.forallE A rightBodyType).subst σ)
    prototypeDomain prototypeBody domain rows
  leftToNatural : TypeRelated env U registry target (leftType.subst σ)
    ((VExpr.forallE A rightBodyType).subst σ) support
  naturalToRight : TypeRelated env U registry target
    ((VExpr.forallE A rightBodyType).subst σ) (rightType.subst σ) support
  left : PiRowCertificate env U registry target locals σ available A leftBodyType key result
  right : PiRowCertificate env U registry target locals σ available A rightBodyType key result
  path : TypeConversion env U target (leftBodyType.subst (σ.cons key.anchor))
    (rightBodyType.subst (σ.cons key.anchor))
  related : TypeRelated env U registry target (leftBodyType.subst (σ.cons key.anchor))
    (rightBodyType.subst (σ.cons key.anchor)) result

/-- Both extracted rows use the very same result profile. The bridge is
obtained from the two actual whole-Pi conversion chains, never from raw
injectivity or a claim that the original body types coincide. -/
theorem OriginalLambdaOrigin.pairedRow
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A left right leftType rightType : VExpr}
    (leftOrigin : OriginalLambdaOrigin sourceEnv env U registry source A left leftType)
    (rightOrigin : OriginalLambdaOrigin sourceEnv env U registry source A right rightType)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile (n + 1)} {leftFootprint rightFootprint : Footprint}
    (leftCertificate : CodeCert env U registry target locals σ leftType support leftFootprint)
    (rightCertificate : CodeCert env U registry target locals σ rightType support rightFootprint)
    (leftResources : leftFootprint.Available available)
    (rightResources : rightFootprint.Available available)
    (bridge : TypeRelated env U registry target (leftType.subst σ) (rightType.subst σ) support)
    {key : Key n} {output : Atom n} (typed : (Profile.fn key output).HasType support) :
    Nonempty (NativePairedLambdaRow env U registry target locals σ available A
      leftOrigin.bodyType rightOrigin.bodyType leftType rightType key output support) := by
  obtain ⟨leftNatural⟩ := leftOrigin.assignedCertificate henv hscoped hle closed hTarget
    substitutions fits leftCertificate leftResources
  obtain ⟨rightNatural⟩ := rightOrigin.assignedCertificate henv hscoped hle closed hTarget
    substitutions fits rightCertificate rightResources
  have whole := leftNatural.related.trans henv
    (bridge.trans henv (rightNatural.related.symm henv typed.wf_type))
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  obtain ⟨leftRow⟩ := leftNatural.naturalCertificate.piOrigins henv hscoped hTarget closed
    (leftOrigin.domainStrong.defeq.mono hle) (leftOrigin.bodyTypeStrong.defeq.mono hle)
    substitutions fits leftOrigin.domainJoint leftOrigin.bodyTypeJoint leftNatural.resources
    _ member key result row
  obtain ⟨rightRow⟩ := rightNatural.naturalCertificate.piOrigins henv hscoped hTarget closed
    (rightOrigin.domainStrong.defeq.mono hle) (rightOrigin.bodyTypeStrong.defeq.mono hle)
    substitutions fits rightOrigin.domainJoint rightOrigin.bodyTypeJoint rightNatural.resources
    _ member key result row
  have selected := whole.singleton member
  change TypeRelated env U registry target
    (.forallE (A.subst σ) (leftOrigin.bodyType.subst σ.lift))
    (.forallE (A.subst σ) (rightOrigin.bodyType.subst σ.lift))
    (.pi protoDomain protoBody domain rows) at selected
  obtain ⟨path, related⟩ := selected.literalPiBody henv hscoped hTarget row rightRow.anchor
  have code := rightNatural.related.left_diagonal target .refl (.refl hTarget)
  simp only [lift'_refl, Profile.rename_refl] at code
  obtain ⟨display⟩ := code _ member
  exact ⟨⟨protoDomain, protoBody, domain, rows, member, result, resultTyped, row, display,
    bridge.trans henv (rightNatural.related.symm henv typed.wf_type), rightNatural.related,
    leftRow, rightRow,
    by simpa only [inst_lift_cons] using path,
    by simpa only [inst_lift_cons] using related⟩⟩

/-- Close the semantic binder using only the returned comparison at its
frozen anchor and the original endpoint self comparisons. The two beta
equalities are typed at their own natural codomains and then aligned by the
actual retained body path. -/
theorem NativePairedLambdaRow.close
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A left right leftBodyType rightBodyType leftType rightType : VExpr}
    {key : Key n} {output : Atom n} {support leftSupport rightSupport : Profile (n + 1)}
    (row : NativePairedLambdaRow env U registry target locals σ available A
      leftBodyType rightBodyType leftType rightType key output support)
    (typed : (Profile.fn key output).HasType support)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (formedA : env.HasType U source A (.sort level))
    (leftBody : env.HasType U (A :: source) left leftBodyType)
    (rightBody : env.HasType U (A :: source) right rightBodyType)
    (leftSelf : Related env U registry target ((VExpr.lam A left).subst σ)
      ((VExpr.lam A left).subst σ) (leftType.subst σ) (.fn key output) leftSupport)
    (rightSelf : Related env U registry target ((VExpr.lam A right).subst σ)
      ((VExpr.lam A right).subst σ) (rightType.subst σ) (.fn key output) rightSupport)
    (bodyRelated : Related env U registry target (right.subst (σ.cons key.anchor))
      (left.subst (σ.cons key.anchor)) (rightBodyType.subst (σ.cons key.anchor))
      (.singleton output) row.result) :
    Related env U registry target ((VExpr.lam A right).subst σ)
      ((VExpr.lam A left).subst σ) (rightType.subst σ) (.fn key output) support := by
  have argument := row.right.alignment.path.cast row.right.anchor.2.1
  have context : OnCtx (A.subst σ :: target) (env.IsType U) :=
    ⟨hTarget, _, formedA.subst henv substitutions hTarget⟩
  have leftTyped := leftBody.subst henv (substitutions.lift henv formedA) context
  have rightTyped := rightBody.subst henv (substitutions.lift henv formedA) context
  have leftBeta := IsDefEq.beta leftTyped argument
  have rightBeta := IsDefEq.beta rightTyped argument
  simp only [inst_lift_cons] at leftBeta rightBeta
  have head (body : VExpr) : HeadBeta
      (.app ((VExpr.lam A body).subst σ) key.anchor) (body.subst (σ.cons key.anchor)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A.subst σ) (body := body.subst σ.lift)
        (argument := key.anchor) (trailing := []))
  have anchor := Related.headBeta henv (head right) (head left)
    rightBeta (row.path.cast leftBeta) bodyRelated
  have leftNatural := Related.convert henv typed row.leftToNatural leftSelf
  have rightNatural := Related.convert henv typed
    (row.naturalToRight.symm henv typed.wf_type) rightSelf
  have comparison := Related.functionAtAnchor henv hscoped hTarget row.display row.member
    row.row row.typed typed row.naturalToRight.left_diagonal rightNatural leftNatural
    (by simpa only [inst_lift_cons] using anchor)
  exact Related.convert henv typed row.naturalToRight comparison

end Lean4Lean.AnchoredSource.Adapted
