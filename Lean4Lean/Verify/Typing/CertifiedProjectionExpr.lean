import Lean4Lean.Verify.Typing.ProjectionDeterminism
import Lean4Lean.Verify.TypeChecker.ProjectionCertificate

namespace Lean4Lean

open Lean
open TypeChecker.Inner

/- Finite native translation evidence for expressions, primitive
projections, and the selected constructor-field prefix.

The projection constructor retains the exact executable proposal, generated
candidate, and accepted certificate.  The syntax generator remains
untrusted: its candidate is recursively translated by `CertifiedTrExprS`.
The selected-field relation recursively embeds evidence for every preceding
projection inserted by production. -/
mutual
  inductive CertifiedTrExprS (env : VEnv) (Us : List Name) :
      VLCtx → Expr → VExpr → Prop
    | bvar : Delta.find? (.inl index) = some (target, type) →
        CertifiedTrExprS env Us Delta (.bvar index) target
    | fvar : Delta.find? (.inr fvarId) = some (target, type) →
        CertifiedTrExprS env Us Delta (.fvar fvarId) target
    | sort : VLevel.ofLevel Us level = some targetLevel →
        CertifiedTrExprS env Us Delta (.sort level) (.sort targetLevel)
    | const :
        env.constants name = some constant →
        levels.mapM (VLevel.ofLevel Us) = some targetLevels →
        levels.length = constant.uvars →
        CertifiedTrExprS env Us Delta (.const name levels)
          (.const name targetLevels)
    | app :
        env.HasType Us.length Delta.toCtx fnTarget (.forallE domain body) →
        env.HasType Us.length Delta.toCtx argTarget domain →
        CertifiedTrExprS env Us Delta fn fnTarget →
        CertifiedTrExprS env Us Delta arg argTarget →
        CertifiedTrExprS env Us Delta (.app fn arg) (.app fnTarget argTarget)
    | lam :
        env.IsType Us.length Delta.toCtx domainTarget →
        CertifiedTrExprS env Us Delta domain domainTarget →
        CertifiedTrExprS env Us ((none, .vlam domainTarget) :: Delta)
          body bodyTarget →
        CertifiedTrExprS env Us Delta (.lam name domain body info)
          (.lam domainTarget bodyTarget)
    | forallE :
        env.IsType Us.length Delta.toCtx domainTarget →
        env.IsType Us.length (domainTarget :: Delta.toCtx) bodyTarget →
        CertifiedTrExprS env Us Delta domain domainTarget →
        CertifiedTrExprS env Us ((none, .vlam domainTarget) :: Delta)
          body bodyTarget →
        CertifiedTrExprS env Us Delta (.forallE name domain body info)
          (.forallE domainTarget bodyTarget)
    | letE :
        env.HasType Us.length Delta.toCtx valueTarget typeTarget →
        CertifiedTrExprS env Us Delta type typeTarget →
        CertifiedTrExprS env Us Delta value valueTarget →
        CertifiedTrExprS env Us ((none, .vlet typeTarget valueTarget) :: Delta)
          body bodyTarget →
        CertifiedTrExprS env Us Delta (.letE name type value body nondep)
          bodyTarget
    | lit : env.ContainsLits literal →
        CertifiedTrExprS env Us Delta literal.toConstructor target →
        CertifiedTrExprS env Us Delta (.lit literal) target
    | mdata : CertifiedTrExprS env Us Delta body target →
        CertifiedTrExprS env Us Delta (.mdata data body) target
    | proj :
        CertifiedTrExprS env Us Delta concreteMajor major →
        CertifiedTrProj env Us Delta structName index concreteMajor major
          concreteType target →
        CertifiedTrExprS env Us Delta (.proj structName index concreteMajor)
          target

  inductive CertifiedTrProj (env : VEnv) (Us : List Name) :
      VLCtx → Name → Nat → Expr → VExpr → Expr → VExpr → Prop
    | canonical
        (P : CanonicalProjectionExpansion)
        (hstruct : P.structName = structName)
        (hindex : P.index = index)
        (hmajor : P.major = major)
        (installed : CanonicalProjectionExpansion.InstalledTyping env Us.length
          Delta.toCtx P)
        (projection : ProjectionResult)
        (generated : GeneratedProjectionCandidate projection)
        (certificate : ProjectionCertificate)
        (hcertificateProjection : certificate.projection = projection)
        (hcertificateCandidate : certificate.candidate = generated.candidate)
        (hprojectionStruct : projection.expansion.struct = concreteMajor)
        (hprojectionName : projection.expansion.typeName = structName)
        (hprojectionIndex : projection.expansion.index = index)
        (constructorTail selected residual : VExpr)
        (parameters : ProjectionParameterSpine env Us.length Delta.toCtx
          P.params.length
          (installed.ctor.type.instL P.familyLevels) P.params
          constructorTail)
        (fields : ProjectionFieldTelescope env Us.length Delta.toCtx
          P.fieldDomains.length constructorTail P.fieldDomains residual)
        (selection : CertifiedProjectionSelectedField env Us Delta structName
          concreteMajor major 0 index constructorTail selected)
        (resultTranslation : CertifiedTrExprS env Us Delta projection.type
          selected)
        (candidateTranslation : CertifiedTrExprS env Us Delta
          generated.candidate P.target)
        (candidateTypeTarget : VExpr)
        (candidateTypeTranslation : CertifiedTrExprS env Us Delta
          certificate.candidateType candidateTypeTarget)
        (candidateTyping : env.HasType Us.length Delta.toCtx P.target
          candidateTypeTarget)
        (resultTypeDefEq : env.IsDefEqU Us.length Delta.toCtx
          candidateTypeTarget selected) :
        CertifiedTrProj env Us Delta structName index concreteMajor major
          projection.type P.target

  inductive CertifiedProjectionSelectedField
      (env : VEnv) (Us : List Name) :
      VLCtx → Name → Expr → VExpr →
        Nat → Nat → VExpr → VExpr → Prop
    | nil
        (Hforall : env.IsDefEqU Us.length Delta.toCtx source
          (.forallE selected body)) :
        CertifiedProjectionSelectedField env Us Delta structName concreteMajor
          major position 0 source selected
    | cons
        (Hforall : env.IsDefEqU Us.length Delta.toCtx source
          (.forallE domain body))
        (projectedType : Expr)
        (Hprojection : CertifiedTrProj env Us Delta structName position
          concreteMajor major projectedType projected)
        (Hprojected : env.HasType Us.length Delta.toCtx projected domain)
        (Htail : CertifiedProjectionSelectedField env Us Delta structName
          concreteMajor major (position + 1) remaining
          (body.inst projected) selected) :
        CertifiedProjectionSelectedField env Us Delta structName concreteMajor
          major position (remaining + 1) source selected
end

namespace CertifiedTrProj

theorem sourceWF
    (H : CertifiedTrProj env Us Delta structName index concreteMajor major
      concreteType target) :
    VExpr.WF env Us.length Delta.toCtx major := by
  cases H with
  | canonical P _ _ hmajor installed =>
      exact ⟨_, hmajor ▸ installed.majorType⟩

/-- The exact validation trace types the canonical projection target at the
translation of the literal type returned by legacy inference.  This is the
checker-facing replacement for opaque `TrProj.wf`: it is derived from the
candidate inference result and its successful defeq check. -/
theorem resultTyping
    (H : CertifiedTrProj env Us Delta structName index concreteMajor major
      concreteType target)
    (henv : VEnv.WF env) (hDelta : VLCtx.WF env Us.length Delta) :
    ∃ selected,
      CertifiedTrExprS env Us Delta concreteType selected ∧
      env.HasType Us.length Delta.toCtx target selected := by
  cases H with
  | canonical P hstruct hindex hmajor installed projection generated
      certificate hcertificateProjection hcertificateCandidate
      hprojectionStruct hprojectionName hprojectionIndex constructorTail
      selected residual parameters fields selection resultTranslation
      candidateTranslation candidateTypeTarget candidateTypeTranslation
      candidateTyping resultTypeDefEq =>
      exact ⟨selected, resultTranslation,
        candidateTyping.defeqU_r henv hDelta.toCtx resultTypeDefEq⟩

end CertifiedTrProj

namespace CertifiedTrExprS

/-- Mutual well-formedness: projection targets are typed by the recursively
checked accepted candidate, never by a `targetWF` field. -/
theorem wf
    (H : CertifiedTrExprS env Us Delta expression target)
    (henv : VEnv.Ordered env)
    (hDelta : VLCtx.WF env Us.length Delta) :
    VExpr.WF env Us.length Delta.toCtx target := by
  exact CertifiedTrExprS.rec
    (motive_1 := fun Delta _ target _ =>
      VLCtx.WF env Us.length Delta → VExpr.WF env Us.length Delta.toCtx target)
    (motive_2 := fun Delta _ _ _ _ _ target _ =>
      VLCtx.WF env Us.length Delta → VExpr.WF env Us.length Delta.toCtx target)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (bvar := by
      intro target type Delta index hfind hDelta
      exact ⟨_, hDelta.find?_wf henv hfind⟩)
    (fvar := by
      intro target type Delta fvarId hfind hDelta
      exact ⟨_, hDelta.find?_wf henv hfind⟩)
    (sort := by
      intro level targetLevel Delta hlevel hDelta
      exact ⟨_, VEnv.HasType.sort (.of_ofLevel hlevel)⟩)
    (const := by
      intro name constant targetLevels Delta levels hlookup hlevels hlength
        hDelta
      exact ⟨_, VEnv.HasType.const hlookup (.of_mapM_ofLevel hlevels)
        ((Lean4Lean.List.Forall₂.length_eq
          (List.mapM_eq_some.1 hlevels)).symm.trans hlength)⟩)
    (app := by
      intro fnTarget domain body argTarget Delta fn arg hfn harg Hfn Harg
        ihFn ihArg hDelta
      exact ⟨_, hfn.app harg⟩)
    (lam := by
      intro domainTarget Delta domain body bodyTarget name info hdomain
        Hdomain Hbody ihDomain ihBody hDelta
      rcases hdomain with ⟨_, hdomain⟩
      rcases ihBody ⟨hDelta, nofun, ⟨_, hdomain⟩⟩ with ⟨_, hbody⟩
      exact ⟨_, hdomain.lam hbody⟩)
    (forallE := by
      intro domainTarget bodyTarget Delta domain body name info hdomain hbody
        Hdomain Hbody ihDomain ihBody hDelta
      rcases hdomain with ⟨_, hdomain⟩
      rcases hbody with ⟨_, hbody⟩
      exact ⟨_, hdomain.forallE hbody⟩)
    (letE := by
      intro valueTarget typeTarget Delta type value body bodyTarget name nondep
        hvalue Htype Hvalue Hbody ihType ihValue ihBody hDelta
      exact ihBody ⟨hDelta, nofun, hvalue⟩)
    (lit := by
      intro literal Delta target hliteral Hliteral ih hDelta
      exact ih hDelta)
    (mdata := by
      intro Delta body target data Hbody ih hDelta
      exact ih hDelta)
    (proj := by
      intro Delta concreteMajor major structName index concreteType target
        Hmajor Hprojection ihMajor ihProjection hDelta
      exact ihProjection hDelta)
    (canonical := by
      intros
      solve_by_elim)
    (nil := by intros; trivial)
    (cons := by intros; trivial)
    H hDelta

end CertifiedTrExprS

namespace CertifiedProjectionSelectedField

/-- Forget only the proof packaging of a finite selected-prefix derivation.
Every recursive projection remains the native `CertifiedTrProj` evidence at
the exact preceding position; no callback or externally chosen target is
introduced. -/
theorem toDeclarative
    (H : CertifiedProjectionSelectedField env Us Delta structName
      concreteMajor major position count source selected) :
    ProjectionSelectedField
      (fun current projected => ∃ projectedType,
        CertifiedTrProj env Us Delta structName current concreteMajor major
          projectedType projected)
      env Us.length Delta.toCtx position count source selected := by
  induction count generalizing position source with
  | zero =>
      cases H with
      | nil Hforall => exact .nil Hforall
  | succ count ih =>
      cases H with
      | cons Hforall projectedType Hprojection Hprojected Htail =>
          exact .cons Hforall ⟨projectedType, Hprojection⟩ Hprojected
            (ih Htail)

/-- Selected typehood follows from the final checked forall view; recursive
projection steps do not add a separate well-formedness premise. -/
theorem selectedIsType
    (henv : VEnv.WF env)
    (H : CertifiedProjectionSelectedField env Us Delta structName
      concreteMajor major position count source selected) :
    env.IsType Us.length Delta.toCtx selected := by
  induction count generalizing position source with
  | zero =>
      cases H with
      | nil Hforall =>
          rcases Hforall with ⟨_, Hforall⟩
          exact (Hforall.hasType.2.forallE_inv henv.ordered).1
  | succ count ih =>
      cases H with
      | cons _ _ _ _ Htail => exact ih Htail

/-- Two finite selected-prefix derivations determine definitionally equal
selected types once the mutually recursive projection induction hypothesis
is supplied.  The final kernel-facing theorem discharges that hypothesis
internally from the same finite evidence family. -/
theorem selectedDefEq
    (henv : VEnv.WF env) (hDelta : VLCtx.WF env Us.length Delta)
    (Hleft : CertifiedProjectionSelectedField env Us Delta structName
      concreteMajor major position count leftSource leftSelected)
    (Hright : CertifiedProjectionSelectedField env Us Delta structName
      concreteMajor major position count rightSource rightSelected)
    (Hsource : env.IsDefEqU Us.length Delta.toCtx leftSource rightSource)
    (Hprojection : ∀ current leftType rightType left right,
      CertifiedTrProj env Us Delta structName current concreteMajor major
        leftType left →
      CertifiedTrProj env Us Delta structName current concreteMajor major
        rightType right →
      env.IsDefEqU Us.length Delta.toCtx left right) :
    env.IsDefEqU Us.length Delta.toCtx leftSelected rightSelected :=
  (Hleft.toDeclarative.selectedDefEq henv hDelta.toCtx
    Hright.toDeclarative Hsource) fun current left right Hleft Hright =>
      Hprojection current Hleft.choose Hright.choose left right
        Hleft.choose_spec Hright.choose_spec

end CertifiedProjectionSelectedField

end Lean4Lean
