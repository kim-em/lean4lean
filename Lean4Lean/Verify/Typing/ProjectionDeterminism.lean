import Lean4Lean.Verify.Typing.ProjectionInference

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive.ProjectionNameReady.InferenceMetadata

/-- Exact projection metadata is stable under a lockstep production/abstract
environment extension.  All selected source declarations and positions are
kept literally unchanged; only their lookup and typing proofs are transported.

This is the metadata half of deterministic projection expansion.  In
particular, it does not accept or return an expansion target, motive, or field
telescope. -/
def rebase
    {source target : ConstMap} {env env' : VEnv}
    (H : InferenceMetadata safety source env name index)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    InferenceMetadata safety target env' name index where
  familyInfo := H.familyInfo
  familyLookup := hproduction H.familyLookup
  familyVisible := H.familyVisible
  family := {
    decl := H.family.decl
    familyIdx := H.family.familyIdx
    alignment := H.family.alignment.rebase
      (hproduction H.family.alignment.lookup) hproduction
    familyNameExact := H.family.familyNameExact
    installed := H.family.installed.mono henv
    recursor := H.family.recursor
    recursorName := H.family.recursorName
    recursorLookup := henv.constants H.family.recursorLookup
    recursorShape := H.family.recursorShape }
  sourceOwner := H.sourceOwner
  sourceOwner_eq := H.sourceOwner_eq
  sourceOwner_mem := H.sourceOwner_mem
  sourceOwner_name := H.sourceOwner_name
  sourceOwnerLookup := henv.constants H.sourceOwnerLookup
  sourceOwnerTranslation := H.sourceOwnerTranslation.mono henv
  constructor := {
    constructorName := H.constructor.constructorName
    productionSingle := H.constructor.productionSingle
    sourceSingle := H.constructor.sourceSingle
    alignment := H.constructor.alignment.rebase hproduction }
  index_lt := H.index_lt
  sourceConstructor := H.sourceConstructor
  sourceConstructor_eq := H.sourceConstructor_eq
  sourceConstructor_mem := H.sourceConstructor_mem
  sourceConstructor_name := H.sourceConstructor_name
  sourceConstructorLookup := henv.constants H.sourceConstructorLookup
  sourceConstructorTranslation := H.sourceConstructorTranslation.mono henv
  eliminatorInfo := H.eliminatorInfo
  eliminatorLookup := hproduction H.eliminatorLookup
  eliminatorVisible := H.eliminatorVisible
  eliminator := H.eliminator
  eliminatorAbstractLookup := henv.constants H.eliminatorAbstractLookup
  eliminatorTranslation := H.eliminatorTranslation.mono henv

/-- Rebasing exact projection metadata does not change any selected syntax or
source position.  These equations are kept together so later expansion
stability proofs do not have to unfold the certificate implementation. -/
structure RebaseExact
    (H : InferenceMetadata safety source env name index)
    (H' : InferenceMetadata safety target env' name index) : Prop where
  familyInfo : H'.familyInfo = H.familyInfo
  decl : H'.family.decl = H.family.decl
  familyIdx : H'.family.familyIdx = H.family.familyIdx
  sourceOwner : H'.sourceOwner = H.sourceOwner
  constructorName : H'.constructor.constructorName =
    H.constructor.constructorName
  sourceConstructor : H'.sourceConstructor = H.sourceConstructor
  eliminatorInfo : H'.eliminatorInfo = H.eliminatorInfo
  eliminator : H'.eliminator = H.eliminator

theorem rebase_exact
    {source target : ConstMap} {env env' : VEnv}
    (H : InferenceMetadata safety source env name index)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    RebaseExact H (H.rebase hproduction henv) where
  familyInfo := rfl
  decl := rfl
  familyIdx := rfl
  sourceOwner := rfl
  constructorName := rfl
  sourceConstructor := rfl
  eliminatorInfo := rfl
  eliminator := rfl

/-- The exact abstract major spine is also stable under the same environment
extension.  Its universe, parameter, and index syntax is unchanged; only the
typing and strict-translation derivations are weakened. -/
def MajorSpine.rebase
    {source target : ConstMap} {env env' : VEnv}
    {H : InferenceMetadata safety source env name index}
    (S : MajorSpine H Us Delta concreteArgs major)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    MajorSpine (H.rebase hproduction henv) Us Delta concreteArgs major where
  familyLevels := S.familyLevels
  params := S.params
  indices := S.indices
  familyLevels_wf := S.familyLevels_wf
  familyLevels_length := S.familyLevels_length
  params_length := S.params_length
  indices_length := S.indices_length
  majorType := S.majorType.mono henv
  paramsTranslation := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.mono henv) S.paramsTranslation
  indicesTranslation := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.mono henv) S.indicesTranslation

@[simp] theorem MajorSpine.rebase_familyLevels
    {source target : ConstMap} {env env' : VEnv}
    {H : InferenceMetadata safety source env name index}
    (S : MajorSpine H Us Delta concreteArgs major)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    (S.rebase hproduction henv).familyLevels = S.familyLevels := rfl

@[simp] theorem MajorSpine.rebase_params
    {source target : ConstMap} {env env' : VEnv}
    {H : InferenceMetadata safety source env name index}
    (S : MajorSpine H Us Delta concreteArgs major)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    (S.rebase hproduction henv).params = S.params := rfl

@[simp] theorem MajorSpine.rebase_indices
    {source target : ConstMap} {env env' : VEnv}
    {H : InferenceMetadata safety source env name index}
    (S : MajorSpine H Us Delta concreteArgs major)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    (S.rebase hproduction henv).indices = S.indices := rfl

end VerifyInductive.ProjectionNameReady.InferenceMetadata

namespace ProjectionParameterSpine

/-- The exact common-parameter WHNF trace is stable when the abstract
environment grows.  Every exposed forall, supplied argument, and residual
expression is kept literally unchanged. -/
theorem mono
    (H : ProjectionParameterSpine env U Gamma count source arguments residual)
    (henv : env ≤ env') :
    ProjectionParameterSpine env' U Gamma count source arguments residual := by
  induction H with
  | nil Hdefeq => exact .nil (Hdefeq.mono henv)
  | cons Hforall Hargument _ ih =>
      exact .cons (Hforall.mono henv) (Hargument.mono henv) ih

/-- Parameter consumption remains functional when the two abstract argument
spines are merely pointwise definitionally equal.  This is the form needed
after translating the same concrete major application twice: strict
translation determines each argument only up to definitional equality, not
literal syntax. -/
theorem residualDefEqOfArguments
    (henv : VEnv.WF env) (hGamma : OnCtx Gamma (env.IsType U))
    (Hleft : ProjectionParameterSpine env U Gamma count leftSource
      leftArguments leftResidual)
    (Hright : ProjectionParameterSpine env U Gamma count rightSource
      rightArguments rightResidual)
    (Hsource : env.IsDefEqU U Gamma leftSource rightSource)
    (Harguments : List.Forall₂ (env.IsDefEqU U Gamma)
      leftArguments rightArguments) :
    env.IsDefEqU U Gamma leftResidual rightResidual := by
  induction Hleft generalizing rightSource rightArguments rightResidual with
  | nil HleftResidual =>
      cases Hright with
      | nil HrightResidual =>
          exact (HleftResidual.symm.trans henv hGamma Hsource).trans henv
            hGamma HrightResidual
  | @cons leftSource leftDomain leftBody leftArgument leftArguments
      leftResidual count HleftForall HleftArgument HleftTail ih =>
      cases Hright with
      | @cons rightSource rightDomain rightBody rightArgument rightArguments
          rightResidual _ HrightForall HrightArgument HrightTail =>
          cases Harguments with
          | cons Hargument HargumentTail =>
              have Hforalls : env.IsDefEqU U Gamma
                  (.forallE leftDomain leftBody)
                  (.forallE rightDomain rightBody) :=
                (HleftForall.symm.trans henv hGamma Hsource).trans henv
                  hGamma HrightForall
              rcases Hforalls.forallE_inv henv hGamma with
                ⟨⟨_, Hdomains⟩, _, Hbodies⟩
              have Hargument' : env.IsDefEq U Gamma leftArgument
                  rightArgument leftDomain :=
                Hargument.of_l henv hGamma HleftArgument
              have Hinstantiated : env.IsDefEqU U Gamma
                  (leftBody.inst leftArgument) (rightBody.inst rightArgument) :=
                ⟨_, Hbodies.instDF henv hGamma Hargument'⟩
              exact ih HrightTail Hinstantiated HargumentTail

end ProjectionParameterSpine

namespace ProjectionFieldTelescope

/-- The exact constructor-field WHNF trace is stable under abstract
environment extension.  In particular, all selected domains and the final
residual remain syntactically identical; only their typing derivations are
transported. -/
theorem mono
    (H : ProjectionFieldTelescope env U Gamma count source domains residual)
    (henv : env ≤ env') :
    ProjectionFieldTelescope env' U Gamma count source domains residual := by
  induction H with
  | nil Hdefeq => exact .nil (Hdefeq.mono henv)
  | cons Hforall _ ih => exact .cons (Hforall.mono henv) ih

/-- Pointwise definitional equality between two telescope views.  The
contexts are indexed separately: after each binder the left body is checked
under the left domain and the right body under the right domain.  This is the
right invariant for functionality of projection-field interpretation; it
does not require choosing one WHNF representative as canonical syntax. -/
inductive DefEq
    (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VExpr → List VExpr →
      VExpr → VExpr → Prop
  | nil
      (Hctx : env.IsDefEqCtx U [] leftCtx rightCtx)
      (Hresidual : env.IsDefEqU U leftCtx leftResidual rightResidual) :
      DefEq env U leftCtx rightCtx [] [] leftResidual rightResidual
  | cons
      (Hdomain : env.IsDefEq U leftCtx leftDomain rightDomain (.sort level))
      (Htail : DefEq env U (leftDomain :: leftCtx) (rightDomain :: rightCtx)
        leftDomains rightDomains leftResidual rightResidual) :
      DefEq env U leftCtx rightCtx (leftDomain :: leftDomains)
        (rightDomain :: rightDomains) leftResidual rightResidual

namespace DefEq

@[simp] theorem domains_length
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual) :
    leftDomains.length = rightDomains.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- The pointwise telescope alignment assembles into definitional equality
of the complete progressively extended contexts. -/
theorem context
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual) :
    env.IsDefEqCtx U [] (leftDomains.reverse ++ leftCtx)
      (rightDomains.reverse ++ rightCtx) := by
  induction H with
  | nil Hctx _ => simpa using Hctx
  | cons _ _ ih =>
      simpa [List.reverse_cons, List.append_assoc] using ih

/-- The two final constructor residuals are definitionally equal in the
left complete telescope context. -/
theorem residual
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual) :
    env.IsDefEqU U (leftDomains.reverse ++ leftCtx)
      leftResidual rightResidual := by
  induction H with
  | nil _ Hresidual => simpa using Hresidual
  | cons _ _ ih =>
      simpa [List.reverse_cons, List.append_assoc] using ih

/-- Corresponding field domains at any position are definitionally equal in
the context formed by the preceding domains.  This gives the selected minor
binder a deterministic type without choosing literal WHNF syntax. -/
theorem domainAt
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual)
    (index : Nat) (hindex : index < leftDomains.length) :
    ∃ leftDomain rightDomain level,
      leftDomains[index]? = some leftDomain ∧
      rightDomains[index]? = some rightDomain ∧
      env.IsDefEq U ((leftDomains.take index).reverse ++ leftCtx)
        leftDomain rightDomain (.sort level) := by
  induction H generalizing index with
  | nil => simp at hindex
  | @cons leftCtx leftDomain rightDomain level rightCtx leftDomains
      rightDomains leftResidual rightResidual Hdomain Htail ih =>
      cases index with
      | zero =>
          exact ⟨leftDomain, rightDomain, level, by simp, by simp,
            by simpa using Hdomain⟩
      | succ index =>
          have htail : index < leftDomains.length := by simpa using hindex
          rcases ih index htail with
            ⟨currentLeft, currentRight, currentLevel, hleft, hright,
              Hcurrent⟩
          exact ⟨currentLeft, currentRight, currentLevel, by simpa using hleft,
            by simpa using hright, by
            simpa [List.take, List.reverse_cons, List.append_assoc] using
              Hcurrent⟩

/-- Binderwise telescope equality lifts any equality of the final bodies to
equality of the corresponding complete lambda telescopes. -/
theorem wrapLams
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual)
    (Hbody : env.IsDefEq U (leftDomains.reverse ++ leftCtx)
      leftBody rightBody bodyType) :
    ∃ type, env.IsDefEq U leftCtx
      (VExpr.wrapLams leftDomains leftBody)
      (VExpr.wrapLams rightDomains rightBody) type := by
  induction H generalizing leftBody rightBody bodyType with
  | nil _ _ =>
      exact ⟨bodyType, by simpa [VExpr.wrapLams] using Hbody⟩
  | @cons leftCtx leftDomain rightDomain level rightCtx leftDomains
      rightDomains leftResidual rightResidual Hdomain Htail ih =>
      have Hbody' : env.IsDefEq U (leftDomains.reverse ++
          leftDomain :: leftCtx) leftBody rightBody bodyType := by
        simpa [List.reverse_cons, List.append_assoc] using Hbody
      rcases ih Hbody' with ⟨tailType, HtailBody⟩
      exact ⟨.forallE leftDomain tailType, by
        simpa [VExpr.wrapLams] using Hdomain.lamDF HtailBody⟩

/-- The canonical selector minors built from aligned field telescopes are
definitionally equal.  Their final bodies are the same well-scoped de Bruijn
variable; `wrapLams` supplies the binder congruence. -/
theorem minorDefEq
    (H : DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual)
    (index : Nat) (hindex : index < leftDomains.length) :
    env.IsDefEqU U leftCtx
      (VExpr.wrapLams leftDomains
        (.bvar (leftDomains.length - index - 1)))
      (VExpr.wrapLams rightDomains
        (.bvar (rightDomains.length - index - 1))) := by
  let position := leftDomains.length - index - 1
  have hposition : position < (leftDomains.reverse ++ leftCtx).length := by
    simp only [position, List.length_append, List.length_reverse]
    omega
  let ⟨bodyType, Hlookup⟩ := Lookup.ofLt hposition
  have Hbody : env.IsDefEq U (leftDomains.reverse ++ leftCtx)
      (.bvar position) (.bvar position) bodyType :=
    VEnv.HasType.bvar Hlookup
  rcases H.wrapLams Hbody with ⟨type, Hminor⟩
  refine ⟨type, ?_⟩
  simpa only [position, H.domains_length] using Hminor

end DefEq

/-- Two complete field-telescope traversals are functional up to ordinary
definitional equality.  The proof follows the common field count.  At a
forall step, injectivity supplies the related domains and bodies, and the
body equality is interpreted in the correspondingly extended contexts.

This theorem is independent of primitive projections and candidate syntax;
it is the deterministic declarative telescope component later consumed by
the mutually recursive selected-field interpreter. -/
theorem align
    (henv : VEnv.WF env)
    (Hleft : ProjectionFieldTelescope env U leftCtx count leftSource
      leftDomains leftResidual)
    (Hright : ProjectionFieldTelescope env U rightCtx count rightSource
      rightDomains rightResidual)
    (Hctx : env.IsDefEqCtx U [] leftCtx rightCtx)
    (Hsource : env.IsDefEqU U leftCtx leftSource rightSource) :
    DefEq env U leftCtx rightCtx leftDomains rightDomains
      leftResidual rightResidual := by
  induction Hleft generalizing rightCtx rightSource rightDomains
      rightResidual with
  | nil HleftResidual =>
      cases Hright with
      | nil HrightResidual =>
          have hrightCtx : OnCtx rightCtx (env.IsType U) :=
            Hctx.symm henv.ordered |>.isType' (by trivial)
          have HrightResidual' :=
            HrightResidual.defeqDFC henv.ordered (Hctx.symm henv.ordered)
          exact .nil Hctx
            ((HleftResidual.symm.trans henv
              (Hctx.isType' (by trivial)) Hsource).trans henv
                (Hctx.isType' (by trivial)) HrightResidual')
  | @cons leftCtx leftSource leftDomain leftBody count leftDomains
      leftResidual HleftForall HleftTail ih =>
      cases Hright with
      | @cons rightCtx rightSource rightDomain rightBody _ rightDomains
          rightResidual HrightForall HrightTail =>
          have hleftCtx : OnCtx leftCtx (env.IsType U) :=
            Hctx.isType' (by trivial)
          have HrightForall' :=
            HrightForall.defeqDFC henv.ordered (Hctx.symm henv.ordered)
          have Hforalls : env.IsDefEqU U leftCtx
              (.forallE leftDomain leftBody)
              (.forallE rightDomain rightBody) :=
            (HleftForall.symm.trans henv hleftCtx Hsource).trans henv
              hleftCtx HrightForall'
          rcases Hforalls.forallE_inv henv hleftCtx with
            ⟨⟨level, Hdomains⟩, _, Hbodies⟩
          have Hbody : env.IsDefEqU U (leftDomain :: leftCtx)
              leftBody rightBody := ⟨_, Hbodies⟩
          exact .cons Hdomains
            (ih HrightTail (.succ Hctx Hdomains) Hbody)

end ProjectionFieldTelescope

/-- Declarative interpretation of the selected constructor-field prefix.
`project current projected` is the recursively checked meaning of the
primitive projection inserted for the field at `current`.  The relation is
parametric only so its mutual-recursion principle can be developed in a
small module; the kernel-facing specialization uses the native checked
projection relation itself, never a caller-supplied callback.

Unlike the executable trace, both syntactically dependent and independent
steps have one semantic rule.  If the concrete body is independent, its
instantiation is definitionally unchanged; if it is dependent, this is the
exact instantiation performed by production. -/
inductive ProjectionSelectedField
    (project : Nat → VExpr → Prop)
    (env : VEnv) (U : Nat) (Gamma : List VExpr) :
    Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hforall : env.IsDefEqU U Gamma source (.forallE selected body)) :
      ProjectionSelectedField project env U Gamma position 0 source selected
  | cons
      (Hforall : env.IsDefEqU U Gamma source (.forallE domain body))
      (Hproject : project position projected)
      (Hprojected : env.HasType U Gamma projected domain)
      (Htail : ProjectionSelectedField project env U Gamma (position + 1)
        remaining (body.inst projected) selected) :
      ProjectionSelectedField project env U Gamma position (remaining + 1)
        source selected

namespace ProjectionSelectedField

/-- Every selected domain exposed by the declarative interpreter is an
actual type.  No separate `targetWF` certificate is needed: the final forall
view already contains both sides' typing derivations. -/
theorem selectedIsType
    (henv : VEnv.WF env) (hGamma : OnCtx Gamma (env.IsType U))
    (H : ProjectionSelectedField project env U Gamma position count source
      selected) :
    env.IsType U Gamma selected := by
  induction H with
  | nil Hforall =>
      rcases Hforall with ⟨_, Hforall⟩
      exact (Hforall.hasType.2.forallE_inv henv.ordered).1
  | cons _ _ _ _ ih => exact ih

/-- The declarative selected-field interpreter is functional whenever its
strictly earlier recursive projection evidence is functional.  This is the
induction step used in the mutual expression/projection uniqueness proof:
the premise will be discharged by the induction hypothesis on finite native
evidence, not exposed in any final checker theorem. -/
theorem selectedDefEq
    (henv : VEnv.WF env) (hGamma : OnCtx Gamma (env.IsType U))
    (Hleft : ProjectionSelectedField leftProject env U Gamma position count
      leftSource leftSelected)
    (Hright : ProjectionSelectedField rightProject env U Gamma position count
      rightSource rightSelected)
    (Hsource : env.IsDefEqU U Gamma leftSource rightSource)
    (Hproject : ∀ current left right,
      leftProject current left → rightProject current right →
        env.IsDefEqU U Gamma left right) :
    env.IsDefEqU U Gamma leftSelected rightSelected := by
  induction Hleft generalizing rightSource rightSelected with
  | @nil leftSource leftSelected leftBody position HleftForall =>
      cases Hright with
      | @nil rightSource rightSelected rightBody _ HrightForall =>
          have Hforalls : env.IsDefEqU U Gamma
              (.forallE leftSelected leftBody)
              (.forallE rightSelected rightBody) :=
            (HleftForall.symm.trans henv hGamma Hsource).trans henv hGamma
              HrightForall
          rcases Hforalls.forallE_inv henv hGamma with
            ⟨⟨_, Hselected⟩, _, _⟩
          exact ⟨_, Hselected⟩
  | @cons leftSource leftDomain leftBody position leftProjected remaining
      leftSelected HleftForall HleftProject HleftProjected HleftTail ih =>
      cases Hright with
      | @cons rightSource rightDomain rightBody _ rightProjected _
          rightSelected HrightForall HrightProject HrightProjected HrightTail =>
          have Hforalls : env.IsDefEqU U Gamma
              (.forallE leftDomain leftBody)
              (.forallE rightDomain rightBody) :=
            (HleftForall.symm.trans henv hGamma Hsource).trans henv hGamma
              HrightForall
          rcases Hforalls.forallE_inv henv hGamma with
            ⟨⟨_, Hdomains⟩, _, Hbodies⟩
          have HprojectedEq : env.IsDefEq U Gamma leftProjected
              rightProjected leftDomain :=
            (Hproject position leftProjected rightProjected HleftProject
              HrightProject).of_l henv hGamma HleftProjected
          have Hinstantiated : env.IsDefEqU U Gamma
              (leftBody.inst leftProjected) (rightBody.inst rightProjected) :=
            ⟨_, Hbodies.instDF henv hGamma HprojectedEq⟩
          exact ih HrightTail Hinstantiated

end ProjectionSelectedField

end Lean4Lean
