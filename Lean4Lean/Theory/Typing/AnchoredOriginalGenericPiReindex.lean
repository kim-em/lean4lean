import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational

/-! Native Pi expression reindexing at arbitrary actual original source frames. Both domain and body queries keep their actual occurrences
and captured environments, including when the source contexts differ. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem LambdaGuard.anchorRelated (henv : env.Ordered)
    (guard : LambdaGuard env U registry target σ A key ambient) :
    Related env U registry target key.anchor key.anchor (A.subst σ) key.input ambient := by
  obtain ⟨_, _, _, _, _, _, _, arguments⟩ := guard.anchor
  exact Related.convert henv guard.inputTyped guard.domains arguments

/-- This is an actual fresh binder, retaining its original domain proof.
Its closure ledger is definitionally the domain closure plus the old frame. -/
noncomputable def OriginalRichFrame.atAnchor
    {header : EndpointRef headerEnv U rootSource he ht}
    {initialContext : ContextDerivation headerEnv U rootSource}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (code : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    OriginalRichFrame headerEnv env U registry target (.cons context domain)
      (Locals.push locals) (σ.cons key.anchor) (σ.cons key.anchor) (available.push needs) :=
  .bind frame domain code resources guard.inputTyped (LambdaGuard.anchorRelated henv guard) needs bounded covered


variable
  {leftHeader : EndpointRef leftEnv U leftRootSource leftHeaderExpression leftHeaderType}
  {leftInitialContext : ContextDerivation leftEnv U leftRootSource}
  {rightHeader : EndpointRef rightEnv U rightRootSource rightHeaderExpression rightHeaderType}
  {rightInitialContext : ContextDerivation rightEnv U rightRootSource}
  {leftContext : ContextDerivation leftEnv U leftSource}
  {rightContext : ContextDerivation rightEnv U rightSource}

/-- Exact finite data for one side of the Pi comparison. The certificate is
the original domain query, and the frame is the actual caller's frame. -/
structure OriginalPiSide
    (header : EndpointRef headerEnv U rootSource headerExpression headerType)
    (initialContext : ContextDerivation headerEnv U rootSource)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} (context : ContextDerivation headerEnv U source)
    (domain : EndpointRef headerEnv U source A (.sort u))
    (locals : List Nat) (σ : Subst) (available : Valuation) (ambient : Profile n) where
  frame : OriginalRichFrame headerEnv env U registry target context locals σ σ available
  location : Located header (.ref domain)
  lineage : location.contextDerivation initialContext = context
  footprint : Footprint
  code : RichCert headerEnv env U registry target (.ref domain) locals σ true ambient footprint
  resources : footprint.Available available

noncomputable def OriginalPiSide.atAnchor
    {header : EndpointRef headerEnv U rootSource he ht}
    {initialContext : ContextDerivation headerEnv U rootSource}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    (henv : env.Ordered)
    (side : OriginalPiSide header initialContext env registry target context domain locals σ available (ambient : Profile n))
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    OriginalRichFrame headerEnv env U registry target (.cons context domain)
      (Locals.push locals) (σ.cons key.anchor) (σ.cons key.anchor) (available.push needs) :=
  side.frame.atAnchor henv domain side.location side.lineage side.code side.resources guard needs bounded covered

/-- Both actual body environments are strictly below the pair of parent
Pi environments. This bound is independent of the sizes of the queries. -/
theorem OriginalPiSide.body_pair_bound
    (henv : env.Ordered) (lf : leftEnv.Ordered)
    (rf : rightEnv.Ordered)
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
    {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
    (left : OriginalPiSide leftHeader leftInitialContext env registry target leftContext leftDomain leftLocals σ leftAvailable (ambient : Profile n))
    (right : OriginalPiSide rightHeader rightInitialContext env registry target rightContext rightDomain rightLocals τ rightAvailable ambient)
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
    (leftGuard : LambdaGuard env U registry target σ A key ambient)
    (rightGuard : LambdaGuard env U registry target τ C key ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    (Closure.close (leftBody.dependencyOrigin lf)
      ((left.atAnchor henv leftGuard needs bounded covered).dependencyEnvironment lf)).cost +
    (Closure.close (rightBody.dependencyOrigin rf)
      ((right.atAnchor henv rightGuard needs bounded covered).dependencyEnvironment rf)).cost <
    (Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
      (left.frame.dependencyEnvironment lf)).cost +
    (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
      (right.frame.dependencyEnvironment rf)).cost :=
  Nat.add_lt_add (binder_body_cost (by simp) _) (binder_body_cost (by simp) _)

/-- The expression-reindex induction hypothesis restricted to the two
actual original Pi bodies and their fresh-anchor frames. -/
def OriginalPiBodyReindex
    (henv : env.Ordered) (lf : leftEnv.Ordered)
    (rf : rightEnv.Ordered)
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
    {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
    (left : OriginalPiSide leftHeader leftInitialContext env registry target leftContext leftDomain leftLocals σ leftAvailable (ambient : Profile n))
    (right : OriginalPiSide rightHeader rightInitialContext env registry target rightContext rightDomain rightLocals τ rightAvailable ambient)
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))

    (relevant : Bool) : Prop :=
  ∀ (key : Key n) (output : Profile n) (guard : LambdaGuard env U registry target σ A key ambient)
      (rightGuard : LambdaGuard env U registry target τ C key ambient)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms),
      richSchedule .expressionReindex
        ((Closure.close (leftBody.dependencyOrigin lf)
          ((left.atAnchor henv guard needs bounded covered).dependencyEnvironment lf)).cost +
         (Closure.close (rightBody.dependencyOrigin rf)
          ((right.atAnchor henv rightGuard needs bounded covered).dependencyEnvironment rf)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
          (left.frame.dependencyEnvironment lf)).cost +
         (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
          (right.frame.dependencyEnvironment rf)).cost) →
      B.subst (σ.cons key.anchor) = D.subst (τ.cons key.anchor) →
      ∀ footprint,
      RichCert leftEnv env U registry target leftBody (Locals.push leftLocals)
        (σ.cons key.anchor) relevant output footprint →
      footprint.Available (leftAvailable.push needs) →
      Nonempty (RichCodeTransferResult env U registry target leftBody rightBody (Locals.push rightLocals)
        (σ.cons key.anchor) (τ.cons key.anchor) (rightAvailable.push needs) relevant output)

theorem RichRows.reindexGenericPiRows
    (henv : env.Ordered) (lf : leftEnv.Ordered)
    (rf : rightEnv.Ordered)
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
    {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
    (left : OriginalPiSide leftHeader leftInitialContext env registry target leftContext leftDomain leftLocals σ leftAvailable (ambient : Profile n))
    (right : OriginalPiSide rightHeader rightInitialContext env registry target rightContext rightDomain rightLocals τ rightAvailable ambient)
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
    (equal : (VExpr.forallE A B).subst σ = (VExpr.forallE C D).subst τ)
    (bodyReplay : OriginalPiBodyReindex henv lf rf
      left right leftBody rightBody relevant)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals σ relevant ambient values footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ resultFootprint,
      Nonempty (RichRows rightEnv env U registry target (.ref rightDomain) rightBody rightLocals τ relevant ambient values resultFootprint) ∧
      resultFootprint.Available rightAvailable := by
  match rows with
  | .nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | .cons guard certificate pack covered rest =>
    have domains := (VExpr.forallE.inj equal).1
    have rightGuard : LambdaGuard env U registry target τ C _ ambient := {
      inputTyped := guard.inputTyped, formed := guard.formed, anchor := guard.anchor
      path := by simpa only [domains] using guard.path
      domains := by simpa only [domains] using guard.domains }
    obtain ⟨answer⟩ := bodyReplay _ _ guard rightGuard _
      (fun need member => (pack.atomized_localNeeds need member).1)
      (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
      (richSchedule_strict (left.body_pair_bound henv lf rf right leftBody rightBody
        guard rightGuard _ _ _) _ _)
      (pi_realized_body_eq equal _) _ certificate
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member)))
    obtain ⟨packed, outside, newPack, newCovered, newResources⟩ := Footprint.pack_available answer.resources
      (fun need member => (pack.atomized_localNeeds need member).1)
      (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailResources⟩ := rest.reindexGenericPiRows henv lf rf left right leftBody rightBody equal bodyReplay
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨outside ++ tailFootprint, ⟨.cons rightGuard answer.certificate newPack newCovered tailCode⟩,
      fun i need member => (List.mem_append.mp member).elim (newResources i need) (tailResources i need)⟩
termination_by sizeOf rows

/-- Complete native Pi formation-code R. The domain and body destinations
are independently derived original occurrences. Source unary F supplies the
semantics; strict binary child R calls construct the actual destination code. -/
theorem OriginalRichFrame.nativePiReindexStep
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered)
    (rf : rightEnv.Ordered)
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
    {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
    (left : OriginalPiSide leftHeader leftInitialContext env registry target leftContext leftDomain leftLocals σ leftAvailable (ambient : Profile n))
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (rightLocation : Located rightHeader (.ref rightDomain))
    (rightLineage : rightLocation.contextDerivation rightInitialContext = rightContext)
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
    (lu : u.WF U) (lv : v.WF U) (ru : u'.WF U) (rv : v'.WF U)
    (equal : (VExpr.forallE A B).subst σ = (VExpr.forallE C D).subst τ)
    (leftClosed : leftAvailable.AtomClosed)
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (piLocation : Located leftHeader (.pi lu lv (.ref leftDomain) leftBody))
    (piLineage : piLocation.contextDerivation leftInitialContext = leftContext)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitialContext piLocation
      ((Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
        (left.frame.dependencyEnvironment lf)).cost +
       (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
        (rightFrame.dependencyEnvironment rf)).cost))
    (domainR :
      richSchedule .expressionReindex
        ((Closure.close (leftDomain.dependencyOrigin lf) (left.frame.dependencyEnvironment lf)).cost +
         (Closure.close (rightDomain.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
          (left.frame.dependencyEnvironment lf)).cost +
         (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
          (rightFrame.dependencyEnvironment rf)).cost) →
      A.subst σ = C.subst τ →
      RichCodeTransfer env U registry target (.ref leftDomain) (.ref rightDomain)
        leftLocals rightLocals σ τ leftAvailable rightAvailable)
    (bodyR : ∀ answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
      rightLocals σ τ rightAvailable true ambient,
      OriginalPiBodyReindex henv lf rf left
        ⟨rightFrame, rightLocation, rightLineage, answer.footprint, answer.certificate, answer.resources⟩
        leftBody rightBody relevant)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals σ relevant ambient values footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichCodeTransferResult env U registry target
      (.pi lu lv (.ref leftDomain) leftBody) (.pi ru rv (.ref rightDomain) rightBody)
      rightLocals σ τ rightAvailable relevant (Profile.pi prototypeDomain prototypeBody ambient values)) := by
  have domains := (VExpr.forallE.inj equal).1
  have bodies := (VExpr.forallE.inj equal).2
  have domainBound := Nat.add_lt_add
    (binder_domain_cost (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] []
      (left.frame.dependencyEnvironment lf))
    (binder_domain_cost (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] []
      (rightFrame.dependencyEnvironment rf))
  obtain ⟨domainAnswer⟩ := domainR (richSchedule_strict domainBound _ _) domains left.code left.resources
  let right : OriginalPiSide rightHeader rightInitialContext env registry target rightContext rightDomain
      rightLocals τ rightAvailable ambient :=
    ⟨rightFrame, rightLocation, rightLineage, domainAnswer.footprint, domainAnswer.certificate, domainAnswer.resources⟩
  obtain ⟨rowFootprint, ⟨rowCode⟩, rowResources⟩ := rows.reindexGenericPiRows henv lf rf
    left right leftBody rightBody equal (bodyR domainAnswer) resources
  have rightGuard : PiGuard env U target τ C D prototypeDomain prototypeBody := {
    domainPath := by simpa only [domains] using guard.domainPath
    bodyPath := by simpa only [domains, bodies] using guard.bodyPath }
  have positive := (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
    (rightFrame.dependencyEnvironment rf)).cost_pos
  have sourceBound : (Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
      (left.frame.dependencyEnvironment lf)).cost <
      (Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
        (left.frame.dependencyEnvironment lf)).cost +
      (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
        (rightFrame.dependencyEnvironment rf)).cost := by
    change _ < _ + _
    exact Nat.lt_add_of_pos_right positive
  unfold OriginalCodeInductionAt at sourceF
  rw [piLineage] at sourceF
  obtain ⟨semantics⟩ := sourceF target leftLocals σ σ leftAvailable left.frame sourceBound
    leftClosed formed leftSubstitutions (.pi lu lv left.code guard rows)
    (fun i need member => (List.mem_append.mp member).elim (left.resources i need) (resources i need))
  exact ⟨{
    footprint := domainAnswer.footprint ++ rowFootprint
    certificate := .pi ru rv domainAnswer.certificate rightGuard rowCode
    resources := fun i need member => (List.mem_append.mp member).elim (domainAnswer.resources i need) (rowResources i need)
    related := by simpa only [← equal] using semantics.related }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
