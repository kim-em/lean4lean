import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBetaBody
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda

/-! A beta body reply computes a genuine lambda row from its exact local
needs. Domain certificates come from the selected captured frame, while
semantic code uses only the original domain child. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typedBinderPack from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option quotPrecheck false

section
variable
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (body : Derivation sourceEnv U (A :: source) e e B)
  (argument : Derivation sourceEnv U source a a A)
  (result : Derivation sourceEnv U source (B.inst a) (B.inst a) (.sort v))
  (instantiated : Derivation sourceEnv U source (e.inst a) (e.inst a) (B.inst a))
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

local notation "betaOrigin" => (Derivation.beta domainWF bodyWF domain codomain body argument result instantiated).dependencyOrigin ordered
local notation "base" => frame.captureBase substitutions
local notation "bodyDisplay" => betaCapturedBodyDisplay context domain body argument (.identity context)
local notation "capacity" => environmentCost (Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) :: frame.dependencyEnvironment ordered)
local notation "limit" => (Closure.close betaOrigin (frame.dependencyEnvironment ordered)).cost

private theorem domainBelowBeta :
    (Closure.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit := by
  have pair := Derivation.beta_dependency_comparison_schedule ordered domainWF bodyWF domain codomain body argument result instantiated (frame.dependencyEnvironment ordered)
  have lookup := variable_lookup (body.dependencyOrigin ordered)
    (show Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered))
      (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) ∈
      [Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered))
        (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered))] ++ frame.dependencyEnvironment ordered from List.mem_cons_self)
  simp only [schedule, Phase.code] at pair
  simp only [Closure.cost, List.cons_append, List.nil_append] at pair lookup ⊢
  omega

/-- This is a computed pack for the returned RAW computational query, not
an assumption that its requested profile has the raw query's typing. -/
theorem betaBodyTypedPack
    (henv : env.Ordered) (_hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (reply : BoundedGeneratedQueryReply base (base).initialCaps bodyDisplay σ τ profile capacity)
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (_observation : RichObs sourceEnv env U registry target (.ref (.left body)) reply.answer.reply.locals
      ((Subst.id.cons (a.subst .id)).comp σ) (rawProfile : Profile rank) required)
    (resources : required.Available reply.answer.reply.available) :
    Nonempty (RichTypedBinderPack (.left domain) env registry target locals σ available
      (a.subst σ) (a.subst τ) required rank) := by
  apply typedBinderPack (.left domain) henv required rank
  · intro need member
    let selected := reply.answer.reply.realization.frame
    obtain ⟨answer⟩ := selected.headCode henv formed (resources 0 need member)
    have positions : selected.peel.tailLocals = locals := by
      have first := selected.peel.positions
      have second := reply.answer.reply.locals_eq
      change reply.answer.reply.locals = Locals.push locals at second
      exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
        (List.cons.inj (first.trans second)).2
    have external : ∀ i need, need ∈ reply.answer.reply.available (i + 1) → need ∈ available i := by
      intro i wanted present
      exact reply.answer.capped.availableBound (i + 1) wanted present
    have identityTail : ((Subst.id.cons a).comp σ).tail = σ := by funext i; rfl
    have certificate : RichCert sourceEnv env U registry target (.ref (.left domain)) locals σ true
        answer.support answer.footprint := by
      simpa only [positions, betaCapturedBodyDisplay, Subst.comp, Subst.cons, subst_id, identityTail] using answer.certificate
    have certificateResources : answer.footprint.Available available :=
      fun i wanted present => external i wanted (answer.resources i wanted present)
    have related : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) need.profile answer.support := by
      simpa only [betaCapturedBodyDisplay, Subst.comp, Subst.cons, Subst.head, Subst.tail, subst_id, identityTail] using answer.related
    have smaller : (Closure.close (domain.dependencyOrigin ordered) (frame.leftDiagonal.dependencyEnvironment ordered)).cost < limit := by
      rw [frame.dependencyEnvironment_leftDiagonal]
      exact domainBelowBeta context domainWF bodyWF domain codomain body argument result instantiated frame ordered
    obtain ⟨code⟩ := domainF target locals σ σ available frame.leftDiagonal smaller closed formed
      substitutions.left certificate certificateResources
    exact ⟨answer.support, answer.footprint, ⟨certificate⟩, certificateResources, answer.typed, code.related, related⟩
  · intro i need member
    exact reply.answer.capped.availableBound (i + 1) need (resources (i + 1) need member)

structure GeneratedBetaLambdaRow (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  support : Profile rank
  output : Atom rank
  footprint : Footprint
  observation : RichObs sourceEnv env U registry target
    (.lam domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain)) (.ref (.left body))) locals σ
    (Profile.fn key output) footprint
  resources : footprint.Available available
  outputAdapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom rank bound requested)
  admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)
  domain_eq : key.domain = A.subst σ
  anchor_eq : key.anchor = a.subst σ

/-- The output lambda row is actual rich source syntax at the original
lambda children. Its key and all local needs are computed from the reply. -/
theorem generatedBetaLambdaRow
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (reply : BoundedGeneratedQueryReply base (base).initialCaps bodyDisplay σ τ (.singleton requested) capacity)
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit) :
    Nonempty (GeneratedBetaLambdaRow (env := env) (registry := registry) (target := target) (a := a) (locals := locals) (σ := σ) (available := available) domainWF bodyWF domain codomain body requested) := by
  obtain ⟨selected⟩ := reply.answer.reply.query.atom henv hscoped formed reply.answer.reply.closed
  obtain ⟨packed⟩ := betaBodyTypedPack context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped formed closed reply domainF selected.observation selected.resources
  let key : Key packed.rank := ⟨A.subst σ, a.subst σ, packed.input⟩
  have raw := (argument.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions.left
  have related := packed.related.left_diagonal
  have guard : LambdaGuard env U registry target σ A key packed.support :=
    ⟨packed.typed, packed.certificate.formed, .refl, packed.code,
      ⟨raw, raw, packed.support, packed.typed, packed.certificate.formed, packed.code, related, related⟩⟩
  have bodyQuery : RichObs sourceEnv env U registry target (.ref (.left body)) (Locals.push locals)
      (σ.cons (a.subst σ)) (.singleton (raiseAtom packed.rank packed.bound selected.atom)) selected.footprint := by
    have positions := reply.answer.reply.locals_eq
    change reply.answer.reply.locals = Locals.push locals at positions
    have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
      funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
    simpa only [betaCapturedBodyDisplay, positions, realization, raiseProfile_singleton] using selected.observation.raise packed.bound
  have adapter := GeneralNormalAtomAdapter.raise henv hscoped formed packed.bound selected.adapter
  have raised : raiseAtom packed.rank packed.bound (raiseAtom selected.rank selected.bound requested) =
      raiseAtom packed.rank (Nat.le_trans selected.bound packed.bound) requested := by
    have same := raiseProfile_trans selected.bound packed.bound (.singleton requested)
    simp only [raiseProfile_singleton] at same
    exact List.singleton_inj.mp (congrArg Profile.atoms same)
  rw [raised] at adapter
  exact ⟨⟨packed.rank, Nat.le_trans selected.bound packed.bound, key, packed.support, _, _,
    .lam domainWF bodyWF packed.certificate guard bodyQuery packed.pack (fun _ h => h),
    (fun i need member => (List.mem_append.mp member).elim (packed.resources i need) (packed.external i need)),
    adapter, guard.anchor, rfl, rfl⟩⟩


/-- Connected backward row producer: the incoming actual beta-result query
selects the capture and determines every resource of the returned lambda. -/
theorem generatedBetaLambdaRequest
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall base (base).initialCaps
      (betaInstantiatedDisplay context instantiated (.identity context)) bodyDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (query : RichObs sourceEnv env U registry target (.ref (.left instantiated)) locals σ
      (.singleton requested) footprint)
    (resources : footprint.Available available) :
    Nonempty (GeneratedBetaLambdaRow (env := env) (registry := registry) (target := target)
      (a := a) (locals := locals) (σ := σ) (available := available)
      domainWF bodyWF domain codomain body requested) := by
  obtain ⟨reply⟩ := generatedBetaBody context domainWF bodyWF domain codomain body argument result instantiated
    (.identity context) henv below ordered formed (base).identityRealization (base).identityCapped closed bodyR query resources
  exact generatedBetaLambdaRow context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped below formed closed reply domainF

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
