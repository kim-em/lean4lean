import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCertificateSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient

/-! A native body query is closed through one actual original lambda binder.
Its guard is computed by the strict original domain call and the retained
capture value. No already-completed guard or type-plan is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem nativeBinderQuery
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (term : EndpointState sourceEnv U (A :: source) expression B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv domain codomain term))
    (frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ σ available)
    (ambient : frame.Ambient)
    (domainF : OriginalAmbientCodeInductionAt env registry ordered initial (.lamDomain location)
      (Closure.close ((EndpointState.lam hu hv domain codomain term).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (raw : Ctx.SubstEq env U target σ σ source)
    (certificate : CodeCert env U registry target locals σ A (support : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (typed : input.HasType support)
    (valueTyped : env.HasType U target value (A.subst σ))
    (valueRelated : Related env U registry target value value (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (body : Obs env U registry target (Locals.push locals) (σ.cons value) expression
      (.singleton (output : Atom n)) bodyFootprint)
    (resources : bodyFootprint.Available (available.push needs)) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ (.lam A expression)
      (Profile.fn ⟨A.subst σ, value, input⟩ output) footprint) ∧ footprint.Available available := by
  have smaller := binder_domain_cost (domain.dependencyOrigin ordered)
    [codomain.dependencyOrigin ordered, term.dependencyOrigin ordered] []
    (frame.dependencyEnvironment ordered)
  obtain ⟨answer⟩ := domainF target locals σ σ available frame ambient smaller closed formed raw
    (.legacy (.ofCode certificate certificate.formed)) domainResources
  let guard : LambdaGuard env U registry target σ A ⟨A.subst σ, value, input⟩ support :=
    ⟨typed, certificate.formed, .refl, answer.related,
      ⟨valueTyped, valueTyped, support, typed, certificate.formed, answer.related, valueRelated, valueRelated⟩⟩
  obtain ⟨packed, outside, pack, localCovered, outsideResources⟩ :=
    Footprint.pack_available resources bounded covered
  exact ⟨domainFootprint ++ outside, ⟨.lam certificate guard body pack localCovered⟩,
    by
      intro index need member
      rcases List.mem_append.mp member with first | second
      · exact domainResources index need first
      · exact outsideResources index need second⟩

/-- Every requested body atom is retained, including the empty profile case. -/
def nativeBinderDemand (key : Key n) : List (Atom n) → Profile (n + 1)
  | [] => .empty
  | atom :: atoms => (Profile.fn key atom).union (nativeBinderDemand key atoms)

theorem nativeBinderProfileQuery
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (term : EndpointState sourceEnv U (A :: source) expression B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv domain codomain term))
    (frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ σ available)
    (ambient : frame.Ambient)
    (domainF : OriginalAmbientCodeInductionAt env registry ordered initial (.lamDomain location)
      (Closure.close ((EndpointState.lam hu hv domain codomain term).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (raw : Ctx.SubstEq env U target σ σ source)
    (certificate : CodeCert env U registry target locals σ A (support : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (typed : input.HasType support)
    (valueTyped : env.HasType U target value (A.subst σ))
    (valueRelated : Related env U registry target value value (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (body : Obs env U registry target (Locals.push locals) (σ.cons value) expression
      (profile : Profile n) bodyFootprint)
    (resources : bodyFootprint.Available (available.push needs))
    (fullClosed : (available.push needs).AtomClosed) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ (.lam A expression)
      (nativeBinderDemand ⟨A.subst σ, value, input⟩ profile.atoms) footprint) ∧
      footprint.Available available := by
  suffices all : ∀ atoms : List (Atom n), (∀ atom ∈ atoms, atom ∈ profile.atoms) →
      ∃ footprint, Nonempty (Obs env U registry target locals σ (.lam A expression)
        (nativeBinderDemand ⟨A.subst σ, value, input⟩ atoms) footprint) ∧
        footprint.Available available from all profile.atoms (fun _ member => member)
  intro atoms
  induction atoms with
  | nil => exact fun _ => ⟨[], ⟨.empty⟩, fun _ _ member => nomatch member⟩
  | cons atom atoms ih =>
    intro included
    obtain ⟨selected⟩ := body.atom (included atom List.mem_cons_self)
    obtain ⟨firstFootprint, ⟨first⟩, firstAvailable⟩ :=
      nativeBinderQuery henv ordered initial domain codomain term hu hv location frame ambient domainF
        closed formed raw certificate domainResources typed valueTyped valueRelated needs bounded covered
        selected.observation (selected.atomizes.available_closed resources fullClosed)
    obtain ⟨restFootprint, ⟨rest⟩, restAvailable⟩ :=
      ih (fun item member => included item (List.mem_cons_of_mem _ member))
    exact ⟨firstFootprint ++ restFootprint, ⟨.union first rest⟩, by
      intro index need member
      rcases List.mem_append.mp member with first | second
      · exact firstAvailable index need first
      · exact restAvailable index need second⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
