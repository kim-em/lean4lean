import Lean4Lean.Theory.Typing.AnchoredFamilyPlanFront
import Lean4Lean.Theory.Typing.AnchoredConstructorCaptureExtraction
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope
import Batteries.Tactic.OpenPrivate

/-! Consume the actual source family applications, retaining declaration
substitutions and finite observers for every captured request. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private normal_fn_parts unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
set_option backward.isDefEq.respectTransparency false

structure FamilyPlanConsumption (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (info : VConstant) (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  seedLevels : List VLevel
  seedWF : ∀ level ∈ seedLevels, level.WF U
  seedLength : seedLevels.length = info.uvars
  equivalent : List.Forall₂ (· ≈ ·) seedLevels levels
  signature : ConstantTelescope (info.type.instL seedLevels)
  typeClosed : info.type.Closed
  anchors : List VExpr
  length : anchors.length = arguments.length
  output : Atom rank
  footprint : Footprint
  plan : FamilyPlan env U registry target name seedLevels signature anchors (.singleton output) footprint
  adapter : NormalAtomAdapter env U registry target output (raiseAtom rank bound requested)
  valuation : Valuation
  closed : valuation.AtomClosed
  raw : Ctx.SubstEq env U target (nativeCaptureSubst anchors)
    (nativeCaptureSubst (arguments.map (·.subst σ))) (signature.domains.take arguments.length).reverse
  fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
    (List.range arguments.length) (nativeCaptureSubst anchors)
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
  resources : footprint.Available valuation
  observed : NativeGradedValuation env U registry target locals σ available arguments valuation

private theorem raiseAtom_twice {n k N : Nat} (hn : n ≤ k) (hk : k ≤ N) (a : Atom n) :
    raiseAtom N hk (raiseAtom k hn a) = raiseAtom N (Nat.le_trans hn hk) a := by
  have h := raiseProfile_trans hn hk (.singleton a)
  rw [raiseProfile_singleton, raiseProfile_singleton, raiseProfile_singleton] at h
  exact List.singleton_inj.mp (congrArg Profile.atoms h)

noncomputable def FamilyPlanConsumption.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments requested)
    (N : Nat) (bound : result.rank ≤ N) :
    FamilyPlanConsumption env U registry target locals σ available info name levels arguments requested := by
  refine { result with
    rank := N
    bound := Nat.le_trans result.bound bound
    output := raiseAtom N bound result.output
    plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
    adapter := ?_ }
  simpa only [raiseAtom_twice] using result.adapter.raise henv hscoped hTarget bound

noncomputable def FamilyPlanConsumption.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments a)
    (change : AtomView env U registry target a b) :
    FamilyPlanConsumption env U registry target locals σ available info name levels arguments b :=
  { result with adapter := result.adapter.comp ((change.toAdapter henv hscoped hTarget).raise
      henv hscoped hTarget result.bound) }

noncomputable def FamilyPlanConsumption.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments (a : Atom n)) :
    FamilyPlanConsumption env U registry target locals σ available info name levels arguments (n := n + 1) (AtomData.pad a) := by
  let raised := result.raiseTo henv hscoped hTarget (result.rank + 1) (Nat.le_succ _)
  have bound : n + 1 ≤ raised.rank := Nat.succ_le_succ result.bound
  exact { raised with
    bound := bound
    adapter := by simpa only [raiseAtom_pad] using raised.adapter }

noncomputable def FamilyPlanConsumption.unpad
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments (n := n + 1) (AtomData.pad (a : Atom n))) :
    FamilyPlanConsumption env U registry target locals σ available info name levels arguments a :=
  { result with
    bound := Nat.le_trans (Nat.le_succ _) result.bound
    adapter := by simpa only [raiseAtom_pad] using result.adapter }

/-- Consume one original application leaf. Adapter contravariance is pulled
through the actual family binder's admission; the source argument remains an
actual graded observer rather than a new valuation assumption. -/
theorem FamilyPlanConsumption.app
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A level}, sourceEnv.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {key : Key n} {output : Atom n}
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 1) (.fn key output))
    (typeFormation : sourceEnv.IsDefEqStrong U [] (info.type.instL result.seedLevels)
      (info.type.instL result.seedLevels) (.sort typeLevel))
    {argument : VExpr} {input : Profile n} {argumentFootprint : Footprint}
    (observation : Obs env U registry target locals σ argument input argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : NormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ)) :
    Nonempty (FamilyPlanConsumption env U registry target locals σ available info name levels
      (arguments ++ [argument]) output) := by
  rcases result with ⟨rank, bound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, atom, footprint, plan, adapter, valuation, closed, raw, fits, planResources, observed⟩
  cases rank with
  | zero => omega
  | succ rank =>
    have hn : n ≤ rank := Nat.le_of_succ_le_succ bound
    obtain ⟨front⟩ := plan.front henv hscoped hTarget atom rfl
    cases front with
    | terminal saturated shape relevant captures terminalBound frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toAdapter henv hscoped hTarget
      exact (familyAdapter_not_fn terminalBound (frontAdapter.comp (adapter.comp expose))).elim
    | @binder r domainFoot bodyFoot outside requested domain oldKey oldOutput support packed
        origin domainCode guard body pack covered frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toAdapter henv hscoped hTarget
      have normalized := frontAdapter.comp (adapter.comp expose)
      obtain ⟨⟨keys⟩, ⟨outputs⟩⟩ := normal_fn_parts normalized
      have incoming := AdapterNormal.normalizeAdmission henv hscoped hTarget
        (Admitted.raise henv hn admitted)
      have seed := AdapterNormal.normalizeAdmission henv hscoped hTarget guard.anchor
      have pulled := unnormalize_admission henv hscoped hTarget
        (keys.pull henv hscoped hTarget seed incoming)
      let highInput := raiseProfile rank hn input
      let highObservation := observation.raise hn
      have highInputs : NormalProfileAdapter env U registry target highInput oldKey.input :=
        (NormalProfileAdapter.raise henv hscoped hTarget hn inputs).comp keys.arguments
      let argumentResult : GradedResult env U registry target locals σ available argument oldKey.input := {
        rank := rank
        bound := Nat.le_refl rank
        raw := highInput
        footprint := argumentFootprint
        observation := highObservation
        adapter := by simpa only [raiseProfile_self] using highInputs
        resources := resources
        live := (raiseProfile_live_iff hn input).mpr live }
      have domainBound := (List.getElem?_eq_some_iff.mp origin).1
      obtain ⟨domainLevel, originalDomain⟩ :=
        (signature.prefixFormation typeFormation anchors.length).2 domainBound
      rw [(List.getElem?_eq_some_iff.mp origin).2] at originalDomain
      have sourceEq : (signature.domains.take anchors.length).reverse =
          (signature.domains.take arguments.length).reverse := by rw [length]
      rw [sourceEq] at originalDomain
      have domainCode' := domainCode
      rw [length] at domainCode'
      obtain ⟨childRaw, childFits, childResources⟩ := LambdaGuard.nativeBinderPair henv hscoped hTarget
        (originalDomain.defeq.mono hle) (earlier originalDomain) closed raw fits
        domainCode' guard pack covered planResources pulled
      have childContext : (signature.domains.take (arguments ++ [argument]).length).reverse =
          domain :: (signature.domains.take arguments.length).reverse := by
        simpa only [List.length_append, List.length_singleton, length] using
          signature.prefixContext_cons origin
      have childLocals : List.range (arguments ++ [argument]).length =
          Locals.push (List.range arguments.length) := by
        simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
      refine ⟨{
        rank := rank
        bound := hn
        seedLevels := seedLevels
        seedWF := seedWF
        seedLength := seedLength
        equivalent := equivalent
        signature := signature
        typeClosed := typeClosed
        anchors := anchors ++ [oldKey.anchor]
        length := by simp only [List.length_append, List.length_singleton, length]
        output := oldOutput
        footprint := bodyFoot
        plan := body
        adapter := outputs
        valuation := Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation
        closed := Valuation.push_atomized_closed closed _
        raw := ?_
        fits := ?_
        resources := childResources
        observed := observed.push argumentResult
          (fun need hm => (pack.atomized_localNeeds need hm).1)
          (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha)) }⟩
      · simpa only [childContext, nativeCaptureSubst_append, List.map_append, List.map_cons,
          List.map_nil] using childRaw
      · simpa only [childContext, childLocals, nativeCaptureSubst_append, List.map_append,
          List.map_cons, List.map_nil] using childFits

end Lean4Lean.AnchoredSource.Adapted
