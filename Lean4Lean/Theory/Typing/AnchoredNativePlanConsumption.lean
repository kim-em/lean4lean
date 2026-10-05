import Lean4Lean.Theory.Typing.AnchoredNativePlanPadding
import Lean4Lean.Theory.Typing.AnchoredNativeBinderPair
import Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceInstantiation
import Lean4Lean.Theory.Typing.AnchoredApplicationTrace

/-! Consume actual native application observations. The remaining plan stays
literal; key changes live in finite adapters, and every required source
argument demand retains an actual graded observation in the caller valuation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open NativeRecursorData hiding target levels
set_option backward.isDefEq.respectTransparency false

/-- Finite valuation entries are backed by genuine source argument results. -/
def NativeGradedValuation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) (prior : Valuation) : Prop :=
  ∀ index need, need ∈ prior index → ∃ bound : index < arguments.length,
    Nonempty (GradedResult env U registry target locals σ available
      arguments[arguments.length - 1 - index] need.profile)

theorem NativeGradedValuation.empty :
    NativeGradedValuation env U registry target locals σ available [] (fun _ => []) := by
  intro _ _ h
  cases h

theorem NativeGradedValuation.push
    (observed : NativeGradedValuation env U registry target locals σ available arguments prior)
    (argument : GradedResult env U registry target locals σ available expression (input : Profile n))
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    NativeGradedValuation env U registry target locals σ available (arguments ++ [expression])
      (Valuation.push needs prior) := by
  intro index need member
  cases index with
  | zero =>
    refine ⟨by simp, ⟨?_⟩⟩
    simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel, Nat.sub_zero,
      List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] using
      argument.localDemand need (bounded need member) (covered need member)
  | succ index =>
    obtain ⟨bound, ⟨value⟩⟩ := observed index need member
    have position : (arguments ++ [expression]).length - 1 - (index + 1) =
        arguments.length - 1 - index := by simp only [List.length_append, List.length_singleton]; omega
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ⟨?_⟩⟩
    have same : (arguments ++ [expression])[(arguments ++ [expression]).length - 1 - (index + 1)] =
        arguments[arguments.length - 1 - index] := by
      simp only [position]
      exact List.getElem_append_left (by omega)
    exact same.symm ▸ value

structure NativePlanConsumption (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (data : NativeRecursorData) (levels : List VLevel) (arguments : List VExpr)
    (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  seedLevels : List VLevel
  seedWF : ∀ level ∈ seedLevels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seedLevels levels
  signature : NativeConstantSignature data seedLevels
  typeClosed : signature.type.Closed
  anchors : List VExpr
  length : anchors.length = arguments.length
  output : Atom rank
  footprint : Footprint
  plan : NativePlan env U registry target signature anchors (.singleton output) footprint
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

noncomputable def NativePlanConsumption.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments requested)
    (N : Nat) (bound : result.rank ≤ N) :
    NativePlanConsumption env U registry target locals σ available data levels arguments requested := by
  let raised := result.plan.raiseSingleton henv bound
  refine { result with
    rank := N
    bound := Nat.le_trans result.bound bound
    output := raised.output
    plan := raised.plan
    adapter := ?_ }
  have first := (raised.view.inverse henv).toAdapter henv hscoped hTarget
  have second := result.adapter.raise henv hscoped hTarget bound
  simpa only [raiseAtom_twice] using NormalAtomAdapter.comp first second

noncomputable def NativePlanConsumption.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments a)
    (change : AtomView env U registry target a b) :
    NativePlanConsumption env U registry target locals σ available data levels arguments b :=
  { result with adapter := result.adapter.comp ((change.toAdapter henv hscoped hTarget).raise
      henv hscoped hTarget result.bound) }

noncomputable def NativePlanConsumption.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments (a : Atom n)) :
    NativePlanConsumption env U registry target locals σ available data levels arguments (n := n + 1) (AtomData.pad a) := by
  let raised := result.raiseTo henv hscoped hTarget (result.rank + 1) (Nat.le_succ _)
  have bound : n + 1 ≤ raised.rank := Nat.succ_le_succ result.bound
  exact { raised with
    bound := bound
    adapter := by simpa only [raiseAtom_pad] using raised.adapter }

noncomputable def NativePlanConsumption.unpad
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments (n := n + 1) (AtomData.pad (a : Atom n))) :
    NativePlanConsumption env U registry target locals σ available data levels arguments a :=
  { result with
    bound := Nat.le_trans (Nat.le_succ _) result.bound
    adapter := by simpa only [raiseAtom_pad] using result.adapter }

private theorem normal_fn_parts
    {old key : Key n} {output result : Atom n}
    (adapter : NormalAtomAdapter env U registry target (n := n + 1) (AtomData.fn old output) (AtomData.fn key result)) :
    Nonempty (KeyProgram env U registry target (AdapterNormal.key old) (AdapterNormal.key key)) ∧
    Nonempty (NormalAtomAdapter env U registry target output result) := by
  change AtomAdapter env U registry target (n := n + 1) (AtomData.fn (AdapterNormal.key old) (AdapterNormal.atom output))
    (AtomData.fn (AdapterNormal.key key) (AdapterNormal.atom result)) at adapter
  obtain ⟨sourceKey, sourceOutput, same, ⟨keys⟩, ⟨outputs⟩⟩ := adapter.fn_inv
  obtain ⟨keyEq, outputEq⟩ := AtomData.fn.inj same
  rw [← keyEq] at keys
  rw [← outputEq] at outputs
  exact ⟨⟨keys⟩, ⟨outputs⟩⟩

private theorem unnormalize_admission
    {key : Key n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (admitted : Admitted env U registry target (AdapterNormal.key key) x y) :
    Admitted env U registry target key x y := by
  have result := ((AdapterNormal.profileView (env := env) (U := U) (registry := registry)
    (Γ := target) henv key.input).inverse henv).admissionMapWith hTarget
      (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
      (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) admitted
  exact result

/-- Consume one original application leaf. Adapter contravariance is pulled
through the actual native binder's admission; the source argument remains an
actual graded observer rather than a new valuation assumption. -/
theorem NativePlanConsumption.app
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A level}, sourceEnv.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel} {arguments : List VExpr}
    {key : Key n} {output : Atom n}
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments
      (n := n + 1) (.fn key output))
    (typeFormation : sourceEnv.IsDefEqStrong U [] (result.signature.type.instL result.seedLevels)
      (result.signature.type.instL result.seedLevels) (.sort typeLevel))
    (notFull : arguments.length < data.majorOffset + 1)
    {argument : VExpr} {input : Profile n} {argumentFootprint : Footprint}
    (observation : Obs env U registry target locals σ argument input argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : NormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ)) :
    Nonempty (NativePlanConsumption env U registry target locals σ available data levels
      (arguments ++ [argument]) output) := by
  rcases result with ⟨rank, bound, seedLevels, seedWF, equivalent, signature, typeClosed,
    anchors, length, atom, footprint, plan, adapter, valuation, closed, raw, fits, planResources, observed⟩
  cases rank with
  | zero => omega
  | succ rank =>
    have hn : n ≤ rank := Nat.le_of_succ_le_succ bound
    cases plan with
    | terminal program selected lhsClosed rhsClosed saturated => omega
    | @binder r _ _ _ _ domain oldKey oldOutput support packed domainFoot bodyFoot outside
        origin domainCode guard body pack covered =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toAdapter henv hscoped hTarget
      have normalized := adapter.comp expose
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
