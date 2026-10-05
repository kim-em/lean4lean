import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySourceRequests
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpine

/-! Consume the finite rigid-family program without a literal declaration
telescope. Every frozen request is tied to an actual caller argument original;
finite output adapters preserve those same requests through grade changes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
open private raiseAtom_twice from Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyConsumption
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {env : VEnv} {strata : EquationStratification env}

structure WorldRigidFamilyConsumption
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  programRank : Nat
  programBound : programRank ≤ rank
  past : List RigidFamilyArgument
  plan : RigidFamilySpine programRank
  ready : plan.Ready env U registry target
  adapter : GeneralNormalAtomAdapter env U registry target
    (raiseAtom rank programBound (plan.atom name levels past)) (raiseAtom rank bound requested)
  sources : List.Forall₂ (fun expression argument => Nonempty
    (WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression
      argument.request)) arguments past

noncomputable def WorldRigidFamilyConsumption.bare
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (plan : RigidFamilySpine n) (ready : plan.Ready env U registry target) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels [] (plan.atom name levels []) where
  rank := n
  bound := Nat.le_refl _
  programRank := n
  programBound := Nat.le_refl _
  past := []
  plan := plan
  ready := ready
  adapter := GeneralAtomAdapter.refl _
  sources := .nil

noncomputable def WorldRigidFamilyConsumption.raiseTo
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cursor : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments requested)
    (N : Nat) (bound : cursor.rank ≤ N) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments requested := by
  refine { cursor with
    rank := N
    bound := Nat.le_trans cursor.bound bound
    programBound := Nat.le_trans cursor.programBound bound, adapter := ?_ }
  simpa only [raiseAtom_twice] using cursor.adapter.raise henv hscoped formed bound

noncomputable def WorldRigidFamilyConsumption.adaptRequest
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Atom n} {next : Atom k}
    (cursor : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments requested)
    (bound : k ≤ n)
    (adapter : GeneralNormalAtomAdapter env U registry target requested (raiseAtom n bound next)) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments next := by
  refine { cursor with bound := Nat.le_trans bound cursor.bound, adapter := ?_ }
  simpa only [raiseAtom_twice] using cursor.adapter.comp (adapter.raise henv hscoped formed cursor.bound)

section Output
variable {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
  {root : EndpointRef sourceEnv U source rootExpression rootType}

noncomputable def WorldRigidFamilyConsumption.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments a)
    (action : AtomAction env U registry target a b) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments b :=
  { result with adapter := result.adapter.comp ((action.raise result.bound).toGeneralAdapter henv hscoped formed) }

noncomputable def WorldRigidFamilyConsumption.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (a : Atom n)) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (n := n+1) (.pad a) := by
  let raised := result.raiseTo henv hscoped formed (result.rank+1) (Nat.le_succ _)
  have bound : n+1 ≤ raised.rank := Nat.succ_le_succ result.bound
  exact { raised with bound := bound, adapter := by simpa only [raiseAtom_pad] using raised.adapter }

noncomputable def WorldRigidFamilyConsumption.unpad
    (result : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (n := n+1) (.pad (a : Atom n))) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments a :=
  { result with bound := Nat.le_trans (Nat.le_succ _) result.bound
                adapter := by simpa only [raiseAtom_pad] using result.adapter }

noncomputable def WorldRigidFamilyConsumption.code
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (a : Atom n))
    (action : SortableCodeAction env U registry target relevant (.singleton a) next (.singleton (b : Atom m)))
    (sorted : (Profile.singleton a).HasType (.sort relevant)) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments b := by
  let N := max result.rank m
  let raised := result.raiseTo henv hscoped formed N (Nat.le_max_left _ _)
  have outputBound : m ≤ raised.rank := Nat.le_max_right _ _
  have program : GeneralNormalProfileAdapter env U registry target
      (.singleton (raiseAtom raised.rank raised.bound a))
      (.singleton (raiseAtom raised.rank outputBound b)) := by
    simpa only [raiseProfile_singleton] using
      (action.atGrade raised.bound outputBound).toGeneralAdapter (Profile.HasType.raise_sort raised.bound sorted)
  have selected : Nonempty (GeneralNormalAtomAdapter env U registry target
      (raiseAtom raised.rank raised.bound a) (raiseAtom raised.rank outputBound b)) := by
    obtain ⟨origin, member, ⟨entry⟩⟩ := program.origin (List.mem_singleton_self _)
    have same := List.mem_singleton.mp member
    subst origin
    exact ⟨entry⟩
  exact { raised with bound := outputBound, adapter := raised.adapter.comp (Classical.choice selected) }

/-- Output code actions and grading are replayed on the consumed plan;
none changes the retained source argument owners. -/
noncomputable def WorldRigidFamilyConsumption.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments a)
    (path : GeneralOutputPath env U registry target a b) :
    WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments b := by
  induction path with
  | refl => exact result
  | action path action ih => exact ih.action henv hscoped formed action
  | code path action sorted ih => exact ih.code henv hscoped formed action sorted
  | pad path ih => exact ih.pad henv hscoped formed
  | unpad path ih => exact ih.unpad


end Output

private noncomputable def emptyRequest
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {argument : RigidFamilyArgument}
    (location : Located root node)
    (anchor : env.IsDefEq U target argument.anchor (expression.subst σ) argument.domain) :
    WorldRichFamilySourceRequest controls frontier root registry target locals σ available
      expression argument.request where
  argument := { assigned := assigned, node := node, location := location, query := .empty }
  controlled := {
    annotation := .legacy _ (.legacy _ .empty)
    within := by
      intro control active
      simp only [RichGradedResult.empty, StoredOriginalQuery.headDepth, RichObs.headDepth,
        SortableObs.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := fun _ member => nomatch member }
  anchor := anchor

private theorem forall₂_snoc {R : α → β → Prop}
    (sources : List.Forall₂ R xs ys) (last : R x y) :
    List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction sources with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

private theorem rigidApp
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {n N r : Nat} {key : Key n} {output : Atom n}
    (plan : RigidFamilySpine r) (ready : plan.Ready env U registry target)
    (past : List RigidFamilyArgument)
    (sources : List.Forall₂ (fun expression argument => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available
        expression argument.request)) arguments past)
    (programBound : r ≤ N+1) (bound : n+1 ≤ N+1)
    (adapter : GeneralNormalAtomAdapter env U registry target
      (raiseAtom (N+1) programBound (plan.atom name levels past))
      (raiseAtom (N+1) bound (.fn key output)))
    {argument : EndpointState sourceEnv U source a A}
    (location : Located root argument)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Nonempty (WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels (arguments ++ [a]) output) := by
  have nextBound : n ≤ N := Nat.le_of_succ_le_succ bound
  have expose := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) nextBound key output).toGeneralAdapter henv hscoped formed
  cases plan with
  | terminal flag =>
    exact (GeneralNormalAtomAdapter.family_not_fn programBound (adapter.comp expose)).elim
  | @binder r oldKey child =>
    have oldBound : r ≤ N := Nat.le_of_succ_le_succ programBound
    have oldExpose := ((functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := target) oldBound oldKey (child.atom name levels
        (past ++ [(⟨oldKey.domain, oldKey.anchor⟩ : RigidFamilyArgument)]))).inverse henv).toGeneralAdapter
      henv hscoped formed
    have normalized := oldExpose.comp (adapter.comp expose)
    obtain ⟨actualKey, actualOutput, equal, ⟨keys⟩, ⟨outputs⟩⟩ := normalized.fn_inv
    obtain ⟨rfl, rfl⟩ := AtomData.fn.inj equal
    have incoming := AdapterNormal.normalizeAdmission henv hscoped formed (Admitted.raise henv nextBound admitted)
    have seed := AdapterNormal.normalizeAdmission henv hscoped formed (Admitted.raise henv oldBound ready.1)
    have pulled := unnormalize_admission henv hscoped formed (keys.pull henv hscoped formed seed incoming)
    obtain ⟨anchor, _⟩ := pulled
    let request := emptyRequest (controls := controls) (frontier := frontier)
      (registry := registry) (locals := locals) (available := available)
      (argument := (⟨oldKey.domain, oldKey.anchor⟩ : RigidFamilyArgument)) location anchor
    exact ⟨{
      rank := N, bound := nextBound, programRank := r, programBound := oldBound
      past := past ++ [(⟨oldKey.domain, oldKey.anchor⟩ : RigidFamilyArgument)]
      plan := child, ready := ready.2, adapter := outputs
      sources := forall₂_snoc sources ⟨request⟩ }⟩
  | pad child =>
    apply rigidApp henv hscoped formed child ready past sources
      (Nat.le_trans (Nat.le_succ _) programBound) bound _ location admitted
    simpa only [RigidFamilySpine.atom, raiseAtom_pad] using adapter
termination_by r
decreasing_by all_goals omega

theorem WorldRigidFamilyConsumption.app
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {key : Key n} {output : Atom n}
    (cursor : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (n := n+1) (.fn key output))
    {argument : EndpointState sourceEnv U source a A}
    (location : Located root argument)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Nonempty (WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels (arguments ++ [a]) output) := by
  rcases cursor with ⟨rank, bound, programRank, programBound, past, plan, ready, adapter, sources⟩
  cases rank with
  | zero => omega
  | succ rank => exact rigidApp henv hscoped formed plan ready past sources programBound bound adapter location admitted

private theorem rigidRequests
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {n N r : Nat} {demand : FamilyData (Profile n)}
    (plan : RigidFamilySpine r) (past : List RigidFamilyArgument)
    (sources : List.Forall₂ (fun expression argument => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available
        expression argument.request)) arguments past)
    (programBound : r ≤ N) (bound : n+1 ≤ N)
    (adapter : GeneralNormalAtomAdapter env U registry target
      (raiseAtom N programBound (plan.atom name levels past))
      (raiseAtom N bound (.family demand))) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments demand := by
  cases plan with
  | terminal flag =>
    have property : WorldFamilyRequestProperty controls frontier root registry target locals σ available
        name levels arguments ⟨name, levels, flag, past.map RigidFamilyArgument.request⟩ :=
      ⟨rfl, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl), List.forall₂_map_right_iff.mpr sources⟩
    have high := (FamilyAtomProperty.raise_iff
      (property := WorldFamilyRequestProperty controls frontier root registry target locals σ available
        name levels arguments) programBound
      (.family ⟨name, levels, flag, past.map RigidFamilyArgument.request⟩)).mpr property
    exact (FamilyAtomProperty.raise_iff bound (.family demand)).mp
      (adapter.familyProperty (fun request => request.pad henv hscoped formed) high)
  | binder key child =>
    cases N with
    | zero => omega
    | succ N =>
      have oldBound := Nat.le_of_succ_le_succ programBound
      have expose := ((functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) oldBound key (child.atom name levels
          (past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)]))).inverse henv).toGeneralAdapter
        henv hscoped formed
      exact (GeneralNormalAtomAdapter.fn_not_family bound (expose.comp adapter)).elim
  | pad child =>
    apply rigidRequests henv hscoped formed child past sources
      (Nat.le_trans (Nat.le_succ _) programBound) bound
    simpa only [RigidFamilySpine.atom, raiseAtom_pad] using adapter
termination_by r
decreasing_by all_goals omega

theorem WorldRigidFamilyConsumption.familyRequests
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cursor : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
      name levels arguments (n := n+1) (.family demand)) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments demand :=
  rigidRequests henv hscoped formed cursor.plan cursor.past cursor.sources
    cursor.programBound cursor.bound cursor.adapter

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
