import Lean4Lean.Theory.Typing.AnchoredSourcePruning
import Lean4Lean.Theory.Typing.AnchoredSourceBinder
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Capture-avoiding source substitution from finite actual observations.
Every replacement is stored at an original footprint occurrence. Under a
binder only external replacements are lifted, preserving its exact input. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Valuation.push_atomized_closed {available : Valuation}
    (closed : available.AtomClosed) (head : List Need) :
    (Valuation.push (head ++ head.flatMap Need.singletons) available).AtomClosed := by
  intro index need member selected hs
  cases index with
  | zero => exact (Valuation.atomize_closed (fun _ => head)) 0 need member selected hs
  | succ index => exact closed index need member selected hs

private theorem raiseProfile_map {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    raiseProfile N bound profile = profile.map (raiseAtom N bound) := by
  induction profile with
  | nil => exact raiseProfile_empty bound
  | cons atom rest ih =>
    change raiseProfile N bound ((Profile.singleton atom).union rest) = _
    rw [raiseProfile_union, raiseProfile_singleton, ih]
    rfl

/-- Closing the original local leaves under singleton selection retains both
their original grades and literal coverage by the original binder input. -/
theorem BinderPack.atomized_localNeeds {input : Profile n}
    (pack : BinderPack n input required outside) :
    ∀ need ∈ required.localNeeds ++ required.localNeeds.flatMap Need.singletons,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms := by
  intro need member
  rcases List.mem_append.mp member with original | selected
  · exact pack.localNeeds need original
  · obtain ⟨old, hold, selected⟩ := List.mem_flatMap.mp selected
    obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp selected
    obtain ⟨bound, covered⟩ := pack.localNeeds old hold
    refine ⟨bound, ?_⟩
    intro high hh
    apply covered high
    simp only [Need.atGrade, dif_pos bound] at hh ⊢
    rw [raiseProfile_singleton] at hh
    cases List.mem_singleton.mp hh
    rw [raiseProfile_map]
    exact List.mem_map.mpr ⟨atom, ha, rfl⟩

theorem BinderPack.available_atomized_localNeeds {input : Profile n} {available : Valuation}
    (pack : BinderPack n input required outside) (resources : outside.Available available) :
    required.Available (Valuation.push
      (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available) := by
  have old := pack.available resources
  intro index need member
  cases index with
  | zero => exact List.mem_append_left _ (old 0 need member)
  | succ index => exact old (index + 1) need member

inductive SourceSupply (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization replacement : Subst) :
    Footprint → Footprint → Type where
  | nil : SourceSupply env U registry target locals realization replacement [] []
  | cons {index : Nat} {need : Need}
      (observation : Obs env U registry target locals realization (replacement index)
        need.profile first)
      (tail : SourceSupply env U registry target locals realization replacement rest remaining) :
      SourceSupply env U registry target locals realization replacement
        ((index, need) :: rest) (first ++ remaining)

theorem SourceSupply.split
    {supply : SourceSupply env U registry target locals realization replacement (left ++ right) result} :
    ∃ first second,
      Nonempty (SourceSupply env U registry target locals realization replacement left first) ∧
      Nonempty (SourceSupply env U registry target locals realization replacement right second) ∧
      result = first ++ second := by
  induction left generalizing result with
  | nil => exact ⟨[], result, ⟨.nil⟩, ⟨supply⟩, rfl⟩
  | cons entry rest ih =>
    cases supply with
    | cons observation tail =>
      obtain ⟨first, second, ⟨sfirst⟩, ⟨ssecond⟩, he⟩ := ih (supply := tail)
      subst_vars
      exact ⟨_, _, ⟨.cons observation sfirst⟩, ⟨ssecond⟩, (List.append_assoc ..).symm⟩

private theorem BinderPack.external_prefix
    (pack : BinderPack n input required outside) (before : Footprint) :
    BinderPack n input (before.sourceLift (.skip .refl) ++ required) (before ++ outside) := by
  induction before with
  | nil => exact pack
  | cons entry rest ih =>
    rcases entry with ⟨index, need⟩
    exact .external index need ih

/-- A lifted replacement has no use of the new local variable. Consequently
the old binder pack survives with exactly the same finite input profile. -/
theorem SourceSupply.underBinder
    (pack : BinderPack n input required outside)
    (supply : SourceSupply env U registry target locals realization replacement outside result)
    (anchor : VExpr) :
    ∃ bodyResult,
      Nonempty (SourceSupply env U registry target (Locals.push locals)
        (realization.cons anchor) replacement.lift required bodyResult) ∧
      BinderPack n input bodyResult result := by
  induction pack generalizing result with
  | nil =>
    cases supply
    exact ⟨[], ⟨.nil⟩, .nil⟩
  | «local» need bound rest ih =>
    obtain ⟨bodyResult, ⟨bodySupply⟩, normal⟩ := ih supply
    exact ⟨(0, need) :: bodyResult,
      ⟨.cons (replacement := replacement.lift) (index := 0) (.var (Locals.push locals) (realization.cons anchor) 0 need.profile) bodySupply⟩,
      .local need bound normal⟩
  | external index need rest ih =>
    cases supply with
    | cons observation tail =>
      obtain ⟨bodyResult, ⟨bodySupply⟩, normal⟩ := ih tail
      have lifted := observation.renameSource (.skip .refl) (realization.cons anchor)
        rfl (Locals.push locals)
      rw [← lift_eq_lift'] at lifted
      exact ⟨_, ⟨.cons lifted bodySupply⟩, normal.external_prefix _⟩

private theorem replacement_lift (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext index
  cases index <;> simp only [Subst.comp, Subst.lift, Subst.cons, subst_bvar, lift_subst_cons]

theorem LambdaGuard.sourceSubstitute
    (guard : LambdaGuard env U registry target sourceRealization annotation key support)
    (replacement realization : Subst)
    (realized : replacement.comp realization = sourceRealization) :
    LambdaGuard env U registry target realization (annotation.subst replacement) key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [subst_subst, realized] using guard.path
  · simpa only [subst_subst, realized] using guard.domains

theorem PiGuard.sourceSubstitute
    (guard : PiGuard env U target sourceRealization A B prototypeDomain prototypeBody)
    (replacement realization : Subst)
    (realized : replacement.comp realization = sourceRealization) :
    PiGuard env U target realization (A.subst replacement) (B.subst replacement.lift)
      prototypeDomain prototypeBody := by
  constructor
  · simpa only [subst_subst, realized] using guard.domainPath
  · simpa only [subst_subst, ← Subst.comp_lift, realized] using guard.bodyPath

mutual
theorem Obs.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : Obs env U registry target locals sourceRealization expression demand required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {result : Footprint}
    (supply : SourceSupply env U registry target newLocals realization replacement required result) :
    Nonempty (Obs env U registry target newLocals realization (expression.subst replacement)
      demand result) := by
  match observation with
  | .var _ _ _ _ =>
    cases supply with
    | cons value tail =>
      cases tail
      simpa only [List.append_nil, subst_bvar] using Nonempty.intro value
  | .empty => cases supply; exact ⟨.empty⟩
  | .sort relevant => cases supply; exact ⟨.sort relevant⟩
  | .app fn arg admitted =>
    obtain ⟨first, second, ⟨fnSupply⟩, ⟨argSupply⟩, rfl⟩ := SourceSupply.split (supply := supply)
    obtain ⟨hf⟩ := fn.substitute replacement realization realized newLocals fnSupply
    obtain ⟨ha⟩ := arg.substitute replacement realization realized newLocals argSupply
    exact ⟨.app hf ha (by simpa only [subst_subst, realized] using admitted)⟩
  | .lam domain guard body normal =>
    obtain ⟨first, second, ⟨domainSupply⟩, ⟨externalSupply⟩, rfl⟩ :=
      SourceSupply.split (supply := supply)
    obtain ⟨hd⟩ := domain.substitute replacement realization realized newLocals domainSupply
    obtain ⟨bodyResult, ⟨bodySupply⟩, bodyNormal⟩ := externalSupply.underBinder normal _
    obtain ⟨hb⟩ := body.substitute replacement.lift (realization.cons _)
      (by rw [replacement_lift, realized]) (Locals.push newLocals) bodySupply
    exact ⟨.lam hd (guard.sourceSubstitute replacement realization realized) hb bodyNormal⟩
  | .pi domain guard bodies =>
    obtain ⟨first, second, ⟨domainSupply⟩, ⟨bodySupply⟩, rfl⟩ :=
      SourceSupply.split (supply := supply)
    obtain ⟨hd⟩ := domain.substitute replacement realization realized newLocals domainSupply
    obtain ⟨hb⟩ := bodies.substitute replacement realization realized newLocals bodySupply
    exact ⟨.pi hd (guard.sourceSubstitute replacement realization realized) hb⟩
  | .union left right =>
    obtain ⟨first, second, ⟨leftSupply⟩, ⟨rightSupply⟩, rfl⟩ :=
      SourceSupply.split (supply := supply)
    obtain ⟨hl⟩ := left.substitute replacement realization realized newLocals leftSupply
    obtain ⟨hr⟩ := right.substitute replacement realization realized newLocals rightSupply
    exact ⟨.union hl hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.view hs view⟩
  | .pad source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.pad hs⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.unpad hs⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.rowShift hs⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (cert : CodeCert env U registry target locals sourceRealization expression demand required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {result : Footprint}
    (supply : SourceSupply env U registry target newLocals realization replacement required result) :
    Nonempty (CodeCert env U registry target newLocals realization (expression.subst replacement)
      demand result) := by
  match cert with
  | .seed observation formed =>
    obtain ⟨hs⟩ := observation.substitute replacement realization realized newLocals supply
    exact ⟨.seed hs formed⟩
  | .union left right =>
    obtain ⟨first, second, ⟨leftSupply⟩, ⟨rightSupply⟩, rfl⟩ :=
      SourceSupply.split (supply := supply)
    obtain ⟨hl⟩ := left.substitute replacement realization realized newLocals leftSupply
    obtain ⟨hr⟩ := right.substitute replacement realization realized newLocals rightSupply
    exact ⟨.union hl hr⟩
  | .pad source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.pad hs⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.unpad hs⟩
  | .down source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.down hs⟩
  | .map view source =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.map view hs⟩
  | .select source member =>
    obtain ⟨hs⟩ := source.substitute replacement realization realized newLocals supply
    exact ⟨.select hs member⟩
termination_by sizeOf cert
decreasing_by all_goals simp_wf; omega

theorem PiRows.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : PiRows env U registry target locals sourceRealization A B ambient rows required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {result : Footprint}
    (supply : SourceSupply env U registry target newLocals realization replacement required result) :
    Nonempty (PiRows env U registry target newLocals realization (A.subst replacement)
      (B.subst replacement.lift) ambient rows result) := by
  match bodies with
  | .nil => cases supply; exact ⟨.nil⟩
  | .cons guard body normal covered tail =>
    obtain ⟨first, second, ⟨externalSupply⟩, ⟨tailSupply⟩, rfl⟩ :=
      SourceSupply.split (supply := supply)
    obtain ⟨bodyResult, ⟨bodySupply⟩, bodyNormal⟩ := externalSupply.underBinder normal _
    obtain ⟨hb⟩ := body.substitute replacement.lift (realization.cons _)
      (by rw [replacement_lift, realized]) (Locals.push newLocals) bodySupply
    obtain ⟨ht⟩ := tail.substitute replacement realization realized newLocals tailSupply
    exact ⟨.cons (guard.sourceSubstitute replacement realization realized)
      hb bodyNormal covered ht⟩
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega
end

/-- Literal value selection uses actual singleton observations and finite
union. It never changes a surviving function row's key or input demand. -/
theorem Obs.subprofile
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {expression : VExpr}
    {input selected : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals realization expression input footprint)
    (included : ∀ atom ∈ selected.atoms, atom ∈ input.atoms) :
    ∃ required, Nonempty (Obs env U registry target locals realization expression selected required) ∧
      Footprint.Atomizes required footprint := by
  induction selected with
  | nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | cons head tail ih =>
    obtain ⟨headSelection⟩ := observation.atom (included head List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailObs⟩, tailSelection⟩ :=
      ih (fun atom h => included atom (List.mem_cons_of_mem _ h))
    exact ⟨headSelection.footprint ++ tailFootprint,
      ⟨.union headSelection.observation tailObs⟩, headSelection.atomizes.append tailSelection⟩

theorem Obs.localDemand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {expression : VExpr}
    {input : Profile N} {footprint : Footprint}
    (observation : Obs env U registry target locals realization expression input footprint)
    (need : Need) (bound : need.rank ≤ N)
    (included : ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    ∃ required,
      Nonempty (Obs env U registry target locals realization expression need.profile required) ∧
      Footprint.Atomizes required footprint := by
  simp only [Need.atGrade, dif_pos bound] at included
  obtain ⟨required, ⟨selected⟩, footprint⟩ := observation.subprofile included
  exact ⟨required, ⟨selected.lower bound⟩, footprint⟩

/-- Build every beta replacement from the one original argument observation.
The finite pack supplies each requested grade and literal input inclusion. -/
theorem SourceSupply.instantiate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {argument : VExpr}
    {input packed : Profile N} {argumentFootprint required outside : Footprint}
    (argumentObservation : Obs env U registry target locals realization argument input argumentFootprint)
    (normal : BinderPack N packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms) :
    ∃ result,
      Nonempty (SourceSupply env U registry target locals realization (.one argument) required result) ∧
      Footprint.Atomizes result (argumentFootprint ++ outside) := by
  induction normal with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ h => nomatch h⟩
  | «local» need bound rest ih =>
    obtain ⟨first, ⟨firstObs⟩, firstSelected⟩ := argumentObservation.localDemand need bound
      (fun atom h => included atom (List.mem_append_left _ h))
    obtain ⟨remaining, ⟨tailSupply⟩, tailSelected⟩ :=
      ih (fun atom h => included atom (List.mem_append_right _ h))
    exact ⟨first ++ remaining,
      ⟨.cons (replacement := .one argument) (index := 0) firstObs tailSupply⟩,
      (firstSelected.append_left _).append tailSelected⟩
  | external index need rest ih =>
    obtain ⟨remaining, ⟨tailSupply⟩, tailSelected⟩ := ih included
    refine ⟨(index, need) :: remaining,
      ⟨.cons (replacement := .one argument) (index := index + 1)
        (.var locals realization index need.profile) tailSupply⟩, ?_⟩
    intro i request member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨need, List.mem_append_right _ List.mem_cons_self, .inl rfl⟩
    · obtain ⟨old, hold, chosen⟩ := tailSelected i request member
      refine ⟨old, ?_, chosen⟩
      rcases List.mem_append.mp hold with harg | hout
      · exact List.mem_append_left _ harg
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hout)

private theorem one_realized (argument : VExpr) (realization : Subst) :
    (Subst.one argument).comp realization = realization.cons (argument.subst realization) := by
  funext index
  cases index <;> rfl

/-- Concrete source beta contraction after the original body child has
transported its anchor to the actual argument. No semantic replacement
function is assumed: all replacements come from `argumentObservation`. -/
theorem Obs.instantiate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {argument body : VExpr}
    {input packed : Profile N} {demand : Profile n}
    {argumentFootprint bodyFootprint outside : Footprint}
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (realization.cons (argument.subst realization)) body demand bodyFootprint)
    (argumentObservation : Obs env U registry target locals realization argument input argumentFootprint)
    (normal : BinderPack N packed bodyFootprint outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms) :
    ∃ result, Nonempty (Obs env U registry target locals realization (body.inst argument) demand result) ∧
      Footprint.Atomizes result (argumentFootprint ++ outside) := by
  obtain ⟨result, ⟨supply⟩, selected⟩ := SourceSupply.instantiate argumentObservation normal included
  obtain ⟨observation⟩ := bodyObservation.substitute (.one argument) realization
    (one_realized argument realization) locals supply
  exact ⟨result, ⟨by simpa only [inst_eq] using observation⟩, selected⟩

theorem CodeCert.instantiate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {argument body : VExpr}
    {input packed : Profile N} {demand : Profile n}
    {argumentFootprint bodyFootprint outside : Footprint}
    (bodyCertificate : CodeCert env U registry target (Locals.push locals)
      (realization.cons (argument.subst realization)) body demand bodyFootprint)
    (argumentObservation : Obs env U registry target locals realization argument input argumentFootprint)
    (normal : BinderPack N packed bodyFootprint outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms) :
    ∃ result,
      Nonempty (CodeCert env U registry target locals realization (body.inst argument) demand result) ∧
      Footprint.Atomizes result (argumentFootprint ++ outside) := by
  obtain ⟨result, ⟨supply⟩, selected⟩ := SourceSupply.instantiate argumentObservation normal included
  obtain ⟨certificate⟩ := bodyCertificate.substitute (.one argument) realization
    (one_realized argument realization) locals supply
  exact ⟨result, ⟨by simpa only [inst_eq] using certificate⟩, selected⟩

end Lean4Lean.AnchoredSource
