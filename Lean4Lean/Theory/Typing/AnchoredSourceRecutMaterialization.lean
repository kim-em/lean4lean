import Lean4Lean.Theory.Typing.AnchoredSourceRecut
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental

/-! Exact materialization of a finite re-cut ledger.  This pass performs no
profile adaptation: all adaptation has already happened in the symbolic
observer.  Consequently the returned demand and each original BinderPack
input are preserved literally, including beneath lambdas and Pi rows. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace Recut

inductive ExactSupply (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (realization replacement : Subst) :
    Footprint → Footprint → Type where
  | nil : ExactSupply env U registry Γ locals realization replacement [] []
  | cons (observation : Obs env U registry Γ locals realization (replacement index)
        need.profile firstFootprint)
      (tail : ExactSupply env U registry Γ locals realization replacement rest tailFootprint) :
      ExactSupply env U registry Γ locals realization replacement
        ((index, need) :: rest) (firstFootprint ++ tailFootprint)

theorem ExactSupply.split
    (supply : ExactSupply env U registry Γ locals realization replacement (left ++ right) produced) :
    ∃ leftProduced rightProduced, produced = leftProduced ++ rightProduced ∧
      Nonempty (ExactSupply env U registry Γ locals realization replacement left leftProduced) ∧
      Nonempty (ExactSupply env U registry Γ locals realization replacement right rightProduced) := by
  induction left generalizing produced with
  | nil => exact ⟨[], produced, rfl, ⟨.nil⟩, ⟨supply⟩⟩
  | cons entry rest ih =>
    cases supply with
    | cons observation tail =>
      obtain ⟨leftProduced, rightProduced, rfl, ⟨left⟩, ⟨right⟩⟩ := ih tail
      exact ⟨_, _, (List.append_assoc ..).symm, ⟨.cons observation left⟩, ⟨right⟩⟩

private theorem pack_prepend (footprint : Footprint)
    (pack : BinderPack n input required outside) :
    BinderPack n input (Footprint.sourceLift (.skip .refl) footprint ++ required)
      (footprint ++ outside) := by
  induction footprint with
  | nil => exact pack
  | cons entry rest ih =>
    exact .external entry.1 entry.2 ih

theorem ExactSupply.underBinder
    (normal : BinderPack n input required outside)
    (supply : ExactSupply env U registry Γ locals realization replacement outside produced)
    (anchor : VExpr) :
    ∃ bodyProduced,
      Nonempty (ExactSupply env U registry Γ (Locals.push locals)
        (realization.cons anchor) replacement.lift required bodyProduced) ∧
      BinderPack n input bodyProduced produced := by
  induction normal generalizing produced with
  | nil =>
    cases supply
    exact ⟨[], ⟨.nil⟩, .nil⟩
  | «local» need bound rest ih =>
    obtain ⟨bodyProduced, ⟨body⟩, normal⟩ := ih supply
    exact ⟨_, ⟨.cons (.var _ _ 0 need.profile) body⟩, .local need bound normal⟩
  | external index need rest ih =>
    cases supply with
    | cons observation tail =>
      obtain ⟨bodyProduced, ⟨body⟩, normal⟩ := ih tail
      have lifted := observation.renameSource (.skip .refl) (realization.cons anchor)
        (by rfl) (Locals.push locals)
      simp only [← lift_eq_lift'] at lifted
      have lifted' := lifted
      change Obs env U registry Γ (Locals.push locals) (realization.cons anchor)
        (replacement.lift (index + 1)) need.profile _ at lifted'
      exact ⟨_, ⟨.cons lifted' body⟩, pack_prepend _ normal⟩

private structure SplitResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (Γ : List VExpr)
    (locals : List Nat) (realization replacement : Subst)
    (left right produced : Footprint) where
  leftProduced : Footprint
  rightProduced : Footprint
  equation : produced = leftProduced ++ rightProduced
  leftSupply : ExactSupply env U registry Γ locals realization replacement left leftProduced
  rightSupply : ExactSupply env U registry Γ locals realization replacement right rightProduced

private noncomputable def ExactSupply.splitResult
    (supply : ExactSupply env U registry Γ locals realization replacement (left ++ right) produced) :
    SplitResult env U registry Γ locals realization replacement left right produced :=
  let h := supply.split
  let h' := Classical.choose_spec h
  let h'' := Classical.choose_spec h'
  ⟨Classical.choose h, Classical.choose h', h''.1,
    Classical.choice h''.2.1, Classical.choice h''.2.2⟩

private structure UnderBinderResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (Γ : List VExpr)
    (locals : List Nat) (realization replacement : Subst) (anchor : VExpr)
    (input : Profile n) (required produced : Footprint) where
  bodyProduced : Footprint
  supply : ExactSupply env U registry Γ (Locals.push locals) (realization.cons anchor)
    replacement.lift required bodyProduced
  pack : BinderPack n input bodyProduced produced

private noncomputable def ExactSupply.underBinderResult
    (normal : BinderPack n input required outside)
    (supply : ExactSupply env U registry Γ locals realization replacement outside produced)
    (anchor : VExpr) :
    UnderBinderResult env U registry Γ locals realization replacement anchor input required produced :=
  let h := supply.underBinder normal anchor
  let h' := Classical.choose_spec h
  ⟨Classical.choose h, Classical.choice h'.1, h'.2⟩

private theorem realization_underBinder (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext index
  cases index <;> simp only [Subst.comp, Subst.lift, Subst.cons, subst_bvar, lift_subst_cons]

mutual
noncomputable def materializeObs
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : Obs env U registry Γ locals sourceRealization expression demand required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {produced : Footprint}
    (supply : ExactSupply env U registry Γ newLocals realization replacement required produced) :
    Obs env U registry Γ newLocals realization (expression.subst replacement) demand produced := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    cases supply
    exact .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases supply
    exact .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases supply
    exact .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases supply
    exact .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .var _ _ _ _ =>
    cases supply with
    | cons observation tail =>
      cases tail
      simpa only [List.append_nil, subst_bvar] using observation
  | .empty => cases supply; exact .empty
  | .sort relevant => cases supply; exact .sort relevant
  | .app fn arg arguments admitted =>
    obtain ⟨_, _, rfl, fnSupply, argSupply⟩ := supply.splitResult
    exact .app (materializeObs fn replacement realization realized newLocals fnSupply)
      (materializeObs arg replacement realization realized newLocals argSupply) arguments
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨_, _, rfl, domainSupply, externalSupply⟩ := supply.splitResult
    obtain ⟨_, bodySupply, bodyPack⟩ := externalSupply.underBinderResult normal _
    exact .lam (materializeCode domain replacement realization realized newLocals domainSupply)
      (guard.sourceSubstitute replacement realization realized)
      (materializeObs body replacement.lift (realization.cons _)
        (by rw [realization_underBinder, realized]) (Locals.push newLocals) bodySupply)
      bodyPack covered
  | .pi domain guard bodies =>
    obtain ⟨_, _, rfl, domainSupply, rowSupply⟩ := supply.splitResult
    exact .pi (materializeCode domain replacement realization realized newLocals domainSupply)
      (guard.sourceSubstitute replacement realization realized)
      (materializeRows bodies replacement realization realized newLocals rowSupply)
  | .union left right =>
    obtain ⟨_, _, rfl, leftSupply, rightSupply⟩ := supply.splitResult
    exact .union (materializeObs left replacement realization realized newLocals leftSupply)
      (materializeObs right replacement realization realized newLocals rightSupply)
  | .view source view => exact .view (materializeObs source replacement realization realized newLocals supply) view
  | .pad source => exact .pad (materializeObs source replacement realization realized newLocals supply)
  | .unpad source => exact .unpad (materializeObs source replacement realization realized newLocals supply)
  | .rowShift source => exact .rowShift (materializeObs source replacement realization realized newLocals supply)
termination_by sizeOf observation

noncomputable def materializeCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry Γ locals sourceRealization expression demand required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {produced : Footprint}
    (supply : ExactSupply env U registry Γ newLocals realization replacement required produced) :
    CodeCert env U registry Γ newLocals realization (expression.subst replacement) demand produced := by
  match certificate with
  | .seed observation formed =>
    exact .seed (materializeObs observation replacement realization realized newLocals supply) formed
  | .union left right =>
    obtain ⟨_, _, rfl, leftSupply, rightSupply⟩ := supply.splitResult
    exact .union (materializeCode left replacement realization realized newLocals leftSupply)
      (materializeCode right replacement realization realized newLocals rightSupply)
  | .pad source => exact .pad (materializeCode source replacement realization realized newLocals supply)
  | .familyPad source => exact .familyPad (materializeCode source replacement realization realized newLocals supply)
  | .unpad source => exact .unpad (materializeCode source replacement realization realized newLocals supply)
  | .down source => exact .down (materializeCode source replacement realization realized newLocals supply)
  | .map view source => exact .map view (materializeCode source replacement realization realized newLocals supply)
  | .select source member => exact .select (materializeCode source replacement realization realized newLocals supply) member
  | .focusMinimal source minimal bound => exact .focusMinimal (materializeCode source replacement realization realized newLocals supply) minimal bound
termination_by sizeOf certificate

noncomputable def materializeRows
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : PiRows env U registry Γ locals sourceRealization A B ambient rows required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) {produced : Footprint}
    (supply : ExactSupply env U registry Γ newLocals realization replacement required produced) :
    PiRows env U registry Γ newLocals realization (A.subst replacement)
      (B.subst replacement.lift) ambient rows produced := by
  match bodies with
  | .nil => cases supply; exact .nil
  | .cons guard body normal covered tail =>
    obtain ⟨_, _, rfl, externalSupply, tailSupply⟩ := supply.splitResult
    obtain ⟨_, bodySupply, bodyPack⟩ := externalSupply.underBinderResult normal _
    exact .cons (guard.sourceSubstitute replacement realization realized)
      (materializeCode body replacement.lift (realization.cons _)
        (by rw [realization_underBinder, realized]) (Locals.push newLocals) bodySupply)
      bodyPack covered (materializeRows tail replacement realization realized newLocals tailSupply)
termination_by sizeOf bodies
end

/-- Concrete source payload for an original returned bare-head observer.
Its ordinary source footprint is empty; its native internal witnesses remain
in the payload, never become external source resource slots. -/
abbrev ClosedPayload (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (realization heads : Subst)
    (index : Nat) (need : Need) :=
  Obs env U registry Γ locals realization (heads index) need.profile []

private theorem atomizes_empty {footprint : Footprint}
    (selection : footprint.Atomizes []) : footprint = [] := by
  cases footprint with
  | nil => rfl
  | cons first rest =>
    obtain ⟨_, impossible, _⟩ := selection first.1 first.2 (by simp)
    cases impossible

theorem Selects.materialize
    {entry : Entry env U registry Γ sourceRealization
      (ClosedPayload env U registry Γ locals realization heads) index}
    (selection : Selects entry need) :
    Nonempty (Obs env U registry Γ locals realization (heads index) need.profile []) := by
  cases selection with
  | whole => exact ⟨entry.payload⟩
  | atom atom member =>
    obtain ⟨selected⟩ := entry.payload.atom member
    have empty := atomizes_empty selected.atomizes
    exact ⟨empty ▸ selected.observation⟩

theorem ReturnLedger.materialize
    {ledger : Ledger env U registry Γ sourceRealization
      (ClosedPayload env U registry Γ locals realization heads)}
    (origins : ReturnLedger ledger footprint) :
    Nonempty (ExactSupply env U registry Γ locals realization heads footprint []) := by
  induction origins with
  | nil => exact ⟨.nil⟩
  | cons origin tail ih =>
    obtain ⟨first⟩ := origin.selection.materialize
    obtain ⟨rest⟩ := ih
    exact ⟨.cons first rest⟩

/-- The actual observer and the symbolic returned recut have exactly the same
raw demand. In particular no second graded substitution changes the request
which the earlier-stage theorem must certify. -/
theorem Result.materialize
    {ledger : Ledger env U registry Γ sourceRealization
      (ClosedPayload env U registry Γ locals realization heads)}
    (result : Result ledger cutLocals expression requested)
    (realized : heads.comp realization = sourceRealization) :
    Nonempty (Obs env U registry Γ locals realization (expression.subst heads)
      result.value.raw []) := by
  obtain ⟨supply⟩ := result.origins.materialize
  exact ⟨materializeObs result.value.observation heads realization realized locals supply⟩

/-- Guard reconstruction materializes at its original exact code demand. -/
theorem CodeResult.materialize
    {ledger : Ledger env U registry Γ sourceRealization
      (ClosedPayload env U registry Γ locals realization heads)}
    (result : CodeResult ledger cutLocals expression requested)
    (realized : heads.comp realization = sourceRealization) :
    Nonempty (CodeCert env U registry Γ locals realization (expression.subst heads)
      requested []) := by
  obtain ⟨supply⟩ := result.origins.materialize
  exact ⟨materializeCode result.certificate heads realization realized locals supply⟩

/-- An original descendant's actual graded transfer result directly supplies
one finite cut answer. Its raw observer, type support, code, and raw relation
are retained; this does not invoke the fundamental theorem on that observer. -/
def Answer.ofTransferResult
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {leftRealization rightRealization headRealization heads : Subst}
    {available : Valuation} {left sourceType : VExpr} {index : Nat} {requested : Need}
    (result : GradedTransferResult env U registry Γ locals leftRealization rightRealization
      available left (heads index) sourceType requested.profile)
    (closedHead : result.resultFootprint = [])
    (realized : (heads index).subst rightRealization = headRealization index) :
    Answer env U registry Γ headRealization
      (ClosedPayload env U registry Γ locals rightRealization heads) index requested where
  entry := {
    need := ⟨result.rank, result.rawDemand⟩
    payload := by
      change Obs env U registry Γ locals rightRealization (heads index) result.rawDemand []
      simpa only [closedHead] using result.observation
    type := sourceType.subst leftRealization
    support := result.support
    typed := result.rawTyped
    code := result.typeCode
    related := by simpa only [realized] using result.rawRelated }
  bound := result.bound
  adapter := result.adapter

end Recut
end Lean4Lean.AnchoredSource.Adapted
