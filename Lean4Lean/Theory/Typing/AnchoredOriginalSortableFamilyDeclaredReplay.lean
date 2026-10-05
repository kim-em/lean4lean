import Lean4Lean.Theory.Typing.AnchoredOriginalSortableSeededSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyDeclaredPrefix
import Lean4Lean.Theory.Typing.AnchoredSortableRealization

/-! The actual rich backward spine drives the earlier declared telescope.
Every final request and seed remains literal; no source domain typing is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableCert.closedSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {oldLocals : List Nat} {oldRealization : Subst}
    {expression : VExpr} {support : Profile n}
    (certificate : SortableCert env U registry target oldLocals oldRealization expression relevant support [])
    (closed : expression.Closed) (locals : List Nat) (realization : Subst) :
    SortableCert env U registry target locals realization expression relevant support [] := by
  have changed := certificate.realizePrefix closed realization (by intro i hi; omega)
  simpa only [lift'_refl, Footprint.sourceLift, List.map_nil] using
    changed.renameSource .refl realization rfl locals

inductive SortableSpineSeedCoverage :
    SortableSpineSeeds env U registry target locals σ available expression → Footprint → Prop where
  | constant : SortableSpineSeedCoverage (SortableSpineSeeds.constant (name := name) (levels := levels)) []
  | app {required : Footprint}
      {function : SortableSpineSeeds env U registry target locals σ available f}
      {argument : SortableArgumentSeed env U registry target locals σ available a}
      (tail : SortableSpineSeedCoverage function (externalArguments required))
      (bounded : ∀ need, (0, need) ∈ required → need.rank ≤ argument.rank)
      (covered : ∀ need, (0, need) ∈ required → ∀ atom ∈ (need.atGrade argument.rank).atoms,
        atom ∈ argument.demand.atoms) :
      SortableSpineSeedCoverage (.app function argument) required

def SortableSeededApplicationInput.declaredApplication
    (henv : env.Ordered)
    (frame : SortableSeededApplicationInput env U registry target locals σ available A B a result before) :
    OriginalDeclaredApplication env U registry target σ A B a result :=
  ⟨frame.collected.rank, Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound,
    frame.key, frame.support, rfl, frame.guard.familyAdmission henv⟩

noncomputable def OriginalEndpointFactor.OriginalSortableSeededSpine.familyKeys
    (spine : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) : List FamilyKey := by
  induction spine with
  | constant => exact []
  | application frame function keys => exact keys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]
  | conversion plan certificate transfer term keys => exact keys

/-- The complete forward pass consumes the backward producer's concrete
frames. Its only original semantic calls are locations in the earlier
closed declaration header, with reconstructed exact source tails. -/
theorem OriginalEndpointFactor.OriginalSortableSeededSpine.familyDeclared
    {sourceEnv headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {expected : VConstant}
    (lookup : sourceEnv.constants name = some expected)
    (signature : ConstantTelescope (expected.type.instL levels))
    (typeClosed : (expected.type.instL levels).Closed)
    (header : OriginalFamilyHeader headerEnv U (expected.type.instL levels))
    (calls : header.SortableFundamentals env registry)
    {expression assigned : VExpr} {profile : Profile n} {footprint required : Footprint}
    (spine : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    (coverage : SortableSpineSeedCoverage spine.seeds required)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    ∃ declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature
        expression.getAppFnArgs.2 assigned profile required spine.familyKeys,
      SortableGradedValuation env U registry target locals σ available
        expression.getAppFnArgs.2 declared.valuation := by
  induction spine generalizing required with
  | @constant assigned n profile footprint replay =>
    cases coverage
    have typeEq : replay.info.type.instL levels = expected.type.instL levels := congrArg
      (fun info : VConstant => info.type.instL levels)
      (Option.some.inj (replay.lookup.symm.trans lookup))
    have empty : replay.transfer.footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      rintro ⟨index, need⟩ member
      have scope : (replay.info.type.instL levels).Closed := by rw [typeEq]; exact typeClosed
      have impossible := replay.transfer.certificate.scoped scope index need member
      omega
    have code : SortableCert env U registry target locals σ (expected.type.instL levels) true profile [] := by
      rw [← typeEq, ← empty]
      exact replay.transfer.certificate
    have actual := code.closedSource typeClosed [] (nativeCaptureSubst [])
    have pair := replay.transfer.related.symm henv code.formed.wf_value
    rw [typeEq, typeClosed.subst_eq Subst.Fixes.zero] at pair
    let cursor := OriginalFamilyPrefix.initial header signature
    let declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature
        [] assigned profile [] [] := {
      cursor := cursor
      valuation := fun _ => []
      closed := by intro _ _ member; cases member
      substitutions := .nil
      fitted := SortableTailPairedFits.diagonal (cursor.location.contextDerivation .nil) .nil
      footprint := []
      certificate := by simpa only [List.length_nil, List.drop_zero, List.range_zero,
        List.map_nil, ← signature.type_eq] using actual
      resources := fun _ _ member => nomatch member
      seedAvailable := fun _ _ member => nomatch member
      related := by simpa only [List.length_nil, List.drop_zero, ← signature.type_eq,
        typeClosed.subst_eq Subst.Fixes.zero] using pair
      history := by simpa only [List.length_nil, List.take_zero, List.reverse_nil,
        List.range_zero, List.map_nil, List.drop_zero, signature.type_eq] using
        (OriginalSortableFamilyRowHistory.nil (header := header) (env := env) (registry := registry)
          (target := target)) }
    exact ⟨declared, SortableGradedValuation.empty⟩
  | @application A B a n result before f frame function ih =>
    cases coverage with
    | app previousCoverage seedBound seedCovered =>
      have beforeBound : f.getAppFnArgs.2.length < signature.domains.length := by
        simp only [getAppFnArgs_app, List.length_append, List.length_singleton] at bound
        omega
      obtain ⟨previous, observed⟩ := ih previousCoverage (by omega)
      have raisedSeed := Nat.le_trans (Nat.le_max_right n frame.seed.rank) frame.collected.bound
      have requestBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.collected.rank := by
        intro need member
        exact Nat.le_trans (seedBound need (mem_argumentNeeds.mp member)) raisedSeed
      have requestCovered : ∀ need ∈ argumentNeeds required 0,
          ∀ atom ∈ (need.atGrade frame.collected.rank).atoms, atom ∈ frame.key.input.atoms := by
        intro need member atom ha
        rw [need.atGrade_raise raisedSeed (seedBound need (mem_argumentNeeds.mp member))] at ha
        exact frame.seedCovered atom (raiseProfile_subset raisedSeed
          (seedCovered need (mem_argumentNeeds.mp member)) atom ha)
      obtain ⟨next, needs, same, bounded, covered⟩ := previous.advance henv hscoped below calls
        hTarget (frame.declaredApplication henv) beforeBound requestBound requestCovered
      have observedNext : SortableGradedValuation env U registry target locals σ available
          (f.getAppFnArgs.2 ++ [a]) next.valuation := by
        rw [same]
        obtain ⟨_, _, _, _, _, _, anchor, _⟩ := frame.guard.anchor
        exact observed.push (SortableGradedResult.exact frame.argumentObservation frame.argumentResources
          (Related.live henv hscoped hTarget anchor)) bounded covered
      have done : ∃ declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature
          (f.getAppFnArgs.2 ++ [a]) (B.inst a) result required
          (function.familyKeys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]),
          SortableGradedValuation env U registry target locals σ available
            (f.getAppFnArgs.2 ++ [a]) declared.valuation := ⟨next, observedNext⟩
      change ∃ declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature
          (f.app a).getAppFnArgs.2 (B.inst a) result required
          (function.familyKeys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]),
          SortableGradedValuation env U registry target locals σ available
            (f.app a).getAppFnArgs.2 declared.valuation
      rw [show (f.app a).getAppFnArgs.2 = f.getAppFnArgs.2 ++ [a] from by simp]
      exact done
  | conversion plan certificate transfer term ih =>
    obtain ⟨previous, observed⟩ := ih coverage bound
    exact ⟨{ previous with related := (previous.related.trans henv
      (transfer.related.symm henv certificate.formed.wf_value)) }, observed⟩

end Lean4Lean.AnchoredSource.Adapted
