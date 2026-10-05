import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaInstantiation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Paired reconstruction of a query-owned canonical instantiation. The
argument remains a real query child, outside the canonical parent's mask.
Both its reconstructed query and its assigned-type certificate stay at their
actual original nodes. No frame reserve or source comparison is inserted. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace CanonicalDeltaInstantiation
variable {argument : EndpointState sourceEnv U source a A} {result : Profile n}

/-- The exact two child answers reconstruct a recipe for every codomain B,
including projected codomains. Parent interpretation is obtained by its
actual canonical lower-call ledger. The admission used to reanchor its row
is computed from that same paired parent and the actual argument answer. -/
theorem rebuildFromAnswers
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.parent.depth)
    (calls : recipe.parent.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (resources : recipe.footprint.Available available)
    (argumentAnswer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available recipe.rawInput)
    (codeAnswer : RichComputationalValue sourceEnv env U registry target argument.typeFormation.node
      locals σ τ available recipe.support) :
    ∃ right : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals τ B relevant result,
      right.footprint.Available available ∧
      TypeRelated env U registry target ((B.inst a).subst σ) ((B.inst a).subst τ) result ∧
      right.parent.depth = recipe.parent.depth ∧
      HEq right.query argumentAnswer.rightQuery.observation ∧
      (∀ policy, right.query.headDepth policy = argumentAnswer.rightQuery.observation.headDepth policy ∧
        right.certificate.headDepth policy ≤ codeAnswer.rightQuery.observation.headDepth policy) ∧
      (∀ rank control, right.depth rank control ≤ max (recipe.parent.depth control)
        (max (argumentAnswer.rightQuery.observation.stratifiedDepth rank control)
          (codeAnswer.rightQuery.observation.stratifiedDepth rank control))) := by
  have parentResources : recipe.parentFootprint.Available available := by
    intro index need member
    exact resources index need (List.mem_append_left _ (List.mem_append_left _ member))
  obtain ⟨parent, parentDepth, whole⟩ := recipe.parent.rebuild henv hscoped formed cutoff cutoffBound fuel
    constants callerSchedule bounded calls frame substitutions parentResources
  have code := codeAnswer.related.code_of_sortable henv hscoped formed recipe.certificate.formed
  have high := recipe.adapter.termMap henv hscoped formed
    (Profile.HasType.raise recipe.queryBound recipe.typed)
    (code.left_diagonal.raise henv recipe.queryBound) argumentAnswer.related
  have paired : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ)
      recipe.key.input recipe.support := by
    simpa only [lower_raised] using Related.lower henv recipe.queryBound formed high
  have raw := (argument.sound.defeq.mono sourceBelow).substDF henv substitutions.wf formed substitutions
  have admission := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
    (by simpa only [subst] using whole) recipe.selected recipe.anchor raw paired
  let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
  let change : AtomView env U registry target (n := n + 1)
      (.fn recipe.key unused) (.fn (reanchorKey recipe.key (a.subst τ)) unused) := .reanchor admission
  let rightParent : CanonicalDeltaElimination env U registry target strata source τ (.forallE A B)
      relevant (.pi recipe.prototypeDomain recipe.prototypeBody recipe.ambient
        (reanchorRows recipe.key (reanchorKey recipe.key (a.subst τ)) recipe.rows)) recipe.parentFootprint :=
    .map change parent
  let argumentQuery := argumentAnswer.rightQuery.adaptRequest henv hscoped formed recipe.queryBound recipe.adapter
  obtain ⟨supportFootprint, certificate, certificateAvailable, certificateDepth⟩ :=
    codeAnswer.rightQuery.code_headDepth henv recipe.certificate.formed
  let right : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals τ B relevant result := {
    prototypeDomain := recipe.prototypeDomain
    prototypeBody := recipe.prototypeBody
    ambient := recipe.ambient
    rows := reanchorRows recipe.key (reanchorKey recipe.key (a.subst τ)) recipe.rows
    key := reanchorKey recipe.key (a.subst τ)
    parentFootprint := recipe.parentFootprint
    parent := rightParent
    selected := reanchorRows.changed (newKey := reanchorKey recipe.key (a.subst τ)) recipe.selected
    anchor := rfl
    queryRank := argumentQuery.rank
    queryBound := argumentQuery.bound
    rawInput := argumentQuery.raw
    argumentFootprint := argumentQuery.footprint
    query := argumentQuery.observation
    adapter := argumentQuery.adapter
    support := recipe.support
    supportFootprint := supportFootprint
    certificate := certificate
    typed := recipe.typed }
  refine ⟨right, ?_, ?_, parentDepth, HEq.rfl, ?_, ?_⟩
  · intro index need member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact parentResources index need member
      · exact argumentQuery.resources index need member
    · exact certificateAvailable index need member
  · have output := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
      (by simpa only [subst] using whole) recipe.selected recipe.anchor raw paired
    simpa only [subst_inst, inst_lift_cons] using output
  · intro policy
    exact ⟨rfl, certificateDepth policy⟩
  · intro rank control
    have parentEq := congrFun parentDepth control
    have certLe := certificateDepth (stratifiedHeadPolicy rank control)
    change max (parent.depth control)
      (max (argumentAnswer.rightQuery.observation.stratifiedDepth rank control)
        (certificate.stratifiedDepth rank control)) ≤ _
    rw [parentEq]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans certLe (Nat.le_max_right _ _)⟩)
      (Nat.le_max_right _ _)⟩

/-- Masked bounds refer to this same reconstructed recipe and its exact
returned argument observation. The two child bounds are facts about the
actual answers, as supplied by the qualified original induction hypotheses;
this lemma introduces neither a sponsor budget nor a frame reservation. -/
theorem rebuildWithinFromAnswers
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (bounded : WithinAbove cutoff fuel (recipe.depth (strata.headOrdinal registry)))
    (calls : recipe.parent.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (resources : recipe.footprint.Available available)
    (argumentAnswer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available recipe.rawInput)
    (codeAnswer : RichComputationalValue sourceEnv env U registry target argument.typeFormation.node
      locals σ τ available recipe.support)
    (argumentBound : WithinAbove cutoff fuel (fun control =>
      argumentAnswer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control))
    (codeBound : WithinAbove cutoff fuel (fun control =>
      codeAnswer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control)) :
    ∃ right : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals τ B relevant result,
      right.footprint.Available available ∧
      TypeRelated env U registry target ((B.inst a).subst σ) ((B.inst a).subst τ) result ∧
      right.parent.depth = recipe.parent.depth ∧
      HEq right.query argumentAnswer.rightQuery.observation ∧
      (∀ policy, right.query.headDepth policy = argumentAnswer.rightQuery.observation.headDepth policy ∧
        right.certificate.headDepth policy ≤ codeAnswer.rightQuery.observation.headDepth policy) ∧
      WithinAbove cutoff fuel (right.depth (strata.headOrdinal registry)) := by
  have parentBound : WithinAbove cutoff fuel recipe.parent.depth := fun control above =>
    Nat.le_trans (Nat.le_max_left _ _) (bounded control above)
  obtain ⟨right, resources, related, parentEq, queryEq, policies, depthBound⟩ :=
    recipe.rebuildFromAnswers henv hscoped formed cutoff cutoffBound fuel constants callerSchedule
      parentBound calls frame substitutions sourceBelow resources argumentAnswer codeAnswer
  refine ⟨right, resources, related, parentEq, queryEq, policies, ?_⟩
  intro control above
  exact Nat.le_trans (depthBound (strata.headOrdinal registry) control)
    (Nat.max_le.mpr ⟨parentBound control above,
      Nat.max_le.mpr ⟨argumentBound control above, codeBound control above⟩⟩)

end CanonicalDeltaInstantiation
end Lean4Lean.AnchoredSource.Adapted
