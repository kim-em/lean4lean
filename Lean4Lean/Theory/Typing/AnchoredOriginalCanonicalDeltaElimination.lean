import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaBodyRecipe
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaBodyReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure
import Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered

/-! Arbitrarily finite Pi elimination below one charged canonical type root.
Body steps retain actual binder demands, and later domain/body steps may act
on their result. The interpreter uses the same actual frame and its complete
suffixes; there is only one canonical lower F call, at the retained root. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A stored, computed admission suffices when the codomain does not use
its binder. All remaining context dependence still follows the paired parent. -/
private theorem independentBody {A B : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target
      ((VExpr.forallE A B.lift).subst σ) ((VExpr.forallE A B.lift).subst τ)
      (.pi prototypeDomain prototypeBody ambient rows))
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key anchor anchor) :
    TypeRelated env U registry target (B.subst σ) (B.subst τ) result := by
  have output := TypeRelated.literalPiBody_pair henv hscoped formed
    (by simpa only [subst] using whole) selected admitted
  simpa only [lift_subst_lift, inst_lift] using output.2

inductive CanonicalDeltaElimination (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env) :
    (source : List VExpr) → (σ : Subst) → (expression : VExpr) → (relevant : Bool) →
      {n : Nat} → Profile n → Footprint → Type where
  | root (source : List VExpr) (σ : Subst)
      (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) :
      CanonicalDeltaElimination env U registry target strata source σ expression relevant profile []
  | domain
      (parent : CanonicalDeltaElimination env U registry target strata source σ (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint) :
      CanonicalDeltaElimination env U registry target strata source σ A true support footprint
  | body
      (parent : CanonicalDeltaElimination env U registry target strata source σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
      (selected : (key, result) ∈ rows)
      (anchor : key.anchor = σ 0) :
      CanonicalDeltaElimination env U registry target strata (A :: source) σ B relevant result
        ((0, ⟨n, key.input⟩) :: footprint.sourceLift (.skip .refl))
  | fixedBody
      (parent : CanonicalDeltaElimination env U registry target strata source σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor) :
      CanonicalDeltaElimination env U registry target strata source σ B relevant result footprint
  | action
      (change : SortableCodeAction env U registry target relevant profile nextRelevant nextProfile)
      (parent : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint) :
      CanonicalDeltaElimination env U registry target strata source σ expression nextRelevant nextProfile footprint

namespace CanonicalDeltaElimination
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env}

noncomputable def depth
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint) : Nat → Nat :=
  match recipe with
  | .root _ _ packet => packet.chargeDepth
  | .domain parent | .body parent _ _ | .fixedBody parent _ _ | .action _ parent => parent.depth

def Calls
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    (parentKey : EquationControlMeasure.Key strata.rules.length) : Prop :=
  match recipe with
  | .root _ _ packet => packet.CodeBelow parentKey
  | .domain parent | .body parent _ _ | .fixedBody parent _ _ | .action _ parent => parent.Calls parentKey

private theorem action_formed
    (action : SortableCodeAction env U registry target relevant profile nextRelevant nextProfile)
    (formed : profile.HasType (.sort relevant)) : nextProfile.HasType (.sort nextRelevant) := by
  induction action with
  | id => exact formed
  | retag targetFormed => exact targetFormed
  | comp first second ihfirst ihsecond => exact ihsecond (ihfirst formed)
  | union first second ihfirst ihsecond => exact (ihfirst formed).union (ihsecond formed)
  | support change => exact change.preservesSort formed
  | pad => exact formed.pad_sort
  | down => simpa only [Profile.down_sort] using formed.down
  | unpad => simpa only [Profile.down_sort] using formed.pad_inv
  | sortPad => exact formed.sortPad
  | familyPad => exact formed.familyPad
  | map change => exact change.mapType_sort formed
  | select member => exact formed.singleton_of_mem member
  | focusMinimal minimal bound => exact formed.restrict bound minimal.formation.wf_value

/-- A local reanchor is the existing finite code action, not an extra
semantic transformer stored in the recipe grammar. -/
noncomputable def map {a b : Atom n} (change : AtomView env U registry target a b)
    (parent : CanonicalDeltaElimination env U registry target strata source σ expression relevant
      (profile : Profile n) footprint) :
    CanonicalDeltaElimination env U registry target strata source σ expression relevant
      (change.mapType profile) footprint := .action (.map change) parent

theorem formed
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint) :
    profile.HasType (.sort relevant) := by
  induction recipe with
  | root _ _ packet => exact packet.formed
  | domain parent ih => exact (Profile.WF.pi_iff.mp ih.1).1
  | body parent selected _ ih | fixedBody parent selected _ ih =>
    exact (Profile.HasType.pi_iff.mp ih).2 _ _ selected
  | action change parent ih => exact action_formed change ih

/-- All path steps keep the root charge. In particular, taking another Pi
component after a dependent body never exposes an unmasked child packet. -/
@[simp] theorem domain_depth
    (parent : CanonicalDeltaElimination env U registry target strata source σ (.forallE A B)
      relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint) :
    parent.domain.depth = parent.depth := rfl

@[simp] theorem body_depth {σ : Subst}
    (parent : CanonicalDeltaElimination env U registry target strata source σ.tail (.forallE A B)
      relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
    (parent.body selected anchor).depth = parent.depth := rfl

/-- The actual source-context frame discharges every binder demand. It may
contain merges, captured owners and dormant histories: recursive body steps
use its computed full suffix, not a synthesized replacement frame. -/
theorem interpret
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.depth)
    (calls : recipe.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) :
    TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  induction recipe generalizing sourceEnv locals τ available with
  | root source σ packet =>
    exact packet.interpret henv hscoped formed cutoff cutoffBound fuel constants callerSchedule bounded calls σ τ
  | domain parent ih =>
    exact TypeRelated.literalPiDomain henv hscoped formed (by
      simpa only [subst] using ih bounded calls frame substitutions resources)
  | fixedBody parent selected admitted ih =>
    exact independentBody henv hscoped formed (ih bounded calls frame substitutions resources) selected admitted
  | action change parent ih =>
    exact change.codeMap henv hscoped (ih bounded calls frame substitutions resources)
  | @body source A B relevant prototypeDomain prototypeBody n support rows footprint key result σ parent selected anchor ih =>
    cases context with
    | cons context domain =>
      have previous : footprint.Available (fun i => available (i + 1)) := by
        intro i need member
        apply resources (i + 1) need
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨(i, need), member, rfl⟩
      have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
        cases substitutions with
        | cons tail _ _ => exact tail
      have whole := ih bounded calls frame.fullTail.frame tailSubstitutions previous
      have member : (⟨n, key.input⟩ : Need) ∈ available 0 :=
        resources 0 _ List.mem_cons_self
      exact TypeRelated.literalPiRowFromFrame henv hscoped formed frame substitutions whole selected member anchor

/-- Reconstruct the right query from the same paired frame. A body step
computes its right admission from the actual whole-Pi witness and head lookup,
copies the selected row with a finite reanchor action, and keeps exactly the
same source demands and root depth. -/
theorem rebuild
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.depth)
    (calls : recipe.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) :
    ∃ next : CanonicalDeltaElimination env U registry target strata source τ expression relevant profile footprint,
      next.depth = recipe.depth ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  induction recipe generalizing sourceEnv locals τ available with
  | root source σ packet =>
    exact ⟨.root source τ packet, rfl,
      packet.interpret henv hscoped formed cutoff cutoffBound fuel constants callerSchedule bounded calls σ τ⟩
  | domain parent ih =>
    obtain ⟨next, depthEq, whole⟩ := ih bounded calls frame substitutions resources
    exact ⟨.domain next, depthEq, TypeRelated.literalPiDomain henv hscoped formed (by
      simpa only [subst] using whole)⟩
  | fixedBody parent selected admitted ih =>
    obtain ⟨next, depthEq, whole⟩ := ih bounded calls frame substitutions resources
    exact ⟨.fixedBody next selected admitted, depthEq,
      independentBody henv hscoped formed whole selected admitted⟩
  | action change parent ih =>
    obtain ⟨next, depthEq, whole⟩ := ih bounded calls frame substitutions resources
    exact ⟨.action change next, depthEq, change.codeMap henv hscoped whole⟩
  | @body source A B relevant prototypeDomain prototypeBody n support rows footprint key result σ parent selected anchor ih =>
    cases context with
    | cons context domain =>
      have previous : footprint.Available (fun i => available (i + 1)) := by
        intro i need member
        apply resources (i + 1) need
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨(i, need), member, rfl⟩
      have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
        cases substitutions with
        | cons tail _ _ => exact tail
      obtain ⟨next, depthEq, whole⟩ := ih bounded calls frame.fullTail.frame tailSubstitutions previous
      have member : (⟨n, key.input⟩ : Need) ∈ available 0 := resources 0 _ List.mem_cons_self
      have admitted := TypeRelated.literalPiRightAdmissionFromFrame henv hscoped formed
        frame substitutions whole selected member anchor
      let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
      let change : AtomView env U registry target (n := n + 1)
          (.fn key unused) (.fn (reanchorKey key (τ 0)) unused) := .reanchor admitted
      let widened : CanonicalDeltaElimination env U registry target strata source τ.tail (.forallE A B)
          relevant (.pi prototypeDomain prototypeBody support (reanchorRows key (reanchorKey key (τ 0)) rows)) footprint :=
        .map change next
      refine ⟨.body (key := reanchorKey key (τ 0)) widened
        (reanchorRows.changed (newKey := reanchorKey key (τ 0)) selected) rfl, ?_, ?_⟩
      · exact depthEq
      exact TypeRelated.literalPiRowFromFrame henv hscoped formed frame substitutions whole selected member anchor


/-- Discharge an unused binder from its actual paired source frame. The
returned recipe has only the parent's footprint, so a destination outside
that binder needs no captured argument query or additional reserve. The
admission stored by `fixedBody` is produced here, not supplied by the caller. -/
theorem eraseUnusedBinder
    {σ : Subst}
    (parent : CanonicalDeltaElimination env U registry target strata source σ.tail (.forallE A B.lift)
      relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel parent.depth)
    (calls : parent.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U (A :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (A :: source))
    (resources : Footprint.Available
      ((0, (⟨n, key.input⟩ : Need)) :: footprint.sourceLift (.skip .refl)) available) :
    ∃ next : CanonicalDeltaElimination env U registry target strata source τ.tail B relevant result footprint,
      next.depth = parent.depth ∧
      footprint.Available (fun i => available (i + 1)) ∧
      TypeRelated env U registry target (B.subst σ.tail) (B.subst τ.tail) result := by
  cases context with
  | cons context domain =>
    have previous : footprint.Available (fun i => available (i + 1)) := by
      intro i need member
      apply resources (i + 1) need
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨(i, need), member, rfl⟩
    have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
      cases substitutions with
      | cons tail _ _ => exact tail
    obtain ⟨next, depthEq, whole⟩ := parent.rebuild henv hscoped formed cutoff cutoffBound fuel
      constants callerSchedule bounded calls frame.fullTail.frame tailSubstitutions previous
    have member : (⟨n, key.input⟩ : Need) ∈ available 0 := resources 0 _ List.mem_cons_self
    have admitted := TypeRelated.literalPiRightAdmissionFromFrame henv hscoped formed
      frame substitutions whole selected member anchor
    exact ⟨.fixedBody next selected admitted, depthEq, previous,
      independentBody henv hscoped formed whole selected admitted⟩


end CanonicalDeltaElimination

/-- Original endpoints are retained separately from the canonical recipe.
Domain/body factories below use the source's actual Pi exposure route. -/
structure CanonicalDeltaEliminationAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source expression (.sort level))
    (σ : Subst) (relevant : Bool) (profile : Profile n) (footprint : Footprint) where
  recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint

def CanonicalDeltaTypeAt.elimination
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant profile) :
    CanonicalDeltaEliminationAt sourceEnv env U registry target strata node σ relevant profile [] :=
  ⟨.root source σ query.packet⟩

/-- Copying an actual source-independent recipe requires neither the old
parent location nor a newly invented parent at the destination. -/
def CanonicalDeltaEliminationAt.reindex
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalDeltaEliminationAt sourceEnv env U registry target strata node σ relevant profile footprint)
    (destination : EndpointState destinationEnv U source expression (.sort destinationLevel)) :
    CanonicalDeltaEliminationAt destinationEnv env U registry target strata destination σ relevant profile footprint :=
  ⟨query.recipe⟩

def CanonicalDeltaEliminationAt.piDomain
    {node : EndpointState sourceEnv U source (.forallE A B) (.sort level)}
    (query : CanonicalDeltaEliminationAt sourceEnv env U registry target strata node σ relevant
      (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (_route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body)) :
    CanonicalDeltaEliminationAt sourceEnv env U registry target strata domain σ true support footprint :=
  ⟨.domain query.recipe⟩

def CanonicalDeltaEliminationAt.piBody {σ : Subst}
    {node : EndpointState sourceEnv U source (.forallE A B) (.sort level)}
    (query : CanonicalDeltaEliminationAt sourceEnv env U registry target strata node σ.tail relevant
      (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (_route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body))
    (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
    CanonicalDeltaEliminationAt sourceEnv env U registry target strata body σ relevant result
      ((0, ⟨n, key.input⟩) :: footprint.sourceLift (.skip .refl)) :=
  ⟨.body query.recipe selected anchor⟩


/-- The unused-binder application edge ends at the caller's actual original
`(B.lift).inst a` formation. It drops the head demand and retains every outer
request; the destination does not need a parent Pi or an argument reserve. -/
theorem CanonicalDeltaEliminationAt.unusedApplicationBody
    {σ : Subst} {A B a : VExpr}
    (parent : CanonicalDeltaElimination env U registry target strata source σ.tail (.forallE A B.lift)
      relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel parent.depth)
    (calls : parent.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U (A :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (A :: source))
    (resources : Footprint.Available
      ((0, (⟨n, key.input⟩ : Need)) :: footprint.sourceLift (.skip .refl)) available)
    (destination : EndpointState destinationEnv U source (B.lift.inst a) (.sort level)) :
    ∃ query : CanonicalDeltaEliminationAt destinationEnv env U registry target strata
        destination τ.tail relevant result footprint,
      query.recipe.depth = parent.depth ∧
      footprint.Available (fun i => available (i + 1)) := by
  revert destination
  rw [inst_lift]
  intro destination
  obtain ⟨next, depthEq, outside, _⟩ := parent.eraseUnusedBinder selected anchor
    henv hscoped formed cutoff cutoffBound fuel constants callerSchedule bounded calls frame substitutions resources
  exact ⟨⟨next⟩, depthEq, outside⟩

end Lean4Lean.AnchoredSource.Adapted
