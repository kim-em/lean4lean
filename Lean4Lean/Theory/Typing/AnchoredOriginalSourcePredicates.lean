import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraphAmbient
import Lean4Lean.Theory.Typing.ConstantHeaderProvenance

/-! Hereditary source predicates separate the semantic target environment
from the declaration stage of the original proofs. A closed earlier header
may have arbitrary proof size, but strictly smaller declaration stage. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000

mutual
def RawOriginalRichFrame.AllSources (P : VEnv → Prop)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  P sourceEnv ∧ match frame with
  | .nil => True
  | .reserve previous _ => previous.AllSources P
  | .merge left right => left.AllSources P ∧ right.AllSources P
  | .header (capturedEnv := capturedEnv) .. => P capturedEnv
  | .bind previous .. => previous.AllSources P
  | .capture previous .. => previous.AllSources P
  | .group (capturedEnv := capturedEnv) previous _ _ _ entries =>
      previous.AllSources P ∧ P capturedEnv ∧ entries.AllSources P
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

def RawRichGroupEntry.AllSources (P : VEnv → Prop)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) : Prop :=
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ _query _resources _answer => frame.AllSources P
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

def RawRichGroupEntries.AllSources (P : VEnv → Prop)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Prop :=
  match entries with
  | .nil => True
  | .cons entry rest => entry.AllSources P ∧ rest.AllSources P
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

def OriginalRichFrame.AllSources (P : VEnv → Prop)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  frame.raw.AllSources P

theorem RawOriginalRichFrame.AllSources.source
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (sources : frame.AllSources P) : P sourceEnv := by
  rw [RawOriginalRichFrame.AllSources.eq_def] at sources
  exact sources.1

theorem OriginalRichFrame.AllSources.source
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (sources : frame.AllSources P) : P sourceEnv := RawOriginalRichFrame.AllSources.source sources

mutual
theorem RawOriginalRichFrame.AllSources.mono
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (sources : frame.AllSources P) (implication : ∀ source, P source → Q source) : frame.AllSources Q := by
  match frame, sources with
  | .nil, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, trivial⟩
  | .reserve previous _, sources | .bind previous .., sources | .capture previous .., sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, RawOriginalRichFrame.AllSources.mono sources.2 implication⟩
  | .merge left right, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, RawOriginalRichFrame.AllSources.mono sources.2.1 implication,
      RawOriginalRichFrame.AllSources.mono sources.2.2 implication⟩
  | .header .., sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, implication _ sources.2⟩
  | .group previous _ _ _ entries, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, RawOriginalRichFrame.AllSources.mono sources.2.1 implication,
      implication _ sources.2.2.1, RawRichGroupEntries.AllSources.mono sources.2.2.2 implication⟩
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.AllSources.mono
    {entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input}
    (sources : entry.AllSources P) (implication : ∀ source, P source → Q source) : entry.AllSources Q := by
  match entry, sources with
  | .mk .., sources =>
    rw [RawRichGroupEntry.AllSources.eq_def] at sources ⊢
    exact RawOriginalRichFrame.AllSources.mono sources implication
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.AllSources.mono
    {entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs}
    (sources : entries.AllSources P) (implication : ∀ source, P source → Q source) : entries.AllSources Q := by
  match entries, sources with
  | .nil, sources => rw [RawRichGroupEntries.AllSources.eq_def]; trivial
  | .cons entry rest, sources =>
    rw [RawRichGroupEntries.AllSources.eq_def] at sources ⊢
    exact ⟨RawRichGroupEntry.AllSources.mono sources.1 implication,
      RawRichGroupEntries.AllSources.mono sources.2 implication⟩
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

mutual
theorem RawOriginalRichFrame.allSources_ambient
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    frame.AllSources (· ≤ env) ↔ frame.Ambient := by
  rw [RawOriginalRichFrame.AllSources.eq_def, RawOriginalRichFrame.Ambient.eq_def]
  match frame with
  | .nil | .header .. => rfl
  | .reserve previous _ | .bind previous .. | .capture previous .. =>
    exact and_congr_right fun _ => previous.allSources_ambient
  | .merge left right =>
    exact and_congr_right fun _ => and_congr left.allSources_ambient right.allSources_ambient
  | .group previous _ _ _ entries =>
    exact and_congr_right fun _ => and_congr previous.allSources_ambient
      (and_congr_right fun _ => entries.allSources_ambient)
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.allSources_ambient
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.AllSources (· ≤ env) ↔ entry.Ambient := by
  match entry with
  | .mk _ _ _ _ _ _ frame .. =>
    rw [RawRichGroupEntry.AllSources.eq_def, RawRichGroupEntry.Ambient.eq_def]
    exact frame.allSources_ambient
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.allSources_ambient
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    entries.AllSources (· ≤ env) ↔ entries.Ambient := by
  match entries with
  | .nil => rw [RawRichGroupEntries.AllSources.eq_def, RawRichGroupEntries.Ambient.eq_def]
  | .cons entry rest =>
    rw [RawRichGroupEntries.AllSources.eq_def, RawRichGroupEntries.Ambient.eq_def]
    exact and_congr entry.allSources_ambient rest.allSources_ambient
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

theorem OriginalRichFrame.allSources_ambient
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    frame.AllSources (· ≤ env) ↔ frame.Ambient := frame.raw.allSources_ambient

def OriginalCaptureMap.AllSources (P : VEnv → Prop)
    {context : ContextDerivation sourceEnv U sourceContext}
    (graph : OriginalCaptureMap (common := common) context raw) : Prop :=
  P sourceEnv ∧ match graph with
  | .empty _ | .identity _ => True
  | .tail previous => previous.AllSources P
  | .capture previous _ ownerMap _ _ => previous.AllSources P ∧ ownerMap.AllSources P
  | .bind previous .. => previous.AllSources P
  | .weaken previous _ => previous.AllSources P

theorem OriginalCaptureMap.AllSources.source
    {context : ContextDerivation sourceEnv U sourceContext}
    {graph : OriginalCaptureMap (common := common) context raw}
    (sources : graph.AllSources P) : P sourceEnv := by
  rw [OriginalCaptureMap.AllSources.eq_def] at sources
  exact sources.1

theorem OriginalCaptureMap.AllSources.mono
    {context : ContextDerivation sourceEnv U sourceContext}
    {graph : OriginalCaptureMap (common := common) context raw}
    (sources : graph.AllSources P) (implication : ∀ source, P source → Q source) : graph.AllSources Q := by
  induction graph with
  | empty | identity => exact ⟨implication _ sources.1, trivial⟩
  | tail _ ih | bind _ _ _ _ ih | weaken _ _ ih =>
    exact ⟨implication _ sources.1, ih sources.2⟩
  | capture _ _ _ _ _ left right => exact ⟨implication _ sources.1, left sources.2.1, right sources.2.2⟩

theorem OriginalCaptureMap.allSources_ambient
    {context : ContextDerivation sourceEnv U sourceContext}
    (graph : OriginalCaptureMap (common := common) context raw) :
    graph.AllSources (· ≤ env) ↔ graph.Ambient env := by
  induction graph with
  | empty | identity => rfl
  | tail _ ih | bind _ _ _ _ ih | weaken _ _ ih => exact and_congr_right fun _ => ih
  | capture _ _ _ _ _ left right => exact and_congr_right fun _ => and_congr left right

/-- Stage concerns original source environments; the semantic target may
contain more declarations. No orderedness is invented for empty frames. -/
def SourceAtStage (stage : Nat) (source : VEnv) : Prop :=
  ∀ ordered : source.Ordered, ordered.constantCount ≤ stage

/-- Inclusion bounds declaration count independently of the chosen
orderedness proofs or finite-domain enumerations. -/
theorem SourceAtStage.ofBelow (ordered : env.Ordered) (below : sourceEnv ≤ env) :
    SourceAtStage ordered.constantCount sourceEnv := by
  intro sourceOrdered
  let sourceDomain := Classical.choice sourceOrdered.constantDomain
  let targetDomain := Classical.choice ordered.constantDomain
  exact sourceDomain.nodup.length_le_of_subset (l₂ := targetDomain.names) (by
    intro name member
    obtain ⟨value, lookup⟩ := (sourceDomain.present name).mp member
    exact (targetDomain.present name).mpr ⟨value, below.constants lookup⟩)

/-- Every already ambient frame satisfies the initial global stage bound.
Smaller stages require explicit preservation, not this initialization lemma. -/
theorem OriginalRichFrame.Ambient.atStage
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.Ambient) (ordered : env.Ordered) :
    frame.AllSources (SourceAtStage ordered.constantCount) :=
  RawOriginalRichFrame.AllSources.mono (frame.allSources_ambient.mpr ambient)
    (fun _ below => SourceAtStage.ofBelow ordered below)

theorem SourceAtStage.mono (bound : stage ≤ next) (source : SourceAtStage stage env) :
    SourceAtStage next env := fun ordered => Nat.le_trans (source ordered) bound

/-- The actual incoming header is earlier even when its universe packet or
formation proof differs from the header charged by the local closure size. -/
theorem originalHeader_stage_lt
    (origin : ConstantHeaderOrigin sourceEnv name info) (ordered : sourceEnv.Ordered)
    (stageBound : SourceAtStage stage sourceEnv) : origin.ordered.constantCount < stage :=
  Nat.lt_of_lt_of_le (origin.count_lt ordered) (stageBound ordered)

theorem originalHeader_lex_lt
    (origin : ConstantHeaderOrigin sourceEnv name info) (ordered : sourceEnv.Ordered)
    (stageBound : SourceAtStage stage sourceEnv) (headerCost parentCost : Nat) :
    Prod.Lex Nat.lt Nat.lt (origin.ordered.constantCount, headerCost) (stage, parentCost) :=
  Prod.Lex.left _ _ (originalHeader_stage_lt origin ordered stageBound)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
