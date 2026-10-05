import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTableClosure

/-! Exact base ancestry for paired owned-frame reconstruction. An identity
sandbox does not erase the generation which built its raw frame. The finite
positive history below retains that generation, its exact controls and ledger,
and the histories of every identity leaf it uses. No reconstruction function
or completed F/R answer is stored. Arbitrary old identity witnesses need not
admit this stronger evidence; producers must carry it from the closed start.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Equality of sites includes the actual raw frame and annotated environment,
not just the numerical cost of that environment. -/
inductive WorldFrameSite (strata : EquationStratification env) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) : Type where
  | mk {context : ContextDerivation sourceEnv U source}
      (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (controls : OriginalWorldControls strata sourceEnv)
      (environment : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)) :
      WorldFrameSite strata U registry target

/-- The resource table belongs to this exact frame site, including an opaque
identity base. Closure is not recoverable from its world environment. -/
def WorldFrameSite.TableClosed (site : WorldFrameSite strata U registry target) : Prop :=
  match site with
  | .mk (available := available) _ _ _ => available.AtomClosed

/-- Pure left diagonalization keeps all original sites and annotations; it
changes only the paired raw frame. Its right side is already its left side. -/
noncomputable def WorldFrameSite.leftDiagonal
    (site : WorldFrameSite strata U registry target) : WorldFrameSite strata U registry target :=
  match site with
  | .mk frame controls environment => .mk frame.leftDiagonal controls (by
      simpa only [RawOriginalRichFrame.dependencyEnvironment_leftDiagonal] using environment)

theorem WorldFrameSite.tableClosed_leftDiagonal
    (site : WorldFrameSite strata U registry target) :
    site.leftDiagonal.TableClosed ↔ site.TableClosed := by
  cases site
  rfl

/-- Every actual identity occurrence is enumerated, including duplicates in
merges and in dormant route/owner generations. No dictionary deduplication can
substitute another frame with an equal scalar ledger. -/
noncomputable def WorldGenerated.baseUses
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    List (WorldFrameSite strata U registry target) := by
  induction generated with
  | identity ambient sources controls environment => exact [.mk base.frame.raw controls environment]
  | empty => exact []
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ihFirst ihSecond => exact ihFirst ++ ihSecond
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih => exact ih
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih => exact ih
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact tailIH ++ seedIH ++ priorIH ++
      (List.finRange history.route.frames.length).flatMap (fun index => historyIH index) ++
      entries.attach.flatMap (fun entry => ownerIH entry.val entry.property)

mutual
/-- A frame either starts empty or is exactly the output of a positive
generation whose own bases have finite ancestry. This is data, not a semantic
callback claiming that the frame can already be rebuilt. -/
inductive WorldFrameHistory (strata : EquationStratification env) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (P : VEnv → Prop) :
    WorldFrameSite strata U registry target → Type where
  | nil (controls : OriginalWorldControls strata sourceEnv) :
      WorldFrameHistory strata U registry target P
        (.mk (.nil (locals := locals) (σ := σ) (τ := τ) (available := available)) controls .nil)
  | leftDiagonal (history : WorldFrameHistory strata U registry target P site) :
      WorldFrameHistory strata U registry target P site.leftDiagonal
  | generated {base : OriginalCaptureBase env U registry target}
      (generation : WorldGenerated strata P base caps left right graph frame controls)
      (bases : WorldBaseHistories strata U registry target P generation.baseUses) :
      WorldFrameHistory strata U registry target P (.mk frame controls generation.environment)

inductive WorldBaseHistories (strata : EquationStratification env) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (P : VEnv → Prop) :
    List (WorldFrameSite strata U registry target) → Type where
  | nil : WorldBaseHistories strata U registry target P []
  | cons (head : WorldFrameHistory strata U registry target P site)
      (tail : WorldBaseHistories strata U registry target P sites) :
      WorldBaseHistories strata U registry target P (site :: sites)
end


mutual
/-- Readiness includes the dormant generation, not only the raw queries
visible through the sandbox. The original route boundaries and control
prefixes remain available when ancestry is opened. -/
noncomputable def WorldFrameHistory.Ready
    (history : WorldFrameHistory strata U registry target P site)
    (frontier : List (World strata.rules.length)) (cutoff : Nat) (fuel : Nat → Nat) : Prop :=
  match history with
  | .nil controls => site.TableClosed ∧ controls.HasPrefix cutoff fuel
  | .leftDiagonal previous => previous.Ready frontier cutoff fuel
  | .generated generation bases =>
      Nonempty (generation.Controlled frontier) ∧ generation.Replayable ∧ generation.TablesClosed ∧
      generation.UsesControlPrefix cutoff fuel ∧ bases.Ready frontier cutoff fuel
termination_by structural history

noncomputable def WorldBaseHistories.Ready
    (histories : WorldBaseHistories strata U registry target P sites)
    (frontier : List (World strata.rules.length)) (cutoff : Nat) (fuel : Nat → Nat) : Prop :=
  match histories with
  | .nil => True
  | .cons head tail => head.Ready frontier cutoff fuel ∧ tail.Ready frontier cutoff fuel
termination_by structural histories
end

/-- Ancestry gives closure of the exact site consumed by an identity leaf. -/
theorem WorldFrameHistory.Ready.tableClosed
    {history : WorldFrameHistory strata U registry target P site}
    (ready : history.Ready frontier cutoff fuel) : site.TableClosed := by
  cases history with
  | nil => exact ready.1
  | leftDiagonal previous =>
    exact (WorldFrameSite.tableClosed_leftDiagonal _).mpr
      (WorldFrameHistory.Ready.tableClosed (history := previous) ready)
  | generated generation bases => exact ready.2.2.1.closed
termination_by structural history

theorem WorldFrameHistory.nil_ready
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (controls : OriginalWorldControls strata sourceEnv)
    (closed : available.AtomClosed)
    (controlPrefix : controls.HasPrefix cutoff fuel) :
    (WorldFrameHistory.nil (U := U) (registry := registry) (target := target) (P := P)
      (locals := locals) (σ := σ) (τ := τ) (available := available) controls).Ready
      frontier cutoff fuel := ⟨closed, controlPrefix⟩

noncomputable def WorldBaseHistories.append
    (first : WorldBaseHistories strata U registry target P xs)
    (second : WorldBaseHistories strata U registry target P ys) :
    WorldBaseHistories strata U registry target P (xs ++ ys) := by
  match first with
  | .nil => exact second
  | .cons head tail => exact .cons head (tail.append second)
termination_by structural first

theorem WorldBaseHistories.ready_append
    (first : WorldBaseHistories strata U registry target P xs)
    (second : WorldBaseHistories strata U registry target P ys)
    (firstReady : first.Ready frontier cutoff fuel)
    (secondReady : second.Ready frontier cutoff fuel) :
    (first.append second).Ready frontier cutoff fuel := by
  cases first with
  | nil => exact secondReady
  | cons head tail => exact ⟨firstReady.1, tail.ready_append second firstReady.2 secondReady⟩
termination_by structural first

noncomputable def WorldBaseHistories.flatMap
    (indices : List α) (sites : α → List (WorldFrameSite strata U registry target))
    (histories : ∀ index, WorldBaseHistories strata U registry target P (sites index)) :
    WorldBaseHistories strata U registry target P (indices.flatMap sites) :=
  match indices with
  | [] => .nil
  | head :: tail => (histories head).append (WorldBaseHistories.flatMap tail sites histories)

theorem WorldBaseHistories.ready_flatMap
    (indices : List α) (sites : α → List (WorldFrameSite strata U registry target))
    (histories : ∀ index, WorldBaseHistories strata U registry target P (sites index))
    (ready : ∀ index ∈ indices, (histories index).Ready frontier cutoff fuel) :
    (WorldBaseHistories.flatMap indices sites histories).Ready frontier cutoff fuel := by
  induction indices with
  | nil => trivial
  | cons head tail ih =>
    exact (histories head).ready_append _ (ready head (List.mem_cons_self ..))
      (ih (fun index member => ready index (List.mem_cons_of_mem _ member)))

noncomputable def WorldBaseHistories.cast
    (histories : WorldBaseHistories strata U registry target P sites)
    (same : sites = next) : WorldBaseHistories strata U registry target P next :=
  same ▸ histories

theorem WorldBaseHistories.ready_cast
    (histories : WorldBaseHistories strata U registry target P sites)
    (same : sites = next) (ready : histories.Ready frontier cutoff fuel) :
    (histories.cast same).Ready frontier cutoff fuel := by
  cases same
  exact ready

/-- The finite reconstruction evidence on the exact generation selected by a
recursive call. Closing the visible resource table alone cannot create this
evidence: dormant histories and individual merge branches are retained too. -/
structure WorldGenerated.Hereditary
    {base : OriginalCaptureBase env U registry target}
    (generation : WorldGenerated strata P base caps left right graph frame controls)
    (frontier : List (World strata.rules.length)) where
  tablesClosed : generation.TablesClosed
  bases : WorldBaseHistories strata U registry target P generation.baseUses
  ready : bases.Ready frontier controls.cutoff controls.fuel

/-- Changing the common scope does not change a single stored frame site. -/
noncomputable def WorldGenerated.Hereditary.weaken
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {generation : WorldGenerated strata P base caps left right graph frame controls}
    (data : generation.Hereditary frontier)
    {nextCaps : CaptureCaps}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = left)
    (rightTail : Subst.lift_l ρ nextRight = right)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = caps) :
    (WorldGenerated.weaken generation insertion leftTail rightTail capsTail).Hereditary frontier :=
  ⟨data.tablesClosed, data.bases, data.ready⟩

/-- A merge retains both positional histories, even when their frame sites
are equal. Neither branch's table closure is inferred from the merged table. -/
noncomputable def WorldGenerated.Hereditary.merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {firstFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ firstAvailable}
    {secondFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ secondAvailable}
    {first : WorldGenerated strata P base caps left right graph firstFrame controls}
    {second : WorldGenerated strata P base caps left right graph secondFrame controls}
    (firstData : first.Hereditary frontier)
    (secondData : second.Hereditary frontier) :
    (WorldGenerated.merge first second).Hereditary frontier :=
  ⟨⟨firstData.tablesClosed, secondData.tablesClosed⟩,
    firstData.bases.append secondData.bases,
    firstData.bases.ready_append secondData.bases firstData.ready secondData.ready⟩

/-- Closed empty generation creates the stronger invariant internally. -/
def WorldGenerated.emptyBaseHistories
    {base : OriginalCaptureBase env U registry target}
    (common : List VExpr) (left right : Subst) (below : sourceEnv ≤ env)
    (source : P sourceEnv) (controls : OriginalWorldControls strata sourceEnv) :
    WorldBaseHistories strata U registry target P
      (WorldGenerated.empty (base := base) (commonCaps := caps)
        common left right below source controls).baseUses := .nil

/-- The exact old generation is retained when creating a unary identity
sandbox. Thus a later paired reconstruction can structurally unwrap its base;
it does not have to recover original owners from an untyped numeric ledger. -/
theorem WorldGenerated.identitySandboxWithHistory
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (bases : WorldBaseHistories strata U registry target P generated.baseUses)
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (tablesClosed : generated.TablesClosed)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (basesReady : bases.Ready frontier controls.cutoff controls.fuel) :
    let sandbox := frame.captureBase substitutions
    ∃ identity : WorldGenerated strata P sandbox sandbox.initialCaps σ τ
        (.identity context) frame.raw controls,
      identity.worlds = generated.worlds ∧
      identity.TablesClosed ∧
      (∃ ancestry : WorldBaseHistories strata U registry target P identity.baseUses,
        ancestry.Ready frontier controls.cutoff controls.fuel) ∧
      identity.UsesControlPrefix controls.cutoff controls.fuel ∧
      Nonempty (identity.Controlled frontier) := by
  let sandbox := frame.captureBase substitutions
  let identity : WorldGenerated strata P sandbox sandbox.initialCaps σ τ
      (.identity context) frame.raw controls :=
    WorldGenerated.identity (base := sandbox) generated.erase.ambientGenerated.ambient.2
      generated.erase.sources.2 controls generated.environment
  let ancestry : WorldBaseHistories strata U registry target P identity.baseUses :=
    .cons (.generated generated bases) .nil
  obtain ⟨annotation, sponsored⟩ :=
    ready.annotation.sponsored_subset ready.sponsored generated.storedQueries_in_retained
  have ancestryReady : ancestry.Ready frontier controls.cutoff controls.fuel := by
    simp only [ancestry, WorldBaseHistories.Ready, WorldFrameHistory.Ready]
    exact ⟨⟨⟨ready⟩, replayable, tablesClosed, compatible, basesReady⟩, trivial⟩
  refine ⟨identity, rfl, tablesClosed.closed, ⟨ancestry, ancestryReady⟩,
    ⟨rfl, rfl⟩, ⟨⟨annotation, ?_, sponsored⟩⟩⟩
  intro control active
  have smaller := StoredOriginalQuery.maximumDepth_mono
    (stratifiedHeadPolicy (strata.headOrdinal registry) control) generated.storedQueries_in_retained
  rw [RawOriginalRichFrame.storedQueries_depth, generated.retainedQueries_depth] at smaller
  exact Nat.le_trans smaller (ready.within control active)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
