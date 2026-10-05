import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrence

/-! A finite construction trace for the actual frames emitted by source
query traversal. Only the retained original binder constructor extends the
fixed incoming frame; arbitrary equal target substitutions do not suffice. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive OriginalFrameExtension
    {baseContext : ContextDerivation sourceEnv U baseSource}
    (base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable) :
    {source : List VExpr} → {context : ContextDerivation sourceEnv U source} →
    {locals : List Nat} → {σ τ : Subst} → {available : Valuation} →
    RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available → Type where
  | refl : OriginalFrameExtension base base
  | bind {context : ContextDerivation sourceEnv U source}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (previous : OriginalFrameExtension base tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      OriginalFrameExtension base (.bind tail domain certificate resources typed arguments needs bounded covered)

def OriginalFrameExtension.length
    (extension : OriginalFrameExtension base frame) : Nat :=
  match extension with
  | .refl => 0
  | .bind previous .. => previous.length + 1

def OriginalFrameExtension.prefix
    (extension : OriginalFrameExtension base frame) : List VExpr :=
  match extension with
  | .refl => []
  | .bind (A := A) previous .. => A :: previous.prefix

theorem OriginalFrameExtension.prefix_length
    (extension : OriginalFrameExtension base frame) : extension.prefix.length = extension.length := by
  induction extension with
  | refl => rfl
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    simpa only [OriginalFrameExtension.prefix, length, List.length_cons] using congrArg (· + 1) ih

theorem OriginalFrameExtension.source_eq
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension base frame) : source = extension.prefix ++ baseSource := by
  induction extension with
  | refl => rfl
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    simpa only [OriginalFrameExtension.prefix, List.cons_append] using congrArg (_ :: ·) ih

/-- The entire original substitution tail is retained, independently of the
particular query expression or of any coincidence after realization. -/
theorem OriginalFrameExtension.sourceTail
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension base frame) :
    Subst.lift_l (.skipN .refl extension.length) σ = baseLeft ∧
    Subst.lift_l (.skipN .refl extension.length) τ = baseRight := by
  induction extension with
  | refl => exact ⟨rfl, rfl⟩
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    exact ⟨capture_tail_cons _ _ _ _ ih.1, capture_tail_cons _ _ _ _ ih.2⟩

noncomputable def OriginalFrameExtension.trans
    {firstContext : ContextDerivation sourceEnv U firstSource}
    {first : RawOriginalRichFrame sourceEnv env U registry target firstContext firstLocals firstLeft firstRight firstAvailable}
    {middleContext : ContextDerivation sourceEnv U middleSource}
    {middle : RawOriginalRichFrame sourceEnv env U registry target middleContext middleLocals middleLeft middleRight middleAvailable}
    {lastContext : ContextDerivation sourceEnv U lastSource}
    {last : RawOriginalRichFrame sourceEnv env U registry target lastContext lastLocals lastLeft lastRight lastAvailable}
    (left : OriginalFrameExtension first middle) (right : OriginalFrameExtension middle last) :
    OriginalFrameExtension first last := by
  induction right with
  | refl => exact left
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    exact .bind ih domain certificate resources typed arguments needs bounded covered


noncomputable def OriginalFrameExtension.route
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U occurrenceSource expression assigned}
    {last : EndpointState sourceEnv U occurrenceSource expression natural}
    {location : Located root first}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (route : PrefixRoute sourceEnv U occurrenceSource expression first last)
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    OriginalFrameExtension base (occurrence.route route).frame.raw := by
  induction route with
  | done => exact extension
  | expose reference rest ih => exact ih _ extension
  | convert plan term rest ih => exact ih _ extension

noncomputable def OriginalFrameExtension.locationCast
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {first last : Located root node}
    (same : first = last)
    (occurrence : OriginalRichOccurrenceFrame first initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    OriginalFrameExtension base (same ▸ occurrence).frame.raw := by
  cases same
  exact extension

noncomputable def OriginalFrameExtension.piAnchor
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    OriginalFrameExtension base (occurrence.piAnchor henv sourceBelow certificate resources guard pack covered).frame.raw := by
  exact .bind extension _ _ _ _ _ _ _ _

noncomputable def OriginalFrameExtension.lamAnchor
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    OriginalFrameExtension base (occurrence.lamAnchor henv sourceBelow certificate resources guard pack covered).frame.raw := by
  exact .bind extension _ _ _ _ _ _ _ _


/-- Every listed occurrence has an actual finite sequence of original binder
extensions above the same input frame. -/
def AllFrameExtensions
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {baseContext : ContextDerivation sourceEnv U baseSource}
    (base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable)
    (entries : List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)) : Prop :=
  ∀ entry ∈ entries, Nonempty (OriginalFrameExtension base entry.occurrence.frame.raw)

theorem AllFrameExtensions.nil
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {initialContext : ContextDerivation sourceEnv U source}
    {ordered : sourceEnv.Ordered} {initialEnvironment : List Closure}
    {rootLeft rootRight : Subst}
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable} :
    AllFrameExtensions (root := root) (initialContext := initialContext)
      (ordered := ordered) (initialEnvironment := initialEnvironment)
      (rootLeft := rootLeft) (rootRight := rootRight) base [] := by
  intro entry member
  cases member

theorem AllFrameExtensions.cons
    (extension : OriginalFrameExtension base entry.occurrence.frame.raw)
    (tail : AllFrameExtensions base entries) : AllFrameExtensions base (entry :: entries) := by
  intro found member
  rcases List.mem_cons.mp member with same | member
  · subst found; exact ⟨extension⟩
  · exact tail found member

theorem AllFrameExtensions.append
    (left : AllFrameExtensions base first) (right : AllFrameExtensions base second) :
    AllFrameExtensions base (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact left entry member
  · exact right entry member


/-- The same trace property on the actual mutually stored owner ledger. -/
def RawRichGroupEntries.FrameExtensions
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {baseContext : ContextDerivation sourceEnv U baseSource}
    (base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Prop :=
  match entries with
  | .nil => True
  | .cons entry tail => Nonempty (OriginalFrameExtension base entry.frame) ∧ tail.FrameExtensions base

@[simp] theorem richGroupedEntriesRaw_frameExtensions
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)) :
    (richGroupedEntriesRaw entries).FrameExtensions base ↔
      ∀ entry ∈ entries, Nonempty (OriginalFrameExtension base entry.frame.raw) := by
  induction entries with
  | nil => simp [richGroupedEntriesRaw, RawRichGroupEntries.FrameExtensions]
  | cons entry entries ih =>
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.FrameExtensions, List.mem_cons,
      forall_eq_or_imp, ← ih]
    rfl


theorem OriginalFrameExtension.insertion
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension base frame) :
    Ctx.Lift' (.skipN .refl extension.length) baseSource source := by
  induction extension with
  | refl => exact .refl
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    exact .skip ih

/-- The actual owner trace establishes both complete realization tails and
the displayed value of the captured source expression. This does not use
an equality between two already-realized target expressions as provenance. -/
theorem RichGroupedCaptureEntry.extensionRealizations
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation sourceEnv U source}
    {base : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (extension : OriginalFrameExtension base entry.frame.raw) :
    extension.length = entry.depth ∧
      Subst.lift_l (.skipN .refl entry.depth) entry.ownerLeft = σ ∧
      Subst.lift_l (.skipN .refl entry.depth) entry.ownerRight = τ ∧
      leftValue = rawCapture.subst σ ∧ rightValue = rawCapture.subst τ := by
  have lengthEq : extension.length = entry.depth := by
    have first := congrArg List.length extension.source_eq
    have second := congrArg List.length entry.source_eq
    simp only [List.length_append, extension.prefix_length, ← entry.depth_eq] at first second
    omega
  have tails := extension.sourceTail
  rw [lengthEq] at tails
  refine ⟨lengthEq, tails.1, tails.2, ?_, ?_⟩
  · rw [← entry.left_eq, entry.expression_eq, subst_lift', tails.1]
  · rw [← entry.right_eq, entry.expression_eq, subst_lift', tails.2]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
