import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFuture

/-! Paired rich header frames retain both actual source-certificate
directions. This is needed under nested dependent binders: a frame's right
certificate cannot be obtained by relabelling its left realization.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def RichBinderValue.leftDiagonal
    (value : RichBinderValue sourceEnv env U registry target node locals left right available input) :
    RichBinderValue sourceEnv env U registry target node locals left left available input :=
  { value with related := value.related.left_diagonal }

def HeaderValueAlignment.leftDiagonal
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerLeft declaredLeft ownerAvailable headerAvailable input :=
  { answer with value := answer.value.leftDiagonal }

def HeaderRichTail.leftDiagonal
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    HeaderRichTail header field major env registry target context locals left left available := by
  match tail with
  | .nil => exact .nil
  | .skip tail domain location lineage arguments =>
    exact .skip tail.leftDiagonal domain location lineage arguments.hasType.1
  | .push tail domain location lineage owner answer arguments needs bounded covered =>
    exact .push tail.leftDiagonal domain location lineage owner answer.leftDiagonal
      arguments.left_diagonal needs bounded covered
termination_by sizeOf tail

def HeaderBinderFrame.leftDiagonal
    (frame : HeaderBinderFrame header field major env registry target context locals left right available) :
    HeaderBinderFrame header field major env registry target context locals left left available := by
  match frame with
  | .captured tail => exact .captured tail.leftDiagonal
  | .bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    exact .bind tail.leftDiagonal domain location lineage certificate resources typed
      arguments.left_diagonal needs bounded covered
termination_by sizeOf frame

structure HeaderPairedFrame
    {headerEnv sourceEnv : VEnv} {U : Nat}
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {headerSource : List VExpr} (context : ContextDerivation headerEnv U headerSource)
    (locals : List Nat) (left right : Subst) (available : Valuation) where
  forward : HeaderBinderFrame header field major env registry target context locals left right available
  backward : HeaderBinderFrame header field major env registry target context locals right left available

def HeaderPairedFrame.symm
    (frame : HeaderPairedFrame header field major env registry target context locals left right available) :
    HeaderPairedFrame header field major env registry target context locals right left available :=
  ⟨frame.backward, frame.forward⟩

def HeaderPairedFrame.left
    (frame : HeaderPairedFrame header field major env registry target context locals σ τ available) :
    HeaderPairedFrame header field major env registry target context locals σ σ available :=
  ⟨frame.forward.leftDiagonal, frame.forward.leftDiagonal⟩

def HeaderPairedFrame.right
    (frame : HeaderPairedFrame header field major env registry target context locals σ τ available) :
    HeaderPairedFrame header field major env registry target context locals τ τ available :=
  frame.symm.left

noncomputable def HeaderPairedFrame.future
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (frame : HeaderPairedFrame header field major env registry Γ context locals σ τ available) :
    HeaderPairedFrame header field major env registry Δ context locals (σ.lift_r ρ) (τ.lift_r ρ)
      (available.rename ρ) :=
  ⟨frame.forward.future henv future, frame.backward.future henv future⟩

private theorem admitted_reverse
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target key y x := by
  obtain ⟨anchorRaw, pairRaw, support, typed, formed, code, anchor, pair⟩ := admitted
  exact ⟨anchorRaw.trans pairRaw, pairRaw.symm, support, typed, formed, code,
    Related.trans henv hscoped anchor pair, Related.symm henv pair⟩

/-- The original incoming domain certificate and the fixed domain child's
actual transferred certificate build both binder directions. The right
guard is derived from that same transfer, not assumed separately. -/
theorem HeaderPairedFrame.pushAdmitted
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (frame : HeaderPairedFrame header field major env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (certificate : RichCert headerEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available)
    (answer : RichCodeTransferResult env U registry target (.ref domain) (.ref domain)
      locals σ τ available true support)
    (guard : LambdaGuard env U registry target σ A key support)
    (admitted : Admitted env U registry target key x y)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Nonempty (HeaderPairedFrame header field major env registry target (.cons context domain)
      (Locals.push locals) (σ.cons x) (τ.cons y) (available.push needs)) ∧
    Ctx.SubstEq env U target (σ.cons x) (τ.cons y) (A :: headerSource) := by
  have raw := (domain.sound.defeq.mono headerBelow).substDF henv substitutions.wf formed substitutions
  have rightGuard : LambdaGuard env U registry target τ A key support :=
    ⟨guard.inputTyped, guard.formed, guard.path.trans (.single raw),
      guard.domains.trans henv answer.related, guard.anchor⟩
  obtain ⟨⟨forward⟩, paired⟩ := frame.forward.pushAdmitted henv headerBelow substitutions domain
    location lineage certificate resources guard admitted needs bounded covered
  obtain ⟨⟨backward⟩, _⟩ := frame.backward.pushAdmitted henv headerBelow (substitutions.symm henv formed)
    domain location lineage answer.certificate answer.resources rightGuard
    (admitted_reverse henv hscoped admitted) needs bounded covered
  exact ⟨⟨⟨forward, backward⟩⟩, paired⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
