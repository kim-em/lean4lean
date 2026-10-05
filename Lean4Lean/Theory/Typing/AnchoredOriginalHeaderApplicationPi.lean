import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationPiRows

/-! Assemble all finite dependent header Pi rows from actual application
seed ledgers. The domain is an exact original-child answer; arbitrary-argument
body semantics and every outgoing rich certificate are reconstructed here.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive HeaderApplicationPiRows
    {seedEnv : VEnv} {U : Nat}
    (root : EndpointRef seedEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (σ : Subst) (available : Valuation) (A : VExpr) (functionIndex : Nat)
    (relevant : Bool) (ambient : Profile n) : List (Key n × Profile n) → Type where
  | nil : HeaderApplicationPiRows root env registry target σ available A functionIndex relevant ambient []
  | cons (head : HeaderApplicationPiRow root env registry target σ available A functionIndex
        relevant ambient key output)
      (tail : HeaderApplicationPiRows root env registry target σ available A functionIndex
        relevant ambient rows) :
      HeaderApplicationPiRows root env registry target σ available A functionIndex relevant ambient ((key, output) :: rows)

variable {seedEnv : VEnv} {U : Nat}
  {root : EndpointRef seedEnv U rootSource rootExpression rootType}

theorem HeaderApplicationPiRows.lookup
    (rows : HeaderApplicationPiRows root env registry target σ available A functionIndex relevant ambient values)
    (member : (key, output) ∈ values) :
    Nonempty (HeaderApplicationPiRow root env registry target σ available A functionIndex relevant ambient key output) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact ⟨head⟩
    · exact ih member

noncomputable def RichRows.append
    (first : RichRows sourceEnv env U registry target domain body locals σ relevant ambient firstValues firstFootprint)
    (second : RichRows sourceEnv env U registry target domain body locals σ relevant ambient secondValues secondFootprint) :
    RichRows sourceEnv env U registry target domain body locals σ relevant ambient
      (firstValues ++ secondValues) (firstFootprint ++ secondFootprint) := by
  match first with
  | .nil => exact second
  | .cons guard code pack covered rest =>
    simpa only [List.cons_append, List.append_assoc] using
      RichRows.cons guard code pack covered (rest.append second)
termination_by sizeOf first

theorem HeaderApplicationPiRows.reconstruct
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (rows : HeaderApplicationPiRows root env registry target σ available A functionIndex relevant ambient values) :
    ∃ footprint,
      Nonempty (RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient
        values footprint) ∧ footprint.Available available := by
  induction rows with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons head tail ih =>
    obtain ⟨headFootprint, ⟨headCode⟩, headResources⟩ := head.reconstruct henv hscoped headerBelow formed
      substitutions frame domain location lineage body domainCode domainResources functionLookup
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailResources⟩ := ih
    refine ⟨headFootprint ++ tailFootprint, ⟨headCode.append tailCode⟩, ?_⟩
    intro index need member
    exact (List.mem_append.mp member).elim (headResources index need) (tailResources index need)

/-- Complete finite-row introduction for a dependent header `Π x : A, F x`.
All body seeds retain their original source roots, query paths and grades;
replay produces both code at the actual original header and all future rows.
The domain answer is the fixed original domain child's concrete output. -/
theorem HeaderBinderFrame.applicationPi
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (domainAnswer : RichCodeTransferResult env U registry target (.ref domain) (.ref domain)
      locals σ σ available true (ambient : Profile n))
    (prototype : PiGuard env U target σ A (.app (.bvar (functionIndex + 1)) (.bvar 0))
      prototypeDomain prototypeBody)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (rows : HeaderApplicationPiRows root env registry target σ available A functionIndex relevant ambient values) :
    ∃ footprint,
      Nonempty (RichCert headerEnv env U registry target (.pi hu hv (.ref domain) body) locals σ relevant
        (Profile.pi prototypeDomain prototypeBody ambient values) footprint) ∧
      footprint.Available available ∧
      TypeRelated env U registry target
        ((VExpr.forallE A (.app (.bvar (functionIndex + 1)) (.bvar 0))).subst σ)
        ((VExpr.forallE A (.app (.bvar (functionIndex + 1)) (.bvar 0))).subst σ)
        (Profile.pi prototypeDomain prototypeBody ambient values) := by
  obtain ⟨rowFootprint, ⟨rowCode⟩, rowResources⟩ := rows.reconstruct henv hscoped headerBelow formed
    substitutions frame domain location lineage body domainAnswer.certificate domainAnswer.resources functionLookup
  refine ⟨_, ⟨.pi hu hv domainAnswer.certificate prototype rowCode⟩, ?_, ?_⟩
  · intro index need member
    exact (List.mem_append.mp member).elim (domainAnswer.resources index need) (rowResources index need)
  · have originalDomain := domain.sound.defeq.mono headerBelow
    have originalBody := body.sound.defeq.mono headerBelow
    have hA := originalDomain.subst henv substitutions formed
    have hB := originalBody.subst henv (substitutions.lift henv originalDomain) ⟨formed, _, hA⟩
    apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
      .refl .refl prototype.domainPath prototype.bodyPath domainAnswer.related
    · intro key output member
      obtain ⟨row⟩ := rows.lookup member
      exact ⟨ambient, row.guard.inputTyped, domainAnswer.certificate.formed, Profile.le_refl _,
        row.guard.path, row.guard.domains⟩
    · intro key output member Δ ρ future x y admitted
      obtain ⟨row⟩ := rows.lookup member
      have pair := row.capability henv hscoped headerBelow substitutions frame domain location lineage
        body domainAnswer.certificate domainAnswer.resources functionLookup future admitted
      exact ⟨pair, pair, pair.left_diagonal⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
