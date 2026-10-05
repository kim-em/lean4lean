import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! Native Pi source reconstruction from finite returned original-body
queries. Every binder pack and external footprint is computed from the
returned resources. Projected, applied and action-transformed body queries
remain rich syntax at the same original body endpoint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure RichPiRowResult
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A B : VExpr} {v : VLevel}
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (ambient : Profile n) (key : Key n) (output : Profile n) where
  guard : LambdaGuard env U registry target σ A key ambient
  formed : output.HasType (.sort relevant)
  needs : List Need
  bounded : ∀ need ∈ needs, need.rank ≤ n
  covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms
  result : RichGradedResult sourceEnv env U registry target body (Locals.push locals)
    (σ.cons key.anchor) (available.push needs) output

inductive RichPiRowResults
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A B : VExpr} {v : VLevel}
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (ambient : Profile n) : List (Key n × Profile n) → Type where
  | nil : RichPiRowResults sourceEnv env U registry target body locals σ available relevant ambient []
  | cons (head : RichPiRowResult sourceEnv env U registry target body locals σ available
        relevant ambient key output)
      (tail : RichPiRowResults sourceEnv env U registry target body locals σ available relevant ambient rows) :
      RichPiRowResults sourceEnv env U registry target body locals σ available relevant ambient ((key, output) :: rows)

/-- Reconstruct the exact row query, with its actual source-local demands
packed at the row's declared rank. No pack or outgoing certificate is assumed. -/
theorem RichPiRowResults.reconstruct
    (henv : env.Ordered)
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (results : RichPiRowResults sourceEnv env U registry target body locals σ available relevant ambient rows) :
    ∃ footprint, Nonempty (RichRows sourceEnv env U registry target domain body locals σ
      relevant ambient rows footprint) ∧ footprint.Available available := by
  induction results with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons head tail ih =>
    obtain ⟨bodyFootprint, ⟨bodyCode⟩, bodyAvailable⟩ := head.result.code henv head.formed
    obtain ⟨packed, outside, pack, covered, outsideAvailable⟩ :=
      Footprint.pack_available bodyAvailable head.bounded head.covered
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailAvailable⟩ := ih
    refine ⟨outside ++ tailFootprint, ⟨.cons head.guard bodyCode pack covered tailCode⟩, ?_⟩
    intro index need member
    exact (List.mem_append.mp member).elim (outsideAvailable index need) (tailAvailable index need)

/-- Assemble a native rich Pi at its actual original domain/body nodes,
including an empty row list. Both exact source certificates are reconstructed
from the finite generalized results of those fixed children. -/
theorem RichGradedResult.pi
    (henv : env.Ordered)
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domainResult : RichGradedResult sourceEnv env U registry target domain locals σ available ambient)
    (ambientFormed : ambient.HasType (.sort true))
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichPiRowResults sourceEnv env U registry target body locals σ available relevant ambient values) :
    ∃ footprint, Nonempty (RichCert sourceEnv env U registry target (.pi hu hv domain body)
      locals σ relevant (Profile.pi prototypeDomain prototypeBody ambient values) footprint) ∧
      footprint.Available available := by
  obtain ⟨domainFootprint, ⟨domainCode⟩, domainAvailable⟩ := domainResult.code henv ambientFormed
  obtain ⟨rowFootprint, ⟨rowCode⟩, rowAvailable⟩ := rows.reconstruct (domain := domain) henv
  refine ⟨domainFootprint ++ rowFootprint, ⟨.pi hu hv domainCode guard rowCode⟩, ?_⟩
  intro index need member
  exact (List.mem_append.mp member).elim (domainAvailable index need) (rowAvailable index need)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
