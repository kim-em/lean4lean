import Lean4Lean.Theory.Typing.AnchoredNativeSpineCertificate

/-! Backward family-header requests retain actual argument observations in
addition to the cuts needed by the residual type. The finite input grade is
the maximum of those two grades; interpreting the ORIGINAL argument child
then produces the domain certificate at that exact grade.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- One actual perargument request, including its finite source footprint. -/
structure FamilyArgumentRequest (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (argument : VExpr) where
  rank : Nat
  input : Profile rank
  footprint : Footprint
  observation : Obs env U registry target locals σ argument input footprint
  resources : footprint.Available available

/-- The resulting Pi row can ask for more argument information than its
codomain needs. Its binder pack therefore records the actual smaller cuts,
with literal inclusion into the retained full input. -/
structure FamilyApplicationInput (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (A B a : VExpr)
    (result : Profile n) (before : Footprint)
    (request : FamilyArgumentRequest env U registry target locals σ available a) where
  residual : CodeCert env U registry target locals σ (B.inst a) result before
  required : Footprint
  cuts : InstFootprint env U registry target locals σ a 0 before required
  factored : FactoredArguments env U registry target locals σ available a required n
  rank : Nat
  rank_eq : rank = max factored.rank request.rank
  outputBound : n ≤ rank
  cutBound : factored.rank ≤ rank
  requestBound : request.rank ≤ rank
  input : Profile rank
  input_eq : input = (raiseProfile rank cutBound factored.input).union
    (raiseProfile rank requestBound request.input)
  argumentFootprint : Footprint
  argumentObservation : Obs env U registry target locals σ a input argumentFootprint
  argumentAvailable : argumentFootprint.Available available
  support : Profile rank
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals σ A support domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A ⟨A.subst σ, a.subst σ, input⟩ support
  body : CodeCert env U registry target (Locals.push locals) (σ.cons (a.subst σ)) B
    (raiseProfile rank outputBound result) required

namespace FamilyApplicationInput
variable (frame : FamilyApplicationInput env U registry target locals σ available A B a
  (result : Profile n) before request)

def key : Key frame.rank := ⟨A.subst σ, a.subst σ, frame.input⟩

def profile : Profile (frame.rank + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support
    [(frame.key, raiseProfile frame.rank frame.outputBound result)]

def footprint : Footprint := frame.domainFootprint ++ frame.factored.outside

theorem cutCovered : ∀ atom ∈ (raiseProfile frame.rank frame.cutBound frame.factored.input).atoms,
    atom ∈ frame.input.atoms := by
  rw [frame.input_eq]
  exact fun _ member => List.mem_append_left _ member

/-- Every explicit requested argument atom occurs in the resulting row key;
the producer cannot silently replace a nonempty request by its type cuts. -/
theorem requestCovered : ∀ atom ∈ (raiseProfile frame.rank frame.requestBound request.input).atoms,
    atom ∈ frame.key.input.atoms := by
  change ∀ atom ∈ _, atom ∈ frame.input.atoms
  rw [frame.input_eq]
  exact fun _ member => List.mem_append_right _ member

noncomputable def certificate : CodeCert env U registry target locals σ (.forallE A B)
    frame.profile frame.footprint := by
  apply CodeCert.piLiteral frame.domain
  simpa only [List.append_nil, key] using
    PiRows.cons frame.guard frame.body (frame.factored.pack.raise frame.cutBound)
      frame.cutCovered PiRows.nil

theorem resources : frame.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.domainAvailable i need)
    (frame.factored.outsideAvailable i need)

end FamilyApplicationInput

private theorem one_comp (a : VExpr) (σ : Subst) :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  funext i; cases i <;> rfl

/-- Actual finite extra-request producer. All newly obtained semantics and
domain code come from the original argument child, applied to the union of
its stored request and the residual certificate's actual inverse cuts. -/
theorem CodeCert.familyApplicationInput
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B a : VExpr}
    (argument : OriginalTypePayload sourceEnv env U registry source a A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (request : FamilyArgumentRequest env U registry target locals σ available a)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ (B.inst a) result before)
    (resources : before.Available available) :
    Nonempty (FamilyApplicationInput env U registry target locals σ available A B a
      result before request) := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := certificate.factorInst B a 0 rfl σ rfl locals (Locals.push locals)
  simp only [Subst.liftN, one_comp] at body
  obtain ⟨packed⟩ := cuts.arguments available resources n
  let rank := max packed.rank request.rank
  have cutBound : packed.rank ≤ rank := Nat.le_max_left _ _
  have requestBound : request.rank ≤ rank := Nat.le_max_right _ _
  have outputBound : n ≤ rank := Nat.le_trans packed.bound cutBound
  let input := (raiseProfile rank cutBound packed.input).union
    (raiseProfile rank requestBound request.input)
  have observation : Obs env U registry target locals σ a input
      (packed.argumentFootprint ++ request.footprint) :=
    .union (packed.observation.raise cutBound) (request.observation.raise requestBound)
  have observationAvailable : (packed.argumentFootprint ++ request.footprint).Available available := by
    intro i need member
    exact (List.mem_append.mp member).elim (packed.argumentAvailable i need) (request.resources i need)
  obtain ⟨value⟩ := (argument.2 target locals σ σ available closed hTarget substitutions fits).1
    observation observationAvailable
  have raw := (argument.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have related := value.requestedRelated henv hTarget
  have domain := value.requestedCertificate
  have code := TypeRelated.lower henv value.bound value.typeCode
  exact ⟨{
    residual := certificate
    required := required
    cuts := cuts
    factored := packed
    rank := rank
    rank_eq := rfl
    outputBound := outputBound
    cutBound := cutBound
    requestBound := requestBound
    input := input
    input_eq := rfl
    argumentFootprint := packed.argumentFootprint ++ request.footprint
    argumentObservation := observation
    argumentAvailable := observationAvailable
    support := lowerProfile rank value.bound value.support
    domainFootprint := value.typeFootprint
    domain := domain
    domainAvailable := value.typeAvailable
    guard := ⟨value.requestedTyped, domain.formed, .refl, code,
      ⟨raw, raw, _, value.requestedTyped, domain.formed, code, related, related⟩⟩
    body := body.raise outputBound }⟩

end Lean4Lean.AnchoredSource.Adapted
