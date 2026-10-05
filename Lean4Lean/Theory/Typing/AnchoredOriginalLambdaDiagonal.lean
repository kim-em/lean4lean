import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaFrames
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental

/-! Formation diagonals for literal natural Pi queries use only fixed
original domain/codomain F obligations at exact captured source tails. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem renameCovered {p q : Profile n}
    (covered : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (ρ : Lift) :
    ∀ atom ∈ (p.rename ρ).atoms, atom ∈ (q.rename ρ).atoms := by
  intro atom member
  obtain ⟨old, originalMember, equal⟩ := List.mem_map.mp member
  cases equal
  exact List.mem_map_of_mem (covered old originalMember)

private theorem bodyAt
    {n : Nat} {ambient output packed : Profile n} {key : Key n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (body : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor) B output bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainResources : domainFootprint.Available available)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key z z) :
    TypeRelated env U registry target (B.subst (σ.cons key.anchor)) (B.subst (σ.cons z)) output := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  let needs := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  let frame := (TailPairedFits.diagonal context tail).pushCertificates originalDomain
    domain domain domainResources domainResources guard.inputTyped guard.inputTyped
    arguments (arguments.symm henv) needs
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons z) (A :: source) :=
    .cons substitutions (originalDomain.sound.defeq.mono hle) (guard.path.cast raw)
  have child : GradedTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons z) (Valuation.push needs available) B B (.sort bodyLevel) := (bodyIH target (Locals.push locals) (σ.cons key.anchor) (σ.cons z)
    (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired frame).1
  obtain ⟨answer⟩ := body.transfer_graded henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) child (pack.available_atomized_localNeeds resources)
  exact answer.related

private theorem rowBehavior
    {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (rows : PiRows env U registry target locals σ A B ambient table rowFootprint)
    (domainResources : domainFootprint.Available available)
    (resources : rowFootprint.Available available) :
    ∀ key output, (key, output) ∈ table →
      ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
        Admitted env U registry Δ (key.rename ρ) x y →
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B.subst σ.lift).lift' ρ.cons).inst y) (output.rename ρ) := by
  intro key output member
  match rows with
  | .nil => cases member
  | .cons guard body pack covered rest =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      intro Δ ρ future x y admitted
      have domain' := domain.future henv future
      have guard' := guard.future henv future
      have body' := body.future henv future
      simp only [subst_cons_future] at body'
      have pack' := pack.rename ρ
      have covered' := renameCovered covered ρ
      have outsideResources := fun i need member => resources i need (List.mem_append_left _ member)
      have atArgument := fun z admitted => bodyAt henv hscoped hle context originalDomain originalBody bodyIH
        (closed.rename ρ) (future.targetWF henv) (substitutions.future henv future)
        (tail.future henv future) domain' guard' body' pack' covered'
        (domainResources.rename ρ) (Footprint.Available.rename outsideResources ρ) (z := z) admitted
      have rightAdmission : Admitted env U registry Δ (key.rename ρ) y y := by
        obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
        exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
          Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩
      have left := atArgument x admitted.left_diagonal
      have right := atArgument y rightAdmission
      simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using
        (left.symm henv body'.formed.wf_value).trans henv right
    · exact rowBehavior henv hscoped hle context originalDomain originalBody bodyIH
        closed hTarget substitutions tail domain rest domainResources
        (fun i need present => resources i need (List.mem_append_right _ present)) key output member
termination_by sizeOf rows

private theorem rowDomains
    (rows : PiRows env U registry target locals σ A B ambient table rowFootprint)
    (member : (key, output) ∈ table) :
    key.input.HasType ambient ∧ TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact ⟨guard.inputTyped, guard.path, guard.domains⟩
    · exact rowDomains tail member
termination_by sizeOf rows

theorem CodeCert.piDiagonalOriginal
    {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : PiRows env U registry target locals σ A B ambient table rowFootprint)
    (domainResources : domainFootprint.Available available)
    (resources : rowFootprint.Available available) :
    TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) (Profile.pi prototypeDomain prototypeBody ambient table) := by
  have formedA := originalDomain.sound.defeq.mono hle
  have formedB := originalBody.sound.defeq.mono hle
  have hA := formedA.subst henv substitutions.left hTarget
  have hBodyTarget : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨hTarget, _, hA⟩
  have hB := formedB.subst henv (substitutions.left.lift henv formedA) hBodyTarget
  have domainChild : GradedTransfer env U registry target locals σ σ available
      A A (.sort domainLevel) := (domainIH target locals σ σ available closed hTarget substitutions
    (TailPairedFits.diagonal context tail)).1
  obtain ⟨domainAnswer⟩ := domain.transfer_graded henv hscoped hTarget closed domainChild domainResources
  apply TypeRelated.literalPiPair henv hTarget ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩ .refl .refl
    guard.domainPath guard.bodyPath domainAnswer.related
  · intro key output member
    obtain ⟨typed, path, related⟩ := rowDomains rows member
    exact ⟨ambient, typed, domain.formed, Profile.le_refl _, path, related⟩
  · intro key output member Δ ρ future x y admitted
    have diagonal := rowBehavior henv hscoped hle context originalDomain originalBody bodyIH
      closed hTarget substitutions tail domain rows domainResources resources key output member
      Δ ρ future x y admitted
    exact ⟨diagonal, diagonal, diagonal.left_diagonal⟩

/-- Use the exact formation children retained in this lambda view. -/
theorem LamView.piDiagonal
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (domainIH : StateFundamental env registry (view.location.contextDerivation initial) view.domain)
    (bodyIH : StateFundamental env registry
      ((Located.lamCodomain view.location).contextDerivation initial) view.codomain)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : PiGuard env U target σ A view.bodyType prototypeDomain prototypeBody)
    (rows : PiRows env U registry target locals σ A view.bodyType ambient table rowFootprint)
    (domainResources : domainFootprint.Available available)
    (resources : rowFootprint.Available available) :
    TypeRelated env U registry target ((VExpr.forallE A view.bodyType).subst σ)
      ((VExpr.forallE A view.bodyType).subst σ)
      (Profile.pi prototypeDomain prototypeBody ambient table) := by
  let originalDomain := Classical.choose view.location.originalDomains.1
  have domainEq := Classical.choose_spec view.location.originalDomains.1
  have originalIH : EndpointFundamental env registry
      (view.location.contextDerivation initial) originalDomain := by
    change StateFundamental env registry (view.location.contextDerivation initial) (.ref originalDomain)
    rw [← domainEq]
    exact domainIH
  exact CodeCert.piDiagonalOriginal henv hscoped hle (view.location.contextDerivation initial)
    originalDomain view.codomain originalIH bodyIH closed hTarget substitutions tail
    domain guard rows domainResources resources

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
