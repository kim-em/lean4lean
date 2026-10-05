import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionObserverReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixApplication

/-! A constructor argument frame keeps projected source queries throughout
packing. Its input is fixed only after the seed and all reindexed cuts have
been joined. The resulting Pi code uses the ordinary finite BinderPack;
there is no coercion of the new projection query to legacy Obs.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ProjectionArgumentSeed
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) where
  rank : Nat
  demand : Profile rank
  footprint : Footprint
  query : ProjectionObs env registry target node locals σ demand footprint
  resources : footprint.Available available

/-- These are the actual reconstructed cut queries, not just their erased
profiles. An external resource stays outside the new argument binder. -/
inductive ProjectionCuts
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) : Footprint → Footprint → Footprint → Type where
  | nil : ProjectionCuts env registry target node locals σ [] [] []
  | external (slot : Nat) (need : Need)
      (tail : ProjectionCuts env registry target node locals σ required outside footprint) :
      ProjectionCuts env registry target node locals σ
        ((slot + 1, need) :: required) ((slot, need) :: outside) footprint
  | cut (query : ProjectionObs env registry target node locals σ demand queryFootprint)
      (tail : ProjectionCuts env registry target node locals σ required outside footprint) :
      ProjectionCuts env registry target node locals σ
        ((0, ⟨_, demand⟩) :: required) outside (queryFootprint ++ footprint)

structure ProjectionFactoredArguments
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (required outside : Footprint) (minimum : Nat) where
  rank : Nat
  bound : minimum ≤ rank
  input : Profile rank
  footprint : Footprint
  query : ProjectionObs env registry target node locals σ input footprint
  resources : footprint.Available available
  pack : BinderPack rank input required outside

/-- Join cuts at their actual common grade; the query tree and hence every
field's original metadata are retained in the returned argument syntax. -/
theorem ProjectionCuts.arguments
    (cuts : ProjectionCuts env registry target node locals σ required outside footprint)
    (resources : footprint.Available available) (minimum : Nat) :
    Nonempty (ProjectionFactoredArguments env registry target node locals σ available
      required outside minimum) := by
  induction cuts with
  | nil => exact ⟨⟨minimum, Nat.le_refl _, .empty, [], .empty,
      (fun _ _ member => nomatch member), .nil⟩⟩
  | external slot need tail ih =>
    obtain ⟨result⟩ := ih resources
    exact ⟨{ result with pack := .external slot need result.pack }⟩
  | @cut n demand queryFootprint required outside footprint query tail ih =>
    obtain ⟨rest⟩ := ih
      (fun i need member => resources i need (List.mem_append_right _ member))
    let N := max n rest.rank
    have hn : n ≤ N := Nat.le_max_left _ _
    have ht : rest.rank ≤ N := Nat.le_max_right _ _
    exact ⟨{
      rank := N, bound := Nat.le_trans rest.bound ht
      input := (raiseProfile N hn demand).union (raiseProfile N ht rest.input)
      footprint := queryFootprint ++ rest.footprint
      query := .union (.raise query hn) (.raise rest.query ht)
      resources := fun i need member => (List.mem_append.mp member).elim
        (fun h => resources i need (List.mem_append_left _ h)) (rest.resources i need)
      pack := by simpa only [Need.atGrade, dif_pos hn] using
        BinderPack.local ⟨n, demand⟩ hn (rest.pack.raise ht) }⟩

/-- Construct a capture from an actual whole query at its original cut,
using exact two-display coherence before it joins the constructor input. -/
theorem ProjectionCuts.reindexCut
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary (.proj name index major) 0}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals baseLocals : List Nat}
    {fullRealization σ : Subst} {fullAvailable available : Valuation}
    (query : ProjectionObs env registry target
      (origin.view.cast origin.expression_eq rfl) locals fullRealization demand footprint)
    (rootContext : ContextDerivation sourceEnv U rootSource)
    (argumentContext : ContextDerivation sourceEnv U (boundary ++ rootSource))
    (argument : EndpointState sourceEnv U (boundary ++ rootSource)
      (.proj name index major) argumentType)
    (argumentProvenance : EndpointProvenance argumentContext argument)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (resources : footprint.Available fullAvailable)
    (coherence : DisplayCoherenceAnswer env registry target
      (origin.sourceDisplay rootContext)
      (origin.argumentDisplay argumentContext argument argumentProvenance)
      fullRealization fullAvailable locals baseLocals)
    (tail : ProjectionCuts env registry target argument baseLocals σ required outside tailFootprint)
    (tailResources : tailFootprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionCuts env registry target argument baseLocals σ
      ((0, ⟨_, demand⟩) :: required) outside nextFootprint) ∧
      nextFootprint.Available available := by
  obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := query.reindexFromCoherence rootContext
    argumentContext argument argumentProvenance realizationTail availableTail resources coherence
  exact ⟨nextFootprint ++ tailFootprint, ⟨.cut next tail⟩,
    fun i need member => (List.mem_append.mp member).elim (nextResources i need) (tailResources i need)⟩

structure ProjectionSeededFrame
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) A)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (B : VExpr) (result : Profile n) where
  seed : ProjectionArgumentSeed env registry target node locals σ available
  required : Footprint
  outside : Footprint
  outsideResources : outside.Available available
  collected : ProjectionFactoredArguments env registry target node locals σ available
    required outside (max n seed.rank)
  support : Profile collected.rank
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals σ A support domainFootprint
  domainResources : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A
    ⟨A.subst σ, (VExpr.proj name index major).subst σ,
      (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_right _ _) collected.bound)
        seed.demand).union collected.input⟩ support
  body : CodeCert env U registry target (Locals.push locals)
    (σ.cons ((VExpr.proj name index major).subst σ)) B
    (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_left _ _) collected.bound) result) required

namespace ProjectionSeededFrame
variable {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {index : Nat} {major A B : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) A}
    {result : Profile n}
variable (frame : ProjectionSeededFrame env registry target node locals σ available B result)

def input : Profile frame.collected.rank :=
  (raiseProfile frame.collected.rank (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound)
    frame.seed.demand).union frame.collected.input

def key : Key frame.collected.rank := ⟨A.subst σ, (VExpr.proj name index major).subst σ, frame.input⟩

def argumentQuery : ProjectionObs env registry target node locals σ frame.input
    (frame.seed.footprint ++ frame.collected.footprint) :=
  .union (.raise frame.seed.query (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound))
    frame.collected.query

theorem argumentResources :
    (frame.seed.footprint ++ frame.collected.footprint).Available available :=
  fun i need member => (List.mem_append.mp member).elim (frame.seed.resources i need)
    (frame.collected.resources i need)

def profile : Profile (frame.collected.rank + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support
    [(frame.key, raiseProfile frame.collected.rank
      (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) result)]

def certificate : CodeCert env U registry target locals σ (.forallE A B)
    frame.profile (frame.domainFootprint ++ frame.outside) := by
  have covered : ∀ atom ∈ frame.collected.input.atoms, atom ∈ frame.key.input.atoms :=
    fun _ member => List.mem_append_right _ member
  have rows : PiRows env U registry target locals σ A B frame.support
      [(frame.key, raiseProfile frame.collected.rank
        (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) result)] frame.outside := by
    simpa only [List.append_nil, key, input] using
      PiRows.cons frame.guard frame.body frame.collected.pack covered PiRows.nil
  refine .seed (.pi frame.domain PiGuard.literal rows) (Profile.HasType.pi_iff.mpr ⟨?_, ?_⟩)
  · refine Profile.WF.pi_iff.mpr ⟨frame.domain.formed, ?_⟩
    intro key output member
    cases List.mem_singleton.mp member
    exact ⟨frame.guard.inputTyped, frame.body.formed.wf_value⟩
  · intro key output member
    cases List.mem_singleton.mp member
    exact frame.body.formed

theorem resources : (frame.domainFootprint ++ frame.outside).Available available :=
  fun i need member => (List.mem_append.mp member).elim (frame.domainResources i need)
    (frame.outsideResources i need)

theorem fieldSeedAdmission (henv : env.Ordered) :
    RankedData.RequestAdmission env U (relations env U registry frame.collected.rank) target
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank))
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ) := by
  obtain ⟨anchor, pair, _, _, _, _, anchorTerm, pairTerm⟩ := frame.guard.anchor
  exact ⟨anchor, pair, frame.guard.inputTyped, frame.guard.formed,
    frame.guard.domains.left_diagonal,
    Related.retag henv frame.guard.inputTyped frame.guard.domains.left_diagonal anchorTerm,
    Related.retag henv frame.guard.inputTyped frame.guard.domains.left_diagonal pairTerm⟩

/-- Produce the constructor's argument guard from the actual original
projection rule, on the merged typed seed and reindexed cuts. All semantic
calls remain its three fixed original children. No per-output semantic
packet or typing at a guessed declared constructor domain is assumed. -/
theorem ofOriginalProjection
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major A B : VExpr}
    (rule : OriginalProjectionRule sourceEnv U source name index major major A)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fieldFundamental : StateFundamental env registry context (.ref (.left rule.field)))
    (leftFundamental : DerivationFundamental env registry context rule.left)
    (rightFundamental : DerivationFundamental env registry context rule.right)
    {required outside cutsFootprint : Footprint}
    (seed : ProjectionArgumentSeed env registry target rule.leftNode locals σ available)
    (cuts : ProjectionCuts env registry target rule.leftNode locals σ required outside cutsFootprint)
    (cutsResources : cutsFootprint.Available available)
    (outsideResources : outside.Available available)
    {result : Profile n}
    (body : CodeCert env U registry target (Locals.push locals)
      (σ.cons ((VExpr.proj name index major).subst σ)) B result required) :
    ∃ frame : ProjectionSeededFrame env registry target rule.leftNode locals σ available B result,
      frame.seed = seed := by
  obtain ⟨collected⟩ := cuts.arguments cutsResources (max n seed.rank)
  let query : ProjectionObs env registry target rule.leftNode locals σ
      ((raiseProfile collected.rank (Nat.le_trans (Nat.le_max_right _ _) collected.bound)
        seed.demand).union collected.input) (seed.footprint ++ collected.footprint) :=
    .union (.raise seed.query (Nat.le_trans (Nat.le_max_right _ _) collected.bound)) collected.query
  have queryResources : (seed.footprint ++ collected.footprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim
      (seed.resources i need) (collected.resources i need)
  obtain ⟨answer⟩ := query.projDF rule henv hscoped below closed formed context tails substitutions
    fieldFundamental leftFundamental rightFundamental queryResources
  have raw : env.HasType U target ((VExpr.proj name index major).subst σ) (A.subst σ) :=
    (rule.leftNode.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨{
    seed := seed, required := required, outside := outside, outsideResources := outsideResources
    collected := collected, support := answer.support, domainFootprint := answer.typeFootprint
    domain := answer.certificate, domainResources := answer.typeAvailable
    guard := ⟨answer.typed, answer.certificate.formed, .refl, answer.typeCode,
      ⟨raw, raw, _, answer.typed, answer.certificate.formed, answer.typeCode,
        answer.related, answer.related⟩⟩
    body := body.raise (Nat.le_trans (Nat.le_max_left _ _) collected.bound) }, rfl⟩

end ProjectionSeededFrame

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
