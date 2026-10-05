import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBetaRow
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentPack

/-! Backward beta reconstruction selects a finite owner-query ledger from
the actual captured body and computes its argument supply. The lambda and
application retain the original beta premises throughout. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option quotPrecheck false

private theorem raiseAtom_compose {n k N : Nat} (first : n ≤ k) (second : k ≤ N) (atom : Atom n) :
    raiseAtom N second (raiseAtom k first atom) = raiseAtom N (Nat.le_trans first second) atom := by
  have same := raiseProfile_trans first second (.singleton atom)
  simp only [raiseProfile_singleton] at same
  exact List.singleton_inj.mp (congrArg Profile.atoms same)

private noncomputable def adaptOutput
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Atom n} {output : Atom k} (bound : n ≤ k)
    (adapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom k bound requested))
    (answer : RichGradedResult sourceEnv env U registry target node locals σ available (.singleton output)) :
    RichGradedResult sourceEnv env U registry target node locals σ available (.singleton requested) where
  rank := answer.rank
  bound := Nat.le_trans bound answer.bound
  raw := answer.raw
  footprint := answer.footprint
  observation := answer.observation
  adapter := by
    have raised := GeneralNormalAtomAdapter.raise henv hscoped formed answer.bound adapter
    rw [raiseAtom_compose] at raised
    have first := answer.adapter
    simp only [raiseProfile_singleton] at first ⊢
    exact GeneralProfileAdapter.comp first (.cons (List.mem_singleton_self _) raised (.nil _))
  resources := answer.resources
  live := answer.live

section
variable
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (body : Derivation sourceEnv U (A :: source) e e B)
  (argument : Derivation sourceEnv U source a a A)
  (result : Derivation sourceEnv U source (B.inst a) (B.inst a) (.sort v))
  (instantiated : Derivation sourceEnv U source (e.inst a) (e.inst a) (B.inst a))
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

local notation "original" => Derivation.beta domainWF bodyWF domain codomain body argument result instantiated
local notation "base" => frame.captureBase substitutions
local notation "bodyDisplay" => betaCapturedBodyDisplay context domain body argument (.identity context)
local notation "capacity" => environmentCost (Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) :: frame.dependencyEnvironment ordered)
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost

/-- Used computational footprints exclude a unit-weight literal sort, so
replaying their owners to the argument is funded by the actual beta reserve. -/
theorem betaArgumentReplaySchedule
    (observation : RichObs sourceEnv env U registry target (.ref (.left body)) bodyLocals bodySubst profile footprint)
    (member : (index, need) ∈ footprint) :
    richSchedule .expressionReindex
      (capacity + (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) <
        richSchedule .fundamental limit := by
  have used : 2 ≤ (body.dependencyOrigin ordered).weight := by
    by_cases known : 2 ≤ (body.dependencyOrigin ordered).weight
    · exact known
    have small' : ((EndpointState.ref (.left body)).dependencyOrigin ordered).weight < 2 := by
      change (body.dependencyOrigin ordered).weight < 2
      omega
    obtain ⟨level, same⟩ := EndpointState.dependency_small_sort ordered (.ref (.left body)) small'
    subst e
    have impossible := observation.sortScoped index need member
    omega
  have product := Nat.mul_le_mul_right
    (1 + (argument.dependencyOrigin ordered).weight + (domain.dependencyOrigin ordered).weight) used
  have coefficient : 2 * (argument.dependencyOrigin ordered).weight + (domain.dependencyOrigin ordered).weight <
      ((original).dependencyOrigin ordered).weight := by
    rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.beta domainWF bodyWF domain codomain body argument result instantiated)]
    simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at *
    omega
  have positive := (argument.dependencyOrigin ordered).weight_pos
  have previousBound : environmentCost (frame.dependencyEnvironment ordered) ≤
      (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
      (Closure.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost := by
    have first : 1 + environmentCost (frame.dependencyEnvironment ordered) ≤
        (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost :=
      Nat.le_mul_of_pos_left _ positive
    omega
  change richSchedule .expressionReindex
    (max ((Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
      (Closure.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost)
      (environmentCost (frame.dependencyEnvironment ordered)) +
      (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) < _
  rw [Nat.max_eq_left previousBound]
  apply richSchedule_strict
  have scaled := Nat.mul_lt_mul_of_pos_right coefficient (Nat.zero_lt_succ (environmentCost (frame.dependencyEnvironment ordered)))
  simpa only [Closure.cost, Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_one,
    Nat.mul_comm 2, Nat.mul_two, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scaled

/-- All remaining calls are the finite original owner requests discovered
from this particular body answer, not an argument-query supplier. -/
theorem generatedBetaApplication
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (reply : BoundedGeneratedQueryReply base (base).initialCaps bodyDisplay σ τ (.singleton requested) capacity)
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit) :
    ∃ needs : List Need,
      ∃ queries : CapturedArgumentQueries base (base).initialCaps source σ τ a capacity needs,
        queries.Calls (OriginalNestedDisplay.identity base (.ref (.left argument)) (.ofLocation .here context))
          ordered (richSchedule .fundamental limit) →
        Nonempty (RichGradedResult sourceEnv env U registry target (EndpointRef.left original).expose
          locals σ available (.singleton requested)) := by
  obtain ⟨selected⟩ := reply.answer.reply.query.atom henv hscoped formed reply.answer.reply.closed
  obtain ⟨packed⟩ := betaBodyTypedPack context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped formed closed reply domainF selected.observation selected.resources
  have used : ∀ need ∈ selected.footprint.localNeeds, need ∈ reply.answer.reply.available 0 :=
    fun need member => selected.resources 0 need (Footprint.mem_localNeeds.mp member)
  obtain ⟨queries⟩ := reply.answer.capped.argumentQueries reply.answer.reply.realization.frame.valid
    reply.answer.reply.realization.substitutions ordered selected.footprint.localNeeds used (reply.bounded ordered)
  simp only [subst_id] at queries
  refine ⟨selected.footprint.localNeeds, queries, ?_⟩
  intro calls
  obtain ⟨supply⟩ := queries.supplyAtBase (.ofLocation .here context) henv hscoped formed ordered closed
    (fun nonempty => by
      obtain ⟨need, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact betaArgumentReplaySchedule context domainWF bodyWF domain codomain body argument result instantiated frame ordered
        selected.observation (Footprint.mem_localNeeds.mp member)) calls
  obtain ⟨argumentQuery⟩ := binderPackArgumentQuery henv hscoped formed packed.pack supply
  let key : Key packed.rank := ⟨A.subst σ, a.subst σ, packed.input⟩
  have raw := (argument.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions.left
  have related := packed.related.left_diagonal
  have guard : LambdaGuard env U registry target σ A key packed.support :=
    ⟨packed.typed, packed.certificate.formed, .refl, packed.code,
      ⟨raw, raw, packed.support, packed.typed, packed.certificate.formed, packed.code, related, related⟩⟩
  have bodyQuery : RichObs sourceEnv env U registry target (.ref (.left body)) (Locals.push locals)
      (σ.cons (a.subst σ)) (.singleton (raiseAtom packed.rank packed.bound selected.atom)) selected.footprint := by
    have positions := reply.answer.reply.locals_eq
    change reply.answer.reply.locals = Locals.push locals at positions
    have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
      funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
    simpa only [betaCapturedBodyDisplay, positions, realization, raiseProfile_singleton] using selected.observation.raise packed.bound
  have live : Atom.Live env U registry target (raiseAtom packed.rank packed.bound selected.atom) := by
    have raised := (raiseProfile_live_iff packed.bound (.singleton selected.atom)).mpr
      (Profile.Live.singleton_iff.mpr selected.live)
    simpa only [raiseProfile_singleton, Profile.Live.singleton_iff] using raised
  let fn : RichGradedResult sourceEnv env U registry target
      (.lam domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain)) (.ref (.left body)))
      locals σ available (Profile.fn key (raiseAtom packed.rank packed.bound selected.atom)) := {
    rank := packed.rank + 1, bound := Nat.le_refl _, raw := _, footprint := _
    observation := .lam domainWF bodyWF packed.certificate guard bodyQuery packed.pack (fun _ h => h)
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun i need member => (List.mem_append.mp member).elim (packed.resources i need) (packed.external i need)
    live := Profile.Live.singleton_iff.mpr ⟨guard.anchor, live⟩ }
  obtain ⟨application⟩ := RichGradedResult.app henv hscoped formed closed (.ref (.left domain))
    (.ref (.left codomain)) (.ref (.left result)) domainWF bodyWF fn argumentQuery (.refl _) guard.anchor
  have adapter := GeneralNormalAtomAdapter.raise henv hscoped formed packed.bound selected.adapter
  rw [raiseAtom_compose] at adapter
  exact ⟨adaptOutput henv hscoped formed (Nat.le_trans selected.bound packed.bound) adapter application⟩


/-- Arbitrary finite computational profiles reconstruct by a finite union
of the exact owner ledgers discovered for their output atoms. -/
theorem generatedBetaExpansion
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall base (base).initialCaps
      (betaInstantiatedDisplay context instantiated (.identity context)) bodyDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (query : RichObs sourceEnv env U registry target (.ref (.left instantiated)) locals σ
      (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ ledgers : List (Σ needs, CapturedArgumentQueries base (base).initialCaps source σ τ a capacity needs),
      (∀ entry ∈ ledgers,
        entry.2.Calls (OriginalNestedDisplay.identity base (.ref (.left argument)) (.ofLocation .here context))
          ordered (richSchedule .fundamental limit)) →
      Nonempty (RichGradedResult sourceEnv env U registry target (EndpointRef.left original).expose
        locals σ available profile) := by
  suffices collect : ∀ atoms : List (Atom n), (∀ atom ∈ atoms, atom ∈ profile.atoms) →
      ∃ ledgers : List (Σ needs, CapturedArgumentQueries base (base).initialCaps source σ τ a capacity needs),
        (∀ entry ∈ ledgers,
          entry.2.Calls (OriginalNestedDisplay.identity base (.ref (.left argument)) (.ofLocation .here context))
            ordered (richSchedule .fundamental limit)) →
        Nonempty (RichGradedResult sourceEnv env U registry target (EndpointRef.left original).expose
          locals σ available (.mk atoms)) from collect profile.atoms (fun _ h => h)
  intro atoms
  induction atoms with
  | nil => exact fun _ => ⟨[], fun _ => ⟨.empty⟩⟩
  | cons atom atoms ih =>
    intro included
    have observation := RichObs.select query (included atom List.mem_cons_self)
    obtain ⟨reply⟩ := generatedBetaBody context domainWF bodyWF domain codomain body argument result instantiated
      (.identity context) henv below ordered formed (base).identityRealization (base).identityCapped closed bodyR observation resources
    obtain ⟨needs, queries, reconstruct⟩ := generatedBetaApplication context domainWF bodyWF domain codomain body argument result instantiated
      frame substitutions ordered henv hscoped below formed closed reply domainF
    obtain ⟨rest, reconstructRest⟩ := ih (fun wanted member => included wanted (List.mem_cons_of_mem _ member))
    refine ⟨⟨needs, queries⟩ :: rest, ?_⟩
    intro calls
    obtain ⟨first⟩ := reconstruct (calls _ List.mem_cons_self)
    obtain ⟨last⟩ := reconstructRest (fun entry member => calls entry (List.mem_cons_of_mem _ member))
    exact ⟨first.union henv hscoped formed last⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
