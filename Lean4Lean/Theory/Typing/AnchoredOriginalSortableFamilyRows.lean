import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyConsumption

/-! The finite original family row ledger preserves all body leaves and
full parameter inputs before rebuilding any bare family binder. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private captureVariables_succ lookup_suffix from Lean4Lean.Theory.Typing.AnchoredFamilyCaptureObservation
set_option backward.isDefEq.respectTransparency false

namespace SortablePiRowCertificate
variable (row : SortablePiRowCertificate env U registry target locals σ available relevant A B (key : Key n) result)

def seedNeeds (extra : List Need) : List Need :=
  (row.bodyFootprint.localNeeds ++ extra) ++
    (row.bodyFootprint.localNeeds ++ extra).flatMap Need.singletons

theorem seedCoverage (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    ∀ need ∈ row.seedNeeds extra, need.rank ≤ n ∧
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
  have original : ∀ need ∈ row.bodyFootprint.localNeeds ++ extra,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨bound, included⟩ := row.pack.localNeeds need member
      exact ⟨bound, fun atom h => row.covered atom (included atom h)⟩
    · exact ⟨extraBound need member, extraCovered need member⟩
  intro need member
  rcases List.mem_append.mp member with member | member
  · exact original need member
  · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp selected
    obtain ⟨bound, included⟩ := original old oldMember
    refine ⟨bound, ?_⟩
    intro high member
    apply included high
    simp only [Need.atGrade, dif_pos bound] at member ⊢
    exact raiseProfile_subset bound
      (fun a h => by cases List.mem_singleton.mp h; exact atomMember) high member

theorem seedClosed (extra : List Need) (closed : available.AtomClosed) :
    (Valuation.push (row.seedNeeds extra) available).AtomClosed :=
  Valuation.push_atomized_closed closed _

theorem seedBodyAvailable (extra : List Need) :
    row.bodyFootprint.Available (Valuation.push (row.seedNeeds extra) available) := by
  have original := row.pack.available row.outsideAvailable
  intro index need member
  cases index with
  | zero => exact List.mem_append_left _ (List.mem_append_left _ (original 0 need member))
  | succ index => exact original (index + 1) need member

end SortablePiRowCertificate

theorem SortablePiRowCertificate.pushSeedOriginal
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    {A B : VExpr} {n : Nat} {key : Key n} {result : Profile n} {level : VLevel}
    (context : ContextDerivation headerEnv U source)
    (original : EndpointRef headerEnv U source A (.sort level))
    (domainIH : StateSortableFundamental env registry context (.ref original))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : SortableTailFits headerEnv env U registry target source locals seed seed available)
    (row : SortablePiRowCertificate env U registry target locals seed available relevant A B key result)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Ctx.SubstEq env U target (seed.cons key.anchor) (seed.cons key.anchor) (A :: source) ∧
    Nonempty (SortableTailPairedFits env registry target (.cons context original) (Locals.push locals)
      (seed.cons key.anchor) (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available)) := by
  let frame := SortableTailPairedFits.diagonal context fits
  obtain ⟨domain⟩ := domainIH target locals seed seed available closed hTarget substitutions frame
    row.domain row.domainAvailable
  obtain ⟨_, anchorTyped, _, _, _, _, anchorRelated, _⟩ := row.alignment.admission henv row.anchor
  have related := Related.retag henv row.inputTyped domain.related anchorRelated
  have coverage := row.seedCoverage extra bounded covered
  exact ⟨.cons substitutions (original.sound.defeq.mono below) anchorTyped,
    ⟨frame.pushCertificates original row.domain row.domain row.domainAvailable row.domainAvailable
      row.inputTyped row.inputTyped related related (row.seedNeeds extra)
      (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2)⟩⟩

theorem SortablePiRowCertificate.seedCoverageRaised
    (row : SortablePiRowCertificate env U registry target locals seed available relevant A B (key : Key n) result)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    {N : Nat} (bound : n ≤ N) :
    ∀ need ∈ row.seedNeeds extra, need.rank ≤ N ∧
      ∀ atom ∈ (need.atGrade N).atoms, atom ∈ (raiseKey N bound key).input.atoms := by
  intro need member
  obtain ⟨low, included⟩ := row.seedCoverage extra bounded covered need member
  refine ⟨Nat.le_trans low bound, ?_⟩
  rw [need.atGrade_raise bound low]
  exact raiseProfile_subset bound included

inductive OriginalSortableFamilyCodeRows (header : OriginalFamilyHeader headerEnv U declaredType) (env : VEnv)
    (registry : CanonicalHead.Registry) (target : List VExpr) (required : Footprint) :
    (source : List VExpr) → (locals : List Nat) → (seed : Subst) →
    (available : Valuation) → VExpr → List VExpr → List FamilyKey → Type where
  | nil (resources : required.Available available) :
      OriginalSortableFamilyCodeRows header env registry target required source locals seed available
        expression [] []
  | cons
      (original : EndpointRef headerEnv U source A (.sort level))
      (location : Located header.reference (.ref original))
      (row : SortablePiRowCertificate env U registry target locals seed available true A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra)
      (tail : OriginalSortableFamilyCodeRows header env registry target required (A :: source)
        (Locals.push locals) (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available)
        B domains keys) :
      OriginalSortableFamilyCodeRows header env registry target required source locals seed available
        (.forallE A B) (A :: domains) (⟨n, key, support⟩ :: keys)

def OriginalSortableFamilyCodeRows.terminalLocals
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : List Nat :=
  match rows with
  | .nil _ => locals
  | .cons _ _ _ _ _ _ _ _ tail => tail.terminalLocals

def OriginalSortableFamilyCodeRows.terminalValuation
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : Valuation :=
  match rows with
  | .nil _ => available
  | .cons _ _ _ _ _ _ _ _ tail => tail.terminalValuation

theorem OriginalSortableFamilyCodeRows.terminal_mem
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    {index : Nat} {need : Need} (member : need ∈ available index) :
    need ∈ rows.terminalValuation (keys.length + index) := by
  induction rows generalizing index with
  | nil => simpa only [OriginalSortableFamilyCodeRows.terminalValuation, List.length_nil, Nat.zero_add] using member
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    have later := ih (index := index + 1) member
    simpa only [OriginalSortableFamilyCodeRows.terminalValuation, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- Availability covers the full argument demand, not merely whichever
atoms appeared in the terminal type certificate. -/
theorem OriginalSortableFamilyCodeRows.captureAvailable
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) :
    (FamilyKey.captureFootprint keys).Available rows.terminalValuation := by
  induction rows with
  | nil => intro index need member; cases member
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      simpa only [Nat.add_zero, OriginalSortableFamilyCodeRows.terminalValuation] using
        tail.terminal_mem (index := 0) inputPresent
    · exact ih index need member

theorem OriginalSortableFamilyCodeRows.terminalLocals_eq
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    (count : Nat) (localNames : locals = List.range count) :
    rows.terminalLocals = List.range (count + keys.length) := by
  induction rows generalizing count with
  | nil => simpa only [OriginalSortableFamilyCodeRows.terminalLocals, List.length_nil, Nat.add_zero] using localNames
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    have names := (congrArg Locals.push localNames).trans
      (show Locals.push (List.range count) = List.range (count + 1) by
        simp only [List.range_succ_eq_map, Locals.push])
    simpa only [OriginalSortableFamilyCodeRows.terminalLocals, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (count + 1) names
theorem OriginalSortableFamilyCodeRows.length
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : keys.length = domains.length := by
  induction rows with
  | nil => rfl
  | cons original location row admission extra bounded covered inputPresent tail ih => exact congrArg Nat.succ ih

/-- Construct the complete terminal capture tree from actual row origins.
The domain chain is moved along source binders syntactically, so variable
interpretation can return to its exact original frozen key domain. -/
theorem OriginalSortableFamilyCodeRows.captures
    {headerEnv env : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target domains : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {required : Footprint} {expression : VExpr} {keys : List FamilyKey}
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    Nonempty (FamilyCaptures env U registry target (domains.reverse ++ source) rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor))) (constantCaptureVariables keys.length)
      (FamilyKey.uniform N keys bounded) (FamilyKey.captureFootprint keys)) := by
  induction rows with
  | nil => exact ⟨.nil⟩
  | @cons source A level locals seed available B n key result domains keys
      original location row support admission extra bounds covered inputPresent tail ih =>
    have bound := bounded ⟨n, key, support⟩ List.mem_cons_self
    obtain ⟨previous⟩ := ih (fun key member => bounded key (List.mem_cons_of_mem _ member))
    let finalSeed := familySubst (seed.cons key.anchor) (keys.map (·.key.anchor))
    have lookup : Lookup (domains.reverse ++ A :: source) keys.length (A.liftN (keys.length + 1)) := by
      simpa only [List.length_reverse, ← tail.length] using lookup_suffix domains.reverse source A
    have domainEq : (A.liftN (keys.length + 1)).subst finalSeed = A.subst seed := by
      rw [show keys.length + 1 = (keys.map (·.key.anchor)).length + 1 by simp]
      rw [show A.liftN ((keys.map (·.key.anchor)).length + 1) =
        A.lift.liftN (keys.map (·.key.anchor)).length by
          rw [liftN_liftN]; congr 1; omega]
      rw [familySubst_liftN, lift_subst_cons]
    have valueEq : finalSeed keys.length = key.anchor := by
      simpa only [List.length_map, Nat.add_zero, Subst.cons] using
        familySubst_drop (seed.cons key.anchor) (keys.map (·.key.anchor)) 0
    have alignment : DomainChain env U registry target (raiseKey N bound key).input
        (raiseKey N bound key).domain ((A.liftN (keys.length + 1)).subst finalSeed) := by
      rw [domainEq]
      exact row.alignment.raise henv bound
    have observation := (Obs.var (env := env) (U := U) (registry := registry) (target := target)
      tail.terminalLocals finalSeed keys.length key.input).raise bound
    have anchor : RankedData.RequestAdmission env U (relations env U registry N) target
        (raiseDataRequest N bound (⟨key, support⟩ : DataRequest (Profile n)))
        (finalSeed keys.length) (finalSeed keys.length) := by
      rw [valueEq]
      exact RankedData.RequestAdmission.raiseFamily henv bound admission
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      captureVariables_succ, List.map_cons, familySubst, List.foldl_cons,
      FamilyKey.uniform, FamilyKey.request, FamilyKey.captureFootprint, OriginalSortableFamilyCodeRows.terminalLocals,
      finalSeed] using
      (show Nonempty _ from ⟨FamilyCaptures.cons lookup observation (.refl _) alignment anchor previous⟩)

end Lean4Lean.AnchoredSource.Adapted
