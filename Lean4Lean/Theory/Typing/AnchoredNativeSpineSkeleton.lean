import Lean4Lean.Theory.Typing.AnchoredNativeRetelescope
import Lean4Lean.Theory.Typing.AnchoredNativeArgumentLedger

/-! Turn actual finite argument-observation ledgers into coverage for the
selected demand spine, then build its guard-free native telescope skeleton.
All guards and assigned-type certificates are subsequently supplied by the
checked registered-header retelescoping driver. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

inductive NativeSpineSeedCoverage :
    NativeSpineSeeds env U registry target locals σ available expression → Footprint → Prop where
  | constant : NativeSpineSeedCoverage (NativeSpineSeeds.constant (name := name) (levels := levels)) []
  | app {required : Footprint}
      {function : NativeSpineSeeds env U registry target locals σ available f}
      {argument : NativeArgumentSeed env U registry target locals σ available a}
      (tail : NativeSpineSeedCoverage function (externalArguments required))
      (bounded : ∀ need, (0, need) ∈ required → need.rank ≤ argument.rank)
      (covered : ∀ need, (0, need) ∈ required → ∀ atom ∈ (need.atGrade argument.rank).atoms,
        atom ∈ argument.demand.atoms) :
      NativeSpineSeedCoverage (.app function argument) required

/-- The demand path retains exactly the original finite argument packets. -/
def NativeSpineDemandPath.seeds
    (path : NativeSpineDemandPath sourceEnv env U registry source target locals σ available
      name levels expression assigned atom root) :
    NativeSpineSeeds env U registry target locals σ available expression :=
  match path with
  | .constant => .constant
  | .application frame function => .app function.seeds frame.seed
  | .conversion _ term => term.seeds

theorem NativeSeededSpineCertificate.rootDemand_seeds
    {profile : Profile n}
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    {atom : Atom n} (typed : (Profile.singleton atom).HasType profile) :
    (spine.rootDemand typed).path.seeds = spine.seeds := by
  induction spine with
  | constant => rfl
  | application frame function ih =>
    exact congrArg (fun f => NativeSpineSeeds.app f frame.seed) (ih (frame.demandTyped typed))
  | conversion edge certificate transfer term ih => exact ih typed

/-- Every seed is collected from a real original argument observation in the
ledger. The empty native prefix has no unaccounted source requirements. -/
theorem NativeArgumentLedger.spineSeeds
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {expression : VExpr} {name : Name} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    {required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available expression.getAppFnArgs.2 required)
    (minimum : Nat) :
    ∃ seeds : NativeSpineSeeds env U registry target locals σ available expression,
      NativeSpineSeedCoverage seeds required := by
  induction expression generalizing required with
  | const actual actualLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    have empty : required = [] := by
      cases required with
      | nil => rfl
      | cons entry tail =>
        obtain ⟨index, need⟩ := entry
        have bad := ledger.scoped index need List.mem_cons_self
        simp only [getAppFnArgs_const, List.length_nil] at bad
        omega
    subst required
    exact ⟨.constant, .constant⟩
  | app f a ihF ihA =>
    simp only [getAppFnArgs_app] at head ledger
    obtain ⟨cover⟩ := ledger.lastSeed minimum
    obtain ⟨function, covered⟩ := ihF head ledger.withoutLast
    exact ⟨.app function cover.seed, .app covered
      (fun need member => (cover.covered need (mem_argumentNeeds.mpr member)).1)
      (fun need member => (cover.covered need (mem_argumentNeeds.mpr member)).2)⟩
  | bvar | sort | lam | forallE | proj | elim =>
    simp only [getAppFnArgs] at head
    contradiction

noncomputable def NativeRetelescopeSkeleton.raise
    (skeleton : NativeRetelescopeSkeleton env U registry target signature arguments (atom : Atom n) footprint)
    (bound : n ≤ N) :
    NativeRetelescopeSkeleton env U registry target signature arguments (raiseAtom N bound atom) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseAtom_self] using skeleton
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseAtom_self] using skeleton
    · have low : n ≤ N := by omega
      rw [raiseAtom_step low]
      exact .pad (ih low)

theorem NativeRetelescopeSkeleton.arguments_bound
    (skeleton : NativeRetelescopeSkeleton env U registry target signature arguments atom footprint) :
    arguments.length ≤ signature.domains.length := by
  induction skeleton with
  | terminal leaf =>
    rw [NativeRecursorData.takeForalls_length signature.telescope, leaf.saturated]
    exact Nat.le_refl _
  | binder origin body pack covered ih => simp only [List.length_append, List.length_singleton] at ih; omega
  | pad body ih => exact ih

private theorem coverage_pack
    {required : Footprint} {input : Profile n}
    (bounded : ∀ need, (0, need) ∈ required → need.rank ≤ n)
    (covered : ∀ need, (0, need) ∈ required → ∀ atom ∈ (need.atGrade n).atoms,
      atom ∈ input.atoms) :
    ∃ packed, BinderPack n packed required (externalArguments required) ∧
      ∀ atom ∈ packed.atoms, atom ∈ input.atoms := by
  induction required with
  | nil => exact ⟨.empty, .nil, fun _ h => nomatch h⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    obtain ⟨packed, pack, included⟩ := ih
      (fun n h => bounded n (List.mem_cons_of_mem _ h))
      (fun n h => covered n (List.mem_cons_of_mem _ h))
    cases index with
    | zero => exact ⟨(need.atGrade n).union packed, .local need (bounded need List.mem_cons_self) pack,
        fun atom hm => (List.mem_append.mp hm).elim (covered need List.mem_cons_self atom) (included atom)⟩
    | succ index => exact ⟨packed, .external index need pack, included⟩

/-- Rebuild the complete finite computational skeleton from the retained
original application frames, starting at its actual native terminal. -/
theorem NativeSpineDemandPath.skeleton
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression assigned : VExpr}
    {atom : Atom n} {root : Atom N}
    (path : NativeSpineDemandPath sourceEnv env U registry source target locals σ available
      name levels expression assigned atom root)
    {data : NativeRecursorData} {signature : NativeConstantSignature data levels}
    {required : Footprint}
    (coverage : NativeSpineSeedCoverage path.seeds required)
    (tail : NativeRetelescopeSkeleton env U registry target signature
      (expression.getAppFnArgs.2.map (·.subst σ)) atom required) :
    Nonempty (NativeRetelescopeSkeleton env U registry target signature [] root []) := by
  induction path generalizing required with
  | constant =>
    cases coverage
    exact ⟨tail⟩
  | @application n N A B a result before f atom root frame function ih =>
    cases coverage with
    | app functionCoverage bounded covered =>
      obtain ⟨packed, pack, included⟩ := coverage_pack bounded covered
      have highPack := pack.raise (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound)
      have highIncluded := raiseProfile_subset
        (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound) included
      let high := tail.raise (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound)
      have lengthBound := tail.arguments_bound
      simp only [getAppFnArgs_app, List.map_append, List.map_singleton, List.length_append,
        List.length_map, List.length_singleton] at lengthBound
      have before : f.getAppFnArgs.2.length < signature.domains.length := by omega
      have origin : signature.domains[(f.getAppFnArgs.2.map (·.subst σ)).length]? =
          some signature.domains[f.getAppFnArgs.2.length] := by
        simp only [List.length_map, List.getElem?_eq_getElem before]
      have child : NativeRetelescopeSkeleton env U registry target signature
          (f.getAppFnArgs.2.map (·.subst σ) ++ [frame.key.anchor]) (frame.output atom) required := by
        simpa only [getAppFnArgs_app, List.map_append, List.map_singleton,
          SeededApplicationCodeInput.key, SeededApplicationCodeInput.output] using high
      apply ih functionCoverage
      exact .binder origin child highPack
        (fun a h => frame.seedCovered a (highIncluded a h))
  | conversion edge term ih => exact ih coverage tail

/-- End-to-end finite producer: actual routed argument observers are merged
before the original application children are queried, then the selected
computational demand path builds the matching whole native skeleton. -/
theorem HasTypeStrong.nativeSkeleton
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {expression assigned : VExpr} {structural : Bool} {name : Name} {levels : List VLevel}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    {data : NativeRecursorData} {signature : NativeConstantSignature data levels}
    {atom : Atom n} {required : Footprint}
    (leaf : NativeInitialTerminal env U registry target signature
      (expression.getAppFnArgs.2.map (·.subst σ)) (.singleton atom) required)
    (ledger : NativeArgumentLedger env U registry target locals σ available
      expression.getAppFnArgs.2 required)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (resources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support) :
    ∃ root : NativeSpineRootDemand sourceEnv env U registry source target locals σ available
      name levels expression assigned atom,
      Nonempty (NativeRetelescopeSkeleton env U registry target signature [] root.demand []) := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head n
  obtain ⟨spine, seedEq⟩ := HasTypeStrong.seededSpineCertificate henv hscoped hle earlier
    closed hTarget substitutions fits original head seeds certificate resources
  let root := spine.rootDemand typed
  have rootCoverage : NativeSpineSeedCoverage root.path.seeds required := by
    change NativeSpineSeedCoverage (spine.rootDemand typed).path.seeds required
    rw [spine.rootDemand_seeds typed, seedEq]
    exact coverage
  exact ⟨root, root.path.skeleton rootCoverage (.terminal leaf)⟩

end Lean4Lean.AnchoredSource.Adapted
