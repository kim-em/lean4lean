import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption

/-! Expose the actual first family-plan binder or terminal through its
finite views and padding. Padding changes the binder grade, while terminal
requests and their original declaration certificates remain literal. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

private inductive FamilyAtom : {n : Nat} → Atom n → Prop where
  | family (demand : FamilyData (Profile n)) : FamilyAtom (n := n + 1) (.family demand)
  | pad {atom : Atom n} : FamilyAtom atom → FamilyAtom (n := n + 1) (.pad atom)

private theorem FamilyAtom.rigid {a b : Atom n}
    (shape : FamilyAtom b) (adapter : AtomAdapter env U registry Γ a b) : a = b := by
  induction shape with
  | family demand => cases adapter; rfl
  | pad shape ih =>
    cases adapter with
    | refl => rfl
    | pad child => exact congrArg AtomData.pad (ih child)

private theorem FamilyAtom.shift {a : Atom n} (shape : FamilyAtom a) :
    AdapterNormal.shiftAtom a = AtomData.pad a := by
  cases shape <;> rfl

private theorem FamilyAtom.normal {a : Atom n} (shape : FamilyAtom a) :
    AdapterNormal.atom a = a := by
  induction shape with
  | family demand => rfl
  | pad shape ih =>
    change AdapterNormal.shiftAtom (AdapterNormal.atom _) = _
    rw [ih, shape.shift]

private theorem FamilyAtom.raise {n N : Nat} (bound : n ≤ N) {a : Atom n}
    (shape : FamilyAtom a) : FamilyAtom (raiseAtom N bound a) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseAtom_self] using shape
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseAtom_self] using shape
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact .pad (ih small)

private theorem FamilyAtom.notFn {a : Atom (m + 1)}
    (shape : FamilyAtom a) {key : Key m} {output : Atom m} :
    a ≠ .fn key output := by
  cases shape <;> intro same <;> cases same

/-- A frozen family terminal cannot be consumed as another function
binder, even through hereditary normalization and arbitrary outer padding. -/
theorem familyAdapter_not_fn
    {demand : FamilyData (Profile n)} {key : Key m} {output : Atom m}
    (bound : n + 1 ≤ m + 1)
    (adapter : NormalAtomAdapter env U registry target
      (raiseAtom (m + 1) bound (.family demand)) (.fn key output)) : False := by
  have shape := (FamilyAtom.family demand).raise bound
  change AtomAdapter env U registry target (n := m + 1) (AdapterNormal.atom _)
    (.fn (AdapterNormal.key key) (AdapterNormal.atom output)) at adapter
  rw [shape.normal] at adapter
  obtain ⟨actualKey, actualOutput, equal, _, _⟩ := adapter.fn_inv
  exact shape.notFn equal

theorem fnAdapter_not_family
    {demand : FamilyData (Profile n)} {key : Key m} {output : Atom m}
    (bound : n + 1 ≤ m + 1)
    (adapter : NormalAtomAdapter env U registry target (n := m + 1)
      (.fn key output) (raiseAtom (m + 1) bound (.family demand))) : False := by
  have shape := (FamilyAtom.family demand).raise bound
  change AtomAdapter env U registry target (n := m + 1)
    (.fn (AdapterNormal.key key) (AdapterNormal.atom output)) (AdapterNormal.atom _) at adapter
  rw [shape.normal] at adapter
  exact shape.notFn (shape.rigid adapter).symm

private theorem raiseFamily_inj
    {first : FamilyData (Profile n)} {second : FamilyData (Profile m)}
    (leftBound : n + 1 ≤ N) (rightBound : m + 1 ≤ N)
    (same : raiseAtom N leftBound (.family first) = raiseAtom N rightBound (.family second)) :
    n = m ∧ HEq first second := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases leftTop : n + 1 = N + 1
    · have leftRank : n = N := by omega
      subst n
      by_cases rightTop : m + 1 = N + 1
      · have rightRank : m = N := by omega
        subst m
        simp only [raiseAtom_self] at same
        exact ⟨rfl, heq_of_eq (AtomData.family.inj same)⟩
      · have small : m + 1 ≤ N := by omega
        rw [raiseAtom_self, raiseAtom_step small] at same
        cases same
    · have leftSmall : n + 1 ≤ N := by omega
      by_cases rightTop : m + 1 = N + 1
      · have rightRank : m = N := by omega
        subst m
        rw [raiseAtom_step leftSmall, raiseAtom_self] at same
        cases same
      · have rightSmall : m + 1 ≤ N := by omega
        rw [raiseAtom_step leftSmall, raiseAtom_step rightSmall] at same
        exact ih leftSmall rightSmall (AtomData.pad.inj same)

/-- Finite function adapters and outer grade changes cannot alter a frozen
family descriptor, including any argument's exact support. -/
theorem familyAdapter_exact
    {first : FamilyData (Profile n)} {second : FamilyData (Profile m)}
    (leftBound : n + 1 ≤ N) (rightBound : m + 1 ≤ N)
    (adapter : NormalAtomAdapter env U registry target
      (raiseAtom N leftBound (.family first)) (raiseAtom N rightBound (.family second))) :
    n = m ∧ HEq first second := by
  have leftShape := (FamilyAtom.family first).raise leftBound
  have rightShape := (FamilyAtom.family second).raise rightBound
  change AtomAdapter env U registry target (AdapterNormal.atom _) (AdapterNormal.atom _) at adapter
  rw [leftShape.normal, rightShape.normal] at adapter
  exact raiseFamily_inj leftBound rightBound (rightShape.rigid adapter)

inductive FamilyPlanFront (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel) {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (arguments : List VExpr) :
    {N : Nat} → Atom N → Footprint → Type where
  | terminal {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint)
      (bound : n + 1 ≤ N)
      (adapter : NormalAtomAdapter env U registry target
        (raiseAtom N bound (.family ⟨name, levels, relevant, keys⟩)) requested) :
      FamilyPlanFront env U registry target name levels signature arguments requested footprint
  | binder {domain : VExpr} {key : Key n} {output : Atom n} {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : FamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (adapter : NormalAtomAdapter env U registry target (n := n + 1) (.fn key output) requested) :
      FamilyPlanFront env U registry target name levels signature arguments requested
        (domainFootprint ++ outside)

noncomputable def FamilyPlanFront.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : FamilyPlanFront env U registry target name levels signature arguments atom footprint)
    (change : AtomView env U registry target atom atom') :
    FamilyPlanFront env U registry target name levels signature arguments atom' footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    exact .terminal sat shape rel captures bound (adapter.comp (change.toAdapter henv hscoped hTarget))
  | binder origin domain guard body pack covered adapter =>
    exact .binder origin domain guard body pack covered (adapter.comp (change.toAdapter henv hscoped hTarget))

noncomputable def FamilyPlanFront.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : FamilyPlanFront env U registry target name levels signature arguments (atom : Atom N) footprint) :
    FamilyPlanFront env U registry target name levels signature arguments (N := N + 1) (.pad atom) footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    apply FamilyPlanFront.terminal sat shape rel captures (Nat.le_trans bound (Nat.le_succ N))
    simpa only [raiseAtom_step bound, raiseAtom_step (Nat.le_refl N), raiseAtom_self] using adapter.raise henv hscoped hTarget (Nat.le_succ N)
  | @binder n domainFootprint bodyFootprint outside requested domainExpr key output support packed
      origin domain guard body pack covered adapter =>
    have guard' := guard.raise henv (Nat.le_succ _)
    have pack' := pack.raise (Nat.le_succ _)
    have covered' := raiseProfile_subset (Nat.le_succ _) covered
    simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
      raiseProfile_step (Nat.le_refl _), raiseProfile_self] at guard' pack' covered'
    refine .binder origin (.pad domain) guard' (.pad body) pack' covered' ?_
    have first := ((AtomView.commutePadFn (env := env) (U := U) (registry := registry)
      (Γ := target) key output).inverse henv).toAdapter henv hscoped hTarget
    have second := adapter.raise henv hscoped hTarget (Nat.le_succ _)
    simp only [raiseAtom_step (Nat.le_refl _), raiseAtom_self] at second
    exact first.comp second

theorem FamilyPlan.front
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile N}
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint)
    (atom : Atom N) (singleton : demand = Profile.singleton atom) :
    Nonempty (FamilyPlanFront env U registry target name levels signature arguments atom footprint) := by
  match N, demand, footprint, plan with
  | _, _, _, .terminal sat shape rel captures =>
    cases List.singleton_inj.mp singleton
    exact ⟨.terminal sat shape rel captures (Nat.le_refl _) (by
      rw [raiseAtom_self]; exact .refl _)⟩
  | _, _, _, .binder origin domain guard body pack covered =>
    cases List.singleton_inj.mp singleton
    exact ⟨.binder origin domain guard body pack covered (.refl _)⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp singleton
    obtain ⟨front⟩ := source.front henv hscoped hTarget _ rfl
    exact ⟨front.view henv hscoped hTarget change⟩
  | _, _, _, .pad source =>
    obtain ⟨original, same, output⟩ := List.map_eq_singleton_iff.mp singleton
    cases output
    obtain ⟨front⟩ := source.front henv hscoped hTarget original same
    exact ⟨front.pad henv hscoped hTarget⟩
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
