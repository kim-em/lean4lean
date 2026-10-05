import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableBodyCompile

/-! Syntactic dependency interpretation for the retained-program compiler.
Variables carry finite query traces, not semantic answers. A Pi carries the
interpretation of its domain and of each row under the row's finite input.
Changing a resource environment composes actual finite traces. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev RecipeVariableDependency (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (available : Valuation) (index : Nat) (profile : Profile n) : Prop :=
  ∃ footprint, Nonempty (SortableVariableTrace env U registry target index profile footprint) ∧
    footprint.Available available

private theorem variableTraceReplay
    (trace : VariableTrace env U registry target index profile footprint)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      RecipeVariableDependency env U registry target available i need.profile) :
    RecipeVariableDependency env U registry target available index profile := by
  induction trace with
  | leaf profile => exact supplied _ _ List.mem_cons_self
  | empty => exact ⟨[], ⟨.legacy .empty⟩, fun _ _ member => by cases member⟩
  | union left right leftIH rightIH =>
    obtain ⟨lf, ⟨l⟩, hl⟩ := leftIH (fun i need member => supplied i need (List.mem_append_left _ member))
    obtain ⟨rf, ⟨r⟩, hr⟩ := rightIH (fun i need member => supplied i need (List.mem_append_right _ member))
    exact ⟨lf ++ rf, ⟨.union l r⟩, fun i need member =>
      (List.mem_append.mp member).elim (hl i need) (hr i need)⟩
  | view child change ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.action next (.view change)⟩, resources⟩
  | pad child ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.pad next⟩, resources⟩
  | unpad child ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.unpad next⟩, resources⟩
  | rowShift child ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.action (.pad next) (.view (.commutePadFn _ _))⟩, resources⟩

/-- Substitution for every variable leaf in a finite trace. All replacements
are concrete traces with finite available footprints, including code actions. -/
theorem SortableVariableTrace.replayDependency
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      RecipeVariableDependency env U registry target available i need.profile) :
    RecipeVariableDependency env U registry target available index profile := by
  induction trace with
  | legacy trace => exact variableTraceReplay trace supplied
  | union left right leftIH rightIH =>
    obtain ⟨lf, ⟨l⟩, hl⟩ := leftIH (fun i need member => supplied i need (List.mem_append_left _ member))
    obtain ⟨rf, ⟨r⟩, hr⟩ := rightIH (fun i need member => supplied i need (List.mem_append_right _ member))
    exact ⟨lf ++ rf, ⟨.union l r⟩, fun i need member =>
      (List.mem_append.mp member).elim (hl i need) (hr i need)⟩
  | code child action formed ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.code next action formed⟩, resources⟩
  | action child action ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.action next action⟩, resources⟩
  | pad child ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.pad next⟩, resources⟩
  | unpad child ih =>
    obtain ⟨fp, ⟨next⟩, resources⟩ := ih supplied
    exact ⟨fp, ⟨.unpad next⟩, resources⟩

abbrev RecipeResourceDependency (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (first second : Valuation) : Prop :=
  ∀ index need, need ∈ first index →
    RecipeVariableDependency env U registry target second index need.profile

theorem RecipeVariableDependency.leaf (member : need ∈ available index) :
    RecipeVariableDependency env U registry target available index need.profile :=
  ⟨[(index, need)], ⟨.legacy (.leaf need.profile)⟩, fun _ _ selected => by
    cases List.mem_singleton.mp selected
    exact member⟩

theorem RecipeVariableDependency.transport
    (dependency : RecipeVariableDependency env U registry target first index profile)
    (replacement : RecipeResourceDependency env U registry target first second) :
    RecipeVariableDependency env U registry target second index profile := by
  obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
  exact SortableVariableTrace.replayDependency trace
    (fun i need member => replacement i need (resources i need member))

private theorem legacyTraceRename
    (trace : VariableTrace env U registry target index profile footprint)
    (rename : Nat → Nat) :
    Nonempty (SortableVariableTrace env U registry target (rename index) profile
      (footprint.map fun entry => (rename entry.1, entry.2))) := by
  induction trace with
  | leaf => exact ⟨.legacy (.leaf _)⟩
  | empty => exact ⟨.legacy .empty⟩
  | union left right leftIH rightIH =>
    obtain ⟨l⟩ := leftIH
    obtain ⟨r⟩ := rightIH
    simpa only [List.map_append] using Nonempty.intro (SortableVariableTrace.union l r)
  | view child change ih =>
    obtain ⟨next⟩ := ih
    exact ⟨.action next (.view change)⟩
  | pad child ih => obtain ⟨next⟩ := ih; exact ⟨.pad next⟩
  | unpad child ih => obtain ⟨next⟩ := ih; exact ⟨.unpad next⟩
  | rowShift child ih =>
    obtain ⟨next⟩ := ih
    exact ⟨.action (.pad next) (.view (.commutePadFn _ _))⟩

private theorem traceRename
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (rename : Nat → Nat) :
    Nonempty (SortableVariableTrace env U registry target (rename index) profile
      (footprint.map fun entry => (rename entry.1, entry.2))) := by
  induction trace with
  | legacy trace => exact legacyTraceRename trace rename
  | union left right leftIH rightIH =>
    obtain ⟨l⟩ := leftIH
    obtain ⟨r⟩ := rightIH
    simpa only [List.map_append] using Nonempty.intro (SortableVariableTrace.union l r)
  | code child action formed ih =>
    obtain ⟨next⟩ := ih
    exact ⟨.code next action formed⟩
  | action child action ih => obtain ⟨next⟩ := ih; exact ⟨.action next action⟩
  | pad child ih => obtain ⟨next⟩ := ih; exact ⟨.pad next⟩
  | unpad child ih => obtain ⟨next⟩ := ih; exact ⟨.unpad next⟩

/-- Binding introduces the same finite head resources on both sides. Only
outer leaves are replaced; no arbitrary new binder admission is assumed. -/
theorem RecipeResourceDependency.push
    (replacement : RecipeResourceDependency env U registry target first second)
    (head : List Need) :
    RecipeResourceDependency env U registry target (Valuation.push head first)
      (Valuation.push head second) := by
  intro index need member
  cases index with
  | zero => exact RecipeVariableDependency.leaf member
  | succ index =>
    obtain ⟨fp, ⟨trace⟩, resources⟩ := replacement index need member
    refine ⟨fp.map (fun entry => (entry.1 + 1, entry.2)), traceRename trace Nat.succ, ?_⟩
    intro i requested selected
    obtain ⟨⟨oldIndex, oldNeed⟩, oldMember, equal⟩ := List.mem_map.mp selected
    cases equal
    exact resources oldIndex oldNeed oldMember

/-- Exactly the finite binder table exposed by a row input. -/
def recipeDependencyInputs (profile : Profile n) : List Need :=
  [⟨n, profile⟩] ++ [Need.mk n profile].flatMap Need.singletons

/-- A Pi atom is executable dependency data for its domain and every row.
There is no physical-row or anchor-reconstruction requirement here. -/
def RecipePiDependency
    (domain body : {n : Nat} → Profile n → Valuation → Prop)
    (available : Valuation) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ support rows =>
      domain support available ∧ ∀ key result, (key, result) ∈ rows →
        body result (Valuation.push (recipeDependencyInputs key.input) available)
  | _ + 1, .pad atom => RecipePiDependency domain body available atom
  | _ + 1, _ => False

/-- This model records only the raw constructors that pending Pi elimination
can visit. At a variable it computes finite ordinary query syntax; at a Pi it
retains the recursively available domain and body demand programs. -/
def RecipeDependencyProfile (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    VExpr → {n : Nat} → Profile n → Valuation → Prop
  | .bvar index, _, profile, available =>
      RecipeVariableDependency env U registry target available index profile
  | .forallE A B, _, profile, available =>
      ∀ atom ∈ profile.atoms,
        RecipePiDependency (RecipeDependencyProfile env U registry target A)
          (RecipeDependencyProfile env U registry target B) available atom
  | _, _, _, _ => True
termination_by expression => sizeOf expression

/-- Environment replacement is structural even inside arbitrarily nested
Pi rows. The fresh binder input remains the same exact finite table. -/
theorem RecipePiDependency.transport
    {atom : Atom n}
    {domain body : {n : Nat} → Profile n → Valuation → Prop}
    (domainMove : ∀ {n} {p : Profile n} {first second},
      RecipeResourceDependency env U registry target first second → domain p first → domain p second)
    (bodyMove : ∀ {n} {p : Profile n} {first second},
      RecipeResourceDependency env U registry target first second → body p first → body p second)
    (replacement : RecipeResourceDependency env U registry target first second)
    (dependency : RecipePiDependency domain body first atom) :
    RecipePiDependency domain body second atom := by
  induction n with
  | zero => exact dependency
  | succ n ih =>
    cases atom with
    | pi A B support rows =>
      exact ⟨domainMove replacement dependency.1,
        fun key result member => bodyMove (replacement.push _) (dependency.2 key result member)⟩
    | pad atom => exact ih dependency
    | _ => exact dependency

/-- An actual finite trace replacement, rather than a type-relation oracle,
is sufficient to move the entire dependency interpretation. -/
theorem RecipeDependencyProfile.transport
    {profile : Profile n}
    (replacement : RecipeResourceDependency env U registry target first second)
    (dependency : RecipeDependencyProfile env U registry target expression profile first) :
    RecipeDependencyProfile env U registry target expression profile second := by
  induction expression generalizing n first second with
  | bvar index =>
    simp only [RecipeDependencyProfile] at dependency ⊢
    exact RecipeVariableDependency.transport dependency replacement
  | forallE A B domainIH bodyIH =>
    simp only [RecipeDependencyProfile] at dependency ⊢
    intro atom member
    exact RecipePiDependency.transport
      (fun change evidence => domainIH change evidence)
      (fun change evidence => bodyIH change evidence)
      replacement (dependency atom member)
  | _ => simp only [RecipeDependencyProfile]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
