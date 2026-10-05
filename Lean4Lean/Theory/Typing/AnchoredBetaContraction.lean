import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredDataValueLaws
import Lean4Lean.Theory.Typing.AnchoredBeta
import Batteries.Tactic.OpenPrivate

/-! Typed head-beta contraction, including function-valued observations.
The raw equality is required at the actual assigned type. This theorem does
not infer that equality from an independently typed lambda body.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private def TypeHead : VExpr → Prop
  | .sort _ | .forallE .. => True
  | _ => False

private theorem headBeta_not_typeHead
    (h : HeadBeta expanded expression) (different : expanded ≠ expression) (ρ : Lift) :
    ¬ TypeHead (expanded.lift' ρ) := by
  cases h with
  | refl => exact (different rfl).elim
  | apply => exact fun h => h
  | proj => exact fun h => h
  | @contract A body argument trailing =>
    have shape : ∀ (fn : VExpr) (args : List VExpr),
        (∃ f a, fn = .app f a) → ¬ TypeHead ((mkApps fn args).lift' ρ) := by
      intro fn args
      induction args generalizing fn with
      | nil => rintro ⟨f, a, rfl⟩; exact fun h => h
      | cons a args ih => intro _; exact ih (.app fn a) ⟨fn, a, rfl⟩
    exact shape (.app (.lam A body) argument) trailing ⟨_, _, rfl⟩

private theorem HeadBeta.strip_trace
    (reduction : HeadBeta expanded expression)
    (trace : CanonicalDataHead.Trace registry expanded added result)
    (typedHead : TypeHead (result.lift' postMap)) :
    CanonicalDataHead.Trace registry expression added result := by
  by_cases equal : expanded = expression
  · simpa only [equal] using trace
  · cases trace with
    | refl => exact (headBeta_not_typeHead reduction equal postMap typedHead).elim
    | @next _ out added result step tail =>
      have exactStep := reduction.step (registry := registry) equal
      have output := Option.some.inj (step.symm.trans exactStep)
      cases output
      simpa only [List.append_nil] using tail

private def Exposure.contractHeadBeta (henv : env.Ordered)
    (reduction : HeadBeta expanded expression)
    (path : TypeConversion env U Γ expanded expression)
    (E : Exposure env U registry Γ expanded Δ ρ head)
    (shape : TypeHead head) : Exposure env U registry Γ expression Δ ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := reduction.strip_trace E.trace (E.result_eq ▸ shape)
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := E.terminal
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := ((E.insertion henv).path henv path.symm).trans E.sound
  headType := E.headType

private theorem HeadBeta.strip_stopped_trace
    (scope : registry.Scoped) (reduction : HeadBeta expanded expression)
    (trace : CanonicalDataHead.Trace registry expanded added result)
    (stopped : CanonicalDataHead.step registry (result.lift' postMap) = none) :
    CanonicalDataHead.Trace registry expression added result := by
  by_cases equal : expanded = expression
  · simpa only [equal] using trace
  · cases trace with
    | refl =>
      have selected := reduction.step (registry := registry) equal
      rw [CanonicalDataHead.step_rename registry scope, selected] at stopped
      contradiction
    | @next _ out added result selected tail =>
      have exactStep := reduction.step (registry := registry) equal
      have output := Option.some.inj (selected.symm.trans exactStep)
      cases output
      simpa only [List.append_nil] using tail

private def Exposure.contractStoppedHeadBeta (henv : env.Ordered)
    (scope : registry.Scoped) (reduction : HeadBeta expanded expression)
    (path : TypeConversion env U Γ expanded expression)
    (E : Exposure env U registry Γ expanded Δ ρ head)
    (stopped : CanonicalDataHead.step registry head = none) :
    Exposure env U registry Γ expression Δ ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := reduction.strip_stopped_trace scope E.trace (E.result_eq ▸ stopped)
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := E.terminal
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := ((E.insertion henv).path henv path.symm).trans E.sound
  headType := E.headType

private def ConstructorExposure.contractHeadBeta (henv : env.Ordered)
    (scope : registry.Scoped) (reduction : HeadBeta expanded expression)
    (equal : env.IsDefEq U Γ expanded expression type)
    (E : ConstructorExposure env U registry Γ expanded type Δ ρ head)
    (stopped : CanonicalDataHead.step registry head = none) :
    ConstructorExposure env U registry Γ expression type Δ ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := reduction.strip_stopped_trace scope E.trace (E.result_eq ▸ stopped)
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := E.terminal
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := ((E.insertion henv).eq henv equal.symm).trans E.sound

def RankedData.ConstructorWitness.contractHeadBeta (henv : env.Ordered)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (W : RankedData.ConstructorWitness env U registry lower Γ leftExpanded rightExpanded type demand) :
    RankedData.ConstructorWitness env U registry lower Γ left right type demand :=
  { W with
    leftExposure := W.leftExposure.prepend henv
      (ConstructorOrigin.ofHeadBeta henv W.leftExposure.baseWF hl cl).symm
    rightExposure := W.rightExposure.prepend henv
      (ConstructorOrigin.ofHeadBeta henv W.rightExposure.baseWF hr cr).symm }

theorem RankedData.ConstructorRelation.contractHeadBeta (henv : env.Ordered)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : RankedData.ConstructorRelation env U registry lower Γ leftExpanded rightExpanded type demand) :
    RankedData.ConstructorRelation env U registry lower Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨W⟩ := H Δ ρ future
  exact ⟨W.contractHeadBeta henv (hl.lift ρ) (hr.lift ρ)
    (cl.weak' henv future.weakening) (cr.weak' henv future.weakening)⟩

theorem TypeRelated.contractHeadBeta (henv : env.Ordered)
    {leftExpanded rightExpanded left right : VExpr} {profile : Profile n}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : TypeConversion env U Γ leftExpanded left)
    (cr : TypeConversion env U Γ rightExpanded right)
    (H : TypeRelated env U registry Γ leftExpanded rightExpanded profile) :
    TypeRelated env U registry Γ left right profile := by
  induction n generalizing Γ leftExpanded rightExpanded left right with
  | zero =>
    intro Δ ρ future atom hm
    obtain ⟨Ω, τ, u, v, ⟨el⟩, ⟨er⟩, huv, hu⟩ := H Δ ρ future atom hm
    exact ⟨Ω, τ, u, v,
      ⟨el.contractHeadBeta henv (hl.lift ρ) (cl.weak' henv future.weakening) trivial⟩,
      ⟨er.contractHeadBeta henv (hr.lift ρ) (cr.weak' henv future.weakening) trivial⟩, huv, hu⟩
  | succ n ih =>
    intro Δ ρ future atom hm
    have h := H Δ ρ future atom hm
    have hl := hl.lift ρ
    have hr := hr.lift ρ
    have cl := cl.weak' henv future.weakening
    have cr := cr.weak' henv future.weakening
    cases atom with
    | sort relevant =>
      obtain ⟨Ω, τ, u, v, ⟨el⟩, ⟨er⟩, huv, hu⟩ := h
      exact ⟨Ω, τ, u, v,
        ⟨el.contractHeadBeta henv hl cl trivial⟩,
        ⟨er.contractHeadBeta henv hr cr trivial⟩, huv, hu⟩
    | fn | ctor | record => exact h.elim
    | family demand =>
      obtain ⟨display⟩ := h
      refine ⟨{ display with
        leftExposure := display.leftExposure.contractStoppedHeadBeta henv display.registryScoped hl cl display.leftTerminal
        rightExposure := display.rightExposure.contractStoppedHeadBeta henv display.registryScoped hr cr display.rightTerminal
        path := ?_ }⟩
      exact (((display.leftExposure.insertion henv).path henv cl.symm).trans display.path).trans
        ((display.rightExposure.insertion henv).path henv cr)
    | pad atom => exact ih hl hr cl cr h
    | pi A B domain rows =>
      obtain ⟨display⟩ := h
      exact ⟨{ display with
        leftExposure := display.leftExposure.contractHeadBeta henv hl cl trivial
        rightExposure := display.rightExposure.contractHeadBeta henv hr cr trivial }⟩


theorem FunctionBehavior.contractHeadBeta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lower : ∀ (Γ : List VExpr) (leftExpanded rightExpanded left right type : VExpr)
      (value support : Profile n),
      HeadBeta leftExpanded left → HeadBeta rightExpanded right →
      env.IsDefEq U Γ leftExpanded left type → env.IsDefEq U Γ rightExpanded right type →
      Related env U registry Γ leftExpanded rightExpanded type value support →
      Related env U registry Γ left right type value support)
    {Γ : List VExpr} {leftExpanded rightExpanded left right type : VExpr}
    {key : Key n} {output : Atom n} {profile : Profile (n + 1)}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ leftExpanded rightExpanded type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile := by
  obtain ⟨seed, A, B, domain, rows, result, hm, hrow, typed, display, behavior⟩ := H
  refine ⟨seed, A, B, domain, rows, result, hm, hrow, typed, display, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := display.leftExposure.insertion henv
  have exposurePath := display.leftExposure.sound.weak' henv future.weakening
  have leftEq := (insertion.eq henv cl).weak' henv future.weakening
  have rightEq := (insertion.eq henv cr).weak' henv future.weakening
  have leftPi := exposurePath.cast leftEq
  have rightPi := exposurePath.cast rightEq
  obtain ⟨_, _, _, _, rowPath, _⟩ := display.rowDomains key result hrow
  have argumentPath := rowPath.weak' henv future.weakening
  have argumentEq : env.IsDefEq U Δ x y ((key.domain.lift' display.map).lift' ρ) := by
    simpa only [Key.rename, lift'_comp] using admitted.2.1
  have pair := argumentPath.cast argumentEq
  obtain ⟨level, bodyType⟩ := display.leftBodyType
  have bodyType' := bodyType.weak' henv future.weakening.cons
  have bodyEq := bodyType'.instDF henv (future.targetWF henv) pair
  have leftX := IsDefEq.appDF leftPi pair.hasType.1
  have leftY := IsDefEq.defeqDF bodyEq.symm (IsDefEq.appDF leftPi pair.hasType.2)
  have rightX := IsDefEq.appDF rightPi pair.hasType.1
  have rightY := IsDefEq.defeqDF bodyEq.symm (IsDefEq.appDF rightPi pair.hasType.2)
  have leftHead := hl.lift (display.map.comp ρ)
  have rightHead := hr.lift (display.map.comp ρ)
  obtain ⟨leftBehavior, rightBehavior, crossBehavior⟩ := behavior Δ ρ future x y admitted
  exact ⟨lower Δ _ _ _ _ _ _ _ (leftHead.app x) (leftHead.app y)
      (by simpa only [lift'_comp] using leftX) (by simpa only [lift'_comp] using leftY) leftBehavior,
    lower Δ _ _ _ _ _ _ _ (rightHead.app x) (rightHead.app y)
      (by simpa only [lift'_comp] using rightX) (by simpa only [lift'_comp] using rightY) rightBehavior,
    lower Δ _ _ _ _ _ _ _ (leftHead.app x) (rightHead.app x)
      (by simpa only [lift'_comp] using leftX) (by simpa only [lift'_comp] using rightX) crossBehavior⟩


open private sort_cover pi_cover family_cover TypeRelated.sort_member_path from Lean4Lean.Theory.Typing.AnchoredBeta

theorem Related.contractHeadBeta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {value support : Profile n}
    {Γ : List VExpr} {leftExpanded rightExpanded left right type : VExpr}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : Related env U registry Γ leftExpanded rightExpanded type value support) :
    Related env U registry Γ left right type value support := by
  induction n generalizing Γ leftExpanded rightExpanded left right type with
  | zero =>
    intro requested hm Δ ρ future
    rcases H requested hm Δ ρ future with empty | ⟨Ω, τ, insertion, typed, code, terms⟩
    · exact .inl empty
    have hl' := (hl.lift ρ).lift τ
    have hr' := (hr.lift ρ).lift τ
    have cl' := (cl.weak' henv future.weakening).weak' henv insertion.weakening
    have cr' := (cr.weak' henv future.weakening).weak' henv insertion.weakening
    have hΩ := insertion.targetWF henv
    obtain ⟨cover, hcover, _⟩ := typed ((requested.rename ρ).rename τ) (by
      rw [Profile.rename_singleton, Profile.rename_singleton]
      exact List.mem_singleton_self _)
    have hsort := code Ω .refl (.refl hΩ) cover
      (by simpa only [Profile.rename_refl] using hcover)
    simp only [lift'_refl] at hsort
    obtain ⟨level, path⟩ := SortRelated.path henv hsort
    change TypeRelated env U registry Ω ((leftExpanded.lift' ρ).lift' τ)
      ((rightExpanded.lift' ρ).lift' τ) ((Profile.singleton requested).rename ρ |>.rename τ) at terms
    exact .inr ⟨Ω, τ, insertion, typed, code,
      TypeRelated.contractHeadBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) terms⟩
  | succ n ih =>
    intro requested hm Δ ρ future
    rcases H requested hm Δ ρ future with empty | ⟨Ω, τ, insertion, typed, code, terms⟩
    · exact .inl empty
    have hl' := (hl.lift ρ).lift τ
    have hr' := (hr.lift ρ).lift τ
    have cl' := (cl.weak' henv future.weakening).weak' henv insertion.weakening
    have cr' := (cr.weak' henv future.weakening).weak' henv insertion.weakening
    have hΩ := insertion.targetWF henv
    refine .inr ⟨Ω, τ, insertion, typed, code, ?_⟩
    intro atom ha
    have ht := typed.singleton_of_mem ha
    have hv := terms atom ha
    cases atom with
    | fn key output =>
      exact FunctionBehavior.contractHeadBeta henv (fun Γ le re l r A p d hl hr cl cr h =>
        ih hl hr cl cr h) hl' hr' cl' cr' hv
    | pad lower => exact ih hl' hr' cl' cr' hv
    | sort relevant =>
      change TypeRelated env U registry Ω ((leftExpanded.lift' ρ).lift' τ)
        ((rightExpanded.lift' ρ).lift' τ) (.sort (n := n + 1) relevant) at hv
      obtain ⟨r, hm⟩ := sort_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.contractHeadBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv
    | ctor demand => exact RankedData.ConstructorRelation.contractHeadBeta henv hl' hr' cl' cr' hv
    | record demand =>
      exact RankedData.RecordRelation.contractHeadBeta henv (fun Γ le re l r A p d hl hr cl cr h =>
        ih hl hr cl cr h) hl' hr' cl' cr' hv
    | family demand =>
      change TypeRelated env U registry Ω ((leftExpanded.lift' ρ).lift' τ)
        ((rightExpanded.lift' ρ).lift' τ) (.singleton (n := n + 1) (.family demand)) at hv
      obtain ⟨r, hm⟩ := family_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.contractHeadBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv
    | pi A B domain rows =>
      change TypeRelated env U registry Ω ((leftExpanded.lift' ρ).lift' τ)
        ((rightExpanded.lift' ρ).lift' τ) (.pi A B domain rows) at hv
      obtain ⟨r, hm⟩ := pi_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.contractHeadBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv

end Lean4Lean.AnchoredSemantics
