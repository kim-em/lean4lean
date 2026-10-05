import Lean4Lean.Theory.Typing.AnchoredFunctionDisplayReplay
import Lean4Lean.Theory.Typing.AnchoredTransitivity
import Lean4Lean.Theory.Typing.AnchoredPadding
import Lean4Lean.Theory.Typing.AnchoredLiteralPiTransport

/-! Finite application paths for a native RHS. Nodes contain concrete typed
displays and actual admitted arguments, never a semantic producer callback.
Every application or unpadding step strictly lowers the finite demand rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

inductive RhsApplicationPath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) :
    (n : Nat) → List VExpr → VExpr → Atom n →
    (m : Nat) → List VExpr → VExpr → Atom m → Type where
  | done : RhsApplicationPath env U registry n Γ type atom n Γ type atom
  | app
      (display : PiWitness env U registry (relations env U registry n)
        Γ type type A B domain rows)
      (literal : display.leftExposure.postContext = display.context)
      (row : (key, result) ∈ rows)
      (typed : (Profile.singleton output).HasType result)
      (future : FutureInsertion env U display.context Δ ρ)
      (admitted : Admitted env U registry Δ (key.rename (display.map.comp ρ)) x y)
      (tail : RhsApplicationPath env U registry n Δ
        ((display.leftBody.lift' ρ.cons).inst x) (output.rename (display.map.comp ρ))
        m Ω finalType finalAtom) :
      RhsApplicationPath env U registry (n + 1) Γ type (.fn key output)
        m Ω finalType finalAtom
  | unpad (tail : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom) :
      RhsApplicationPath env U registry (n + 1) Γ type (.pad atom) m Ω finalType finalAtom

namespace RhsApplicationPath

def leftAction : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    VExpr → VExpr
  | .done, expression => expression
  | .app (ρ := ρ) (x := x) display _ _ _ _ _ tail, expression =>
    tail.leftAction (.app (expression.lift' (display.map.comp ρ)) x)
  | .unpad tail, expression => tail.leftAction expression

def rightAction : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    VExpr → VExpr
  | .done, expression => expression
  | .app (ρ := ρ) (y := y) display _ _ _ _ _ tail, expression =>
    tail.rightAction (.app (expression.lift' (display.map.comp ρ)) y)
  | .unpad tail, expression => tail.rightAction expression

/-- The first application fixes the output support from its stored row.
Later applications and unpadding retain this finite, computed choice. -/
def supportAction : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    Profile n → Profile m
  | .done, support => support
  | .app (ρ := ρ) (result := result) display _ _ _ _ _ tail, _ =>
    tail.supportAction (result.rename (display.map.comp ρ))
  | .unpad tail, support => tail.supportAction support.down

def hasApplication : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom → Bool
  | .done => false
  | .app .. => true
  | .unpad tail => tail.hasApplication

theorem supportAction_independent
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (nonempty : path.hasApplication = true) (first second : Profile n) :
    path.supportAction first = path.supportAction second := by
  induction path with
  | done => cases nonempty
  | app => rfl
  | unpad tail ih => exact ih nonempty first.down second.down

def castStart (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (types : type = type') (atoms : atom = atom') :
    RhsApplicationPath env U registry n Γ type' atom' m Ω finalType finalAtom :=
  types ▸ atoms ▸ path

theorem leftAction_castStart
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (types : type = type') (atoms : atom = atom') (expression : VExpr) :
    (path.castStart types atoms).leftAction expression = path.leftAction expression := by
  cases types
  cases atoms
  rfl

theorem rightAction_castStart
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (types : type = type') (atoms : atom = atom') (expression : VExpr) :
    (path.castStart types atoms).rightAction expression = path.rightAction expression := by
  cases types
  cases atoms
  rfl

theorem supportAction_castStart
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (types : type = type') (atoms : atom = atom') (support : Profile n) :
    (path.castStart types atoms).supportAction support = path.supportAction support := by
  cases types
  cases atoms
  rfl

/-- The stored finite path can query any new proof of the original RHS
capability. Internal saturation frames and selected type supports may differ. -/
theorem replayExact
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Ω : List VExpr} {type finalType left right : VExpr}
    {atom : Atom n} {finalAtom : Atom m} {support : Profile n}
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type (.singleton atom) support) :
    Related env U registry Ω (path.leftAction left) (path.rightAction right)
      finalType (.singleton finalAtom) (path.supportAction support) := by
  induction path generalizing left right with
  | done => exact related
  | @app n Γ type A B domain rows key result output Δ ρ x y m Ω finalType finalAtom
      display literal row typed future admitted tail ih =>
    have outputs := related.atDisplay henv hscoped hΓ display row typed
      Δ ρ future x y admitted
    have paired := Related.trans henv hscoped outputs.2.2 outputs.2.1
    exact ih (future.targetWF henv) paired
  | unpad tail ih =>
    exact ih hΓ (Related.unpad henv hΓ related)

theorem replay
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Ω : List VExpr} {type finalType left right : VExpr}
    {atom : Atom n} {finalAtom : Atom m} {support : Profile n}
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type (.singleton atom) support) :
    ∃ result : Profile m, Related env U registry Ω
      (path.leftAction left) (path.rightAction right) finalType (.singleton finalAtom) result :=
  ⟨path.supportAction support, path.replayExact henv hscoped hΓ related⟩

/-- A path containing an application has a base-chosen support even when
the incoming RHS relation was obtained with an arbitrary private support. -/
theorem replayFixed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Ω : List VExpr} {type finalType left right : VExpr}
    {atom : Atom n} {finalAtom : Atom m} {support : Profile n}
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (nonempty : path.hasApplication = true)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type (.singleton atom) support) :
    Related env U registry Ω (path.leftAction left) (path.rightAction right)
      finalType (.singleton finalAtom) (path.supportAction .empty) := by
  rw [← path.supportAction_independent nonempty support .empty]
  exact path.replayExact henv hscoped hΓ related

/-- A repeated native reduction adds only inhabited proof slots. Transport
the finite path into that new frame, retaining a commuting proof insertion
at its final world. No arbitrary future-world amalgamation is required. -/
theorem proofFutureWithSupport
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Γ' Ω : List VExpr} {type finalType : VExpr}
    {atom : Atom n} {finalAtom : Atom m} {κ : Lift}
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (insertion : ProofInsertion env U Γ Γ' κ) :
    ∃ Ω' τ, ProofInsertion env U Ω Ω' τ ∧
      ∃ changed : RhsApplicationPath env U registry n Γ' (type.lift' κ) (atom.rename κ)
        m Ω' (finalType.lift' τ) (finalAtom.rename τ),
        (∀ expression, changed.leftAction (expression.lift' κ) =
          (path.leftAction expression).lift' τ) ∧
        (∀ expression, changed.rightAction (expression.lift' κ) =
          (path.rightAction expression).lift' τ) ∧
        (∀ support : Profile n, changed.supportAction (support.rename κ) =
          (path.supportAction support).rename τ) ∧
        changed.hasApplication = path.hasApplication := by
  induction path generalizing Γ' κ with
  | done => exact ⟨Γ', κ, insertion, .done, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  | unpad tail ih =>
    obtain ⟨Ω', τ, last, changed, leftEq, rightEq, supportEq, hasEq⟩ := ih insertion
    refine ⟨Ω', τ, last, .unpad changed, leftEq, rightEq, ?_, hasEq⟩
    intro support
    simpa only [supportAction, Profile.down_rename] using supportEq support.down
  | @app n Γ type A B domain rows key result output Δ ρ x y m Ω finalType finalAtom
      display literal row typed future admitted tail ih =>
    obtain ⟨shifted, j, leg, square, bodyEq, literal'⟩ :=
      display.proofFutureLiteral henv hscoped literal insertion
    obtain ⟨W, α, β, proof, future', push⟩ := leg.pushout future henv
    have maps : κ.comp (shifted.map.comp β) = (display.map.comp ρ).comp α := by
      rw [← Lift.comp_assoc, ← square, Lift.comp_assoc, push, ← Lift.comp_assoc]
    have harg : Admitted env U registry W
        ((key.rename κ).rename (shifted.map.comp β)) (x.lift' α) (y.lift' α) := by
      simpa only [← Key.rename_comp, maps] using admitted.future henv proof.toFuture
    have htype : (shifted.leftBody.lift' β.cons).inst (x.lift' α) =
        (((display.leftBody.lift' ρ.cons).inst x).lift' α) := by
      rw [bodyEq, ← lift'_comp]
      change (display.leftBody.lift' (j.comp β).cons).inst (x.lift' α) = _
      rw [push, lift'_inst_hi, ← lift'_comp]
      rfl
    have hatom : (output.rename κ).rename (shifted.map.comp β) =
        (output.rename (display.map.comp ρ)).rename α := by
      simp only [← Atom.rename_comp, maps]
    obtain ⟨Ω', τ, last, changed, leftEq, rightEq, supportEq, _⟩ := ih proof
    let next : RhsApplicationPath env U registry n W
        ((shifted.leftBody.lift' β.cons).inst (x.lift' α))
        ((output.rename κ).rename (shifted.map.comp β))
        m Ω' (finalType.lift' τ) (finalAtom.rename τ) :=
      changed.castStart htype.symm hatom.symm
    have nextLeft (expression : VExpr) : next.leftAction (expression.lift' α) =
        (tail.leftAction expression).lift' τ := by
      simpa only [next, leftAction_castStart] using leftEq expression
    have nextRight (expression : VExpr) : next.rightAction (expression.lift' α) =
        (tail.rightAction expression).lift' τ := by
      simpa only [next, rightAction_castStart] using rightEq expression
    have nextSupport (support : Profile n) : next.supportAction (support.rename α) =
        (tail.supportAction support).rename τ := by
      simpa only [next, supportAction_castStart] using supportEq support
    refine ⟨Ω', τ, last, .app shifted literal'
      (List.mem_map.mpr ⟨(key, result), row, rfl⟩) ?_ future' harg next, ?_, ?_, ?_, ?_⟩
    · simpa only [Profile.rename_singleton] using
        (Profile.rename_hasType_iff (ρ := κ)).mpr typed
    · intro expression
      simpa only [leftAction, lift', ← lift'_comp, maps] using
        nextLeft (.app (expression.lift' (display.map.comp ρ)) x)
    · intro expression
      simpa only [rightAction, lift', ← lift'_comp, maps] using
        nextRight (.app (expression.lift' (display.map.comp ρ)) y)
    · intro support
      simpa only [supportAction, ← Profile.rename_comp, maps] using
        nextSupport (result.rename (display.map.comp ρ))
    · rfl

/-- Backwards-compatible term-action projection of the stronger finite
support-preserving transport. -/
theorem proofFuture
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Γ' Ω : List VExpr} {type finalType : VExpr}
    {atom : Atom n} {finalAtom : Atom m} {κ : Lift}
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (insertion : ProofInsertion env U Γ Γ' κ) :
    ∃ Ω' τ, ProofInsertion env U Ω Ω' τ ∧
      ∃ changed : RhsApplicationPath env U registry n Γ' (type.lift' κ) (atom.rename κ)
        m Ω' (finalType.lift' τ) (finalAtom.rename τ),
        (∀ expression, changed.leftAction (expression.lift' κ) =
          (path.leftAction expression).lift' τ) ∧
        (∀ expression, changed.rightAction (expression.lift' κ) =
          (path.rightAction expression).lift' τ) := by
  obtain ⟨Ω', τ, frame, changed, left, right, _⟩ :=
    path.proofFutureWithSupport henv hscoped insertion
  exact ⟨Ω', τ, frame, changed, left, right⟩

end RhsApplicationPath
end Lean4Lean.AnchoredSemantics
