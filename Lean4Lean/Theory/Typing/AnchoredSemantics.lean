import Lean4Lean.Theory.Typing.AnchoredTypeExposure
import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Typing.AnchoredRelations
import Lean4Lean.Theory.Typing.CanonicalDataHeadApplication
import Lean4Lean.Theory.Typing.CanonicalDataHeadLevels
import Lean4Lean.Theory.Typing.CanonicalDataHeadTraceSubstitution
import Lean4Lean.Theory.Typing.TypedWorldMixed
import Lean4Lean.Theory.Typing.NativeCaptureTransport

/-!
Rank-recursive target predicates for the anchored-observation construction.

These definitions use the concrete canonical head machine and generated,
inhabited proof insertions. No source observation or adequacy predicate occurs
in them. Each function demand has one atomic output. Admission keeps the raw
domain, anchor and input demand fixed, while existentially choosing its type
support. A Pi witness retains the particular support used by each covering row.

This is a candidate target interpretation, not a proved equality foundation.
Its support-change theorem is checked in `AnchoredSupport`. Its source-observation
producer and coverage outside the canonical machine's fragment remain obligations.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

/-- Both exposed universe levels agree, not merely their proof/data flag. -/
def SortRelated (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (relevant : Bool) : Prop :=
  ∃ Δ ρ u v,
    Nonempty (Exposure env U registry Γ left Δ ρ (.sort u)) ∧
    Nonempty (Exposure env U registry Γ right Δ ρ (.sort v)) ∧
    u ≈ v ∧ Relevant u relevant

/-- A common typed display of two type codes. Each row supplies capabilities
for the ACTUAL instantiated codomains, as well as paths to the frozen raw
prototype. Prototype paths alone would not support dependent application. -/
structure PiWitness (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right prototypeDomain prototypeBody : VExpr)
    (domain : Profile n) (rows : List (Key n × Profile n)) where
  context : List VExpr
  map : Lift
  leftDomain : VExpr
  leftBody : VExpr
  rightDomain : VExpr
  rightBody : VExpr
  leftExposure : Exposure env U registry Γ left context map (.forallE leftDomain leftBody)
  rightExposure : Exposure env U registry Γ right context map (.forallE rightDomain rightBody)
  leftDomainType : env.IsType U context leftDomain
  rightDomainType : env.IsType U context rightDomain
  leftBodyType : env.IsType U (leftDomain :: context) leftBody
  rightBodyType : env.IsType U (rightDomain :: context) rightBody
  domains : TypeConversion env U context leftDomain rightDomain
  bodies : TypeConversion env U (leftDomain :: context) leftBody rightBody
  prototypeDomainPath : TypeConversion env U context leftDomain (prototypeDomain.lift' map)
  prototypeBodyPath : TypeConversion env U (leftDomain :: context)
    leftBody (prototypeBody.lift' map.cons)
  domainRelated : lower.code context leftDomain rightDomain (domain.rename map)
  rowDomains : ∀ key output, (key, output) ∈ rows →
    ∃ support : Profile n,
      (key.rename map).input.HasType support ∧ support.HasType (.sort true) ∧
      support ≤ domain.rename map ∧
      TypeConversion env U context (key.domain.lift' map) leftDomain ∧
      lower.code context (key.domain.lift' map) leftDomain support
  rowBodies : ∀ key output, (key, output) ∈ rows →
    ∀ Δ ρ, FutureInsertion env U context Δ ρ → ∀ x y,
      Admission env U lower Δ (key.rename (map.comp ρ)) x y →
      lower.code Δ ((leftBody.lift' ρ.cons).inst x)
        ((leftBody.lift' ρ.cons).inst y) (output.rename (map.comp ρ)) ∧
      lower.code Δ ((rightBody.lift' ρ.cons).inst x)
        ((rightBody.lift' ρ.cons).inst y) (output.rename (map.comp ρ)) ∧
      lower.code Δ ((leftBody.lift' ρ.cons).inst x)
        ((rightBody.lift' ρ.cons).inst x) (output.rename (map.comp ρ))

def CodeAtom (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right : VExpr) : Atom (n + 1) → Prop
  | .sort relevant => SortRelated env U registry Γ left right relevant
  | .fn .. | .ctor .. | .record .. => False
  | .family demand => Nonempty (RankedData.FamilyWitness env U registry lower Γ left right demand)
  | .pi A B domain rows => Nonempty (PiWitness env U registry lower Γ left right A B domain rows)
  | .pad atom => lower.code Γ left right (.singleton atom)

/-- Function behavior retains one chosen actual display and its selected
codomain row. The anchor realizes its own demand in the base context: a
vacuous function behavior at an impossible key cannot support source eta.
Admission is independent of the covering row's support witness. -/
def FunctionBehavior (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (key : Key n) (output : Atom n) (typeProfile : Profile (n + 1)) : Prop :=
  Admission env U lower Γ key key.anchor key.anchor ∧
  ∃ A B, ∃ (domain : Profile n) (rows : List (Key n × Profile n)) (resultType : Profile n),
    (AtomData.pi A B domain rows : Atom (n + 1)) ∈ typeProfile.atoms ∧
    (key, resultType) ∈ rows ∧ (Profile.singleton output).HasType resultType ∧
    ∃ display : PiWitness env U registry lower Γ type type A B domain rows,
      ∀ Δ ρ, FutureInsertion env U display.context Δ ρ → ∀ x y,
        Admission env U lower Δ (key.rename (display.map.comp ρ)) x y →
        lower.term Δ
          (.app (left.lift' (display.map.comp ρ)) x)
          (.app (left.lift' (display.map.comp ρ)) y)
          ((display.leftBody.lift' ρ.cons).inst x)
          (.singleton (output.rename (display.map.comp ρ)))
          (resultType.rename (display.map.comp ρ)) ∧
        lower.term Δ
          (.app (right.lift' (display.map.comp ρ)) x)
          (.app (right.lift' (display.map.comp ρ)) y)
          ((display.leftBody.lift' ρ.cons).inst x)
          (.singleton (output.rename (display.map.comp ρ)))
          (resultType.rename (display.map.comp ρ)) ∧
        lower.term Δ
          (.app (left.lift' (display.map.comp ρ)) x)
          (.app (right.lift' (display.map.comp ρ)) x)
          ((display.leftBody.lift' ρ.cons).inst x)
          (.singleton (output.rename (display.map.comp ρ)))
          (resultType.rename (display.map.comp ρ))

/-- Future worlds are quantified before choosing a display. Thus extension
uses composition of actual insertion histories, rather than requiring an
arbitrary pair of chosen displays to admit a coherent transport. -/
def FutureCode (env : VEnv) (U : Nat)
    (core : List VExpr → VExpr → VExpr → Profile n → Prop)
    (Γ : List VExpr) (left right : VExpr) (profile : Profile n) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    core Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ)

def TermAtom (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (typeProfile : Profile (n + 1)) : Atom (n + 1) → Prop
  | .fn key output => FunctionBehavior env U registry lower Γ left right type key output typeProfile
  | .pad atom => lower.term Γ left right type (.singleton atom) typeProfile.down
  | .ctor demand => RankedData.ConstructorRelation env U registry lower Γ left right type demand
  | .record demand => RankedData.RecordRelation env U registry lower Γ left right type demand
  | atom => FutureCode env U (fun Δ l r profile =>
      ∀ a ∈ profile.atoms, CodeAtom env U registry lower Δ l r a)
      Γ left right (.singleton atom)

/-- Saturation adds only a generated inhabited proof insertion. All operands
and profiles are lifted from the requested context, so this never asserts
semantic reflection for a private display component. -/
def SaturatedTerm (env : VEnv) (U : Nat)
    (core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop)
    (Γ : List VExpr) (left right type : VExpr) (value typeProfile : Profile n) : Prop :=
  value = .empty ∨ ∃ Δ ρ,
    ProofInsertion env U Γ Δ ρ ∧
    core Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ)

def FutureTerm (env : VEnv) (U : Nat)
    (core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop)
    (Γ : List VExpr) (left right type : VExpr) (value typeProfile : Profile n) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    core Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ)

/-- Separate atoms can use separate inhabited proof frames. Combining finite
demands therefore does not assert a common unsaturated display for them. -/
def EachAtom
    (core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop)
    (Γ : List VExpr) (left right type : VExpr) (value typeProfile : Profile n) : Prop :=
  ∀ atom ∈ value.atoms, core Γ left right type (.singleton atom) typeProfile

def relations (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) :
    (n : Nat) → Relations n
  | 0 =>
    let code := FutureCode env U fun Γ left right (profile : Profile 0) =>
      ∀ relevant ∈ profile.atoms, SortRelated env U registry Γ left right relevant
    { code := code
      term := EachAtom <| FutureTerm env U <| SaturatedTerm env U fun Γ left right type value typeProfile =>
        value.HasType typeProfile ∧ code Γ type type typeProfile ∧ code Γ left right value }
  | n + 1 =>
    let lower := relations env U registry n
    let code := FutureCode env U fun Γ left right (profile : Profile (n + 1)) =>
      ∀ atom ∈ profile.atoms, CodeAtom env U registry lower Γ left right atom
    { code := code
      term := EachAtom <| FutureTerm env U <| SaturatedTerm env U fun Γ left right type value typeProfile =>
        value.HasType typeProfile ∧ code Γ type type typeProfile ∧
          ∀ atom ∈ value.atoms, TermAtom env U registry lower Γ left right type typeProfile atom }

def TypeRelated (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (profile : Profile n) : Prop :=
  (relations env U registry n).code Γ left right profile

def Related (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (value typeProfile : Profile n) : Prop :=
  (relations env U registry n).term Γ left right type value typeProfile

def Admitted (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (key : Key n) (left right : VExpr) : Prop :=
  Admission env U (relations env U registry n) Γ key left right

end Lean4Lean.AnchoredSemantics
