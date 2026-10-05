import Lean4Lean.Theory.Typing.AnchoredOriginalClosureMeasure

/-! Original Strong derivations as finite data. Reification preserves every
original premise, including instantiated beta and projection formation
premises. No substitution, weakening, endpoint extraction, or semantic
interpretation is used to obtain this tree. The tree is chosen through a
Nonempty theorem because Strong itself lives in Prop. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv

section
set_option hygiene false
variable (env : VEnv) (uvars : Nat)
local notation:65 Γ " ⊢ " e " : " A:30 => Derivation Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => Derivation Γ e1 e2 A

inductive Derivation : List VExpr → VExpr → VExpr → VExpr → Type where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | elimDF {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericType owner = some type →
    type.Closed →
    schema.Permission uvars owner levels target →
    (∀ level ∈ target' :: levels', level.WF uvars) →
    List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels') →
    typeLevel.WF uvars →
    Γ ⊢ type.instL (target :: levels) ≡ type.instL (target' :: levels') : .sort typeLevel →
    Γ ⊢ .elim block owner.val (target :: levels) ≡
      .elim block owner.val (target' :: levels') : type.instL (target :: levels)
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | projDF :
    env.projections typeName info →
    (∀ l ∈ levels, l.WF uvars) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    fieldLevel.WF uvars →
    Γ ⊢ fieldType : .sort fieldLevel →
    Γ ⊢ sourceMajor ≡ major :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    Γ ⊢ sourceMajor ≡ major' :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    info.ctorType.Closed →
    (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero →
    Γ ⊢ .proj typeName index major ≡
      .proj typeName index major' : fieldType
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ B.inst e' : .sort v →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A.lift::A::Γ ⊢ B.liftN 1 1 : .sort v →
    Γ ⊢ e : .forallE A B →
    A::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) →
    A::Γ ⊢ A.lift : .sort u →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls →
    [] ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  | elimIota {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericEquations block owner = some rules →
    df ∈ rules →
    InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission uvars owner levels target →
    typeLevel.WF uvars →
    Γ ⊢ df.type.instL (target :: levels) : .sort typeLevel →
    Γ ⊢ df.lhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.rhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.lhs.instL (target :: levels) ≡ df.rhs.instL (target :: levels) :
      df.type.instL (target :: levels)
  | projIota :
    env.projections typeName info →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType →
    args[info.nparams + index]? = some field →
    Γ ⊢ field : fieldType →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) ≡ field :
      fieldType
  | structEta :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) :
      VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) ≡ e :
      VExpr.mkApps (.const typeName levels) params
  | unitLike :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    info.numFields = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e' : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e ≡ e' : VExpr.mkApps (.const typeName levels) params

end

/-- Forget only the finite tree; replay exactly the same original rules. -/
theorem Derivation.forget (derivation : Derivation env U source left right type) :
    env.IsDefEqStrong U source left right type := by
  induction derivation with
  | bvar => apply VEnv.IsDefEqStrong.bvar <;> assumption
  | symm => apply VEnv.IsDefEqStrong.symm <;> assumption
  | trans => apply VEnv.IsDefEqStrong.trans <;> assumption
  | sortDF => apply VEnv.IsDefEqStrong.sortDF <;> assumption
  | constDF => apply VEnv.IsDefEqStrong.constDF <;> assumption
  | elimDF => apply VEnv.IsDefEqStrong.elimDF <;> assumption
  | appDF hu hv => apply VEnv.IsDefEqStrong.appDF hu hv <;> assumption
  | projDF => apply VEnv.IsDefEqStrong.projDF <;> assumption
  | lamDF hu hv => apply VEnv.IsDefEqStrong.lamDF hu hv <;> assumption
  | forallEDF => apply VEnv.IsDefEqStrong.forallEDF <;> assumption
  | defeqDF => apply VEnv.IsDefEqStrong.defeqDF <;> assumption
  | beta hu hv => apply VEnv.IsDefEqStrong.beta hu hv <;> assumption
  | eta hu hv => apply VEnv.IsDefEqStrong.eta hu hv <;> assumption
  | proofIrrel => apply VEnv.IsDefEqStrong.proofIrrel <;> assumption
  | extra => apply VEnv.IsDefEqStrong.extra <;> assumption
  | elimIota => apply VEnv.IsDefEqStrong.elimIota <;> assumption
  | projIota => apply VEnv.IsDefEqStrong.projIota <;> assumption
  | structEta => apply VEnv.IsDefEqStrong.structEta <;> assumption
  | unitLike => apply VEnv.IsDefEqStrong.unitLike <;> assumption

/-- Prop induction proves existence of a finite data tree. We do not eliminate
an original proof into a number, nor identify proof identities. -/
theorem Derivation.reify (original : env.IsDefEqStrong U source left right type) :
    Nonempty (Derivation env U source left right type) := by
  induction original with
  | bvar =>
    constructor
    apply Derivation.bvar <;> first | assumption | exact Classical.choice (by assumption)
  | symm =>
    constructor
    apply Derivation.symm <;> first | assumption | exact Classical.choice (by assumption)
  | trans =>
    constructor
    apply Derivation.trans <;> first | assumption | exact Classical.choice (by assumption)
  | sortDF =>
    constructor
    apply Derivation.sortDF <;> first | assumption | exact Classical.choice (by assumption)
  | constDF =>
    constructor
    apply Derivation.constDF <;> first | assumption | exact Classical.choice (by assumption)
  | elimDF =>
    constructor
    apply Derivation.elimDF <;> first | assumption | exact Classical.choice (by assumption)
  | appDF hu hv =>
    constructor
    apply Derivation.appDF hu hv <;> first | assumption | exact Classical.choice (by assumption)
  | projDF =>
    constructor
    apply Derivation.projDF <;> first | assumption | exact Classical.choice (by assumption)
  | lamDF hu hv =>
    constructor
    apply Derivation.lamDF hu hv <;> first | assumption | exact Classical.choice (by assumption)
  | forallEDF =>
    constructor
    apply Derivation.forallEDF <;> first | assumption | exact Classical.choice (by assumption)
  | defeqDF =>
    constructor
    apply Derivation.defeqDF <;> first | assumption | exact Classical.choice (by assumption)
  | beta hu hv =>
    constructor
    apply Derivation.beta hu hv <;> first | assumption | exact Classical.choice (by assumption)
  | eta hu hv =>
    constructor
    apply Derivation.eta hu hv <;> first | assumption | exact Classical.choice (by assumption)
  | proofIrrel =>
    constructor
    apply Derivation.proofIrrel <;> first | assumption | exact Classical.choice (by assumption)
  | extra =>
    constructor
    apply Derivation.extra <;> first | assumption | exact Classical.choice (by assumption)
  | elimIota =>
    constructor
    apply Derivation.elimIota <;> first | assumption | exact Classical.choice (by assumption)
  | projIota =>
    constructor
    apply Derivation.projIota <;> first | assumption | exact Classical.choice (by assumption)
  | structEta =>
    constructor
    apply Derivation.structEta <;> first | assumption | exact Classical.choice (by assumption)
  | unitLike =>
    constructor
    apply Derivation.unitLike <;> first | assumption | exact Classical.choice (by assumption)

/-- Finite budgets for structural endpoint nodes, with domain-origin
captures for their binder premises. -/
def applicationOrigin (domain codomain function argument result : Origin) : Origin :=
  .binder domain [codomain] [function, argument, result]

def lambdaOrigin (domain codomain body : Origin) : Origin :=
  .binder domain [codomain, body] []

def betaLeftOrigin (domain codomain body argument result : Origin) : Origin :=
  applicationOrigin domain codomain (lambdaOrigin domain codomain body) argument result

/-- The synthetic application in eta has a retained source domain for its
bound argument. Its codomain formation uses a SECOND type-origin slot. -/
def etaBodyOrigin (codomain liftedCodomain liftedTerm liftedDomain : Origin) : Origin :=
  .binder liftedDomain [liftedCodomain]
    [liftedTerm, .rule [liftedDomain], codomain]

/-- A finite lambda/application/variable exposure ledger. Repeated formation
references are explicitly reserved, and no synthetic Strong proof is treated
as an original recursive premise. -/
def etaLeftOrigin (domain codomain liftedCodomain liftedTerm liftedDomain : Origin) : Origin :=
  .binder domain [codomain, etaBodyOrigin codomain liftedCodomain liftedTerm liftedDomain] []

/-- The schedule is computed from the actual original children. In beta,
`instantiated` is the stored original endpoint premise, not an instantiated
copy of `body`. All source formation premises retain their own reserves. -/
def Derivation.origin : Derivation env U source left right type → Origin
  | .bvar _ _ formation => .rule [formation.origin]
  | .symm original => .rule [original.origin]
  | .trans first second => .rule [first.origin, second.origin]
  | .sortDF .. => .rule []
  | .constDF _ _ _ _ _ _ closed ambient => .rule [closed.origin, ambient.origin]
  | .elimDF _ _ _ _ _ _ _ formation => .rule [formation.origin]
  | .appDF _ _ domain codomain function argument result =>
      .rule [applicationOrigin domain.origin codomain.origin function.origin argument.origin result.origin,
        result.origin]
  | .projDF _ _ _ _ _ _ _ field leftMajor rightMajor _ _ =>
      .rule [field.origin, leftMajor.origin, rightMajor.origin]
  | .lamDF _ _ domain codomain codomain' body body' =>
      .rule [lambdaOrigin domain.origin codomain.origin body.origin,
        lambdaOrigin domain.origin codomain'.origin body'.origin,
        .binder domain.origin [codomain'.origin, codomain.origin] []]
  | .forallEDF _ _ domain body body' => .binder domain.origin [body.origin, body'.origin] []
  | .defeqDF _ types terms => .rule [types.origin, terms.origin]
  | .beta _ _ domain codomain body argument result instantiated =>
      .rule [.typedBeta domain.origin body.origin argument.origin instantiated.origin
        [.binder domain.origin [codomain.origin] [], result.origin],
        betaLeftOrigin domain.origin codomain.origin body.origin argument.origin result.origin]
  | .eta _ _ domain codomain liftedCodomain term liftedTerm liftedDomain =>
      .rule [term.origin,
        etaLeftOrigin domain.origin codomain.origin liftedCodomain.origin liftedTerm.origin liftedDomain.origin]
  | .proofIrrel proposition left right => .rule [proposition.origin, left.origin, right.origin]
  | .extra _ _ _ _ formation left right ambientLeft ambientRight =>
      .rule [formation.origin, left.origin, right.origin, ambientLeft.origin, ambientRight.origin]
  | .elimIota _ _ _ _ _ _ formation left right =>
      .rule [formation.origin, left.origin, right.origin]
  | .projIota _ projection _ field => .rule [projection.origin, field.origin]
  | .structEta _ _ _ major constructor => .rule [major.origin, constructor.origin]
  | .unitLike _ _ _ _ left right => .rule [left.origin, right.origin]

/-- The beta schedule now applies to actual original Strong premises. -/
theorem Derivation.beta_comparison_schedule
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (body : Derivation env U (A :: source) e e B)
    (argument : Derivation env U source a a A)
    (result : Derivation env U source (B.inst a) (B.inst a) (.sort v))
    (instantiated : Derivation env U source (e.inst a) (e.inst a) (B.inst a))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close instantiated.origin captured).cost +
        (Closure.close body.origin
          (.bundle (.close argument.origin captured) (.close domain.origin captured) :: captured)).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.beta domainWF bodyWF domain codomain body argument result
          instantiated).origin captured).cost) :=
  schedule_strict (Nat.lt_trans
    (typed_beta_comparison domain.origin body.origin argument.origin instantiated.origin
      [.binder domain.origin [codomain.origin] [], result.origin] captured)
    (original_child_same_environment (Origin.rule_child (by simp)) captured)) _ _

/-- Both eta endpoints fit below the original eta rule, with the left
endpoint ledger reserving the actual domain type closures under its binders. -/
theorem Derivation.eta_endpoint_schedule
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (liftedCodomain : Derivation env U (A.lift :: A :: source)
      (B.liftN 1 1) (B.liftN 1 1) (.sort v))
    (term : Derivation env U source e e (.forallE A B))
    (liftedTerm : Derivation env U (A :: source) e.lift e.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation env U (A :: source) A.lift A.lift (.sort u))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close term.origin captured).cost +
        (Closure.close (etaLeftOrigin domain.origin codomain.origin liftedCodomain.origin
          liftedTerm.origin liftedDomain.origin) captured).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.eta domainWF bodyWF domain codomain liftedCodomain
          term liftedTerm liftedDomain).origin captured).cost) :=
  schedule_strict (original_two_children term.origin
    (etaLeftOrigin domain.origin codomain.origin liftedCodomain.origin
      liftedTerm.origin liftedDomain.origin) [] captured) _ _

/-- The two ORIGINAL premises at a transitivity midpoint fit below that
original transitivity node. Endpoint reindexing still needs its own proof. -/
theorem Derivation.trans_comparison_schedule
    (first : Derivation env U source left middle type)
    (second : Derivation env U source middle right type)
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close first.origin captured).cost + (Closure.close second.origin captured).cost) <
      schedule .fundamental ((Closure.close (Derivation.trans first second).origin captured).cost) :=
  schedule_strict (original_two_children first.origin second.origin [] captured) _ _

/-- A side of an actual finite original derivation, retaining its assigned
type. Context formations may use the right side of an original domain
equality; no synthetic diagonal proof is stored or charged. -/
inductive EndpointRef (env : VEnv) (U : Nat) :
    List VExpr → VExpr → VExpr → Type where
  | left (original : Derivation env U Γ left right type) : EndpointRef env U Γ left type
  | right (original : Derivation env U Γ left right type) : EndpointRef env U Γ right type

def EndpointRef.origin : EndpointRef env U Γ expression type → Origin
  | .left original | .right original => original.origin

theorem EndpointRef.sound (reference : EndpointRef env U Γ expression type) :
    env.IsDefEqStrong U Γ expression expression type := by
  cases reference with
  | left original => exact original.forget.hasType.1
  | right original => exact original.forget.hasType.2

/-- Context declarations retain their formation derivation at the tail
where the declaration was introduced. They never capture the new variable. -/
inductive ContextDerivation (env : VEnv) (U : Nat) : List VExpr → Type where
  | nil : ContextDerivation env U []
  | cons (tail : ContextDerivation env U source)
      (domain : EndpointRef env U source A (.sort level)) :
      ContextDerivation env U (A :: source)

theorem ContextDerivation.forget (context : ContextDerivation env U source) :
    env.CtxStrong U source := by
  induction context with
  | nil => trivial
  | cons tail domain ih => exact ⟨ih, _, domain.sound⟩

theorem ContextDerivation.reify (context : env.CtxStrong U source) :
    Nonempty (ContextDerivation env U source) := by
  induction source with
  | nil => exact ⟨.nil⟩
  | cons A source ih =>
    obtain ⟨tail, level, domain⟩ := context
    obtain ⟨tail⟩ := ih tail
    obtain ⟨domain⟩ := Derivation.reify domain
    exact ⟨.cons tail (.left domain)⟩

/-- A selected formation is an ACTUAL node of the stored context spine. -/
inductive ContextDerivation.Location :
    ContextDerivation env U source →
    {tailSource : List VExpr} → (tail : ContextDerivation env U tailSource) →
    {A : VExpr} → {level : VLevel} → EndpointRef env U tailSource A (.sort level) → Type where
  | here : Location (.cons tail domain) tail domain
  | there (location : Location context tail domain) :
      Location (.cons context newDomain) tail domain

private def declarationType (_ : EndpointRef env U source A (.sort level)) : VExpr := A

def ContextDerivation.Location.prefix
    (location : Location context tail domain) : List VExpr :=
  match location with
  | .here => []
  | .there (newDomain := newDomain) parent => declarationType newDomain :: parent.prefix

theorem ContextDerivation.Location.source_eq
    {context : ContextDerivation env U source}
    {tail : ContextDerivation env U tailSource}
    {domain : EndpointRef env U tailSource A (.sort level)}
    (location : Location context tail domain) : source = location.prefix ++ (A :: tailSource) := by
  induction location with
  | here => rfl
  | there _ ih => exact congrArg (List.cons _) ih

/-- Both the stored formation and its captured type-origin environment are
finite and confined to earlier context declarations. Target anchor terms
are deliberately absent from this source provenance. -/
def ContextDerivation.closures : ContextDerivation env U source → List Closure
  | .nil => []
  | .cons tail domain => .close domain.origin tail.closures :: tail.closures

theorem ContextDerivation.Location.captured_member
    (location : Location context tail domain) :
    Closure.close domain.origin tail.closures ∈ context.closures := by
  induction location with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

structure ContextDerivation.LookupOrigin (context : ContextDerivation env U source)
    (index : Nat) (type : VExpr) where
  tailSource : List VExpr
  tail : ContextDerivation env U tailSource
  domain : VExpr
  level : VLevel
  formation : EndpointRef env U tailSource domain (.sort level)
  location : Location context tail formation
  index_eq : index = location.prefix.length
  type_eq : type = domain.liftN (index + 1)

theorem ContextDerivation.lookupOrigin
    (context : ContextDerivation env U source) (lookup : Lookup source index type) :
    Nonempty (LookupOrigin context index type) := by
  induction lookup with
  | zero =>
    cases context with
    | cons tail domain =>
      exact ⟨⟨_, tail, _, _, domain, .here, rfl, rfl⟩⟩
  | succ lookup ih =>
    cases context with
    | cons tail domain =>
      obtain ⟨origin⟩ := ih tail
      refine ⟨⟨origin.tailSource, origin.tail, origin.domain, origin.level, origin.formation,
        .there origin.location, ?_, ?_⟩⟩
      · simp only [Location.prefix, List.length_cons, origin.index_eq]
      · exact (congrArg VExpr.lift origin.type_eq).trans (liftN_succ _ _).symm

/-- Actual selected context formation cost is paid by the source environment
maximum. Its tail capture prevents a lookup certificate from depending on
its own declaration slot. -/
theorem ContextDerivation.LookupOrigin.cost_le
    (origin : LookupOrigin context index type) :
    (Closure.close origin.formation.origin origin.tail.closures).cost ≤
      environmentCost context.closures :=
  environment_entry origin.location.captured_member

/-- Reindexing an actual variable's type query can visit the selected
ORIGINAL tail formation even when that formation is larger than the
occurrence's original child. The complete tail closure was already captured. -/
theorem ContextDerivation.LookupOrigin.reindex_schedule
    {context : ContextDerivation env U source}
    (entry : LookupOrigin context index type)
    (lookup : Lookup source index type) {occurrenceLevel : VLevel} (levelWF : occurrenceLevel.WF U)
    (occurrence : Derivation env U source type type (.sort occurrenceLevel)) :
    schedule .coherence
      ((Closure.close occurrence.origin context.closures).cost +
        (Closure.close entry.formation.origin entry.tail.closures).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.bvar lookup levelWF occurrence).origin context.closures).cost) :=
  schedule_strict (lookup_type_reindex occurrence.origin
    (.close entry.formation.origin entry.tail.closures) context.closures entry.cost_le) _ _

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
