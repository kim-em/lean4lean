import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth

/-! Equality transport retains every hereditary declaration depth. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}

@[simp] theorem SortableObs.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : SortableObs env U registry target ms τ expression q g =
      SortableObs env U registry target ls σ expression p f)
    (observation : SortableObs env U registry target ls σ expression p f) :
    (equal.mpr observation).nativeDepth current = observation.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableCert.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : SortableCert env U registry target ms τ expression relevant q g =
      SortableCert env U registry target ls σ expression relevant p f)
    (certificate : SortableCert env U registry target ls σ expression relevant p f) :
    (equal.mpr certificate).nativeDepth current = certificate.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableRows.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : SortableRows env U registry target locals τ A B relevant q ss g =
      SortableRows env U registry target locals σ A B relevant p rs f)
    (bodies : SortableRows env U registry target locals σ A B relevant p rs f) :
    (equal.mpr bodies).nativeDepth current = bodies.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl

@[simp] theorem SortableObs.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : SortableObs env U registry target ls σ expression p f =
      SortableObs env U registry target ms τ expression q g)
    (observation : SortableObs env U registry target ls σ expression p f) :
    (equal.mp observation).nativeDepth current = observation.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableCert.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : SortableCert env U registry target ls σ expression relevant p f =
      SortableCert env U registry target ms τ expression relevant q g)
    (certificate : SortableCert env U registry target ls σ expression relevant p f) :
    (equal.mp certificate).nativeDepth current = certificate.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableRows.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : SortableRows env U registry target locals σ A B relevant p rs f =
      SortableRows env U registry target locals τ A B relevant q ss g)
    (bodies : SortableRows env U registry target locals σ A B relevant p rs f) :
    (equal.mp bodies).nativeDepth current = bodies.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl

@[simp] theorem SortableObs.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (expression : α → VExpr)
    (demand : α → Profile n) (footprint : α → Footprint)
    (observation : SortableObs env U registry target (locals a) (realization a) (expression a)
      (demand a) (footprint a)) :
    (equal ▸ observation : SortableObs env U registry target (locals b) (realization b) (expression b)
      (demand b) (footprint b)).nativeDepth current = observation.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem SortableCert.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (expression : α → VExpr)
    (demand : α → Profile n) (footprint : α → Footprint)
    (certificate : SortableCert env U registry target (locals a) (realization a) (expression a) relevant
      (demand a) (footprint a)) :
    (equal ▸ certificate : SortableCert env U registry target (locals b) (realization b) (expression b) relevant
      (demand b) (footprint b)).nativeDepth current = certificate.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem SortableRows.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (A B : α → VExpr)
    (ambient : α → Profile n) (rows : α → List (Key n × Profile n)) (footprint : α → Footprint)
    (bodies : SortableRows env U registry target (locals a) (realization a) (A a) (B a) relevant
      (ambient a) (rows a) (footprint a)) :
    (equal ▸ bodies : SortableRows env U registry target (locals b) (realization b) (A b) (B b) relevant
      (ambient b) (rows b) (footprint b)).nativeDepth current = bodies.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem SortableObs.nativeDepth_expr_mp (current : Name → Bool)
    {expression other : VExpr} (expressions : expression = other)
    (equal : SortableObs env U registry target locals σ expression demand footprint =
      SortableObs env U registry target locals σ other demand footprint)
    (observation : SortableObs env U registry target locals σ expression demand footprint) :
    (equal.mp observation).nativeDepth current = observation.nativeDepth current := by
  cases expressions; cases equal; rfl

@[simp] theorem SortableFamilyPlan.nativeDepth_mpr (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : SortableFamilyPlan env U registry target name levels signature bs q g =
      SortableFamilyPlan env U registry target name levels signature as p f)
    (plan : SortableFamilyPlan env U registry target name levels signature as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableFamilyPlan.nativeDepth_mp (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : SortableFamilyPlan env U registry target name levels signature as p f =
      SortableFamilyPlan env U registry target name levels signature bs q g)
    (plan : SortableFamilyPlan env U registry target name levels signature as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem SortableFamilyPlan.nativeDepth_rec {α : Sort v} {a b : α}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (current : Name → Bool) (equal : a = b)
    (arguments : α → List VExpr) (demand : α → Profile n) (footprint : α → Footprint)
    (plan : SortableFamilyPlan env U registry target name levels signature (arguments a) (demand a) (footprint a)) :
    (equal ▸ plan : SortableFamilyPlan env U registry target name levels signature (arguments b) (demand b)
      (footprint b)).nativeDepth current = plan.nativeDepth current := by
  cases equal
  rfl

end Lean4Lean.AnchoredSource.Adapted
