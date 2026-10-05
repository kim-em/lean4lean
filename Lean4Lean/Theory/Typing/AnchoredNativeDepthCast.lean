import Lean4Lean.Theory.Typing.AnchoredNativeDepth

/-! Equality transport of observer indices leaves native depth unchanged.
These lemmas concern the actual datatype casts inserted by target transport. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}

@[simp] theorem Obs.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : Obs env U registry target ms τ expression q g =
      Obs env U registry target ls σ expression p f)
    (observation : Obs env U registry target ls σ expression p f) :
    (equal.mpr observation).nativeDepth current = observation.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem CodeCert.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : CodeCert env U registry target ms τ expression q g =
      CodeCert env U registry target ls σ expression p f)
    (certificate : CodeCert env U registry target ls σ expression p f) :
    (equal.mpr certificate).nativeDepth current = certificate.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem PiRows.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : PiRows env U registry target locals τ A B q ss g =
      PiRows env U registry target locals σ A B p rs f)
    (bodies : PiRows env U registry target locals σ A B p rs f) :
    (equal.mpr bodies).nativeDepth current = bodies.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl

@[simp] theorem NativeCaptures.nativeDepth_mpr (current : Name → Bool)
    {data : NativeRecursorData} {p q : SaturatedProgram data} {ws xs : List VExpr}
    {i j : Nat} {r s f g : Footprint}
    (program : p = q) (witnesses : ws = xs) (field : i = j)
    (required : r = s) (footprint : f = g)
    (equal : NativeCaptures env U registry target q xs j s g =
      NativeCaptures env U registry target p ws i r f)
    (captures : NativeCaptures env U registry target p ws i r f) :
    (equal.mpr captures).nativeDepth current = captures.nativeDepth current := by
  cases program; cases witnesses; cases field; cases required; cases footprint; cases equal; rfl

@[simp] theorem NativePlan.nativeDepth_mpr (current : Name → Bool)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : NativePlan env U registry target signature bs q g =
      NativePlan env U registry target signature as p f)
    (plan : NativePlan env U registry target signature as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem Obs.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : Obs env U registry target ls σ expression p f =
      Obs env U registry target ms τ expression q g)
    (observation : Obs env U registry target ls σ expression p f) :
    (equal.mp observation).nativeDepth current = observation.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem CodeCert.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : CodeCert env U registry target ls σ expression p f =
      CodeCert env U registry target ms τ expression q g)
    (certificate : CodeCert env U registry target ls σ expression p f) :
    (equal.mp certificate).nativeDepth current = certificate.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem PiRows.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : PiRows env U registry target locals σ A B p rs f =
      PiRows env U registry target locals τ A B q ss g)
    (bodies : PiRows env U registry target locals σ A B p rs f) :
    (equal.mp bodies).nativeDepth current = bodies.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl

@[simp] theorem NativeCaptures.nativeDepth_mp (current : Name → Bool)
    {data : NativeRecursorData} {p q : SaturatedProgram data} {ws xs : List VExpr}
    {i j : Nat} {r s f g : Footprint}
    (program : p = q) (witnesses : ws = xs) (field : i = j)
    (required : r = s) (footprint : f = g)
    (equal : NativeCaptures env U registry target p ws i r f =
      NativeCaptures env U registry target q xs j s g)
    (captures : NativeCaptures env U registry target p ws i r f) :
    (equal.mp captures).nativeDepth current = captures.nativeDepth current := by
  cases program; cases witnesses; cases field; cases required; cases footprint; cases equal; rfl

@[simp] theorem NativePlan.nativeDepth_mp (current : Name → Bool)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : NativePlan env U registry target signature as p f =
      NativePlan env U registry target signature bs q g)
    (plan : NativePlan env U registry target signature as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl


@[simp] theorem Obs.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (expression : α → VExpr)
    (demand : α → Profile n) (footprint : α → Footprint)
    (observation : Obs env U registry target (locals a) (realization a) (expression a)
      (demand a) (footprint a)) :
    (equal ▸ observation : Obs env U registry target (locals b) (realization b) (expression b)
      (demand b) (footprint b)).nativeDepth current = observation.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem CodeCert.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (expression : α → VExpr)
    (demand : α → Profile n) (footprint : α → Footprint)
    (certificate : CodeCert env U registry target (locals a) (realization a) (expression a)
      (demand a) (footprint a)) :
    (equal ▸ certificate : CodeCert env U registry target (locals b) (realization b) (expression b)
      (demand b) (footprint b)).nativeDepth current = certificate.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem PiRows.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (A B : α → VExpr)
    (ambient : α → Profile n) (rows : α → List (Key n × Profile n)) (footprint : α → Footprint)
    (bodies : PiRows env U registry target (locals a) (realization a) (A a) (B a)
      (ambient a) (rows a) (footprint a)) :
    (equal ▸ bodies : PiRows env U registry target (locals b) (realization b) (A b) (B b)
      (ambient b) (rows b) (footprint b)).nativeDepth current = bodies.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem NativeCaptures.nativeDepth_rec {α : Sort v} {a b : α}
    {data : NativeRecursorData} (current : Name → Bool) (equal : a = b)
    (program : α → SaturatedProgram data) (witnesses : α → List VExpr) (field : α → Nat)
    (required outside : α → Footprint)
    (captures : NativeCaptures env U registry target (program a) (witnesses a) (field a)
      (required a) (outside a)) :
    (equal ▸ captures : NativeCaptures env U registry target (program b) (witnesses b) (field b)
      (required b) (outside b)).nativeDepth current = captures.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem NativePlan.nativeDepth_rec {α : Sort v} {a b : α}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (current : Name → Bool) (equal : a = b)
    (arguments : α → List VExpr) (demand : α → Profile n) (footprint : α → Footprint)
    (plan : NativePlan env U registry target signature (arguments a) (demand a) (footprint a)) :
    (equal ▸ plan : NativePlan env U registry target signature (arguments b) (demand b)
      (footprint b)).nativeDepth current = plan.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem FamilyCaptures.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {ls ms : List Nat} {es fs : List VExpr}
    {ks js : List (DataRequest (Profile n))} {f g : Footprint}
    (locals : ls = ms) (realization : σ = τ) (expressions : es = fs)
    (keys : ks = js) (footprint : f = g)
    (equal : FamilyCaptures env U registry target source ms τ fs js g =
      FamilyCaptures env U registry target source ls σ es ks f)
    (captures : FamilyCaptures env U registry target source ls σ es ks f) :
    (equal.mpr captures).nativeDepth current = captures.nativeDepth current := by
  cases locals; cases realization; cases expressions; cases keys; cases footprint; cases equal; rfl

@[simp] theorem FamilyCaptures.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {ls ms : List Nat} {es fs : List VExpr}
    {ks js : List (DataRequest (Profile n))} {f g : Footprint}
    (locals : ls = ms) (realization : σ = τ) (expressions : es = fs)
    (keys : ks = js) (footprint : f = g)
    (equal : FamilyCaptures env U registry target source ls σ es ks f =
      FamilyCaptures env U registry target source ms τ fs js g)
    (captures : FamilyCaptures env U registry target source ls σ es ks f) :
    (equal.mp captures).nativeDepth current = captures.nativeDepth current := by
  cases locals; cases realization; cases expressions; cases keys; cases footprint; cases equal; rfl

@[simp] theorem FamilyPlan.nativeDepth_mpr (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : FamilyPlan env U registry target name levels signature bs q g =
      FamilyPlan env U registry target name levels signature as p f)
    (plan : FamilyPlan env U registry target name levels signature as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem FamilyPlan.nativeDepth_mp (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : FamilyPlan env U registry target name levels signature as p f =
      FamilyPlan env U registry target name levels signature bs q g)
    (plan : FamilyPlan env U registry target name levels signature as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem FamilyCaptures.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b)
    (locals : α → List Nat) (realization : α → Subst) (expressions : α → List VExpr)
    (keys : α → List (DataRequest (Profile n))) (footprint : α → Footprint)
    (captures : FamilyCaptures env U registry target source (locals a) (realization a) (expressions a)
      (keys a) (footprint a)) :
    (equal ▸ captures : FamilyCaptures env U registry target source (locals b) (realization b) (expressions b)
      (keys b) (footprint b)).nativeDepth current = captures.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem FamilyPlan.nativeDepth_rec {α : Sort v} {a b : α}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (current : Name → Bool) (equal : a = b)
    (arguments : α → List VExpr) (demand : α → Profile n) (footprint : α → Footprint)
    (plan : FamilyPlan env U registry target name levels signature (arguments a) (demand a) (footprint a)) :
    (equal ▸ plan : FamilyPlan env U registry target name levels signature (arguments b) (demand b)
      (footprint b)).nativeDepth current = plan.nativeDepth current := by
  cases equal
  rfl

@[simp] theorem ConstructorPlan.nativeDepth_mpr (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : ConstructorPlan env U registry target name levels signature bs q g =
      ConstructorPlan env U registry target name levels signature as p f)
    (plan : ConstructorPlan env U registry target name levels signature as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem ConstructorPlan.nativeDepth_mp (current : Name → Bool)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : ConstructorPlan env U registry target name levels signature as p f =
      ConstructorPlan env U registry target name levels signature bs q g)
    (plan : ConstructorPlan env U registry target name levels signature as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases arguments; cases profile; cases footprint; cases equal; rfl


@[simp] theorem ConstructorPlan.nativeDepth_rec {α : Sort v} {a b : α}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (current : Name → Bool) (equal : a = b)
    (arguments : α → List VExpr) (demand : α → Profile n) (footprint : α → Footprint)
    (plan : ConstructorPlan env U registry target name levels signature (arguments a) (demand a) (footprint a)) :
    (equal ▸ plan : ConstructorPlan env U registry target name levels signature (arguments b) (demand b)
      (footprint b)).nativeDepth current = plan.nativeDepth current := by
  cases equal
  rfl

end Lean4Lean.AnchoredSource.Adapted
