import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree

/-! Construct the initial all-index guard before the native observation exists.
The finite input tree retains its actual binder guards and original RHS child.
Its terminal requires literal equation arguments. Raw telescope typing is
built from the empty root, so no completed-tree adequacy lemma is used to
justify the tree's own guard. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem onCtx_tail (h : OnCtx (later ++ source) P) : OnCtx source P := by
  induction later with
  | nil => exact h
  | cons _ _ ih => exact ih h.1

private theorem domain_formation {env : VEnv} {U : Nat}
    {domains : List VExpr} {index : Nat} {domain : VExpr}
    (formed : OnCtx domains.reverse (env.IsType U))
    (origin : domains[index]? = some domain) :
    env.IsType U (domains.take index).reverse domain := by
  have h : OnCtx ((domains.drop (index + 1)).reverse ++ (domains.take (index + 1)).reverse)
      (env.IsType U) := by
    rw [← List.reverse_append, List.take_append_drop]
    exact formed
  have formedPrefix :=  onCtx_tail h
  rw [List.take_add_one, origin] at formedPrefix
  simp only [Option.toList_some, List.reverse_append, List.reverse_singleton,
    List.singleton_append, OnCtx] at formedPrefix
  exact formedPrefix.2

private theorem capture_append (values : List VExpr) (value : VExpr) :
    nativeCaptureSubst (values ++ [value]) = (nativeCaptureSubst values).cons value := by
  funext i
  cases i with
  | zero => simp [nativeCaptureSubst, Subst.cons]
  | succ i =>
    simp only [nativeCaptureSubst, List.length_append, List.length_singleton, Subst.cons]
    by_cases hi : i < values.length
    · rw [dif_pos (by omega), dif_pos hi, List.getElem_append_left (by omega)]
      congr 1 <;> omega
    · rw [dif_neg (by omega), dif_neg hi]
      congr 1 <;> omega

structure NativeInitialTerminal (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) (arguments : List VExpr)
    (demand : Profile n) (nativeFootprint : Footprint) where
  program : SaturatedProgram data
  selected : data.saturatedProgram levels arguments = some program
  saturated : arguments.length = data.majorOffset + 1
  noTrailing : program.trailing = []
  prefix_eq : program.prefixArgs = arguments
  witnesses : List VExpr
  witnessLength : witnesses.length = program.equationBody.domains.length
  witnessPrefix : witnesses.take data.indexOffset = arguments.take data.indexOffset
  /-- The initial native call is literally the original equation LHS tuple,
  including every result index and the constructed major. -/
  arguments_eq : arguments = nativeEquationArguments program witnesses
  bodyFootprint : Footprint
  body : Obs env U registry target (List.range program.equationBody.domains.length)
    (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL levels) demand bodyFootprint
  captures : NativeCaptureSupport env U registry target program witnesses
    program.instructions.length bodyFootprint nativeFootprint

inductive NativeInitialTree (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) :
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal (leaf : NativeInitialTerminal env U registry target signature arguments demand footprint) :
      NativeInitialTree env U registry target signature arguments demand footprint
  | binder {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n} {domainFootprint bodyFootprint outside : Footprint}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : NativeInitialTree env U registry target signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      NativeInitialTree env U registry target signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)

/-- The original equation tuple has reflexive raw alignment at every index. -/
def NativeInitialTerminal.finish
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (leaf : NativeInitialTerminal env U registry target signature arguments demand footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst arguments)
      (signature.domains.take arguments.length).reverse) :
    NativeConstantTerminal env U registry target signature arguments demand footprint := by
  have full : signature.domains.take arguments.length = signature.domains := by
    apply List.take_of_length_le
    rw [takeForalls_length signature.telescope, leaf.saturated]
    exact Nat.le_refl _
  exact {
    program := leaf.program
    selected := leaf.selected
    saturated := leaf.saturated
    noTrailing := leaf.noTrailing
    prefix_eq := leaf.prefix_eq
    witnesses := leaf.witnesses
    witnessLength := leaf.witnessLength
    witnessPrefix := leaf.witnessPrefix
    argumentAlignment := by
      rw [← leaf.arguments_eq]
      simpa only [full] using raw
    arguments_eq := leaf.arguments_eq
    bodyFootprint := leaf.bodyFootprint
    body := leaf.body
    captures := leaf.captures }

/-- Build the raw prefix along the same concrete binders that build the tree.
Every domain and anchor comes from the stored registered-domain guard. -/
def NativeInitialTree.finish
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (formed : OnCtx signature.domains.reverse (env.IsType U))
    {arguments : List VExpr} {demand : Profile n} {footprint : Footprint}
    (tree : NativeInitialTree env U registry target signature arguments demand footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst arguments)
      (signature.domains.take arguments.length).reverse) :
    NativeTelescopeTree env U registry target signature arguments demand footprint := by
  match tree with
  | .terminal leaf => exact .terminal (leaf.finish raw)
  | .binder (domain := domain) (key := key) origin domainCode guard body pack covered =>
    have pushed : Ctx.SubstEq env U target
        ((nativeCaptureSubst arguments).cons key.anchor)
        ((nativeCaptureSubst arguments).cons key.anchor)
        (domain :: (signature.domains.take arguments.length).reverse) :=
      by
        obtain ⟨level, domainTyped⟩ := domain_formation formed origin
        exact .cons raw domainTyped (guard.path.cast guard.anchor.2.1)
    have next : Ctx.SubstEq env U target
        (nativeCaptureSubst (arguments ++ [key.anchor]))
        (nativeCaptureSubst (arguments ++ [key.anchor]))
        (signature.domains.take (arguments ++ [key.anchor]).length).reverse := by
      simpa only [capture_append, List.length_append, List.length_singleton,
        List.take_add_one, origin, Option.toList_some, List.reverse_append,
        List.reverse_singleton, List.singleton_append] using pushed
    exact .binder origin domainCode guard (body.finish formed next) pack covered
termination_by sizeOf tree

/-- The public initial construction starts with no native arguments or raw
substitution premises. The terminal's all-index alignment is derived inside. -/
def NativeInitialTree.observation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel} {name : Name}
    {signature : NativeConstantSignature data levels} {demand : Profile n}
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (name_eq : data.name = name) (registered : NativeRecursorRegistered env data)
    (formed : OnCtx signature.domains.reverse (env.IsType U))
    {typeSupport : Profile n} {typeRealization : Subst}
    (typeCertificate : CodeCert env U registry target [] typeRealization
      (signature.type.instL levels) typeSupport [])
    (typed : demand.HasType typeSupport)
    (tree : NativeInitialTree env U registry target signature [] demand []) :
    NativeConstantObservation env U registry target name levels demand where
  data := data
  lookup := lookup
  notDefinition := notDefinition
  name_eq := name_eq
  registered := registered
  signature := signature
  typeSupport := typeSupport
  typeRealization := typeRealization
  typeCertificate := typeCertificate
  typed := typed
  tree := tree.finish formed .nil

end Lean4Lean.AnchoredSource.Adapted
