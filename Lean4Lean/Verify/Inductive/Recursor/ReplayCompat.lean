import Lean4Lean.Verify.TypeChecker.AlphaLocality
import Lean4Lean.Verify.Inductive.Recursor.Rules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A concrete inductive-checker context viewed by the lifted typechecker.
Naming this projection keeps the alpha-locality statements independent of
the implementation details of the `MonadLift TypeChecker.M` instance. -/
def toTypeCheckerContext
    (c : AddInductive.Context) : TypeChecker.Context where
  env := c.env
  lctx := c.lctx
  safety := c.safety
  lparams := c.lparams
  fuel := c.fuel

/-- Exact alpha boundary for Lean's opaque annotation consumer.  It is kept
separate from WHNF/classifier locality because `consumeTypeAnnotations` is
exported as an opaque runtime constant with no equation theorem. -/
def ConsumeTypeAnnotationsAlphaCompat : Prop :=
  ∀ {leftBinders rightBinders : List FVarId}
    {leftDomain rightDomain : Expr},
    TypeChecker.ExprAlphaUnder leftBinders rightBinders
      leftDomain rightDomain →
    TypeChecker.ExprAlphaUnder leftBinders rightBinders
      leftDomain.consumeTypeAnnotationsVerified rightDomain.consumeTypeAnnotationsVerified

/-- A well-formed operational context extension supplies the empty-binder
base of the typechecker's ordered alpha relation.  Old declarations are
literally shared; only binders subsequently opened in the paired classifier
runs belong to the renaming spine. -/
theorem BindingContextLE.orderedBinderRenamingEmpty
    (H : BindingContextLE left right)
    (Hleft : BindingContextWF left)
    (Hright : BindingContextWF right) :
    TypeChecker.Context.OrderedBinderRenaming
      (fun fv => fv ∈ left.lctx.fvars) [] []
      (toTypeCheckerContext left) (toTypeCheckerContext right) where
  env_eq := H.env_eq.symm
  safety_eq := H.safety_eq.symm
  eagerReduce_eq := rfl
  lparams_eq := H.lparams_eq.symm
  fuel_eq := H.fuel_eq.symm
  binders := TypeChecker.LocalContext.OrderedBinderRenaming.empty _ _
  left_lctx_wf := Hleft.wf
  right_lctx_wf := Hright.wf
  shared_declarations fv hfv := (H.declarations fv hfv).symm
  shared_fresh fv hfv := by simp
  left_only_cdecls := Hleft.onlyLams
  right_only_cdecls := Hright.onlyLams

/-- The name-generator cursor of a binding context is absent from its local
context map.  This is the exact freshness fact consumed when two replay
traversals extend an ordered alpha spine. -/
theorem BindingContextWF.currentFind?_eq_none
    (H : BindingContextWF c) :
    c.lctx.find? ⟨c.ngen.curr⟩ = none := by
  rw [H.wf.find?_eq_find?_toList]
  by_contra hne
  rcases Option.ne_none_iff_exists.mp hne with ⟨decl, hfind⟩
  apply H.current_not_mem
  rw [LocalContext.fvars]
  apply List.mem_map.2
  refine ⟨decl, List.mem_of_find?_eq_some hfind.symm, ?_⟩
  have hcursor := List.find?_some hfind.symm
  exact (LawfulBEq.eq_of_beq hcursor).symm

/-- A complete field-decision trace determines the well-formed extension
context and the exact fresh free-variable array introduced by the traversal.
This is deliberately independent of the recursive/nonrecursive decisions:
both branches introduce the same local declaration before classifying it. -/
theorem RecursorFieldDecisions.freshBindings
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root) :
    ∃ Hcurrent : BindingContextWF current,
      BindingContextLE root current ∧
      Nonempty (FreshBoundFVarArray root current all) := by
  induction H with
  | nil =>
      exact ⟨Hroot, BindingContextLE.refl root,
        ⟨FreshBoundFVarArray.empty root⟩⟩
  | @nonrecursive c name dom body bi bu u positions H _ ih =>
      rcases ih with ⟨Hc, HrootCurrent, ⟨Hbindings⟩⟩
      let Hnext := Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi
      let Hstep := BindingContextLE.withLocalDecl c Hc name
        dom.consumeTypeAnnotationsVerified bi
      exact ⟨Hnext, HrootCurrent.trans Hstep,
        ⟨Hbindings.pushCurrent Hc HrootCurrent name
          dom.consumeTypeAnnotationsVerified bi⟩⟩
  | @recursive c name dom body bi bu u positions target H _ ih =>
      rcases ih with ⟨Hc, HrootCurrent, ⟨Hbindings⟩⟩
      let Hnext := Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi
      let Hstep := BindingContextLE.withLocalDecl c Hc name
        dom.consumeTypeAnnotationsVerified bi
      exact ⟨Hnext, HrootCurrent.trans Hstep,
        ⟨Hbindings.pushCurrent Hc HrootCurrent name
          dom.consumeTypeAnnotationsVerified bi⟩⟩

/-- A complete retained field-decision trace canonically opens the original
constructor telescope.  This packages the exact alpha-closing equation for
the checker-chosen field identifiers, rather than replaying or naming them.
The trace relation itself may represent a prefix; the resulting opening has
exactly that prefix's arity. -/
theorem RecursorFieldDecisions.fieldOpening
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars)) :
    Nonempty (ConstructorFieldOpening source terminal all) := by
  have go : ∀ {current terminal all selected positions},
      RecursorFieldDecisions stats root source current terminal
        all selected positions →
      ∃ Hcurrent : BindingContextWF current,
        BindingContextLE root current ∧
        ∃ Hbindings : FreshBoundFVarArray root current all,
          Nonempty (ConstructorFieldOpening source terminal all) := by
    intro current terminal all selected positions Htrace
    induction Htrace with
    | nil =>
        exact ⟨Hroot, BindingContextLE.refl root,
          FreshBoundFVarArray.empty root,
          ⟨ConstructorFieldOpening.empty source⟩⟩
    | @nonrecursive c name dom body bi bu u positions Hprev _ ih =>
        rcases ih with ⟨Hc, HrootCurrent, Hbindings, ⟨Hopening⟩⟩
        let Hnext := Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi
        let Hstep := BindingContextLE.withLocalDecl c Hc name
          dom.consumeTypeAnnotationsVerified bi
        have hopenFvars : Hopening.fvars = Hbindings.fvars :=
          Hopening.fvars_eq_bound Hbindings.toBoundFVarArray
        have hcurrentFresh :
            (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
          rw [hopenFvars]
          intro hmem
          exact Hc.current_not_mem
            (Hbindings.toBoundFVarArray.members _ hmem)
        have hbodyFresh : body.FVarsIn
            (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
          have hbodyScope := (Hopening.currentFVarsIn hsource).2
          apply hbodyScope.mono
          intro fv hfv heq
          subst fv
          rcases hfv with hopen | hroot
          · apply Hc.current_not_mem
            apply Hbindings.toBoundFVarArray.members
            rwa [← hopenFvars]
          · exact Hc.current_not_mem (HrootCurrent hroot)
        exact ⟨Hnext, HrootCurrent.trans Hstep,
          Hbindings.pushCurrent Hc HrootCurrent name
            dom.consumeTypeAnnotationsVerified bi,
          ⟨Hopening.push hcurrentFresh hbodyFresh⟩⟩
    | @recursive c name dom body bi bu u positions target Hprev _ ih =>
        rcases ih with ⟨Hc, HrootCurrent, Hbindings, ⟨Hopening⟩⟩
        let Hnext := Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi
        let Hstep := BindingContextLE.withLocalDecl c Hc name
          dom.consumeTypeAnnotationsVerified bi
        have hopenFvars : Hopening.fvars = Hbindings.fvars :=
          Hopening.fvars_eq_bound Hbindings.toBoundFVarArray
        have hcurrentFresh :
            (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
          rw [hopenFvars]
          intro hmem
          exact Hc.current_not_mem
            (Hbindings.toBoundFVarArray.members _ hmem)
        have hbodyFresh : body.FVarsIn
            (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
          have hbodyScope := (Hopening.currentFVarsIn hsource).2
          apply hbodyScope.mono
          intro fv hfv heq
          subst fv
          rcases hfv with hopen | hroot
          · apply Hc.current_not_mem
            apply Hbindings.toBoundFVarArray.members
            rwa [← hopenFvars]
          · exact Hc.current_not_mem (HrootCurrent hroot)
        exact ⟨Hnext, HrootCurrent.trans Hstep,
          Hbindings.pushCurrent Hc HrootCurrent name
            dom.consumeTypeAnnotationsVerified bi,
          ⟨Hopening.push hcurrentFresh hbodyFresh⟩⟩
  rcases go H with ⟨_, _, _, Hopening⟩
  exact Hopening

/-- Every expression reached by a retained field traversal is scoped by its
actual current local context.  This is the freshness input needed to open
paired forall bodies at the two independently generated cursors. -/
theorem RecursorFieldDecisions.currentFVarsIn
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars)) :
    terminal.FVarsIn (fun fv => fv ∈ current.lctx.fvars) := by
  rcases H.freshBindings Hroot with
    ⟨_Hcurrent, HrootCurrent, ⟨Hbindings⟩⟩
  rcases H.fieldOpening Hroot hsource with ⟨Hopening⟩
  have hopenFvars : Hopening.fvars = Hbindings.fvars :=
    Hopening.fvars_eq_bound Hbindings.toBoundFVarArray
  apply (Hopening.currentFVarsIn hsource).mono
  intro fv hfv
  rcases hfv with hopen | hroot
  · apply Hbindings.members
    rwa [← hopenFvars]
  · exact HrootCurrent hroot

/-- Two completed traversals of the same source telescope consume the same
number of fields.  This is the maximal-telescope part of replay: unlike the
recursive-field mask, it follows solely from the retained terminal
non-forall facts and does not require alpha-invariance of `isRecArg`. -/
theorem RecursorFieldDecisions.completedArity_eq
    (Hleft : RecursorFieldDecisions stats leftRoot source leftCurrent
      leftTerminal leftAll leftSelected leftPositions)
    (Hright : RecursorFieldDecisions stats rightRoot source rightCurrent
      rightTerminal rightAll rightSelected rightPositions)
    (HleftRoot : BindingContextWF leftRoot)
    (HrightRoot : BindingContextWF rightRoot)
    (HleftRight : BindingContextLE leftCurrent rightRoot)
    (hsource : source.FVarsIn (fun fv => fv ∈ leftRoot.lctx.fvars))
    (hleftTerminal : leftTerminal.isForall = false)
    (hrightTerminal : rightTerminal.isForall = false) :
    leftAll.size = rightAll.size := by
  rcases Hleft.freshBindings HleftRoot with
    ⟨_, HleftExtension, _⟩
  have hsourceRight : source.FVarsIn
      (fun fv => fv ∈ rightRoot.lctx.fvars) := by
    apply hsource.mono
    intro fv hfv
    exact HleftRight.fvars (HleftExtension.fvars hfv)
  rcases Hleft.fieldOpening HleftRoot hsource with ⟨leftOpening⟩
  rcases Hright.fieldOpening HrightRoot hsourceRight with ⟨rightOpening⟩
  have hleftResidual : leftOpening.residual.isForall = false := by
    rw [← leftOpening.closed, Expr.abstractList_isForall]
    exact hleftTerminal
  have hrightResidual : rightOpening.residual.isForall = false := by
    rw [← rightOpening.closed, Expr.abstractList_isForall]
    exact hrightTerminal
  exact (leftOpening.telescope.eq_of_residual_not_forall
    rightOpening.telescope hleftResidual hrightResidual).1

/-- The actual two-pass ordering (`leftRoot ≤ leftCurrent ≤ rightRoot`)
constructs the empty alpha spine from the retained first-pass trace.  This
is the precise producer-indexed starting context for recursive `isRecArg`
equivariance. -/
theorem RecursorFieldDecisions.alphaRootBase
    (Hleft : RecursorFieldDecisions stats leftRoot source leftCurrent
      leftTerminal leftAll leftSelected leftPositions)
    (HleftRoot : BindingContextWF leftRoot)
    (HrightRoot : BindingContextWF rightRoot)
    (HleftRight : BindingContextLE leftCurrent rightRoot) :
    TypeChecker.Context.OrderedBinderRenaming
      (fun fv => fv ∈ leftRoot.lctx.fvars) [] []
      (toTypeCheckerContext leftRoot) (toTypeCheckerContext rightRoot) := by
  rcases Hleft.freshBindings HleftRoot with
    ⟨_, HleftExtension, _⟩
  exact (HleftExtension.trans HleftRight).orderedBinderRenamingEmpty
    HleftRoot HrightRoot

/-- Paired field traversals retain their concrete alpha spine as well as the
alpha-independent recursive-field mask.  This is the producer-shaped result
needed by both recursive-field replay and the later `loopUArgs` comparison. -/
def RecursorFieldReplayAlignment
    (leftCurrent rightCurrent : AddInductive.Context)
    (leftTerminal rightTerminal : Expr)
    (leftAll rightAll : Array Expr)
    (leftPositions rightPositions : List Nat)
    (shared : FVarId → Prop) : Prop :=
  ∃ leftBinders rightBinders : List FVarId,
    leftAll = (leftBinders.map Expr.fvar).toArray ∧
    rightAll = (rightBinders.map Expr.fvar).toArray ∧
    TypeChecker.Context.OrderedBinderRenaming shared leftBinders rightBinders
      (toTypeCheckerContext leftCurrent) (toTypeCheckerContext rightCurrent) ∧
    TypeChecker.ExprAlphaUnder leftBinders rightBinders
      leftTerminal rightTerminal ∧
    leftPositions = rightPositions

/-- Open the next paired forall and extend the alpha context in one step.
The caller supplies scope in the two concrete current contexts; generator
freshness then discharges the simultaneous-opening side conditions. -/
theorem RecursorFieldReplayAlignment.openForall
    (H : RecursorFieldReplayAlignment left right
      (.forallE leftName leftDomain leftBody leftBi)
      (.forallE rightName rightDomain rightBody rightBi)
      leftAll rightAll leftPositions rightPositions shared)
    (Hleft : BindingContextWF left)
    (Hright : BindingContextWF right)
    (hleftScope : (Expr.forallE leftName leftDomain leftBody leftBi).FVarsIn
      (fun fv => fv ∈ left.lctx.fvars))
    (hrightScope : (Expr.forallE rightName rightDomain rightBody rightBi).FVarsIn
      (fun fv => fv ∈ right.lctx.fvars))
    (hsharedLeft : ∀ fv, shared fv → fv ∈ left.lctx.fvars)
    (hsharedRight : ∀ fv, shared fv → fv ∈ right.lctx.fvars)
    (hconsume : ∀ {leftBinders rightBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain rightDomain →
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain.consumeTypeAnnotationsVerified
        rightDomain.consumeTypeAnnotationsVerified)
    {leftPositions' rightPositions' : List Nat}
    (hpositions : leftPositions' = rightPositions') :
    RecursorFieldReplayAlignment
        { left with
          ngen := left.ngen.next
          lctx := left.lctx.mkLocalDecl ⟨left.ngen.curr⟩ leftName
            leftDomain.consumeTypeAnnotationsVerified leftBi }
        { right with
          ngen := right.ngen.next
          lctx := right.lctx.mkLocalDecl ⟨right.ngen.curr⟩ rightName
            rightDomain.consumeTypeAnnotationsVerified rightBi }
        (leftBody.instantiate1 (.fvar ⟨left.ngen.curr⟩))
        (rightBody.instantiate1 (.fvar ⟨right.ngen.curr⟩))
        (leftAll.push (.fvar ⟨left.ngen.curr⟩))
        (rightAll.push (.fvar ⟨right.ngen.curr⟩))
        leftPositions' rightPositions' shared := by
  rcases H with ⟨leftBinders, rightBinders, hleftExpressions,
    hrightExpressions, Hcontext, Hterminal, _hpositions⟩
  have hleftBinderFresh :
      (⟨left.ngen.curr⟩ : FVarId) ∉ leftBinders :=
    Hcontext.binders.left_not_mem_of_find?_eq_none
      Hleft.currentFind?_eq_none
  have hrightBinderFresh :
      (⟨right.ngen.curr⟩ : FVarId) ∉ rightBinders :=
    Hcontext.binders.right_not_mem_of_find?_eq_none
      Hright.currentFind?_eq_none
  have hleftBodyFresh : leftBody.FVarsIn
      (fun fv => fv ≠ (⟨left.ngen.curr⟩ : FVarId)) :=
    hleftScope.2.mono fun fv hfv heq => by
      subst fv
      exact Hleft.current_not_mem hfv
  have hrightBodyFresh : rightBody.FVarsIn
      (fun fv => fv ≠ (⟨right.ngen.curr⟩ : FVarId)) :=
    hrightScope.2.mono fun fv hfv heq => by
      subst fv
      exact Hright.current_not_mem hfv
  have Hparts := Hterminal.forall_open hleftBinderFresh
    hrightBinderFresh hleftBodyFresh hrightBodyFresh
  have hsharedFresh : ∀ fv, shared fv →
      fv ≠ (⟨left.ngen.curr⟩ : FVarId) ∧
        fv ≠ (⟨right.ngen.curr⟩ : FVarId) := by
    intro fv hfv
    constructor
    · intro heq
      subst fv
      exact Hleft.current_not_mem (hsharedLeft _ hfv)
    · intro heq
      subst fv
      exact Hright.current_not_mem (hsharedRight _ hfv)
  let Hcontext' := Hcontext.push
    (⟨left.ngen.curr⟩ : FVarId) (⟨right.ngen.curr⟩ : FVarId)
    Hleft.currentFind?_eq_none Hright.currentFind?_eq_none hsharedFresh
    leftName rightName leftDomain.consumeTypeAnnotationsVerified
    rightDomain.consumeTypeAnnotationsVerified leftBi rightBi (hconsume Hparts.1)
  refine ⟨leftBinders ++ [⟨left.ngen.curr⟩],
    rightBinders ++ [⟨right.ngen.curr⟩], ?_, ?_, Hcontext',
    Hparts.2, hpositions⟩
  · simp [hleftExpressions]
  · simp [hrightExpressions]

/-- Equal-arity traces from alpha-aligned roots have the same recursive-field
mask.  The proof follows the actual paired decisions.  Its only operational
inputs are alpha preservation by annotation consumption and by `isRecArg`;
neither is folded into the trace invariant. -/
theorem RecursorFieldDecisions.alphaAlignmentOfSizeEq
    (Hleft : RecursorFieldDecisions stats leftRoot source leftCurrent
      leftTerminal leftAll leftSelected leftPositions)
    (Hright : RecursorFieldDecisions stats rightRoot source rightCurrent
      rightTerminal rightAll rightSelected rightPositions)
    (HleftRoot : BindingContextWF leftRoot)
    (HrightRoot : BindingContextWF rightRoot)
    (hsourceLeft : source.FVarsIn
      (fun fv => fv ∈ leftRoot.lctx.fvars))
    (hsourceRight : source.FVarsIn
      (fun fv => fv ∈ rightRoot.lctx.fvars))
    (Hbase : TypeChecker.Context.OrderedBinderRenaming shared [] []
      (toTypeCheckerContext leftRoot) (toTypeCheckerContext rightRoot))
    (hsharedLeft : ∀ fv, shared fv → fv ∈ leftRoot.lctx.fvars)
    (hsharedRight : ∀ fv, shared fv → fv ∈ rightRoot.lctx.fvars)
    (hconsume : ∀ {leftBinders rightBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain rightDomain →
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain.consumeTypeAnnotationsVerified
        rightDomain.consumeTypeAnnotationsVerified)
    (hclassify : ∀ {left right : AddInductive.Context}
      {leftContextBinders rightContextBinders : List FVarId}
      {leftInputBinders rightInputBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      BindingContextWF left → BindingContextWF right →
      TypeChecker.Context.OrderedBinderRenaming shared
        leftContextBinders rightContextBinders (toTypeCheckerContext left)
          (toTypeCheckerContext right) →
      TypeChecker.ExprAlphaUnder leftInputBinders rightInputBinders
        leftDomain rightDomain →
      AddInductive.isRecArg stats leftDomain left =
        AddInductive.isRecArg stats rightDomain right)
    (hsize : leftAll.size = rightAll.size) :
    RecursorFieldReplayAlignment leftCurrent rightCurrent
      leftTerminal rightTerminal leftAll rightAll leftPositions
      rightPositions shared := by
  induction Hleft generalizing rightCurrent rightTerminal rightAll
      rightSelected rightPositions with
  | nil =>
      cases Hright with
      | nil =>
          exact ⟨[], [], rfl, rfl, Hbase,
            TypeChecker.ExprAlphaUnder.refl source [], rfl⟩
      | nonrecursive Hprev _ => simp at hsize
      | recursive Hprev _ => simp at hsize
  | @nonrecursive left leftName leftDomain leftBody leftBi
      leftAll leftSelected leftPositions HleftPrev hleftRun ih =>
      cases Hright with
      | nil => simp at hsize
      | @nonrecursive right rightName rightDomain rightBody rightBi
          rightAll rightSelected rightPositions HrightPrev hrightRun =>
          have hprefixSize : leftAll.size = rightAll.size := by
            simp only [Array.size_push] at hsize
            omega
          rcases ih HrightPrev hprefixSize with
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          have Halign : RecursorFieldReplayAlignment left right
              (.forallE leftName leftDomain leftBody leftBi)
              (.forallE rightName rightDomain rightBody rightBi)
              leftAll rightAll leftPositions rightPositions shared :=
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          rcases HleftPrev.freshBindings HleftRoot with
            ⟨HleftWF, HleftExtension, _⟩
          rcases HrightPrev.freshBindings HrightRoot with
            ⟨HrightWF, HrightExtension, _⟩
          have Hnext := Halign.openForall HleftWF HrightWF
            (HleftPrev.currentFVarsIn HleftRoot hsourceLeft)
            (HrightPrev.currentFVarsIn HrightRoot hsourceRight)
            (fun fv hfv => HleftExtension (hsharedLeft fv hfv))
            (fun fv hfv => HrightExtension (hsharedRight fv hfv))
            hconsume hpositionsPrefix
          have HnextCopy := Hnext
          rcases HnextCopy with
            ⟨_, _, _, _, HnextContext, _, _⟩
          let HleftNext := HleftWF.withLocalDecl leftName
            leftDomain.consumeTypeAnnotationsVerified leftBi
          let HrightNext := HrightWF.withLocalDecl rightName
            rightDomain.consumeTypeAnnotationsVerified rightBi
          have hclass := hclassify HleftNext HrightNext HnextContext
            Hterminal.forall_domain
          rw [hleftRun, hrightRun] at hclass
          exact Hnext
      | @recursive right rightName rightDomain rightBody rightBi
          rightAll rightSelected rightPositions target HrightPrev hrightRun =>
          have hprefixSize : leftAll.size = rightAll.size := by
            simp only [Array.size_push] at hsize
            omega
          rcases ih HrightPrev hprefixSize with
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          have Halign : RecursorFieldReplayAlignment left right
              (.forallE leftName leftDomain leftBody leftBi)
              (.forallE rightName rightDomain rightBody rightBi)
              leftAll rightAll leftPositions rightPositions shared :=
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          rcases HleftPrev.freshBindings HleftRoot with
            ⟨HleftWF, HleftExtension, _⟩
          rcases HrightPrev.freshBindings HrightRoot with
            ⟨HrightWF, HrightExtension, _⟩
          have Hnext := Halign.openForall HleftWF HrightWF
            (HleftPrev.currentFVarsIn HleftRoot hsourceLeft)
            (HrightPrev.currentFVarsIn HrightRoot hsourceRight)
            (fun fv hfv => HleftExtension (hsharedLeft fv hfv))
            (fun fv hfv => HrightExtension (hsharedRight fv hfv))
            hconsume hpositionsPrefix
          have HnextCopy := Hnext
          rcases HnextCopy with
            ⟨_, _, _, _, HnextContext, _, _⟩
          let HleftNext := HleftWF.withLocalDecl leftName
            leftDomain.consumeTypeAnnotationsVerified leftBi
          let HrightNext := HrightWF.withLocalDecl rightName
            rightDomain.consumeTypeAnnotationsVerified rightBi
          have hclass := hclassify HleftNext HrightNext HnextContext
            Hterminal.forall_domain
          rw [hleftRun, hrightRun] at hclass
          cases hclass
  | @recursive left leftName leftDomain leftBody leftBi
      leftAll leftSelected leftPositions leftTarget HleftPrev hleftRun ih =>
      cases Hright with
      | nil => simp at hsize
      | @nonrecursive right rightName rightDomain rightBody rightBi
          rightAll rightSelected rightPositions HrightPrev hrightRun =>
          have hprefixSize : leftAll.size = rightAll.size := by
            simp only [Array.size_push] at hsize
            omega
          rcases ih HrightPrev hprefixSize with
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          have Halign : RecursorFieldReplayAlignment left right
              (.forallE leftName leftDomain leftBody leftBi)
              (.forallE rightName rightDomain rightBody rightBi)
              leftAll rightAll leftPositions rightPositions shared :=
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          rcases HleftPrev.freshBindings HleftRoot with
            ⟨HleftWF, HleftExtension, _⟩
          rcases HrightPrev.freshBindings HrightRoot with
            ⟨HrightWF, HrightExtension, _⟩
          have Hnext := Halign.openForall HleftWF HrightWF
            (HleftPrev.currentFVarsIn HleftRoot hsourceLeft)
            (HrightPrev.currentFVarsIn HrightRoot hsourceRight)
            (fun fv hfv => HleftExtension (hsharedLeft fv hfv))
            (fun fv hfv => HrightExtension (hsharedRight fv hfv))
            hconsume hpositionsPrefix
          have HnextCopy := Hnext
          rcases HnextCopy with
            ⟨_, _, _, _, HnextContext, _, _⟩
          let HleftNext := HleftWF.withLocalDecl leftName
            leftDomain.consumeTypeAnnotationsVerified leftBi
          let HrightNext := HrightWF.withLocalDecl rightName
            rightDomain.consumeTypeAnnotationsVerified rightBi
          have hclass := hclassify HleftNext HrightNext HnextContext
            Hterminal.forall_domain
          rw [hleftRun, hrightRun] at hclass
          cases hclass
      | @recursive right rightName rightDomain rightBody rightBi
          rightAll rightSelected rightPositions rightTarget HrightPrev
          hrightRun =>
          have hprefixSize : leftAll.size = rightAll.size := by
            simp only [Array.size_push] at hsize
            omega
          rcases ih HrightPrev hprefixSize with
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          have Halign : RecursorFieldReplayAlignment left right
              (.forallE leftName leftDomain leftBody leftBi)
              (.forallE rightName rightDomain rightBody rightBi)
              leftAll rightAll leftPositions rightPositions shared :=
            ⟨leftBinders, rightBinders, hleftExpressions,
              hrightExpressions, Hcontext, Hterminal, hpositionsPrefix⟩
          rcases HleftPrev.freshBindings HleftRoot with
            ⟨HleftWF, HleftExtension, _⟩
          rcases HrightPrev.freshBindings HrightRoot with
            ⟨HrightWF, HrightExtension, _⟩
          have hpositions : leftPositions ++ [leftAll.size] =
              rightPositions ++ [rightAll.size] := by
            rw [hpositionsPrefix, hprefixSize]
          have Hnext := Halign.openForall HleftWF HrightWF
            (HleftPrev.currentFVarsIn HleftRoot hsourceLeft)
            (HrightPrev.currentFVarsIn HrightRoot hsourceRight)
            (fun fv hfv => HleftExtension (hsharedLeft fv hfv))
            (fun fv hfv => HrightExtension (hsharedRight fv hfv))
            hconsume hpositions
          have HnextCopy := Hnext
          rcases HnextCopy with
            ⟨_, _, _, _, HnextContext, _, _⟩
          let HleftNext := HleftWF.withLocalDecl leftName
            leftDomain.consumeTypeAnnotationsVerified leftBi
          let HrightNext := HrightWF.withLocalDecl rightName
            rightDomain.consumeTypeAnnotationsVerified rightBi
          have hclass := hclassify HleftNext HrightNext HnextContext
            Hterminal.forall_domain
          rw [hleftRun, hrightRun] at hclass
          exact Hnext

/-- Complete producer traces satisfy the arity premise automatically.  The
actual first-pass-to-second-pass context ordering supplies the shared root
and the empty alpha spine. -/
theorem RecursorFieldDecisions.alphaAlignment
    (Hleft : RecursorFieldDecisions stats leftRoot source leftCurrent
      leftTerminal leftAll leftSelected leftPositions)
    (Hright : RecursorFieldDecisions stats rightRoot source rightCurrent
      rightTerminal rightAll rightSelected rightPositions)
    (HleftRoot : BindingContextWF leftRoot)
    (HrightRoot : BindingContextWF rightRoot)
    (HleftRight : BindingContextLE leftCurrent rightRoot)
    (hsource : source.FVarsIn (fun fv => fv ∈ leftRoot.lctx.fvars))
    (hleftTerminal : leftTerminal.isForall = false)
    (hrightTerminal : rightTerminal.isForall = false)
    (hconsume : ∀ {leftBinders rightBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain rightDomain →
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain.consumeTypeAnnotationsVerified
        rightDomain.consumeTypeAnnotationsVerified)
    (hclassify : ∀ {left right : AddInductive.Context}
      {leftContextBinders rightContextBinders : List FVarId}
      {leftInputBinders rightInputBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      BindingContextWF left → BindingContextWF right →
      TypeChecker.Context.OrderedBinderRenaming
        (fun fv => fv ∈ leftRoot.lctx.fvars)
        leftContextBinders rightContextBinders
        (toTypeCheckerContext left) (toTypeCheckerContext right) →
      TypeChecker.ExprAlphaUnder leftInputBinders rightInputBinders
        leftDomain rightDomain →
      AddInductive.isRecArg stats leftDomain left =
        AddInductive.isRecArg stats rightDomain right) :
    RecursorFieldReplayAlignment leftCurrent rightCurrent
      leftTerminal rightTerminal leftAll rightAll leftPositions
      rightPositions (fun fv => fv ∈ leftRoot.lctx.fvars) := by
  rcases Hleft.freshBindings HleftRoot with
    ⟨_, HleftExtension, _⟩
  have hsourceRight : source.FVarsIn
      (fun fv => fv ∈ rightRoot.lctx.fvars) := by
    apply hsource.mono
    intro fv hfv
    exact HleftRight (HleftExtension hfv)
  have hsize := Hleft.completedArity_eq Hright HleftRoot HrightRoot
    HleftRight hsource hleftTerminal hrightTerminal
  exact Hleft.alphaAlignmentOfSizeEq Hright HleftRoot HrightRoot
    hsource hsourceRight
    (Hleft.alphaRootBase HleftRoot HrightRoot HleftRight)
    (fun _ hfv => hfv)
    (fun _ hfv => HleftRight (HleftExtension hfv))
    hconsume hclassify hsize

/-- Projection of `alphaAlignment`: completed paired traces have the same
recursive-field positions. -/
theorem RecursorFieldDecisions.positions_eq_of_alpha
    (Hleft : RecursorFieldDecisions stats leftRoot source leftCurrent
      leftTerminal leftAll leftSelected leftPositions)
    (Hright : RecursorFieldDecisions stats rightRoot source rightCurrent
      rightTerminal rightAll rightSelected rightPositions)
    (HleftRoot : BindingContextWF leftRoot)
    (HrightRoot : BindingContextWF rightRoot)
    (HleftRight : BindingContextLE leftCurrent rightRoot)
    (hsource : source.FVarsIn (fun fv => fv ∈ leftRoot.lctx.fvars))
    (hleftTerminal : leftTerminal.isForall = false)
    (hrightTerminal : rightTerminal.isForall = false)
    (hconsume : ∀ {leftBinders rightBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain rightDomain →
      TypeChecker.ExprAlphaUnder leftBinders rightBinders
        leftDomain.consumeTypeAnnotationsVerified
        rightDomain.consumeTypeAnnotationsVerified)
    (hclassify : ∀ {left right : AddInductive.Context}
      {leftContextBinders rightContextBinders : List FVarId}
      {leftInputBinders rightInputBinders : List FVarId}
      {leftDomain rightDomain : Expr},
      BindingContextWF left → BindingContextWF right →
      TypeChecker.Context.OrderedBinderRenaming
        (fun fv => fv ∈ leftRoot.lctx.fvars)
        leftContextBinders rightContextBinders
        (toTypeCheckerContext left) (toTypeCheckerContext right) →
      TypeChecker.ExprAlphaUnder leftInputBinders rightInputBinders
        leftDomain rightDomain →
      AddInductive.isRecArg stats leftDomain left =
        AddInductive.isRecArg stats rightDomain right) :
    leftPositions = rightPositions := by
  rcases Hleft.alphaAlignment Hright HleftRoot HrightRoot HleftRight
      hsource hleftTerminal hrightTerminal hconsume hclassify with
    ⟨_, _, _, _, _, _, hpositions⟩
  exact hpositions

/-- The retained maximal closed residual reflects back to the concrete
terminal expression of a minor traversal. -/
theorem RecInfoMinorTraversalShape.terminal_not_forall
    (H : RecInfoMinorTraversalShape) : H.terminal.isForall = false := by
  rw [← Expr.abstractList_isForall H.terminal H.fieldFVars,
    H.fieldClosed]
  exact H.fieldResidual_not_forall

/-- Closing two applications under their respective fresh binder spines
makes the terminal inductive-application test alpha-invariant.  This is the
non-forall base case of `isRecArg` replay; it uses the existing executable
reflection lemmas for `isValidIndAppIdx`, not semantic completeness. -/
theorem checkPositivityStep.isValidIndAppIdx_eq_of_abstractList_eq
    {left right : Expr} {leftBinders rightBinders paramFVars : List FVarId}
    {stats : AddInductive.InductiveStats} {i : Nat}
    {name : Name} {levels : List Level}
    (hclosed : left.abstractList leftBinders =
      right.abstractList rightBinders)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFVars.map Expr.fvar).toArray)
    (hleftDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ leftBinders)
    (hrightDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ rightBinders) :
    AddInductive.isValidIndAppIdx stats left i =
      AddInductive.isValidIndAppIdx stats right i := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hleft
    have hclosedValid :=
      checkPositivityStep.isValidIndAppIdx.abstractList hleft hconst
        paramFVars leftBinders hparams hleftDisjoint
    rw [hclosed] at hclosedValid
    exact checkPositivityStep.isValidIndAppIdx.of_abstractList
      paramFVars rightBinders 0 hclosedValid hconst hparams hrightDisjoint
  · intro hright
    have hclosedValid :=
      checkPositivityStep.isValidIndAppIdx.abstractList hright hconst
        paramFVars rightBinders hparams hrightDisjoint
    rw [← hclosed] at hclosedValid
    exact checkPositivityStep.isValidIndAppIdx.of_abstractList
      paramFVars leftBinders 0 hclosedValid hconst hparams hleftDisjoint

/-- Pointwise alpha-invariance of `isValidIndAppIdx` lifts through the exact
first-match scan used by `isValidIndApp?`. -/
theorem checkPositivityStep.isValidIndAppFrom?_eq_of_abstractList_eq
    {left right : Expr} {leftBinders rightBinders paramFVars : List FVarId}
    {stats : AddInductive.InductiveStats} {start fuel : Nat}
    (hclosed : left.abstractList leftBinders =
      right.abstractList rightBinders)
    (hconst : ∀ i (hi : i < stats.indConsts.size),
      ∃ name levels, stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFVars.map Expr.fvar).toArray)
    (hleftDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ leftBinders)
    (hrightDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ rightBinders)
    (hscan : start + fuel ≤ stats.indConsts.size) :
    AddInductive.isValidIndAppFrom? stats left start fuel =
      AddInductive.isValidIndAppFrom? stats right start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : start < stats.indConsts.size := by omega
      rcases hconst start hstart with ⟨name, levels, hentry⟩
      have hdecision :=
        checkPositivityStep.isValidIndAppIdx_eq_of_abstractList_eq
          hclosed hentry hparams hleftDisjoint hrightDisjoint
      rw [AddInductive.isValidIndAppFrom?,
        AddInductive.isValidIndAppFrom?, hdecision]
      rw [ih (start := start + 1) (by omega)]

/-- Alpha-invariance of the terminal family classifier under two fresh
binder spines. -/
theorem checkPositivityStep.isValidIndApp?_eq_of_abstractList_eq
    {left right : Expr} {leftBinders rightBinders paramFVars : List FVarId}
    {stats : AddInductive.InductiveStats}
    (hclosed : left.abstractList leftBinders =
      right.abstractList rightBinders)
    (hconst : ∀ i (hi : i < stats.indConsts.size),
      ∃ name levels, stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFVars.map Expr.fvar).toArray)
    (hleftDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ leftBinders)
    (hrightDisjoint : ∀ fv, fv ∈ paramFVars → fv ∉ rightBinders) :
    AddInductive.isValidIndApp? stats left =
      AddInductive.isValidIndApp? stats right := by
  exact checkPositivityStep.isValidIndAppFrom?_eq_of_abstractList_eq
    hclosed hconst hparams hleftDisjoint hrightDisjoint (by omega)

/-- Every ordinal in the complete field array is an actual local declaration
of the traversal's terminal context.  This is the positional bridge needed
before a retained `loopUArgs` input can be related to its selected constructor
field, and does not rely on generated free-variable names. -/
theorem RecursorFieldDecisions.fieldDeclarationAt
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (position : Nat) (hposition : position < all.size) :
    ∃ fv index name type bi kind,
      all[position]! = .fvar fv ∧
      current.lctx.find? fv =
        some (.cdecl index fv name type bi kind) := by
  rcases H.freshBindings Hroot with ⟨Hcurrent, _HrootCurrent, ⟨Hbindings⟩⟩
  have hsize : Hbindings.fvars.length = all.size := by
    have := congrArg Array.size Hbindings.expressions
    simpa using this.symm
  have hpositionFVars : position < Hbindings.fvars.length := by
    simpa [hsize] using hposition
  let fv := Hbindings.fvars[position]'hpositionFVars
  have hfieldOptional : all[position]? = some (.fvar fv) := by
    calc
      all[position]? =
          ((Hbindings.fvars.map Expr.fvar).toArray)[position]? :=
        congrArg (fun xs : Array Expr => xs[position]?) Hbindings.expressions
      _ = some (.fvar fv) := by
        rw [Array.getElem?_eq_getElem (by simpa using hpositionFVars)]
        simp [fv]
  have hfield : all[position]! = .fvar fv := by
    rw [getElem!_pos all position hposition]
    exact (Array.getElem?_eq_some_iff.mp hfieldOptional).2
  have hmember : fv ∈ Hbindings.fvars := by
    exact List.getElem_mem hpositionFVars
  rcases Hcurrent.findCDecl fv (Hbindings.members fv hmember) with
    ⟨index, name, type, bi, kind, hdecl⟩
  exact ⟨fv, index, name, type, bi, kind, hfield, hdecl⟩

/-- The `j`th recursive selection has the local declaration at the exact
ordinal recorded by the executable decision trace. -/
theorem RecursorFieldDecisions.recursiveFieldDeclarationAt
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (j : Nat) (hj : j < selected.size) :
    ∃ fv index name type bi kind,
      selected[j]! = .fvar fv ∧
      all[positions[j]!]! = .fvar fv ∧
      current.lctx.find? fv =
        some (.cdecl index fv name type bi kind) := by
  rcases H.selected_at j hj with ⟨hposition, hselected⟩
  rcases H.fieldDeclarationAt Hroot positions[j]! hposition with
    ⟨fv, index, name, type, bi, kind, hfield, hdecl⟩
  exact ⟨fv, index, name, type, bi, kind,
    hselected.trans hfield, hfield, hdecl⟩

/-- The retained initial `inferType` run is not opaque metadata: for a free
variable it computes exactly the type stored in the production local
context.  This is the first half of the loop replay boundary; subsequent
alpha comparison may therefore start from the two selected constructor-field
declarations rather than arbitrary inferred expressions. -/
theorem RecursorLoopUArgsInput.inferredType_eq_localDecl
    (H : RecursorLoopUArgsInput root (.fvar fv))
    (hfind : root.lctx.find? fv = some decl) :
    H.inferredType = decl.type := by
  have hrun := H.inference
  change ((((TypeChecker.Methods.withFuel root.fuel.recDepth).inferType
      (.fvar fv) true)
        { env := root.env, lctx := root.lctx, safety := root.safety,
          lparams := root.typeCheckerLParams.getD root.lparams,
          fuel := root.fuel }).run' {}) =
    .ok H.inferredType at hrun
  cases hdepth : root.fuel.recDepth with
  | zero =>
      rw [hdepth] at hrun
      simp [TypeChecker.Methods.withFuel, StateT.run, StateT.run',
        Functor.map, StateT.map, Except.map, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift] at hrun
  | succ depth =>
      rw [hdepth] at hrun
      simp only [TypeChecker.Methods.withFuel] at hrun
      have hloose : (.fvar fv : Expr).hasLooseBVars = false := by
        simp [Expr.hasLooseBVars, Expr.looseBVarRange']
      unfold TypeChecker.Inner.inferType' at hrun
      simp only [hloose, Bool.false_eq_true, ↓reduceIte] at hrun
      simp [TypeChecker.Inner.inferFVar, ReaderT.bind, ReaderT.read,
        StateT.bind, StateT.get, StateT.modifyGet, _root_.modify, StateT.run',
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, getThe, modifyGetThe,
        instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
        ReaderT.instMonadLift, instMonadStateOfStateTOfMonad,
        MonadLiftT.monadLift, MonadLift.monadLift,
        liftM, monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        StateT.instMonadLift, StateT.lift] at hrun
      simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
        StateT.instMonad, StateT.bind, StateT.get, StateT.modifyGet,
        StateT.lift, Except.instMonad, Except.bind, Except.pure] at hrun
      simp only [Pure.pure, Functor.map, Applicative.toPure,
        Applicative.toFunctor, Monad.toApplicative, Except.instMonad,
        Except.pure, Except.map] at hrun
      simp [ReaderT.pure, ReaderT.bind, ReaderT.read, StateT.pure,
        StateT.bind, StateT.lift, StateT.map, StateT.modifyGet,
        readThe, MonadReaderOf.read, instMonadReaderOfOfMonadLift,
        instMonadReaderOfReaderTOfMonad, liftM, monadLift,
        MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, ReaderT.read] at hrun
      simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
        ReaderT.read, StateT.instMonad, StateT.bind, StateT.lift,
        StateT.map, StateT.modifyGet, Except.instMonad, Except.bind,
        Except.map] at hrun
      simp only [ReaderT.read, Pure.pure, Functor.map,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        StateT.instMonad, StateT.pure, Except.instMonad, Except.pure,
        Except.map, MonadReader.read, instMonadReaderOfMonadReaderOf,
        readThe, MonadReaderOf.read, instMonadReaderOfReaderTOfMonad] at hrun
      simp [LocalContext.get!, hfind] at hrun
      exact hrun.symm

/-- A retained loop input can always be closed over a caller-selected outer
binder list without losing its connection to the exact production
normalizer result. -/
theorem RecursorLoopUArgsInput.closedNormalized_eq
    (H : RecursorLoopUArgsInput root field)
    (outerBinders : List FVarId) :
    H.closedNormalized outerBinders =
      H.normalizedType.abstractList outerBinders := rfl

/-- When the retained inferred field domain already exposes a forall, the
exact production normalizer run leaves it unchanged. -/
theorem RecursorLoopUArgsInput.normalizedType_eq_of_inferred_forall
    (H : RecursorLoopUArgsInput root field)
    (hinferred : H.inferredType = .forallE name domain body bi) :
    H.normalizedType = H.inferredType := by
  have hnormal := H.normalization
  rw [hinferred] at hnormal ⊢
  change TypeChecker.M.run root.env root.safety root.lctx
      (root.typeCheckerLParams.getD root.lparams)
      root.fuel (TypeChecker.whnf (.forallE name domain body bi)) =
    .ok H.normalizedType at hnormal
  unfold TypeChecker.M.run at hnormal
  generalize hrun : TypeChecker.whnf (.forallE name domain body bi)
      { env := root.env, lctx := root.lctx, safety := root.safety,
        lparams := root.typeCheckerLParams.getD root.lparams,
        fuel := root.fuel }
      ({} : TypeChecker.State) = result at hnormal
  cases result with
  | error error =>
      simp [StateT.run', hrun, Functor.map, Except.map] at hnormal
  | ok result =>
      rcases result with ⟨normalized, outState⟩
      have hresult := TypeChecker.whnf_forall_result_eq
        { env := root.env, lctx := root.lctx, safety := root.safety,
          lparams := root.typeCheckerLParams.getD root.lparams,
          fuel := root.fuel }
        ({} : TypeChecker.State) outState name domain body normalized bi hrun
      rcases hresult with ⟨rfl, _⟩
      simp [StateT.run', hrun, Functor.map, Except.map] at hnormal
      exact hnormal.symm

end VerifyInductive
end Lean4Lean
