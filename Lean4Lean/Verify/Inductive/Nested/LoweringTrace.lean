import Lean4Lean.Verify.Inductive.Nested.Mapping
import Lean4Lean.Verify.Inductive.Nested.ConstructorInstallation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Structural contract for one constructor after nested lowering.  It
records the exact source telescope opened by the executable pass, the arity
check performed before rebuilding it, and the fact that lowering changes
only the constructor type.  The node-level replacement semantics are exposed
separately by `replaceIfNested_recognized`. -/
structure LoweredConstructorShape
    (nparams : Nat) (source target : Constructor) : Prop where
  name : target.name = source.name
  rebuilt : ∃ lctx tail As lowered,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ _ : LocalForallSelection lctx As,
      As.size = nparams ∧ target.type = lctx.mkForall As lowered

theorem LoweredConstructorShape.targetRestoreTelescope
    (H : LoweredConstructorShape nparams source target) :
    RestoreTelescope target.type nparams := by
  rcases H.rebuilt with
    ⟨lctx, tail, As, lowered, Hopening, Hselection, hsize, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

inductive LoweredConstructorShapes (nparams : Nat) :
    List Constructor → List Constructor → Prop
  | nil : LoweredConstructorShapes nparams [] []
  | cons : LoweredConstructorShape nparams source target →
      LoweredConstructorShapes nparams sources targets →
      LoweredConstructorShapes nparams (source :: sources) (target :: targets)

theorem ElimNestedInductive.lowerConstructor.shape
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out => LoweredConstructorShape nparams ctor out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening _Hctx Hselection _hnodup _hnewTypes
    _hnestedAux _hnextIdx _hprefix
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As tail)
    (P := fun _ => True) ?_ ?_
  · intro _ _
    trivial
  · intro lowered nextState _
    exact Except.WF.pure
      ⟨rfl, lctx, tail, As, lowered, Hopening, Hselection, hsize, rfl⟩

/-- Semantic constructor-lowering certificate.  In addition to the rebuilt
telescope shape, it records the complete stateful nested-expression
translation from the opened source tail to the installed constructor type. -/
structure LoweredConstructorTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  translated : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    NestedBindingContextWF lctx openedState.ngen ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReplacement env lctx params As tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- The selected opening of a closed source telescope retains enough
information to reconstruct the closing context used by the stronger
execution invariant. -/
def NestedParamOpening.closingContext
    (H : NestedParamOpening {} #[] source n lctx tail As)
    (Hbinding : NestedBindingContextWF lctx ngen)
    (Hselection : LocalForallSelection lctx As)
    (hnodup : Hselection.fvars.Nodup)
    (Hsource : source.FVarsIn fun _ => False) :
    NestedClosingContext lctx As ngen := by
  refine {
    binding := Hbinding
    selection := Hselection
    nodup := hnodup
    close := ?_ }
  intro body Hbody
  rcases H.forallTelescope with ⟨residual, Htelescope⟩
  rcases H.toRestoreParamOpening.forall_rebuilding_data Hbinding.wf
      Htelescope with
    ⟨decls, _hlctx, hparams, _hlength, _hdeclNodup, _hfind, hrebuild⟩
  have hids : Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions]
      apply Array.toList_inj.mp
      simpa [Function.comp_def] using hparams
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have hsourceFold :
      Hselection.fvars.foldr
          (fun fv result =>
            LocalContext.mkBindingList1 false lctx [] fv
              (result.abstract1 fv)) tail = source := by
    have hclosed := FVarsIn_to_FVarIdsIn Hsource
    have havoid : source.FVarIdsIn
        (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
      hclosed.mono fun fv hfalse => False.elim hfalse
    simpa [hids] using hrebuild havoid
  have hbodyFold : lctx.mkForall As body =
      Hselection.fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 false lctx [] fv
            (result.abstract1 fv)) body := by
    calc
      lctx.mkForall As body =
          lctx.mkForall (Hselection.fvars.map Expr.fvar).toArray body :=
        congrArg (fun xs => lctx.mkForall xs body) Hselection.expressions
      _ = _ := by
        rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
        apply LocalContext.mkBindingList_eq_fold
        · intro fv hfv
          rcases Hselection.declarations fv hfv with
            ⟨index, name, type, bi, kind, hfind⟩
          exact ⟨.cdecl index fv name type bi kind, hfind⟩
        · exact hnodup
  have hsame := LocalContext.sameForallPrefix_fold
    Hselection.declarations body tail
  have hlen : Hselection.fvars.length = n := by
    have := congrArg Array.size Hselection.expressions
    simpa [H.initial_size] using this.symm
  rw [hlen, hsourceFold, ← hbodyFold] at hsame
  have HbodyResidual : (body.abstractList Hselection.fvars).FVarsIn
      (fun _ => False) := by
    apply FVarsIn.abstractList_of
    exact Hbody.mono fun fv hfv => Or.inl hfv
  have HbodyTelescope := Hselection.forallTelescope body
  rw [H.initial_size] at HbodyTelescope
  exact hsame.leftFVarsIn HbodyTelescope Hsource HbodyResidual

theorem LoweredConstructorTranslation.targetRestoreTelescope
    (H : LoweredConstructorTranslation env params nparams source state out) :
    RestoreTelescope out.1.type nparams := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hreplace, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

theorem LoweredConstructorTranslation.newTypesLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, hopenedTypes, _, _,
      _, Hreplace, _⟩
  rcases Hreplace.newTypesLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedTypes] using hsuffix⟩

theorem LoweredConstructorTranslation.nestedAuxLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux, _, _,
      Hreplace, _⟩
  rcases Hreplace.nestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedAux] using hsuffix⟩

theorem LoweredConstructorTranslation.pendingSourceFamilyOrigins
    (H : LoweredConstructorTranslation env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Horigins : PendingSourceFamilyOrigins env params initial cursor state) :
    PendingSourceFamilyOrigins env params initial cursor out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hbinding,
      Hselection, hnodup, hopenedTypes, hopenedAux, _hopenedNext, _hsize,
      Hreplace, _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hopened : PendingSourceFamilyOrigins env params initial cursor
      openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    rcases Horigins j hcursor hjState with ⟨Horigin⟩
    have Haux : NestedAuxLE state openedState := by
      unfold NestedAuxLE
      rw [hopenedAux]
      exact ⟨[], by simp⟩
    have Horigin' := Horigin.mono Haux
    exact ⟨by simpa [hopenedTypes] using Horigin'⟩
  have Hclosing : NestedClosingContext lctx As openedState.ngen :=
    Hopening.closingContext Hbinding Hselection hnodup Hsource
  exact Hreplace.pendingSourceFamilyOrigins Hselection hnodup Hclosing
    hclosures Htail Hopened

theorem LoweredConstructorTranslation.namesWF
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      hopenedNext, _, Hreplace, _⟩
  exact Hreplace.namesWF
    (Hstate.ofCacheCounterEq hopenedAux hopenedNext)

theorem LoweredConstructorTranslation.namesFresh
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      _, _, Hreplace, _⟩
  exact Hreplace.namesFresh (Hstate.ofCacheEq hopenedAux)

theorem LoweredConstructorTranslation.auxFVarsIn
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, _hopenedTypes, hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hinput : tail.FVarsIn
      (fun fv => fv ∈ Hselection.fvars ∨ P fv) :=
    Htail.mono fun _ hfv => Or.inl hfv
  have Hopened : NestedAuxFVarsIn P openedState := by
    intro nested name hentry
    apply Hstate nested name
    rwa [hopenedAux] at hentry
  exact Hreplace.auxFVarsIn Hselection Hinput Hparams Hopened

theorem LoweredConstructorTranslation.pendingNewTypesClosed
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hbinding, Hselection,
      hnodup, hopenedTypes, _hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  let Hclosing := Hopening.closingContext Hbinding Hselection hnodup Hsource
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hopened : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  apply Hreplace.pendingNewTypesClosed Henv Hclosing
  · simpa only [Hclosing, NestedParamOpening.closingContext] using Htail
  · exact Hopened

/-- Constructor lowering interpreted against the final restoration map. The
opened source telescope and rebuilt target telescope are retained verbatim,
while the body traversal is promoted from operational replacement to the
semantic `NestedExprMapping` relation. -/
structure LoweredConstructorMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  mapped : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprMapping env lctx params As finalResult tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- Constructor lowering with its expression mapping upgraded pointwise to
reopening under a restoration parameter array. -/
structure LoweredConstructorReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  reopened : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReopening env lctx params As finalResult restoreAs tail
        openedState (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- A mapped lowered constructor type contains no free-variable IDs: the
translated body remains scoped by the copied source parameters, and the
rebuilt forall telescope closes exactly those parameters. -/
theorem LoweredConstructorMapping.targetFVarIdsClosed
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    out.1.type.FVarIdsIn fun _ => False := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  have Hlowered : lowered.FVarIdsIn (· ∈ Hselection.fvars) :=
    Hmapping.outputFVarIdsIn Hselection (FVarsIn_to_FVarIdsIn Htail)
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rw [htype]
  exact Hopening.toRestoreParamOpening.root_mkForall_fvarIdsClosed hlctxWF
    Htelescope (FVarsIn_to_FVarIdsIn Hsource) Hselection Hlowered

/-- Source and lowered constructor types have exactly the same retained
forall prefix; lowering changes only the residual constructor body. -/
theorem LoweredConstructorMapping.sourceTargetSameForallPrefix
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    Expr.SameForallPrefix nparams source.type out.1.type := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rcases Hopening.toRestoreParamOpening.forall_rebuilding_data hlctxWF
      Htelescope with
    ⟨decls, _hlctx, hparams, _hlength, _hdeclNodup, _hfind, hrebuild⟩
  have hids : Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions]
      apply Array.toList_inj.mp
      simpa [Function.comp_def] using hparams
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have hsourceFold :
      Hselection.fvars.foldr
          (fun fv result =>
            LocalContext.mkBindingList1 false lctx [] fv
              (result.abstract1 fv)) tail = source.type := by
    have hclosed := FVarsIn_to_FVarIdsIn Hsource
    have havoid : source.type.FVarIdsIn
        (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
      hclosed.mono fun fv hfalse => False.elim hfalse
    simpa [hids] using hrebuild havoid
  have htargetFold : lctx.mkForall As lowered =
      Hselection.fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 false lctx [] fv
            (result.abstract1 fv)) lowered := by
    calc
      lctx.mkForall As lowered =
          lctx.mkForall (Hselection.fvars.map Expr.fvar).toArray lowered :=
        congrArg (fun xs => lctx.mkForall xs lowered) Hselection.expressions
      _ = _ := by
        rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
        apply LocalContext.mkBindingList_eq_fold
        · intro fv hfv
          rcases Hselection.declarations fv hfv with
            ⟨index, name, type, bi, kind, hfind⟩
          exact ⟨.cdecl index fv name type bi kind, hfind⟩
        · exact hnodupAs
  have hsame := LocalContext.sameForallPrefix_fold
    Hselection.declarations tail lowered
  have hlen : Hselection.fvars.length = nparams := by
    have := congrArg Array.size Hselection.expressions
    simpa [hsize] using this.symm
  rw [hlen] at hsame
  rw [hsourceFold, ← htargetFold, ← htype] at hsame
  exact hsame

theorem LoweredConstructorMapping.reopens
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopening env params nparams finalResult restoreAs source
      state out := by
  refine ⟨H.name, ?_⟩
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hmapping.reopens hresultParams fvars hparams hnodup Hselection Htail,
    htype⟩

/-- Opening the lowered constructor with restoration's fresh parameters
produces the lowering body renamed from its original parameter selection to
the concrete restoration array. -/
theorem LoweredConstructorReopening.restoreTail
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs := by
  rcases H.reopened with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype⟩
  have Htelescope := Hselection.forallTelescope lowered
  rw [hsize, ← htype] at Htelescope
  have htail := Hrestore.forallResidual Htelescope
  have habstract : lowered.abstract As =
      lowered.abstractList Hselection.fvars :=
    calc
      lowered.abstract As = lowered.abstract
          (Hselection.fvars.map Expr.fvar).toArray :=
        congrArg lowered.abstract Hselection.expressions
      _ = lowered.abstractList Hselection.fvars :=
        Expr.abstract_eq lowered Hselection.fvars
  refine ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype,
    ?_⟩
  simpa [habstract] using htail

/-- The body exposed by restoration is the original constructor body with
the restoration parameters substituted for lowering's fresh parameters.
This is the constructor-scoped inverse theorem: it combines the exact two
telescope traversals with the structural inverse for nested replacement. -/
theorem LoweredConstructorReopening.restoreTail_inverse
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail)
    (restoreEnv : Environment)
    (htargetAs : targetAs = restoreAs)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs ∧
        ((restoredTail.replace
            (finalResult.restoreNestedNode restoreEnv restoreAs {})) ==
          Expr.reopenParams tail As restoreAs) = true := by
  rcases H.restoreTail restoreLctx restoreAs restoredTail Hrestore with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
      htype, hrestoredTail⟩
  rcases Hrestore.params_fvars_extension with
    ⟨restoreFvars, hrestoreList, hrestoreLength⟩
  have hrestoreArray :
      restoreAs = (restoreFvars.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa using hrestoreList
  have hselectionLength : Hselection.fvars.length = As.size := by
    simpa using (congrArg Array.size Hselection.expressions).symm
  have hrestoreSize :
      restoreFvars.length = Hselection.fvars.length := by
    rw [hrestoreLength, hselectionLength, hsize]
  have hresultSize : finalResult.nparams = As.size := by
    rw [hresultNParams, hsize]
  have HtailSource : RestoreSourceDisjoint finalResult restoreEnv tail :=
    Hopening.tailRestoreSourceDisjoint Hsource
  have hinverse := Hreopening.restore_eqv restoreEnv Hselection hnodupAs
    restoreFvars
    (by simpa [htargetAs] using hrestoreArray) hrestoreSize hresultSize
    HtailSource 0
  have hloweredOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray lowered 0
  have hsourceOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray tail 0
  have hrestoredOpen :
      restoredTail = Expr.reopenParams lowered As restoreAs := by
    simpa [Expr.reopenParams] using hrestoredTail
  rw [htargetAs, hloweredOpen, hsourceOpen, ← hrestoredOpen] at hinverse
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
    htype, hrestoredTail, hinverse⟩

/-- Operational constructor restoration consumes a mapped lowering body and
produces the correspondingly renamed source body.  Unlike
`restoreTail_inverse`, this theorem starts from the mapping certificate
available before restoration chooses its fresh variables and concludes about
the `restoredBody` retained by `NestedRestoration`. -/
theorem LoweredConstructorMapping.restoredBody_inverse
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (restoreEnv : Environment)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
  have Hreopening : LoweredConstructorReopening env params nparams finalResult
      restoreAs source state out :=
    H.reopens hresultParams paramFvars hparams hnodup HsourceClosed
  rcases Hreopening.restoreTail_inverse restoreLctx restoreAs openedBody
      Hrestore restoreEnv rfl hresultNParams Hsource with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, _hopenedTypes, _hopenedAux, _hopenedNext, hsize,
      _Hreopening, _htype, _hopenedBody, hinverse⟩
  have hrestoredInverse :
      (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
    rw [Hbody.eq_replace]
    exact hinverse
  exact ⟨lctx, tail, As, Hopening, Hselection, hnodupAs, hsize,
    hrestoredInverse⟩

theorem LoweredConstructorMapping.restoredBody_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved finalResult restoreEnv)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true :=
  H.restoredBody_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreLctx restoreAs openedBody restoredBody Hrestore
    restoreEnv Hbody hresultNParams
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved)

/-- A whole operational `NestedRestoration` of a lowered constructor, with
its restored body related back to the independently checked source
constructor body.  The outer telescope equations are retained explicitly;
the next abstraction layer can therefore prove alpha-equivalence without
replaying either executable traversal. -/
structure ConstructorRestorationBodyInverse
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (nparams : Nat) (source lowered : Constructor) (restoredType : Expr) where
  restoreLctx : LocalContext
  restoreAs : Array Expr
  openedBody : Expr
  restoredBody : Expr
  loweredOpening : RestoreParamOpening {} #[] lowered.type nparams
    restoreLctx restoreAs openedBody
  restoreLctxWF : restoreLctx.WF
  restoreSelection : LocalForallSelection restoreLctx restoreAs
  restoreNodup : restoreSelection.fvars.Nodup
  bodyRestoration : ExprReplacement
    (result.restoreNestedNode env restoreAs {}) openedBody restoredBody
  output : restoredType = if lowered.type.isForall then
    restoreLctx.mkForall restoreAs restoredBody
    else restoreLctx.mkLambda restoreAs restoredBody
  sourceLctx : LocalContext
  sourceTail : Expr
  sourceAs : Array Expr
  sourceClosed : source.type.FVarsIn fun _ => False
  loweredFVarIdsClosed : lowered.type.FVarIdsIn fun _ => False
  sourceLoweredPrefix :
    Expr.SameForallPrefix nparams source.type lowered.type
  sourceOpening : NestedParamOpening {} #[] source.type nparams sourceLctx
    sourceTail sourceAs
  sourceSelection : LocalForallSelection sourceLctx sourceAs
  sourceNodup : sourceSelection.fvars.Nodup
  sourceArity : sourceAs.size = nparams
  bodyInverse :
    (restoredBody == Expr.reopenParams sourceTail sourceAs restoreAs) = true

/-- Whole-constructor restoration inverse stated at its semantic boundary.
This form does not assume any naming convention for generated auxiliary
constructors; callers may establish source disjointness from typing and
freshness instead. -/
theorem LoweredConstructorMapping.nestedRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  rcases Hrestored with
    ⟨restoreLctx, restoreAs, openedBody, restoredBody, Hopening,
      Hbody, houtput⟩
  rcases Hopening.2 with ⟨hrestoreLctxWF, HrestoreSelection,
    hrestoreNodup⟩
  have Hopening' := Hopening.1
  rw [hresultNParams] at Hopening'
  rcases H.restoredBody_inverse hresultParams paramFvars hparams hnodup
      HsourceClosed restoreLctx restoreAs openedBody restoredBody Hopening'
      restoreEnv Hbody hresultNParams HsourceDisjoint with
    ⟨sourceLctx, sourceTail, sourceAs, HsourceOpening, Hselection,
      hsourceNodup, hsourceArity, hinverse⟩
  exact ⟨{
    restoreLctx := restoreLctx
    restoreAs := restoreAs
    openedBody := openedBody
    restoredBody := restoredBody
    loweredOpening := Hopening'
    restoreLctxWF := hrestoreLctxWF
    restoreSelection := HrestoreSelection
    restoreNodup := hrestoreNodup
    bodyRestoration := Hbody
    output := houtput
    sourceLctx := sourceLctx
    sourceTail := sourceTail
    sourceAs := sourceAs
    sourceClosed := HsourceClosed
    loweredFVarIdsClosed := H.targetFVarIdsClosed HsourceClosed
    sourceLoweredPrefix := H.sourceTargetSameForallPrefix HsourceClosed
    sourceOpening := HsourceOpening
    sourceSelection := Hselection
    sourceNodup := hsourceNodup
    sourceArity := hsourceArity
    bodyInverse := hinverse }⟩

theorem LoweredConstructorMapping.nestedRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  exact H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored

/-- Eliminate the source-opening free variables from the body inverse.  The
restored body is the ordinary residual of the original constructor telescope,
instantiated only with restoration's fresh parameter array. -/
theorem ConstructorRestorationBodyInverse.restoredBody_residual
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    ∃ residual,
      Expr.ForallTelescope source.type nparams residual ∧
      (H.restoredBody == residual.instantiateRev H.restoreAs) = true := by
  rcases H.sourceOpening.forallTelescope with ⟨residual, Htelescope⟩
  have htail : H.sourceTail = residual.instantiateRev H.sourceAs :=
    H.sourceOpening.toRestoreParamOpening.forallResidual Htelescope
  have hfree : residual.FVarsIn
      (fun fv => fv ∉ H.sourceSelection.fvars) :=
    (Htelescope.resultFVarsIn H.sourceClosed).mono fun fv hfalse =>
      False.elim hfalse
  have hcancel := hfree.reabstract_instantiateRev_fvarArray H.sourceAs
    H.restoreAs H.sourceSelection.fvars H.sourceSelection.expressions
    H.sourceNodup
  have hopen : Expr.reopenParams H.sourceTail H.sourceAs H.restoreAs =
      residual.instantiateRev H.restoreAs := by
    rw [htail]
    simpa [Expr.reopenParams] using hcancel
  have hinverse := H.bodyInverse
  rw [hopen] at hinverse
  exact ⟨residual, Htelescope, hinverse⟩

/-- Whole-constructor inverse: rebuilding the restored body under the copied
parameter telescope yields a constructor type equivalent to the independent
source constructor type. -/
theorem ConstructorRestorationBodyInverse.restoredType_eqv_source
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    (restoredType == source.type) = true := by
  rcases H.sourceLoweredPrefix.transferRestoreOpening H.loweredOpening with
    ⟨sourceOpened, HsourceRestore⟩
  rcases H.restoredBody_residual with
    ⟨residual, Htelescope, hbodyResidual⟩
  have hsourceOpened :
      sourceOpened = residual.instantiateRev H.restoreAs :=
    HsourceRestore.forallResidual Htelescope
  have hbodyOpened : (H.restoredBody == sourceOpened) = true := by
    rw [hsourceOpened]
    exact hbodyResidual
  have hclosedSource : source.type.FVarIdsIn fun _ => False :=
    FVarsIn_to_FVarIdsIn H.sourceClosed
  have hsourceRebuild :
      H.restoreLctx.mkForall H.restoreAs sourceOpened = source.type :=
    HsourceRestore.root_mkForall_tail H.restoreLctxWF Htelescope hclosedSource
  have hwrapped := H.restoreSelection.mkForall_eqv H.restoreNodup hbodyOpened
  rw [hsourceRebuild] at hwrapped
  have houtput : restoredType =
      H.restoreLctx.mkForall H.restoreAs H.restoredBody := by
    refine H.output.trans ?_
    by_cases hzero : nparams = 0
    · have hsize : H.restoreAs.size = 0 :=
        H.loweredOpening.initial_size.trans hzero
      have hempty : H.restoreAs = #[] :=
        Array.eq_empty_of_size_eq_zero hsize
      rw [hempty]
      split
      · rfl
      · rw [LocalContext.mkForall, LocalContext.mkLambda]
        rw [show (#[] : Array Expr) =
            (([] : List FVarId).map Expr.fvar).toArray from rfl,
          LocalContext.mkBinding_eq, LocalContext.mkBinding_eq]
        simp only [LocalContext.mkBindingList_nil]
    · have hpos : 0 < nparams := Nat.pos_of_ne_zero hzero
      have hisForall :=
        H.sourceLoweredPrefix.target_isForall_of_pos hpos
      simp [hisForall]
  rw [houtput]
  exact hwrapped

/-- Metadata-facing form of the constructor inverse.  Installation exposes a
`ConstructorVal`, while lowering is indexed by the corresponding
`Constructor`; the explicit type equality is the only alignment fact needed
to connect the two verified traces. -/
theorem LoweredConstructorMapping.constructorRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    HsourceClosed restoreEnv HsourceDisjoint hresultNParams
  simpa [htype] using Hrestored.type

theorem LoweredConstructorMapping.constructorRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverseOfSyntax hresultParams paramFvars hparams
    hnodup Hsyntax restoreEnv Hreserved hresultNParams
  simpa [htype] using Hrestored.type

/-- Transport source translation across constructor restoration using exact
semantic disjointness, without imposing a namespace convention on generated
constructor names. -/
theorem LoweredConstructorMapping.restoredType_translation
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed restoreEnv HsourceDisjoint hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  apply Hsource.eqv
  simpa [beq_comm] using Hinverse.restoredType_eqv_source

/-- Recover the independently specified source-constructor translation from
the translation of the exact restored production constructor.  This is the
direction needed by the outer nested verifier: the executable checker sees
the restored type, while the abstract declaration is stated using the
original pre-lowering source type. -/
theorem LoweredConstructorMapping.sourceType_translationOfRestored
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Htranslation : TrExprS venv oldInfo.levelParams []
      newInfo.type targetType) :
    TrExprS venv oldInfo.levelParams [] source.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed restoreEnv HsourceDisjoint hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  exact Htranslation.eqv Hinverse.restoredType_eqv_source

/-- Syntax-specialized reverse transport.  Source closedness and
restoration-name disjointness follow from the independently checked source
syntax and the reserved auxiliary namespace. -/
theorem LoweredConstructorMapping.sourceType_translationOfRestoredSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Htranslation : TrExprS venv oldInfo.levelParams []
      newInfo.type targetType) :
    TrExprS venv oldInfo.levelParams [] source.type targetType := by
  exact H.sourceType_translationOfRestored hresultParams paramFvars hparams
    hnodup Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored htype Htranslation

/-- Transport a source constructor's abstract translation across lowering and
restoration.  This is the semantic premise needed by constructor installation;
unlike translation of the lowered constructor, it is obtained from the
independent pre-lowering source type. -/
theorem LoweredConstructorMapping.restoredType_translationOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  exact H.restoredType_translation hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored htype Hsource

/-- Install a restored constructor from its independent source translation
and exact semantic disjointness from the generated auxiliary declarations. -/
theorem RestoredConstructorStep.installationOfDisjoint
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid constructor Hsafety Huvars Hname
  · exact Hmapping.restoredType_translation hresultParams paramFvars
      hparams hnodup HsourceClosed loweredEnv HsourceDisjoint hresultNParams
      Hstep.restored.restoration htype Hsource
  · exact Hwf

/-- Source-declaration specialization of `installationOfDisjoint`.  A single
`TrSourceConst` supplies the abstract constructor used both by the source
`TrInductDeclCore` and by the exact restored installation trace. -/
theorem RestoredConstructorStep.installationOfSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup HsourceClosed HsourceDisjoint hresultNParams htype Hvalid
    constructor Hsafety
  · rw [hlevels]
    exact Hsource.uvars.symm
  · exact hname.trans Hsource.name.symm
  · simpa [hlevels] using Hsource.type
  · exact Hsource.wf

/-- Preferred source-syntax installation endpoint. Auxiliary family names are
reserved by the lowering cache, while auxiliary constructor names need only
be fresh in the abstract source environment; no constructor namespace
convention is assumed. -/
theorem RestoredConstructorStep.installationOfFresh
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact Huvars
  · exact Hname
  · exact Hsource
  · exact Hwf

/-- Preferred end-to-end constructor endpoint.  Fresh-cache lowering gives
the semantic restoration disjointness, while the independent source
translation is reused unchanged by declaration formation and installation. -/
theorem RestoredConstructorStep.installationOfFreshSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfSource Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.type.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact hlevels
  · exact hname
  · exact Hsource

/-- Namespace-based convenience specialization of
`installationOfDisjoint`.  The semantic endpoint above is the preferred path
for arbitrary kernel constructor names. -/
theorem RestoredConstructorStep.installationOfSyntax
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hreserved : RestoreNamesReserved result loweredEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv
      (.ctorInfo Hstep.oldInfo) constructor)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams htype
    Hvalid constructor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hold.2
  · exact Hsource
  · exact Hwf

theorem LoweredConstructorTranslation.finalMapping
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMapping env params nparams finalResult source state out := by
  refine ⟨H.name, ?_⟩
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreplace, htype⟩
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF.wf, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hreplace.finalMapping Hlater Hmap, htype⟩

theorem ElimNestedInductive.lowerConstructor.translation
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening Hctx Hselection hnodup hopenedTypes
    hopenedAux hopenedNext _hprefix
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  exact Except.WF.pure
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening, Hctx, Hselection,
      hnodup, hopenedTypes, hopenedAux, hopenedNext, hsize, Hlowered, rfl⟩

theorem ElimNestedInductive.lowerConstructor.translationPending
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctor : ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesClosing (Htype := Hctor)
  intro lctx tail As openedState Hopening Hclosing Htail hopenedTypes
    hopenedAux hopenedNext _hprefix
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  have HopenedPending : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  exact Except.WF.pure ⟨
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening,
      Hclosing.binding, Hclosing.selection, Hclosing.nodup,
      hopenedTypes, hopenedAux, hopenedNext, hsize,
      Hlowered, rfl⟩,
    Hlowered.pendingNewTypesClosed Henv Hclosing Htail HopenedPending⟩

/-- Stateful positional correspondence for an entire constructor list. -/
inductive LoweredConstructorTranslations
    (env : Environment) (params : Array Expr) (nparams : Nat) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorTranslations env params nparams [] state ([], state)
  | cons : LoweredConstructorTranslation env params nparams source state step →
      LoweredConstructorTranslations env params nparams sources step.2 out →
      LoweredConstructorTranslations env params nparams (source :: sources)
        state (step.1 :: out.1, out.2)

theorem LoweredConstructorTranslations.newTypesLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.newTypesLE.trans ih

theorem LoweredConstructorTranslations.nestedAuxLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.nestedAuxLE.trans ih

theorem LoweredConstructorTranslations.pendingSourceFamilyOrigins
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (hclosures : MutualInductivesClosed env)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Horigins : PendingSourceFamilyOrigins env params initial cursor state) :
    PendingSourceFamilyOrigins env params initial cursor out.2 := by
  induction H with
  | nil => exact Horigins
  | cons Hhead Htail ih =>
    exact ih (fun source hsource => Hsources source (by simp [hsource]))
      (Hhead.pendingSourceFamilyOrigins hclosures
        (Hsources _ (by simp)) Horigins)

theorem LoweredConstructorTranslations.pendingNewTypesClosed
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    exact ih (fun source hsource => Hsources source (by simp [hsource]))
      (Hhead.pendingNewTypesClosed Henv (Hsources _ (by simp)) Hstate)

theorem LoweredConstructorTranslations.namesWF
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesWF Hstate)

theorem LoweredConstructorTranslations.namesFresh
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesFresh Hstate)

theorem LoweredConstructorTranslations.auxFVarsIn
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    apply ih
    · intro source hsource
      exact Hsources source (by simp [hsource])
    · exact Hhead.auxFVarsIn (Hsources _ (by simp)) Hparams Hstate

inductive LoweredConstructorMappings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorMappings env params nparams finalResult [] state
      ([], state)
  | cons : LoweredConstructorMapping env params nparams finalResult source
      state step →
      LoweredConstructorMappings env params nparams finalResult sources step.2
        out →
      LoweredConstructorMappings env params nparams finalResult
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.length
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) : out.1.length = sources.length := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [ih]

/-- Positional projection of the state-threaded constructor mapping.  Both
the source and target list lookups are retained, so subsequent restoration
folds can align their metadata without a name-based uniqueness assumption. -/
theorem LoweredConstructorMappings.mappingAt
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) (i : Nat) (hi : i < sources.length) :
    ∃ source target before after,
      sources[i]? = some source ∧
      out.1[i]? = some target ∧
      LoweredConstructorMapping env params nparams finalResult source before
        (target, after) := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons source state step sources out Hhead Htail ih =>
    cases i with
    | zero => exact ⟨source, step.1, state, step.2, by simp, by simp, Hhead⟩
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rcases ih i hi with
        ⟨tailSource, tailTarget, before, after, hsource, htarget, Hmapping⟩
      exact ⟨tailSource, tailTarget, before, after, by simpa, by simpa,
        Hmapping⟩

/-- Lockstep alignment of the state-threaded constructor lowering relation
with the exact operational restoration fold.  The production lookup theorem
has already identified the `oldInfo.type` read at every step with that step's
positionally corresponding lowered constructor type. -/
inductive RestoredConstructorMappingTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams [] state [] state sourceProdEnv sourceProdEnv
  | cons
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hrest : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams sources nextState targets finalState
          middleProdEnv targetProdEnv) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
        safety lparams (source :: sources) state (target :: targets) finalState
          sourceProdEnv targetProdEnv


/-- Interpret the proof-independent lowering/restoration trace against the
independently translated source constructors.  This is the constructor-list
implementation/specification bridge: every executable restoration step is
shown to translate the same abstract constructor that appears in the source
inductive specification. -/
theorem RestoredConstructorMappingTrace.sourceSemantics
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv
        sources constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i vctor vconstructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type vctor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type vctor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) vctor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredSourceConstructorTrace.cons Hstep
          { constructor := vctor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

/-- Reconstruct the canonical source-constructor list from translations of
the exact restored production steps.  This reverses the former dependency:
the caller supplies what the executable restoration installs, and the
lowering inverse derives the independent pre-lowering source translation. -/
theorem RestoredConstructorMappingTrace.sourceTranslationsOfRestored
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hrestored : ∀ {source state target nextState stepSource stepTarget}
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        stepSource stepTarget),
      ∃ constructor : VConstVal,
        TrConstVal safety canonicalEnv (.ctorInfo Hstep.restored.newInfo)
          constructor ∧
        constructor.toVConstant.WF canonicalEnv)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    ∃ constructors : List VConstVal,
      List.Forall₂ (fun source constructor =>
        TrSourceConst canonicalEnv lparams source.name source.type constructor)
        sources constructors := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Htail ih =>
    cases Hsyntax with
    | cons HsourceSyntax HtailSyntax =>
      rcases Hrestored Hmapping Hstep with ⟨constructor, Htranslated, Hwf⟩
      have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
          Hstep.restored.newInfo.type constructor.type := by
        have Htype := Htranslated.1.2.2
        change TrExprS canonicalEnv Hstep.restored.newInfo.levelParams []
          Hstep.restored.newInfo.type constructor.type at Htype
        simpa [Hstep.restored.restoration.levelParams] using Htype
      have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
          source.type constructor.type :=
        Hmapping.sourceType_translationOfRestored hresultParams paramFvars
          hparams hnodup HsourceSyntax.closed loweredEnv
          (Hdisjoint source (by simp)) hresultNParams
          Hstep.restored.restoration htype HrestoredType
      have Hsource : TrSourceConst canonicalEnv lparams source.name source.type
          constructor := {
        uvars := by
          have Huvars := Htranslated.1.2.1
          change Hstep.restored.newInfo.levelParams.length = constructor.uvars
            at Huvars
          rw [Hstep.restored.restoration.levelParams, hlevels] at Huvars
          exact Huvars.symm
        name := by
          have HnewName := Htranslated.2
          change Hstep.restored.newInfo.name = constructor.name at HnewName
          exact HnewName.symm.trans <|
            Hstep.restored.restoration.name.trans <|
              hname.trans Hmapping.name
        type := by simpa [hlevels] using HsourceType
        wf := Hwf }
      have HtailDisjoint : ∀ tail ∈ sources,
          RestoreSourceDisjoint result loweredEnv tail.type := by
        intro tail htail
        exact Hdisjoint tail (by simp [htail])
      rcases ih HtailSyntax HtailDisjoint with
        ⟨constructors, Hsources⟩
      exact ⟨constructor :: constructors, .cons Hsource Hsources⟩

/-- Exact-trace source semantics obtained from restored constructor
translations.  The resulting abstract constructor list is both the source
declaration payload and the interpretation of the production restoration
fold. -/
theorem RestoredConstructorMappingTrace.sourceSemanticsOfRestored
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hrestored : ∀ {source state target nextState stepSource stepTarget}
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        stepSource stepTarget),
      ∃ constructor : VConstVal,
        TrConstVal safety canonicalEnv (.ctorInfo Hstep.restored.newInfo)
          constructor ∧
        constructor.toVConstant.WF canonicalEnv)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    ∃ constructors : List VConstVal,
      RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv
          sources constructors := by
  rcases H.sourceTranslationsOfRestored Hrestored Hsyntax Hdisjoint
      hresultParams paramFvars hparams hnodup hresultNParams with
    ⟨constructors, Hsources⟩
  exact ⟨constructors, H.sourceSemantics Hsources Hsyntax Hdisjoint
    hresultParams paramFvars hparams hnodup hresultNParams⟩

inductive LoweredConstructorReopenings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorReopenings env params nparams finalResult restoreAs
      [] state ([], state)
  | cons : LoweredConstructorReopening env params nparams finalResult restoreAs
      source state step →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        sources step.2 out →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.reopens
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopenings env params nparams finalResult restoreAs
      sources state out := by
  induction H with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    apply LoweredConstructorReopenings.cons
    · exact Hhead.reopens hresultParams fvars hparams hnodup
        (Hsources _ (by simp))
    · apply ih
      intro source hsource
      exact Hsources source (by simp [hsource])

theorem LoweredConstructorTranslations.finalMapping
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMappings env params nparams finalResult sources state out := by
  induction H generalizing finalState with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    exact .cons
      (Hhead.finalMapping (Htail.nestedAuxLE.trans Hlater) Hmap)
      (ih Hlater Hmap)

theorem LoweredConstructorTranslations.targetsRestoreTelescope
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    ∀ ctor ∈ out.1, RestoreTelescope ctor.type nparams := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.targetRestoreTelescope
    · exact ih ctor htail

theorem ElimNestedInductive.lowerConstructors.translations
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translation params nparams ctor
        env state hparams hclosures) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

theorem ElimNestedInductive.lowerConstructors.translationsPending
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctors : ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out ∧
        PendingNewTypesClosed cursor out.2 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure ⟨.nil, Hstate⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translationPending params nparams
        ctor env state hparams hclosures Henv (Hctors ctor (by simp)) Hstate) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState
      (fun tail htail => Hctors tail (by simp [htail])) Hlowered.2) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure ⟨.cons Hlowered.1 Htail.1, Htail.2⟩

theorem ElimNestedInductive.lowerConstructors.shapes
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (ctors.mapM
      (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorShapes nparams ctors out.1 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.shape
        params nparams ctor env state) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

/-- Family-level lowering preserves the family header verbatim and changes
only its positionally corresponding constructor types. -/
structure LoweredInductiveShape
    (nparams : Nat) (source target : InductiveType) : Prop where
  name : target.name = source.name
  type : target.type = source.type
  constructors : LoweredConstructorShapes nparams source.ctors target.ctors

theorem ElimNestedInductive.lowerInductive.shape
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out => LoweredInductiveShape nparams indType out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.shapes
      params nparams indType.ctors env state) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

/-- Family-level semantic lowering: headers are preserved and the constructor
list carries the full state-threaded nested-expression translation. -/
structure LoweredInductiveTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorTranslations env params nparams source.ctors
    state (out.1.ctors, out.2)

structure LoweredInductiveMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorMappings env params nparams finalResult
    source.ctors state (out.1.ctors, out.2)

structure LoweredInductiveReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorReopenings env params nparams finalResult
    restoreAs source.ctors state (out.1.ctors, out.2)

theorem LoweredInductiveMapping.reopens
    (H : LoweredInductiveMapping env params nparams finalResult source state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False) :
    LoweredInductiveReopening env params nparams finalResult restoreAs source
      state out :=
  ⟨H.name, H.type,
    H.constructors.reopens hresultParams fvars hparams hnodup Hsource⟩

theorem LoweredInductiveTranslation.newTypesLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := H.constructors.newTypesLE

theorem LoweredInductiveTranslation.nestedAuxLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := H.constructors.nestedAuxLE

theorem LoweredInductiveTranslation.pendingSourceFamilyOrigins
    (H : LoweredInductiveTranslation env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : InductiveConstructorsClosed source)
    (Horigins : PendingSourceFamilyOrigins env params initial cursor state) :
    PendingSourceFamilyOrigins env params initial cursor out.2 :=
  H.constructors.pendingSourceFamilyOrigins hclosures Hsource Horigins

theorem LoweredInductiveTranslation.pendingNewTypesClosed
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed source)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 :=
  H.constructors.pendingNewTypesClosed Henv Hsource Hstate

theorem LoweredInductiveTranslation.namesWF
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 :=
  H.constructors.namesWF Hstate

theorem LoweredInductiveTranslation.namesFresh
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 :=
  H.constructors.namesFresh Hstate

theorem LoweredInductiveTranslation.auxFVarsIn
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 :=
  H.constructors.auxFVarsIn Hsource Hparams Hstate

theorem LoweredInductiveTranslation.finalMapping
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredInductiveMapping env params nparams finalResult source state out :=
  ⟨H.name, H.type, H.constructors.finalMapping Hlater Hmap⟩

theorem LoweredInductiveTranslation.targetRestoreTelescope
    (H : LoweredInductiveTranslation env params nparams source state out) :
    ∀ ctor ∈ out.1.ctors, RestoreTelescope ctor.type nparams :=
  H.constructors.targetsRestoreTelescope

/-- Complete provenance for a family after its dynamic queue slot has been
processed.  The source is classified independently of the lowering step, and
the cache suffix records that the step remains interpretable by the final
restoration map. -/
structure FinalLoweredFamilyOrigin
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (initial : Array InductiveType)
    (finalState : Lean4Lean.ElimNestedInductive.State)
    (target : InductiveType) where
  source : InductiveType
  sourceOrigin : SourceFamilyOrigin env params initial finalState.nestedAux source
  stepState : Lean4Lean.ElimNestedInductive.State
  loweredState : Lean4Lean.ElimNestedInductive.State
  lowered : LoweredInductiveTranslation env params nparams source stepState
    (target, loweredState)
  later : NestedAuxLE loweredState finalState

def FinalLoweredFamilyOrigin.mono
    (H : FinalLoweredFamilyOrigin env params nparams initial state target)
    (Haux : NestedAuxLE state nextState) :
    FinalLoweredFamilyOrigin env params nparams initial nextState target :=
  { H with
    sourceOrigin := H.sourceOrigin.mono Haux
    later := H.later.trans Haux }

theorem FinalLoweredFamilyOrigin.finalMapping
    (H : FinalLoweredFamilyOrigin env params nparams initial finalState target)
    (Hmap : NestedAuxMapModels result finalState) :
    LoweredInductiveMapping env params nparams result H.source H.stepState
      (target, H.loweredState) :=
  H.lowered.finalMapping H.later Hmap

/-- Queue provenance is split at the cursor: earlier slots already have a
lowering certificate, while current and later slots still have raw source
provenance. -/
structure LoweringQueueFamilyOrigins
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (initial : Array InductiveType) (cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  processed : ∀ j, (hj : j < state.newTypes.size) → j < cursor →
    Nonempty (FinalLoweredFamilyOrigin env params nparams initial state
      state.newTypes[j])
  pending : PendingSourceFamilyOrigins env params initial cursor state

def RestorableInductiveType (nparams : Nat) (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, RestoreTelescope ctor.type nparams

def RestorableNewTypesPrefix (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, j < i → (hj : j < state.newTypes.size) →
    RestorableInductiveType nparams state.newTypes[j]

theorem RestorableNewTypesPrefix.zero
    (state : Lean4Lean.ElimNestedInductive.State) :
    RestorableNewTypesPrefix nparams 0 state := by
  intro j hj
  omega

def NewTypeNamePresent (state : Lean4Lean.ElimNestedInductive.State)
    (name : Name) : Prop :=
  ∃ type ∈ state.newTypes.toList, type.name = name

theorem ElimNestedInductive.lowerInductive.translation
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translations params nparams
      indType.ctors env state hparams hclosures) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

theorem ElimNestedInductive.lowerInductive.translationPending
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed indType)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translationsPending params nparams
      indType.ctors env state hparams hclosures Henv Hsource Hstate) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨⟨rfl, rfl, Hctors.1⟩, Hctors.2⟩

/-- Semantic state transition for a dynamic lowering-queue iteration. -/
inductive LowerNextTranslation
    (env : Environment) (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType × Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextTranslation env params nparams i state (none, state)
  | step (hidx : i < state.newTypes.size)
      (Hlowered : LoweredInductiveTranslation env params nparams
        state.newTypes[i] state (target, loweredState)) :
      LowerNextTranslation env params nparams i state
        (some state.newTypes[i], { loweredState with
          newTypes := loweredState.newTypes.set! i target })

theorem LowerNextTranslation.restorablePrefix
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    RestorableNewTypesPrefix nparams (i + 1) nextState := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hidx).choose
    intro j hj hjNext
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hjNext
    by_cases hji : j = i
    · subst j
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[i]
      simpa [Array.getElem_setIfInBounds, hiLowered,
        RestorableInductiveType] using Hlowered.targetRestoreTelescope
    · have hjlt : j < i := by omega
      rcases Hle.getElem (show j < state.newTypes.size by omega) with
        ⟨hjInLowered, hsame⟩
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
          loweredState.newTypes[j] by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjInLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget]
      rw [hsame]
      exact Hprefix j hjlt _

theorem LowerNextTranslation.nestedAuxLE
    (H : LowerNextTranslation env params nparams i state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | done => exact .refl _
  | step _ Hlowered => exact Hlowered.nestedAuxLE

theorem LowerNextTranslation.namesWF
    (H : LowerNextTranslation env params nparams i state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered =>
    exact (Hlowered.namesWF Hstate).ofCacheCounterEq rfl rfl

theorem LowerNextTranslation.namesFresh
    (H : LowerNextTranslation env params nparams i state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered => exact (Hlowered.namesFresh Hstate).ofCacheEq rfl

theorem LowerNextTranslation.preservesTypeName
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hname : NewTypeNamePresent state name) :
    NewTypeNamePresent nextState name := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    rcases Hname with ⟨type, htype, hname⟩
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, htypeEq⟩
    have hjState : j < state.newTypes.size := by simpa using hj
    rcases Hlowered.newTypesLE.getElem hjState with
      ⟨hjLowered, hpreserved⟩
    have hjNext : j < (loweredState.newTypes.set! i target).size := by
      simpa [Array.size_set!] using hjLowered
    let finalType := (loweredState.newTypes.set! i target)[j]
    refine ⟨finalType, by
      exact List.getElem_mem hjNext, ?_⟩
    by_cases hji : j = i
    · subst j
      have hset : finalType = target := by
        simp [finalType, Array.getElem_setIfInBounds, hjLowered]
      rw [hset, Hlowered.name]
      have hsource : state.newTypes[i] = type := by
        simpa using htypeEq
      rw [hsource]
      exact hname
    · have hset : finalType = loweredState.newTypes[j] := by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget
      rw [hset, hpreserved]
      have : state.newTypes[j] = type := by simpa using htypeEq
      rw [this]
      exact hname

/-- A queue step changes only its selected slot. Auxiliary discovery may
append new families before that slot is overwritten, but every distinct
pre-existing index retains its exact family record. -/
theorem LowerNextTranslation.getElem_ne
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (hj : j < state.newTypes.size) (hne : j ≠ i) :
    ∃ hjNext : j < nextState.newTypes.size,
      nextState.newTypes[j] = state.newTypes[j] := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    rcases Hlowered.newTypesLE.getElem hj with
      ⟨hjLowered, hsame⟩
    have hjNext : j <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hjLowered
    refine ⟨hjNext, ?_⟩
    change (loweredState.newTypes.set! i target)[j] = state.newTypes[j]
    have hget := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun h : i = j => hne h.symm)] at hget
    simpa [Array.set!] using hget.trans hsame

/-- The selected queue slot contains the just-lowered target after the step,
even when lowering appended auxiliary families along the way. -/
theorem LowerNextTranslation.getElem_selected
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState)) (hi : i < state.newTypes.size) :
    ∃ target loweredState,
      LoweredInductiveTranslation env params nparams
        state.newTypes[i] state
        (target, loweredState) ∧
      nextState.nestedAux = loweredState.nestedAux ∧
      ∃ hiNext : i < nextState.newTypes.size,
        nextState.newTypes[i] = target := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have hiLowered := Hlowered.newTypesLE.getElem hi |>.choose
    have hiNext : i <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hiLowered
    refine ⟨target, loweredState, Hlowered, rfl, hiNext, ?_⟩
    change (loweredState.newTypes.set! i target)[i] = target
    simp [Array.getElem_setIfInBounds, hiLowered]

theorem LowerNextTranslation.familyOrigins
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hpending : PendingNewTypesClosed i state)
    (hclosures : MutualInductivesClosed env)
    (Horigins : LoweringQueueFamilyOrigins env params nparams initial i state) :
    LoweringQueueFamilyOrigins env params nparams initial (i + 1)
      nextState := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have Haux := Hlowered.nestedAuxLE
    have HsetAux : NestedAuxLE loweredState
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } :=
      ⟨[], by simp [NestedAuxLE]⟩
    have hiLowered := (Hle.getElem hi).choose
    have HpendingOrigins := Hlowered.pendingSourceFamilyOrigins
      hclosures (Hpending i (Nat.le_refl _) hi) Horigins.pending
    constructor
    · intro j hjNext hjProcessed
      by_cases hji : j = i
      · subst j
        rcases Horigins.pending i (Nat.le_refl _) hi with ⟨Hsource⟩
        have Hsource' := Hsource.mono Haux
        have Hfinal : FinalLoweredFamilyOrigin env params nparams initial
            { loweredState with
              newTypes := loweredState.newTypes.set! i target } target := {
          source := state.newTypes[i]
          sourceOrigin := Hsource'
          stepState := state
          loweredState := loweredState
          lowered := Hlowered
          later := HsetAux }
        exact ⟨by
          simpa [Array.getElem_setIfInBounds, hiLowered] using Hfinal⟩
      · have hjOld : j < i := by omega
        have hjState : j < state.newTypes.size := by omega
        rcases Horigins.processed j hjState hjOld with ⟨Hprocessed⟩
        rcases Hle.getElem hjState with ⟨hjLowered, hsame⟩
        have Hprocessed' := Hprocessed.mono (Haux.trans HsetAux)
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact ⟨by simpa [Array.set!, hget, hsame] using Hprocessed'⟩
    · intro j hjCursor hjNext
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hjNext
      rcases HpendingOrigins j (by omega) hjLowered with ⟨Hsource⟩
      have hji : j ≠ i := by omega
      have hget := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun h : i = j => hji h.symm)] at hget
      exact ⟨by simpa [Array.set!, hget] using Hsource⟩

theorem LowerNextTranslation.pendingNewTypesClosed
    (H : LowerNextTranslation env params nparams i state out)
    (Henv : EnvironmentTypesClosed env)
    (Hpending : PendingNewTypesClosed i state) :
    PendingNewTypesClosed (i + 1) out.2 := by
  cases H with
  | done hbound =>
    intro j hcursor hj
    exact Hpending j (by omega) hj
  | step hi Hlowered =>
    rename_i target loweredState
    have HloweredPending := Hlowered.pendingNewTypesClosed Henv
      (Hpending i (Nat.le_refl _) hi) Hpending
    intro j hcursor hj
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hj
    have hne : j ≠ i := by omega
    have hvalue := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
    change InductiveConstructorsClosed
      (loweredState.newTypes.set! i target)[j]
    rw [show (loweredState.newTypes.set! i target)[j] =
      loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
    exact HloweredPending j (by omega) hjLowered

theorem ElimNestedInductive.lowerNext.translation
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextTranslation env params nparams i state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translation params nparams
        state.newTypes[i] env state hparams hclosures) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    exact Except.WF.pure (.step hidx Htarget)
  · rw [dif_neg hidx]
    exact Except.WF.pure (.done (Nat.le_of_not_gt hidx))

theorem ElimNestedInductive.lowerNext.translationPending
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hstate : PendingNewTypesClosed i state) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out =>
        LowerNextTranslation env params nparams i state out ∧
        PendingNewTypesClosed (i + 1) out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translationPending params nparams
        state.newTypes[i] env state hparams hclosures Henv
        (Hstate i (Nat.le_refl _) hidx) Hstate) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    have HnextPending : PendingNewTypesClosed (i + 1)
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } := by
      intro j hcursor hj
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hj
      have hne : j ≠ i := by omega
      have hvalue := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
      change InductiveConstructorsClosed
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
        loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
      exact Htarget.2 j (by omega) hjLowered
    exact Except.WF.pure ⟨.step hidx Htarget.1, HnextPending⟩
  · rw [dif_neg hidx]
    exact Except.WF.pure ⟨.done (Nat.le_of_not_gt hidx),
      fun j hcursor hj => Hstate j (by omega) hj⟩

/-- Complete semantic trace of the dynamically growing lowering queue.  The
queue stops only once the index reaches the then-current array size; each
preceding step contains the semantic family translation, including any new
auxiliary families appended while processing it. -/
inductive LoweringQueueTrace
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) : Nat → Nat →
      Lean4Lean.ElimNestedInductive.State →
      Lean4Lean.ElimNestedInductive.Result ×
        Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state
        ({ state with
          nparams := params.size
          lctx
          params
          aux2nested := state.nestedAux.foldl
            (fun map (nested, name) => map.insert name nested) {}
          types := state.newTypes.toList }, state)
  | step :
      LowerNextTranslation env params nparams i state (some source, nextState) →
      LoweringQueueTrace env params nparams lctx (i + 1) fuel nextState out →
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state out

theorem LoweringQueueTrace.resultContext
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.lctx = lctx ∧ out.1.params = params := by
  induction H with
  | done => exact ⟨rfl, rfl⟩
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNParams
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.nparams = params.size := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultAuxMap
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNestedAuxLE
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | done => exact .refl _
  | step Hnext _ ih => exact Hnext.nestedAuxLE.trans ih

theorem LoweringQueueTrace.resultNamesWF
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesWF Hstate)

theorem LoweringQueueTrace.resultNamesFresh
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesFresh Hstate)

/-- Once an index lies strictly behind the queue cursor, later lowering
steps preserve the exact family stored there through to the final result. -/
theorem LoweringQueueTrace.getElem_before
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hj : j < i) (hbound : j < state.newTypes.size) :
    out.1.types[j]? = some state.newTypes[j] := by
  induction H with
  | done =>
    simp only
    rw [List.getElem?_eq_getElem (by simpa using hbound)]
    rfl
  | step Hnext Htail ih =>
    rcases Hnext.getElem_ne hbound (by omega) with
      ⟨hnextBound, hsame⟩
    simpa [hsame] using ih (by omega) hnextBound

/-- Every not-yet-processed family within the current queue has a unique
future lowering step. The theorem retains that exact semantic translation
and identifies its target at the same index in the final result list. -/
theorem LoweringQueueTrace.translationAt
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hij : i ≤ j) (hj : j < state.newTypes.size) :
    ∃ stepState target loweredState,
      LoweredInductiveTranslation env params nparams state.newTypes[j]
        stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  revert j
  induction H with
  | done hdone =>
    intro j hij hj
    omega
  | @step iStep stateStep sourceStep nextStateStep fuelStep outStep
      Hnext Htail ih =>
    intro j hij hj
    by_cases hji : j = iStep
    · subst j
      rcases Hnext.getElem_selected hj with
        ⟨target, loweredState, Htranslated, hnextAux, hiNext, htarget⟩
      refine ⟨stateStep, target, loweredState, Htranslated, ?_, ?_⟩
      have hfinal := Htail.getElem_before (j := iStep) (by omega) hiNext
      simpa [htarget] using hfinal
      rcases Htail.resultNestedAuxLE with ⟨suffix, hsuffix⟩
      exact ⟨suffix, by simpa [hnextAux] using hsuffix⟩
    · have hij' : iStep + 1 ≤ j := by omega
      rcases Hnext.getElem_ne hj hji with ⟨hjNext, hsame⟩
      rcases ih hij' hjNext with
        ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩
      rw [hsame] at Htranslated
      exact ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩

/-- Every family returned by the exhausted dynamic queue has complete
source/generated provenance and the exact lowering step that produced its
final slot. -/
theorem LoweringQueueTrace.finalFamilyOriginAt
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hpending : PendingNewTypesClosed i state)
    (Horigins : LoweringQueueFamilyOrigins env params nparams initial i state)
    (hj : j < out.1.types.length) :
    Nonempty (FinalLoweredFamilyOrigin env params nparams initial out.2
      out.1.types[j]) := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    have hjState : j < stateDone.newTypes.size := by simpa using hj
    have Hprocessed := Horigins.processed j hjState (by omega)
    simpa using Hprocessed
  | step Hnext Htail ih =>
    exact ih (Hnext.pendingNewTypesClosed Henv Hpending)
      (Hnext.familyOrigins Hpending hclosures Horigins) hj

theorem LoweringQueueTrace.resultRestorable
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    intro type htype
    simp only at htype
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, rfl⟩
    apply Hprefix j
    · have hjSize : j < stateDone.newTypes.size := by simpa using hj
      omega
  | step Hnext Htail ih =>
    exact ih (Hnext.restorablePrefix Hprefix)

theorem LoweringQueueTrace.preservesTypeName
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hname : NewTypeNamePresent state name) :
    ∃ type ∈ out.1.types, type.name = name := by
  induction H with
  | done => simpa [NewTypeNamePresent] using Hname
  | step Hnext Htail ih => exact ih (Hnext.preservesTypeName Hname)

private theorem loweringQueueLoop_refines
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translation params nparams i env state
        hparams hclosures) ?_
    intro next nextState Hnext
    cases Hnext with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure (.done hbound)
    | step hidx Hlowered =>
      exact (ih (i := i + 1) (state := _)).mono fun _ Htail =>
        LoweringQueueTrace.step (LowerNextTranslation.step hidx Hlowered) Htail

/-- The dynamic queue invariant used by auxiliary validation. Every pending
family has closed constructor types, so processing it preserves the cache
free-variable invariant and proves every newly appended family closed before
the cursor can reach it. -/
private theorem loweringQueueLoop_refinesClosed
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hpending : PendingNewTypesClosed i state)
    (Hcache : NestedAuxFVarsIn P state) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out ∧
        NestedAuxFVarsIn P out.2 := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translationPending params nparams i env
        state hparams hclosures Henv Hpending) ?_
    intro next nextState Hnext
    rcases Hnext with ⟨Htranslation, HpendingNext⟩
    cases Htranslation with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure ⟨.done hbound, Hcache⟩
    | step hidx Hlowered =>
      rename_i target loweredState
      have HcacheNext : NestedAuxFVarsIn P
          { loweredState with
            newTypes := loweredState.newTypes.set! i target } := by
        have HcacheLower := Hlowered.auxFVarsIn
          (Hpending i (Nat.le_refl _) hidx) Hparams Hcache
        intro nested name hentry
        exact HcacheLower nested name hentry
      exact (ih (i := i + 1)
        (state := { loweredState with
          newTypes := loweredState.newTypes.set! i target })
        HpendingNext HcacheNext).mono fun _ Htail =>
          ⟨LoweringQueueTrace.step (.step hidx Hlowered) Htail.1,
            Htail.2⟩

/-- End-to-end semantic certificate for nested lowering from the source
parameter telescope through the complete dynamic family queue. -/
structure NestedLoweringRun
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (out : Lean4Lean.ElimNestedInductive.Result ×
      Lean4Lean.ElimNestedInductive.State) : Prop where
  source : ∃ first rest tail paramsState lctx params,
    types = first :: rest ∧
    NestedParamOpening {} #[] first.type nparams
      lctx tail params ∧
    paramsState.newTypes = initialState.newTypes ∧
    paramsState.nestedAux = initialState.nestedAux ∧
    paramsState.nextIdx = initialState.nextIdx ∧
    paramsState.ngen.namePrefix = initialState.ngen.namePrefix ∧
    NestedBindingContextWF lctx paramsState.ngen ∧
    Nonempty (LocalForallSelection lctx params) ∧
    LoweringQueueTrace env params nparams lctx 0 fuel
      paramsState out

theorem NestedLoweringRun.resultRestorable
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultRestorable (.zero paramsState)

/-- Arbitrary final-family provenance, including dynamically appended
auxiliaries.  Unlike `translationAtInitial`, this theorem ranges over the
entire final result and identifies the queue parameters with those retained
by the restoration record. -/
theorem NestedLoweringRun.finalFamilyOriginAt
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : initialState.newTypes = types.toArray)
    (hj : j < out.1.types.length) :
    Nonempty (FinalLoweredFamilyOrigin env out.1.params nparams
      initialState.newTypes out.2 out.1.types[j]) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      hnewTypes, _hnestedAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have Horigins : LoweringQueueFamilyOrigins env params nparams
      initialState.newTypes 0 paramsState := by
    constructor
    · intro j _hj hjProcessed
      omega
    · intro j _hjCursor hjState
      have hjInitial : j < initialState.newTypes.size := by
        simpa [hnewTypes] using hjState
      have Horigin : SourceFamilyOrigin env params initialState.newTypes
          paramsState.nestedAux initialState.newTypes[j] :=
        .original j hjInitial
      exact ⟨by simpa [hnewTypes] using Horigin⟩
  have Hpending : PendingNewTypesClosed 0 paramsState := by
    intro j _hj hjState
    have hjInitial : j < initialState.newTypes.size := by
      simpa [hnewTypes] using hjState
    have hmember : initialState.newTypes[j] ∈ types := by
      have hmemInitial : initialState.newTypes[j] ∈ initialState.newTypes :=
        Array.getElem_mem hjInitial
      simpa [hinitial] using hmemInitial
    have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hnewTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hjState, hjInitial] using heq
    rw [hvalue]
    exact Hsources.constructorsClosed hmember
  have Hfinal := Hqueue.finalFamilyOriginAt Henv hclosures Hpending Horigins hj
  rw [Hqueue.resultContext.2]
  exact Hfinal

theorem NestedLoweringRun.resultNParams
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.nparams = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultNParams.trans Hopening.initial_size

theorem NestedLoweringRun.resultParamsSize
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.size = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, _, Hqueue⟩
  rw [Hqueue.resultContext.2]
  exact Hopening.initial_size

/-- The final restoration context is exactly the source parameter selection
opened before the dynamic lowering queue starts. -/
theorem NestedLoweringRun.resultContextSelection
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    Nonempty (LocalForallSelection out.1.lctx out.1.params) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _,
      _hprefix, _Hctx, Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hselection

theorem NestedLoweringRun.resultContextWF
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.lctx.WF := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _hprefix, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.wf

/-- Every restoration-context free variable was allocated by nested
lowering's own generator, whose prefix is disjoint from the type checker's
private generator. -/
theorem NestedLoweringRun.resultContextKernelFresh
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hprefix : initialState.ngen.namePrefix = `_nested_fresh) :
    ∀ fv ∈ out.1.lctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, hparamsPrefix, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.kernelFreshOfPrefix (hparamsPrefix.trans hprefix)

/-- Lowering stores common parameters in source binder order, whereas its
local context (and therefore every `MLCtx.vlctx`) stores free variables in
most-recent-first order. -/
theorem NestedLoweringRun.resultParams_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.toList.reverse = out.1.lctx.fvars.map Expr.fvar := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hopening.toRestoreParamOpening.root_params_reverse_fvars

/-- Any retained selection of the final parameter array lists exactly the
same free variables as the returned local context, in binder order rather
than the context's most-recent-first order. -/
theorem NestedLoweringRun.resultSelection_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (selection : LocalForallSelection out.1.lctx out.1.params) :
    selection.fvars.reverse = out.1.lctx.fvars := by
  have hparams := H.resultParams_reverse_fvars
  have hselected : out.1.params.toList =
      selection.fvars.map Expr.fvar := by
    calc
      out.1.params.toList =
          (selection.fvars.map Expr.fvar).toArray.toList :=
        congrArg Array.toList selection.expressions
      _ = selection.fvars.map Expr.fvar := by simp
  rw [hselected, ← List.map_reverse] at hparams
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hparams

/-- The executable auxiliary checks can be closed over lowering's retained
parameter telescope.  This removes the concrete free-variable names from the
semantic certificate before restoration reopens the same telescope with its
own fresh names. -/
theorem NestedLoweringRun.closeValidatedNestedAuxiliaries
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ClosedValidatedNestedAuxiliaries venv lparams res := by
  have hfull : mlctx.fvarRevList mlctx.length (Nat.le_refl _) =
      mlctx.vlctx.fvars := mlctx.fvarRevList_all
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [hfull, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  intro name e hfind
  rcases Hvalidated name e hfind with
    ⟨ty, e', ty', ⟨_hfvars, Hexpr, _Htype, _Htyping⟩, HisType⟩
  have Hclosed := hmlctx.mkForall_trS henv Hexpr HisType
    mlctx.length (Nat.le_refl _)
  rw [mlctx.dropN_all] at Hclosed
  have hconcrete : res.lctx.mkForall res.params e =
      mlctx.mkForall mlctx.length (Nat.le_refl _) e := by
    rw [← hlctx]
    exact hmlctx.mkForall_eq mlctx.length (Nat.le_refl _) hparams
  refine ⟨mlctx.mkForall' mlctx.length (Nat.le_refl _) e', ?_⟩
  rw [hconcrete]
  exact Hclosed

/-- The complete evidence available for a generated family at the validation
boundary.  In particular, this retains the inferred type translated by
`checkType`; `closeValidatedNestedAuxiliaries` intentionally forgets that
target after deriving typehood of the cached family application.  Header
alignment can use the built-family equation and this typing witness together
to identify the materialized post-parameter tail. -/
theorem GeneratedFamilyWitness.validatedHeader
    (H : GeneratedFamilyWitness sourceEnv params finalState.nestedAux family)
    (Hmap : NestedAuxMapModels result finalState)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams vlctx result) :
    ∃ sourceTail inferredSource familyTarget inferredTarget,
      Expr.ForallTelescope
        (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
          H.levels)
        H.nestedNParams sourceTail ∧
      H.data.type.type = H.lctx.mkForall H.As
        (sourceTail.instantiateRevRange 0 H.nestedNParams H.args) ∧
      TrTyping venv lparams vlctx H.data.nested inferredSource familyTarget
        inferredTarget ∧
      venv.IsType lparams.length vlctx.toCtx familyTarget := by
  rcases H.built.opening with ⟨sourceTail, Hsource, htype⟩
  have hfind : result.aux2nested.find? H.auxName = some H.data.nested :=
    Hmap _ _ H.cached
  rcases Hvalidated H.auxName H.data.nested hfind with
    ⟨inferredSource, familyTarget, inferredTarget, Htyping, HisType⟩
  exact ⟨sourceTail, inferredSource, familyTarget, inferredTarget,
    Hsource, htype, Htyping, HisType⟩

/-- Fully name-independent auxiliary semantics retained after validation:
the lowering-selected production variables are abstracted into the canonical
de-Bruijn parameter context before restoration is inspected. -/
theorem NestedLoweringRun.validatedAuxiliaryResidualTranslations
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ∃ selection : LocalForallSelection res.lctx res.params,
      ClosedNestedAuxiliaryTranslations venv lparams res selection := by
  rcases H.resultContextSelection with ⟨selection⟩
  exact ⟨selection,
    (H.closeValidatedNestedAuxiliaries henv mlctx hmlctx hlctx Hvalidated
      ).residualTranslations henv selection⟩

theorem NestedLoweringRun.resultParamsFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ e ∈ out.1.params, e.FVarsIn (· ∈ out.1.lctx.fvars) := by
  rcases H.resultContextSelection with ⟨Hselection⟩
  exact Hselection.fvarsIn H.resultContextWF

theorem NestedLoweringRun.resultAuxMap
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultAuxMap

theorem NestedLoweringRun.resultAuxFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hcache : NestedAuxFVarsIn P out.2) :
    NestedAuxMapFVarsIn P
      (show Std.TreeMap Name Expr Name.quickCmp from out.1.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapFVarsIn P
    (out.2.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_fvarsIn out.2.nestedAux.toList
  · intro entry hentry
    exact Hcache entry.1 entry.2 (by simpa using hentry)
  · unfold NestedAuxMapFVarsIn
    intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesReserved
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesWF finalState) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesReserved
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesReserved finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames.reserved entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesFresh env finalState) :
    NestedAuxMapNamesFresh env
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesFresh env
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesFresh finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.validateNestedAuxiliariesWF
    (H : NestedLoweringRun sourceEnv loweringFuel nparams sourceTypes
      initialState (res, finalState))
    (hvalid : CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (Hcache : NestedAuxFVarsIn (· ∈ mlctx.vlctx.fvars) finalState) :
    (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
      res).WF fun _ =>
        ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  apply validateNestedAuxiliaries.WF hvalid mlctx hmlctx hlctx hfresh
  intro name nested hfind
  exact H.resultAuxFVarsIn Hcache name nested hfind

/-- Under the separately stated fresh-name invariant, every final cache entry
is retrieved exactly by the production `aux2nested` map. -/
theorem NestedLoweringRun.resultAuxLookup
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ finalState.nestedAux) :
    result.aux2nested.find? name = some nested := by
  rw [H.resultAuxMap]
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[name]? = some nested
  rw [← Array.foldl_toList]
  exact nestedAuxFold_find finalState.nestedAux.toList {} hnodup
    (by simpa using hentry)

theorem NestedLoweringRun.resultAuxMapModels
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup) :
    NestedAuxMapModels result finalState := by
  intro nested name hentry
  exact H.resultAuxLookup hnodup hentry

theorem NestedLoweringRun.resultNestedAuxLE
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    NestedAuxLE initialState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _hnewTypes,
      hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultNestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hinitialAux] using hsuffix⟩

theorem NestedLoweringRun.resultNamesWF
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesWF initialState) : NestedAuxNamesWF out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesWF
    (Hstate.ofCacheCounterEq hinitialAux hinitialNext)

theorem NestedLoweringRun.resultNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesFresh env initialState) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesFresh (Hstate.ofCacheEq hinitialAux)

theorem NestedLoweringRun.resultFamilyNamesFreshOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hwf : env.constants.WF)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxFamiliesFresh result env := by
  have Hnames := H.resultNamesFresh
    (NestedAuxNamesFresh.empty env initialState hempty)
  have Hmap := H.resultAuxNamesFresh Hnames
  intro name nested hfind
  exact find?_none_of_contains_false hwf (Hmap name nested hfind)


theorem NestedLoweringRun.resultNamesNodupOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hempty : initialState.nestedAux = #[]) :
    (out.2.nestedAux.toList.map Prod.snd).Nodup :=
  (H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty)).nodup

theorem NestedLoweringRun.resultFamilyNamesReservedOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultAuxNamesReserved
    (H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty))

theorem NestedLoweringRun.resultFamilyNamesReservedFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultFamilyNamesReservedOfEmpty hempty

theorem NestedLoweringRun.resultAuxMapModelsOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModels (H.resultNamesNodupOfEmpty hempty)

theorem NestedLoweringRun.resultAuxMapModelsFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModelsOfEmpty hempty

/-- Positional lowering witness for any family present in the initial queue.
Unlike name preservation, this exposes the complete constructor-expression
translation performed at that family's actual dynamic queue step. -/
theorem NestedLoweringRun.translationAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveTranslation env params nparams
        initialState.newTypes[j] stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Haux⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hopening.initial_size, Htranslated, htarget, Haux⟩

/-- Once final cache-name uniqueness is supplied, every initially declared
family has a positional lowering certificate whose constructor bodies are
all interpreted by the actual final restoration map. -/
theorem NestedLoweringRun.finalMappingAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.translationAtInitial hj with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Hlater⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

/-- Parameter-aligned form of `finalMappingAtInitial`.  The expression
mapping for each source family is performed with exactly the parameter array
stored in the final restoration record, rather than merely with an array of
the same size.  This identity is what later lets restoration cancel the
abstraction performed when a nested application was cached. -/
theorem NestedLoweringRun.finalMappingAtInitialAligned
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Hlater⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hqueue.resultContext.2, Hopening.initial_size,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

theorem NestedLoweringRun.preservesInitialTypeName
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hname : NewTypeNamePresent initialState name) :
    ∃ type ∈ out.1.types, type.name = name := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, hnewTypes,
      _hnewAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  apply Hqueue.preservesTypeName
  unfold NewTypeNamePresent at Hname ⊢
  rwa [hnewTypes]

theorem ElimNestedInductive.run.translation
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => NestedLoweringRun env fuel nparams types state out := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesSelected
    intro lctx tail params paramsState Hopening Hctx Hselection _hnodup hnewTypes
      hnestedAux hnextIdx hprefix
    have hparams : params.size = nparams := Hopening.initial_size
    exact (loweringQueueLoop_refines env params nparams lctx 0 fuel paramsState
      hparams hclosures).mono fun _ Hqueue =>
        ⟨⟨first, rest, tail, paramsState, lctx, params,
          rfl, Hopening, hnewTypes, hnestedAux, hnextIdx, hprefix, Hctx,
          ⟨Hselection⟩, Hqueue⟩⟩

/-- The final restoration parameter array is an ordered array of distinct
free variables. -/
def NestedResultParamsNodup
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ fvars : List FVarId,
    result.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup

/-- End-to-end queue safety from the executable source checks.  This closes
the dynamic-generation loop: source constructors are closed, every generated
auxiliary constructor is re-closed over the verified parameter context, and
therefore every final cache witness is open only over the retained result
context. -/
theorem ElimNestedInductive.run.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out =>
        NestedLoweringRun env fuel nparams types state out ∧
        NestedAuxFVarsIn (· ∈ out.1.lctx.fvars) out.2 ∧
        NestedResultParamsNodup out.1 := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesClosing
      (Htype := Hsources.typeClosed (by simp))
    intro lctx tail params paramsState Hopening Hclosing Htail hnewTypes
      hnestedAux hnextIdx hprefix
    have hparams : params.size = nparams := Hopening.initial_size
    have Hparams : ∀ param ∈ params,
        param.FVarsIn (· ∈ lctx.fvars) :=
      Hclosing.selection.fvarsIn Hclosing.binding.wf
    have Hpending : PendingNewTypesClosed 0 paramsState := by
      intro j _hj hj
      have hjState : j < state.newTypes.size := by
        simpa [hnewTypes] using hj
      have hvalue : paramsState.newTypes[j] = state.newTypes[j] := by
        have heq := congrArg
          (fun xs : Array InductiveType => xs[j]!) hnewTypes
        simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
      rw [hvalue]
      have hmember : state.newTypes[j] ∈ first :: rest := by
        have hmemState : state.newTypes[j] ∈ state.newTypes :=
          Array.getElem_mem hjState
        simpa [hinitial] using hmemState
      exact Hsources.constructorsClosed hmember
    have Hcache : NestedAuxFVarsIn (· ∈ lctx.fvars) paramsState := by
      intro nested name hentry
      rw [hnestedAux, hempty] at hentry
      simp at hentry
    exact (loweringQueueLoop_refinesClosed env params nparams lctx 0 fuel
      paramsState hparams hclosures Henv Hparams Hpending Hcache).mono
        fun _ Hqueue => by
          refine ⟨⟨⟨first, rest, tail, paramsState, lctx, params,
            rfl, Hopening, hnewTypes, hnestedAux, hnextIdx,
            hprefix, Hclosing.binding, ⟨Hclosing.selection⟩, Hqueue.1⟩⟩, ?_, ?_⟩
          · rw [Hqueue.1.resultContext.1]
            exact Hqueue.2
          · exact ⟨Hclosing.selection.fvars,
              Hqueue.1.resultContext.2.trans Hclosing.selection.expressions,
              Hclosing.nodup⟩

/-- Exact state transition for one iteration of the dynamic lowering queue.
The successful case retains the source family selected before lowering, while
allowing `lowerInductive` to append freshly discovered auxiliary families
before the selected slot is overwritten. -/
inductive LowerNextResult (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType → Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextResult params nparams i state none state
  | step {target : InductiveType}
      {loweredState : Lean4Lean.ElimNestedInductive.State}
      (hidx : i < state.newTypes.size)
      (shape : LoweredInductiveShape nparams state.newTypes[i] target) :
      LowerNextResult params nparams i state (some state.newTypes[i])
        { loweredState with
          newTypes := loweredState.newTypes.set! i target }

theorem ElimNestedInductive.lowerNext.refines
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextResult params nparams i state out.1 out.2 := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.lowerNext at hout
  simp only [get, bind, StateT.bind, ReaderT.bind, pure] at hout
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M
        Lean4Lean.ElimNestedInductive.State) env state) =
      Except.ok (state, state) := rfl
  rw [hget] at hout
  simp only [Except.bind] at hout
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx] at hout
    change ((Lean4Lean.ElimNestedInductive.lowerInductive
      params nparams state.newTypes[i] env state).bind fun lowered =>
        Except.ok (some state.newTypes[i],
          { lowered.2 with
            newTypes := lowered.2.newTypes.set! i lowered.1 })) =
      Except.ok out at hout
    cases hlower : Lean4Lean.ElimNestedInductive.lowerInductive
        params nparams state.newTypes[i] env state with
    | error err =>
      rw [hlower] at hout
      contradiction
    | ok lowered =>
      rw [hlower] at hout
      simp at hout
      cases hout
      exact .step hidx
        (ElimNestedInductive.lowerInductive.shape
          params nparams state.newTypes[i] env state lowered hlower)
  · rw [dif_neg hidx] at hout
    cases hout
    exact .done (Nat.le_of_not_gt hidx)

/-- The first branch of nested lowering rejects an empty source block. This
is the operational origin of the nonemptiness premise later used to recover
`SourceWF` from `TrInductDeclCore`. -/
theorem ElimNestedInductive.run.source_nonempty
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun _ => types ≠ [] := by
  intro out hout
  cases types with
  | nil =>
    change Except.error _ = Except.ok out at hout
    contradiction
  | cons type types =>
    simp

/-- A successful lowering run carries the exact common-parameter opening of
the first source header into the restoration data returned in `Result`. -/
theorem ElimNestedInductive.run.parameterOpening
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => ∃ first rest tail,
        types = first :: rest ∧
        NestedParamOpening {} #[] first.type nparams
          out.1.lctx tail out.1.params ∧
        out.1.nparams = nparams := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refines
    intro lctx tail params outState Hopening
    have loopWF : ∀ remaining i currentState,
        (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i
          remaining env currentState).WF fun out => ∃ first' rest' tail',
            first :: rest = first' :: rest' ∧
            NestedParamOpening {} #[] first'.type nparams
              out.1.lctx tail' out.1.params ∧
            out.1.nparams = nparams := by
      intro remaining
      induction remaining with
      | zero => intro i currentState; exact Except.WF.throw
      | succ remaining ih =>
        intro i currentState
        simp only [Lean4Lean.ElimNestedInductive.run.loop]
        exact (ElimNestedInductive.lowerNext.refines
          params nparams i env currentState).bind fun next Hnext => by
            rcases next with ⟨next, nextState⟩
            cases Hnext with
            | done hbound =>
              exact Except.WF.pure ⟨first, rest, tail, rfl, Hopening,
                Hopening.initial_size⟩
            | step hidx Hshape =>
              exact ih (i + 1) _
    exact loopWF fuel 0 outState


end VerifyInductive
end Lean4Lean
