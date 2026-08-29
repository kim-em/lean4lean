import Lean4Lean.Verify.Inductive.Constructor.Positivity

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace isRecArg.loop

/-- The recursive-argument classifier used by recursor generation retains
the exact mutual-family target whenever it returns a family index. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg.loop stats type fuel c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget Hc.venv decl.uvars
          (decl.types[target]'htarget).name
          Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero =>
    intro _ h
    simp [AddInductive.isRecArg.loop] at h
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    rw [AddInductive.isRecArg.loop]
    refine (whnfInContext.WF Hc hsource).bind fun normalized hnormalized => ?_
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
        refine withLocalDecl.WF (name := name) (bi := bi)
          (Q := fun result => ∀ target, result = some target →
            ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget Hc.venv decl.uvars
              (decl.types[target]'htarget).name
              Hc.mlctx.vlctx.toCtx depth type')
          Hc Hdom.consumed Hdom.isType ?_
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hopened := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.consumed Hdom.isType hbody''
        have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
          Hc Hdom.consumed Hdom.isType
        have hctx' : checkPositivityStep.VLCtx.NoIndConsts
            (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
          apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
          rfl
        have Hrec := ih Hc' Hstats' hlit hctx'
          (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
        exact Hrec.mono fun result hrec target htarget => by
          rcases hrec target htarget with ⟨htarget, hrecursive⟩
          rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
          rcases hbodyEq with ⟨bodyType, hbodyEq⟩
          exact ⟨htarget, .forallE
            (by simpa [Hstats.uvars] using hsourceExposed)
            (by simpa [Hstats.uvars] using hdomEq)
            (by simpa [Hstats.uvars] using hbodyEq)
            hrecursive⟩
    · cases normalized <;> try { simp at hforall }
      all_goals
        change (Except.ok (AddInductive.isValidIndApp? stats _)).WF _
        exact Except.WF.pure fun target hvalid => by
          rcases checkPositivityStep.isValidIndApp?_some hvalid with
            ⟨htargetLt, hvalidIdx⟩
          have htargetDecl : target < decl.types.length := by
            rw [← Hstats.types_size]
            exact htargetLt
          refine ⟨htargetDecl, .direct
            (by simpa [Hstats.uvars] using hsourceExposed)
            (checkPositivityStep.isValidIndAppIdx.validIndAppAt Hstats
              htargetDecl hexposed hvalidIdx (Or.inr rfl) hlit hctx)⟩

end isRecArg.loop

theorem isRecArg.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg stats type c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget Hc.venv decl.uvars
          (decl.types[target]'htarget).name
          Hc.mlctx.vlctx.toCtx depth type') := by
  unfold AddInductive.isRecArg
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF
      (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact isRecArg.loop.refines Hc Hstats hconsume hlit hctx htype

namespace mkRecInfos.loopCtorArgs.loop

/-- Independently of typing, the recursive-argument array accumulated by
recursor generation is an ordered sublist of the complete field array. This
is the executable source of `IotaRule.fieldPositions_ordered`. -/
theorem selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (hselected : u.toList.Sublist bu.toList)
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih hselected
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotationsVerified
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotationsVerified bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        cases selected with
        | none =>
          apply ih
          simpa using hselected.trans
            (List.sublist_append_left bu.toList [.fvar ⟨c.ngen.curr⟩])
        | some target =>
          apply ih
          simpa using hselected.append_right [.fvar ⟨c.ngen.curr⟩]
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ hselected

end mkRecInfos.loopCtorArgs.loop

/-- Public structural invariant for constructor argument classification. -/
theorem mkRecInfos.loopCtorArgs.selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.selectedSublist stats k .slnil Hk

namespace mkRecRules.loopCtors

/-- The complete named constructor recursion emits one exact source rule per
input constructor, preserves order, and advances the flattened minor ordinal
once per rule. -/
theorem generatedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule)
    (start : Nat) (c : AddInductive.Context) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          checkPositivityStep.GeneratedRecursorRules indTypes stats motives minors lvls
            ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start c with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      refine ⟨[], ?_, .nil, by simp⟩
      simp
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecRules.loopCtors]
      have hone :
          ((fun minorIdx => AddInductive.mkRecInfos.loopCtorArgs stats
            ctor.type fun _ bu u =>
              AddInductive.mkRecRules.loopU indTypes stats motives minors
                lvls u 0 #[] fun v => do
                  let lctx ← getLCtx
                  let rule := {
                    ctor := ctor.name
                    nfields := bu.size
                    rhs := lctx.mkLambda stats.params <|
                      lctx.mkLambda motives <| lctx.mkLambda minors <|
                      lctx.mkLambda bu <|
                      mkAppN (mkAppN minors[minorIdx]! bu) v }
                  return (rule, minorIdx + 1)) start c).WF fun out =>
            checkPositivityStep.GeneratedRecursorRule indTypes stats motives minors lvls
              ctor start out.1 ∧ out.2 = start + 1 := by
        apply mkRecInfos.loopCtorArgs.selectedSublist stats
        intro _ bu u c' hselected
        apply checkPositivityStep.mkRecRules.loopU.generatedCallsFromEmpty
        intro v c'' Hcalls
        exact Except.WF.pure ⟨⟨bu, u, v, c''.lctx, hselected,
          Hcalls, rfl, rfl, rfl⟩, rfl⟩
      exact hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, hnext⟩
        have htail := ih (acc := acc.push out.1)
          (start := out.2) (c := c)
        exact htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, .cons Hrule ?_, ?_⟩
          · simpa [hout]
          · simpa [hnext] using Hgenerated
          · simp at hend ⊢
            omega

end mkRecRules.loopCtors

/-- Public rule-generator boundary: starting with an empty accumulator returns
exactly the ordered rules certified for the selected mutual-family member. -/
theorem mkRecRules.generatedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    (c : AddInductive.Context) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        checkPositivityStep.GeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.generatedRules indTypes stats motives minors
    (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start c
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- Bridge from one verified executable family batch to the flattened
abstract iota accumulator. All traversal and indexing facts are discharged
here; the sole pointwise premise is the semantic translation of each exact
generated source rule into the independent `IotaRule` judgment. -/
theorem IotaBuildCertificate.appendGeneratedRules
    (Hbuild : IotaBuildCertificate env decl block prior)
    (Hgenerated : checkPositivityStep.GeneratedRecursorRules
      indTypes stats motives minors lvls ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (hsemantic : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length),
      checkPositivityStep.GeneratedRecursorRule indTypes stats motives minors
        lvls ctors[i] (start + i) sourceRules[i] →
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate env decl block (prior ++ abstractRules) := by
  apply Hbuild.append hroom
  intro i habstract
  have hsource : i < sourceRules.length := by omega
  have hctor : i < ctors.length := by
    rw [← Hgenerated.length]
    exact hsource
  exact hsemantic i hctor hsource habstract
    (Hgenerated.entry i hctor hsource)

/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursorRecursiveDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env decl.uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursorFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursorRecursiveDomain env decl) → Prop
  | nil : RecursorFieldSelections env decl #[] #[] []
  | nonrecursive : RecursorFieldSelections env decl bu u fields →
      RecursorFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursorFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursorFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursorFieldSelections.map
    (H : RecursorFieldSelections env decl bu u fields)
    (f : Expr → Expr) :
    RecursorFieldSelections env decl (bu.map f) (u.map f) fields := by
  induction H with
  | nil =>
    rw [Array.map_empty]
    exact .nil
  | @nonrecursive bu u fields arg _ ih =>
    rw [Array.map_push]
    exact RecursorFieldSelections.nonrecursive (arg := f arg) ih
  | @recursive bu u fields arg cert _ hindex ih =>
    rw [Array.map_push, Array.map_push]
    apply RecursorFieldSelections.recursive (arg := f arg) (cert := cert) ih
    simpa using hindex

theorem RecursorFieldSelections.selectedSublist
    (H : RecursorFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]

theorem RecursorFieldSelections.fields_length
    (H : RecursorFieldSelections env decl bu u fields) :
    fields.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldSelections.positions_lt
    (H : RecursorFieldSelections env decl bu u fields) :
    ∀ cert ∈ fields, cert.fieldIndex < bu.size := by
  induction H with
  | nil => simp
  | @nonrecursive bu u fields arg _ ih =>
    intro cert hmem
    have := ih cert hmem
    simp only [Array.size_push]
    omega
  | @recursive bu u fields arg cert _ hindex ih =>
    intro old hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · have := ih old hmem
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push, hindex]
      omega

theorem RecursorFieldSelections.positions_ordered
    (H : RecursorFieldSelections env decl bu u fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ ih => exact ih
  | @recursive bu u fields arg cert H hindex ih =>
    simp only [List.map_append, List.map_singleton]
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    rw [hindex]
    rcases List.mem_map.mp hold with ⟨oldCert, hmem, rfl⟩
    exact H.positions_lt oldCert hmem

/-- The selected recursive array and its proof-side certificates remain
pointwise aligned with the final all-fields array. In particular, the
recorded field ordinal selects the very concrete argument paired with that
certificate, even after later fields extend `bu`. -/
theorem RecursorFieldSelections.arguments_at_positions
    (H : RecursorFieldSelections env decl bu u fields) :
    List.Forall₂ (fun cert arg =>
      ∃ h : cert.fieldIndex < bu.size, arg = bu[cert.fieldIndex]'h)
      fields u.toList := by
  induction H with
  | nil => exact .nil
  | @nonrecursive bu u fields arg H ih =>
      have lift : List.Forall₂ (fun cert selected =>
          ∃ h : cert.fieldIndex < (bu.push arg).size,
            selected = (bu.push arg)[cert.fieldIndex]'h)
          fields u.toList := by
        apply List.Forall₂.imp (R := fun cert selected =>
          ∃ h : cert.fieldIndex < bu.size,
            selected = bu[cert.fieldIndex]'h) (fun cert selected hhead => ?_) ih
        rcases hhead with ⟨hpos, heq⟩
        refine ⟨by simp; omega, ?_⟩
        rw [heq]
        exact (Array.getElem_push_lt hpos).symm
      exact lift
  | @recursive bu u fields arg cert H hindex ih =>
      have lift : List.Forall₂ (fun old selected =>
          ∃ h : old.fieldIndex < (bu.push arg).size,
            selected = (bu.push arg)[old.fieldIndex]'h)
          fields u.toList := by
        apply List.Forall₂.imp (R := fun old selected =>
          ∃ h : old.fieldIndex < bu.size,
            selected = bu[old.fieldIndex]'h) (fun old selected hhead => ?_) ih
        rcases hhead with ⟨hpos, heq⟩
        refine ⟨by simp; omega, ?_⟩
        rw [heq]
        exact (Array.getElem_push_lt hpos).symm
      rw [Array.toList_push]
      apply checkPositivityStep.forall₂_append lift
      apply List.Forall₂.cons
      · refine ⟨by simp [hindex], ?_⟩
        simpa [hindex] using (@Array.getElem_push_eq Expr bu arg).symm
      · exact .nil

/-- Selecting recursive fields from an array whose entries have all been
translated determines a pointwise translation of the selected array.  This
is purely the executable left-to-right selection trace: no semantic
uniqueness premise is needed because the target at a recursive step is the
same target already paired with the newly appended all-field argument. -/
theorem RecursorFieldSelections.translations_of_all
    (H : RecursorFieldSelections env decl bu u fields)
    (Hall : List.Forall₂ R bu.toList allArgs) :
    ∃ recursiveArgs, List.Forall₂ R u.toList recursiveArgs := by
  induction H generalizing allArgs with
  | nil =>
      exact ⟨[], .nil⟩
  | @nonrecursive bu u fields arg H ih =>
      rw [Array.toList_push] at Hall
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hall with
        ⟨allPrefix, _translatedArg, _hall, HallPrefix, _Harg⟩
      exact ih HallPrefix
  | @recursive bu u fields arg cert H hindex ih =>
      rw [Array.toList_push] at Hall
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hall with
        ⟨allPrefix, translatedArg, _hall, HallPrefix, Harg⟩
      rcases ih HallPrefix with ⟨recursivePrefix, HrecursivePrefix⟩
      refine ⟨recursivePrefix ++ [translatedArg], ?_⟩
      rw [Array.toList_push]
      exact checkPositivityStep.forall₂_append HrecursivePrefix
        (.cons Harg .nil)

/-- Translation preserves the selector's ordered-sublist invariant. The only
potential ambiguity is translating the same selected source field along the
`bu` and `u` arrays; `IsUnique` resolves exactly that equality. -/
theorem RecursorFieldSelections.translatedSublist
    (H : RecursorFieldSelections semanticEnv decl bu u fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    recursiveArgs.Sublist allArgs := by
  induction H generalizing allArgs recursiveArgs with
  | nil =>
      cases Hbu
      cases Hu
      exact .slnil
  | @nonrecursive bu u fields arg H ih =>
      rw [Array.toList_push] at Hbu
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hbu with
        ⟨allPrefix, translatedArg, rfl,
        HbuPrefix, _⟩
      have Hsub := ih HbuPrefix Hu Hunique
      exact Hsub.trans (List.sublist_append_left allPrefix [translatedArg])
  | @recursive bu u fields arg cert H hindex ih =>
      rw [Array.toList_push] at Hbu Hu
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hbu with
        ⟨allPrefix, translatedArg, rfl,
        HbuPrefix, HargAll⟩
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hu with
        ⟨recursivePrefix, recursiveArg, rfl,
        HuPrefix, HargRec⟩
      have HuniquePrefix : ∀ old ∈ u.toList,
          TrExprS.IsUnique old := by
        intro old hold
        exact Hunique old (by simp [hold])
      have Hsub := ih HbuPrefix HuPrefix HuniquePrefix
      have hargUnique : TrExprS.IsUnique arg :=
        Hunique arg (by simp)
      have heq : recursiveArg = translatedArg :=
        TrExprS.unique hargUnique HargRec HargAll
      subst recursiveArg
      exact Hsub.append_right [translatedArg]

def RecursorRecursiveDomain.toRecursiveField
    (cert : RecursorRecursiveDomain env decl) (arg : VExpr) :
    decl.RecursiveField env where
  fieldIndex := cert.fieldIndex
  arg := arg
  ctx := cert.ctx
  depth := cert.depth
  domain := cert.domain
  recursive := cert.recursive.forgetTarget.toRecursiveArg

/-- Zips the proof-side domain certificates with their final translated field
arguments to obtain the public `RecursiveField` witnesses used by iota rules. -/
inductive RecursorFieldsMaterialize (env : VEnv) (decl : VInductDecl) :
    List (RecursorRecursiveDomain env decl) → List VExpr →
      List (decl.RecursiveField env) → Prop
  | nil : RecursorFieldsMaterialize env decl [] [] []
  | cons : RecursorFieldsMaterialize env decl certs args fields →
      RecursorFieldsMaterialize env decl (cert :: certs) (arg :: args)
        (cert.toRecursiveField arg :: fields)

theorem RecursorFieldsMaterialize.exists_of_length
    (h : certs.length = args.length) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  induction certs generalizing args with
  | nil =>
    cases args <;> simp_all
    exact ⟨[], .nil⟩
  | cons cert certs ih =>
    cases args with
    | nil => simp at h
    | cons arg args =>
      have h' : certs.length = args.length := by
        simpa using Nat.succ.inj h
      rcases ih h' with ⟨fields, hfields⟩
      exact ⟨_, .cons hfields⟩

theorem RecursorFieldsMaterialize.args
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)}
    {translated : List VExpr} {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.arg) = translated := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldsMaterialize.positions
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.fieldIndex) = certs.map (·.fieldIndex) := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldSelections.exists_materialization
    (H : RecursorFieldSelections env decl bu u certs)
    (hargs : List.Forall₂ R u.toList args) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  apply RecursorFieldsMaterialize.exists_of_length
  rw [H.fields_length]
  have hlen := checkPositivityStep.forall₂_length_eq hargs
  simpa using hlen

theorem RecursorFieldsMaterialize.positions_ordered
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  rw [Hmat.positions]
  exact Hsel.positions_ordered

theorem RecursorFieldsMaterialize.positions_lt
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    ∀ field ∈ fields, field.fieldIndex < bu.size := by
  intro field hmem
  have hpos : field.fieldIndex ∈ fields.map (·.fieldIndex) := by
    exact List.mem_map.mpr ⟨field, hmem, rfl⟩
  rw [Hmat.positions] at hpos
  rcases List.mem_map.mp hpos with ⟨cert, hcert, heq⟩
  rw [← heq]
  exact Hsel.positions_lt cert hcert

/-- Materialized recursive fields select the corresponding translated
constructor argument at their certified ordinal. This discharges the
`IotaRule.fields_at_positions` obligation from the executable selection
trace; uniqueness is needed only for the selected source field expression. -/
theorem RecursorFieldsMaterialize.fields_at_positions
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs allArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    ∀ field ∈ fields,
      ∃ h : field.fieldIndex < allArgs.length,
        field.arg = allArgs[field.fieldIndex]'h := by
  intro field hfield
  rcases List.mem_iff_getElem.mp hfield with ⟨j, hj, rfl⟩
  have hfieldsArgs : fields.length = recursiveArgs.length := by
    have := congrArg List.length Hmat.args
    simpa using this
  have hcertFields : certs.length = fields.length := by
    have := congrArg List.length Hmat.positions
    simpa using this.symm
  have hjCert : j < certs.length := by omega
  have hjRec : j < recursiveArgs.length := by omega
  have hjU : j < u.toList.length := by
    simpa only [Array.length_toList, ← Hsel.fields_length, hcertFields] using hj
  have Halign := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hsel.arguments_at_positions j hjCert hjU
  rcases Halign with ⟨hpos, hsource⟩
  have hposAll : certs[j].fieldIndex < allArgs.length := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hbu
    have hp : certs[j].fieldIndex < bu.toList.length := by
      simpa using hpos
    omega
  have hposEq : fields[j].fieldIndex = certs[j].fieldIndex := by
    have h := congrArg (fun xs => xs[j]?) Hmat.positions
    simpa [hj, hjCert] using h
  have hargEq : fields[j].arg = recursiveArgs[j] := by
    have h := congrArg (fun xs => xs[j]?) Hmat.args
    simpa [hj, hjRec] using h
  refine ⟨hposEq.symm ▸ hposAll, ?_⟩
  rw [hargEq]
  have Hrec := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hu j hjU hjRec
  have Hfield := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hbu certs[j].fieldIndex (by simpa using hpos) hposAll
  have hsourceList : u.toList[j] = bu.toList[certs[j].fieldIndex] := by
    simpa using hsource
  have Hfield' : TrExprS trEnv Us Δ u.toList[j]
      allArgs[certs[j].fieldIndex] := by
    rw [hsourceList]
    exact Hfield
  have heq := TrExprS.unique (Hunique u.toList[j]
    (List.getElem_mem hjU)) Hrec Hfield'
  simpa [hposEq] using heq

theorem RecursorFieldsMaterialize.recursive_args_sublist
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs allArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    (fields.map (fun field => field.arg)).Sublist allArgs := by
  rw [Hmat.args]
  exact Hsel.translatedSublist Hbu Hu Hunique

/-- The complete recursive-field fragment of `VInductDecl.IotaRule`, isolated
from the surrounding lhs/rhs telescope bookkeeping. -/
structure IotaFieldCertificate (env : VEnv) (decl : VInductDecl)
    (ctorArgs : List VExpr) (fields : List (decl.RecursiveField env))
    (recursiveArgs : List VExpr) where
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = fields.map (fun field => field.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ fields,
    ∃ h : field.fieldIndex < ctorArgs.length,
      field.arg = ctorArgs[field.fieldIndex]'h
  recursiveArgs_eq : recursiveArgs = fields.map (fun field => field.arg)
  recursive_args : recursiveArgs.Sublist ctorArgs

def RecursorFieldsMaterialize.iotaFieldCertificate
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs ctorArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList ctorArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    IotaFieldCertificate semanticEnv decl ctorArgs fields recursiveArgs where
  fieldPositions := fields.map (fun field => field.fieldIndex)
  fieldPositions_eq := rfl
  fieldPositions_ordered := Hmat.positions_ordered Hsel
  fields_at_positions := Hmat.fields_at_positions Hsel Hbu Hu Hunique
  recursiveArgs_eq := Hmat.args.symm
  recursive_args := by
    rw [← Hmat.args]
    exact Hmat.recursive_args_sublist Hsel Hbu Hu Hunique

/-- Non-recursive equation shape shared by generated iota rules. Recursive
field selection and RHS guardedness are supplied by separate certificates. -/
structure IotaEquationCertificate
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)

/-- Assemble the independent iota judgment from its three reviewable pieces:
equation shape, recursive-field selection, and guarded RHS construction. -/
def VInductDecl.IotaRule.ofCertificates
    (Hshape : IotaEquationCertificate decl block owner ctor rule)
    (Hfields : IotaFieldCertificate env decl
      (Hshape.ctorArgs.drop decl.nparams) fields recursiveArgs)
    (Hrhs : IotaRhsCertificate (block.recursors.map (·.name))
      Hshape.domains (Hshape.ctorArgs.drop decl.nparams)
      recursiveArgs Hshape.rhsBody) :
    decl.IotaRule env block owner ctor rule where
  recursor := Hshape.recursor
  recursor_mem := Hshape.recursor_mem
  recursor_name := Hshape.recursor_name
  rule_uvars := Hshape.rule_uvars
  domains := Hshape.domains
  lhsBody := Hshape.lhsBody
  rhsBody := Hshape.rhsBody
  typeBody := Hshape.typeBody
  lhs_wrapped := Hshape.lhs_wrapped
  rhs_wrapped := Hshape.rhs_wrapped
  type_wrapped := Hshape.type_wrapped
  recursorLevels := Hshape.recursorLevels
  leadingArgs := Hshape.leadingArgs
  ctorLevels := Hshape.ctorLevels
  ctorArgs := Hshape.ctorArgs
  lhs_pattern := Hshape.lhs_pattern
  recursor_levels := Hshape.recursor_levels
  ctor_levels := Hshape.ctor_levels
  leading_arity := Hshape.leading_arity
  constructor_arity := Hshape.constructor_arity
  parameter_args := Hshape.parameter_args
  domains_arity := Hshape.domains_arity
  recursiveFields := fields
  fieldPositions := Hfields.fieldPositions
  fieldPositions_eq := Hfields.fieldPositions_eq
  fieldPositions_ordered := Hfields.fieldPositions_ordered
  fields_at_positions := Hfields.fields_at_positions
  recursiveArgs := recursiveArgs
  recursiveArgs_eq := Hfields.recursiveArgs_eq
  recursive_args := Hfields.recursive_args
  fieldVars := Hrhs.fieldVars
  fieldVars_eq := Hrhs.fieldVars_eq
  fields_in_scope := Hrhs.fields_in_scope
  minorVar := Hrhs.minorVar
  minor_in_scope := Hrhs.minor_in_scope
  rhsArgs := Hshape.ctorArgs.drop decl.nparams ++ Hrhs.recursiveResults
  rhs_spine := Hrhs.rhs_spine
  field_args := by
    simpa using Hrhs.field_args
  recursive_results := by
    simpa using Hrhs.results_length
  rhs_guarded := Hrhs.guarded

/-- Exact concrete common-parameter prefix consumed by recursor generation.
The relation is intentionally separate from field classification: agreement
of these substitutions with the abstract parameter telescope is established
during constructor checking. -/
inductive RecursorParamPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → RecursorParamPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      RecursorParamPrefix stats (i + 1) (body.instantiate1 param) tail →
      RecursorParamPrefix stats i (.forallE name dom body bi) tail

/-- Replaying the cached parameter prefix is deterministic. -/
theorem RecursorParamPrefix.tail_eq
    (Hleft : RecursorParamPrefix stats i source left)
    (Hright : RecursorParamPrefix stats i source right) : left = right := by
  induction Hleft with
  | done hi =>
    cases Hright with
    | done => rfl
    | step hparam _ =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
  | @step i param body left dom name bi hparam Hleft ih =>
    cases Hright with
    | done hi =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
    | step hparam' Hright =>
      have heq : param = _ := Option.some.inj (hparam.symm.trans hparam')
      subst_vars
      exact ih Hright

/-- Consuming the executable common-parameter prefix cannot introduce a
free variable outside the source declaration and the concrete parameters
used for instantiation. -/
theorem RecursorParamPrefix.tailFVarsIn
    (H : RecursorParamPrefix stats i source tail)
    (hsource : source.FVarsIn P)
    (hparams : ∀ (j : Nat) (param : Expr),
      stats.params[j]? = some param → Expr.FVarsIn P param) :
    tail.FVarsIn P := by
  induction H with
  | done => exact hsource
  | step hparam _ ih =>
    exact ih (by
      simpa [Expr.instantiate1] using
        hsource.2.instantiate1 (hparams _ _ hparam))

/-- A partially consumed common-parameter prefix.  Constructor checking
builds this left-to-right; when `stop = stats.params.size`, it is exactly the
complete prefix replay required by recursor generation. -/
inductive RecursorParamSegment (stats : AddInductive.InductiveStats) :
    Nat → Nat → Expr → Expr → Prop
  | done : RecursorParamSegment stats i i source source
  | step {i stop : Nat} {param body tail dom : Expr}
      {name : Name} {bi : BinderInfo} :
      stats.params[i]? = some param →
      RecursorParamSegment stats (i + 1) stop
        (body.instantiate1 param) tail →
      RecursorParamSegment stats i stop (.forallE name dom body bi) tail

theorem RecursorParamSegment.trans
    (H₁ : RecursorParamSegment stats start middle source current)
    (H₂ : RecursorParamSegment stats middle stop current tail) :
    RecursorParamSegment stats start stop source tail := by
  induction H₁ with
  | done => exact H₂
  | step hparam _ ih => exact .step hparam (ih H₂)

theorem RecursorParamSegment.push
    {body param dom : Expr} {name : Name} {bi : BinderInfo}
    (H : RecursorParamSegment stats start i source
      (.forallE name dom body bi))
    (hparam : stats.params[i]? = some param) :
    RecursorParamSegment stats start (i + 1) source
      (body.instantiate1 param) := by
  exact H.trans (.step hparam .done)

theorem RecursorParamSegment.complete
    (H : RecursorParamSegment stats start stop source tail)
    (hstop : stop = stats.params.size) :
    RecursorParamPrefix stats start source tail := by
  induction H with
  | done => exact .done hstop
  | step hparam _ ih => exact .step hparam (ih hstop)

namespace mkRecInfos.loopCtorArgs.loop

/-- `loopCtorArgs.loop` follows a certified common-parameter prefix without
changing either accumulator, then delegates to the supplied tail proof. Fuel
exhaustion is harmless because it cannot return successfully. -/
theorem followsParamPrefix {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t tail : Expr} {i : Nat} {bu u : Array Expr}
    {c : AddInductive.Context} {Q : α → Prop}
    (hprefix : RecursorParamPrefix stats i t tail)
    (Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size bu u fuel c).WF Q) :
    ∀ fuel, (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  intro fuel
  induction fuel generalizing t i with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases hprefix with
    | done hi =>
      subst i
      exact Htail (fuel + 1)
    | @step i param body tail name dom bi hparam hprefix =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop, hparam]
      exact ih hprefix

/-- Typed refinement of the genuine-field suffix of `loopCtorArgs`. Common
parameters have already been exhausted, so every remaining forall binder is a
constructor field. Each successful recursive classification extends an exact
ordered list of independent `RecursiveArg` certificates. -/
theorem recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (Hc : ContextWF c)
    {fields : List (RecursorRecursiveDomain Hc.venv decl)}
    {args : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hparams : stats.params.size ≤ i)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx t type')
    (hfields : RecursorFieldSelections Hc.venv decl bu u fields)
    (hargs : List.Forall₂
      (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) u.toList args)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr}
      {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u depth type' fields args with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      have hparam : stats.params[i]? = none := by
        apply Array.getElem?_eq_none
        omega
      rw [hparam]
      have htypeTr := htype.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
      rcases TrExpr.forallE_source htypeTr with
        ⟨sourceDom', sourceBody', hdom, hbody, hdomType, _, _⟩
      rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
      rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
      refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
        Hc Hdom.consumed Hdom.isType ?_
      let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
        Hc Hdom.consumed Hdom.isType
      have hctx' : checkPositivityStep.VLCtx.NoIndConsts
          (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
        apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
        rfl
      let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have hdomWeak : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx dom
          (sourceDom'.liftN 1 0) := by
        apply Hdom.source.weakFV Hc.checking.tr.wf.ordered
          W
        exact Hc'.mlctx_wf.tr.wf
      have hargsWeak : List.Forall₂
          (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) u.toList
          (args.map fun arg => arg.liftN 1 0) := by
        apply checkPositivityStep.forall₂_map_right hargs
        intro source arg harg
        exact harg.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
      have harg : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        exact TrExprS.fvar (A := consumedDom'.lift) (by
          change VLCtx.find? ((some (⟨c.ngen.curr⟩,
            dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom') ::
              Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type])
      have hopened := Hc.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbody''
      have Hclass := isRecArg.refines Hc' Hstats' hconsume hlit hctx'
        (hdomWeak.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
      refine Hclass.bind fun selected hselected => ?_
      cases selected with
      | none =>
        exact ih Hc' Hstats' (by omega) hlit hctx' hopened
          (.nonrecursive hfields) hargsWeak
      | some target =>
        rcases hselected target rfl with ⟨howner, hrecursive⟩
        let cert : RecursorRecursiveDomain Hc'.venv decl := {
          fieldIndex := bu.size
          ownerIdx := target
          owner_lt := howner
          ctx := Hc'.mlctx.vlctx.toCtx
          depth := depth + 1
          domain := sourceDom'.liftN 1 0
          recursive := hrecursive }
        have hargs' : List.Forall₂
            (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
            (u.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((args.map fun arg => arg.liftN 1 0) ++ [.bvar 0]) := by
          simpa using checkPositivityStep.forall₂_append
            hargsWeak (.cons harg .nil)
        exact ih Hc' Hstats' (by omega) hlit hctx' hopened
          (.recursive hfields (cert := cert) rfl) hargs'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      exact Hk Hc htype hfields hargs

end mkRecInfos.loopCtorArgs.loop

/-- Full constructor-argument refinement, composing exact common-parameter
substitution with typed recursive-field classification. -/
theorem mkRecInfos.loopCtorArgs.recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats) (t tail : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    {decl : VInductDecl} {tail' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hprefix : RecursorParamPrefix stats 0 t tail)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (htail : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx tail tail')
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr} {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  let inputContext := c
  unfold AddInductive.mkRecInfos.loopCtorArgs
  have hread : ((read : AddInductive.M AddInductive.Context) inputContext).WF
      (fun c' => c' = inputContext) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  have Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size #[] #[] fuel inputContext).WF Q := by
    intro fuel
    exact mkRecInfos.loopCtorArgs.loop.recursiveDomains stats k Hc Hstats
      (Nat.le_refl _) hconsume hlit hctx htail .nil .nil Hk
  exact mkRecInfos.loopCtorArgs.loop.followsParamPrefix stats k hprefix Htail
    inputContext.fuel.inductiveFuel

namespace mkRecInfos.loopArgs1

/-- `loopArgs1` cannot manufacture a successful result: after any sequence
of WHNF steps and local index binders it returns only through its supplied
continuation. This structural fact is the outer-loop interface used to count
one motive record per mutual family. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M α)
    {Q : α → Prop}
    (Hk : ∀ indices c, (k indices c).WF Q) :
    ∀ type i indices fuel c,
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, 0, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, i, indices, fuel + 1, c => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        by_cases hparam : i < stats.params.size
        · rw [if_pos hparam]
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 stats.params[i]!)) :
                AddInductive.M Expr) c).WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next (i + 1) indices fuel c
        · rw [if_neg hparam]
          unfold Lean4Lean.withLocalDecl
            MonadLocalNameGenerator.withFreshId
            AddInductive.instMonadLocalNameGeneratorM
            AddInductive.instMonadWithReaderOfLocalContextM
          let c' : AddInductive.Context := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }
          change ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c' >>= fun next =>
              AddInductive.mkRecInfos.loopArgs1 stats next i
                (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel k c').WF Q
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
                AddInductive.M Expr) c').WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next i
              (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel c'
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          by_cases hi : i < stats.params.size
          · simp only [AddInductive.mkRecInfos.loopArgs1, hi, if_pos]
            exact Except.WF.throw
          · simpa [AddInductive.mkRecInfos.loopArgs1, hi] using Hk indices c

end mkRecInfos.loopArgs1

/-- Structural opening of a production local declaration when the proof only
needs to follow the continuation and does not yet claim typing for the new
domain. -/
theorem withLocalDecl.continueRaw
    {α : Type} {Q : α → Prop} {k : Expr → AddInductive.M α}
    {c : AddInductive.Context} {name : Name} {bi : BinderInfo} {ty : Expr}
    (H : (k (.fvar ⟨c.ngen.curr⟩) { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
    AddInductive.instMonadLocalNameGeneratorM
    AddInductive.instMonadWithReaderOfLocalContextM
  exact H

/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopInd1

/-- The first recursor pass appends exactly one `RecInfo` (motive, indices,
major premise) for each mutual family. -/
theorem resultCount
    {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = dIdx)
    (hempty : ∀ r ∈ recInfos.toList, r.minors.isEmpty)
    (harities : ∀ i, i < recInfos.size →
      recInfos[i]!.indices.size = stats.nindices[i]!)
    (Hk : ∀ recInfos c, recInfos.size = indTypes.size →
      (∀ r ∈ recInfos.toList, r.minors.isEmpty) →
      (∀ i, i < recInfos.size →
        recInfos[i]!.indices.size = stats.nindices[i]!) →
      (k recInfos c).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context) hread fun ctx hctx => ?_
    subst ctx
    have hwhnf :
        ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
          AddInductive.M Expr) c).WF (fun _ => True) := by
      intro _ _
      trivial
    refine hwhnf.bind fun type _ => ?_
    apply mkRecInfos.loopArgs1.continueWith stats
    intro indices cIndices
    by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
    · rw [if_pos harity]
      apply withLocalDecl.continueRaw
      let cMajor : AddInductive.Context := { cIndices with
        ngen := cIndices.ngen.next
        lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
          (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices).consumeTypeAnnotationsVerified
          .default }
      have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
          (fun lctx => lctx = cMajor.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      apply withLocalDecl.continueRaw
      apply mkRecInfos.loopInd1.resultCount
        (stats := stats) (indTypes := indTypes) (elimLevel := elimLevel)
        (dIdx := dIdx + 1) (recInfos := recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩, minors := #[], indices := indices,
          major := .fvar ⟨cIndices.ngen.curr⟩ }) (k := k)
        (Q := Q)
      · omega
      · simpa [hsize]
      · intro r hr
        simp only [Array.toList_push, List.mem_append, List.mem_cons,
          List.mem_singleton] at hr
        rcases hr with hr | hr
        · exact hempty r hr
        · rcases hr with rfl | hr
          · rfl
          · contradiction
      · intro i hiPush
        have harityEq : indices.size = stats.nindices[dIdx]! := by
          simpa using harity
        by_cases hilast : i = recInfos.size
        · subst i
          simpa [← hsize, harityEq]
        · have hiOld : i < recInfos.size := by
            have hiPush' : i < recInfos.size + 1 := by simpa using hiPush
            omega
          have hbang :
              (recInfos.push {
                motive := .fvar ⟨cMajor.ngen.curr⟩, minors := #[],
                indices := indices,
                major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
            simp only [Array.getElem!_eq_getD]
            unfold Array.getD
            rw [dif_pos hiPush, dif_pos hiOld]
            exact Array.getElem_push_lt hiOld
          rw [hbang]
          exact harities i hiOld
      · exact Hk
    · rw [if_neg harity]
      exact Except.WF.throw
  · rw [dif_neg hidx]
    apply Hk
    · omega
    · exact hempty
    · exact harities
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopU

/-- The induction-hypothesis loop returns only through its continuation.
Its generated local declarations affect the eventual minor type, but not the
`RecInfo` array whose cardinality is tracked by `loopCtors`. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M α) {Q : α → Prop}
    (Hk : ∀ v c, (k v c).WF Q)
    (i : Nat) (v : Array Expr) (c : AddInductive.Context) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
      rw [AddInductive.mkRecInfos.loopU]
      by_cases hnext : i < u.size
      · rw [dif_pos hnext]
        have hviTy :
            ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
              let some itIdx := AddInductive.isValidIndApp? stats uiTy
                | throw (.other
                  "recursive constructor field lost its inductive result type")
              let itIndices := uiTy.getAppArgs[stats.params.size:]
              let motiveApp := .app
                (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
              return (← getLCtx).mkForall xs motiveApp) c).WF
              (fun _ => True) := by
          intro _ _
          trivial
        refine hviTy.bind fun viTy _ => ?_
        have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
            (fun lctx => lctx = c.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        apply withLocalDecl.continueRaw
        exact continueWith stats u recInfos k Hk (i + 1)
          (v.push (.fvar ⟨c.ngen.curr⟩)) _
      · rw [dif_neg hnext]
        exact Hk v c
termination_by u.size - i

end mkRecInfos.loopU

namespace mkRecInfos.loopUBlueprints

/-- The retained-blueprint hypothesis loop likewise returns only through its
continuation, now carrying one exact call blueprint per recursive field. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallBlueprint →
      AddInductive.M α) {Q : α → Prop}
    (Hk : ∀ v calls c, (k v calls c).WF Q)
    (i : Nat) (v : Array Expr)
    (calls : Array AddInductive.RecCallBlueprint)
    (c : AddInductive.Context) :
    (AddInductive.mkRecInfos.loopUBlueprints stats u recInfos i v calls
      k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopUBlueprints]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hviTy :
        ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
          let some itIdx := AddInductive.isValidIndApp? stats uiTy
            | throw (.other
              "recursive constructor field lost its inductive result type")
          let itIndices := uiTy.getAppArgs[stats.params.size:]
          let lctx ← getLCtx
          let motiveApp := .app
            (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
          let viTy := lctx.mkForall xs motiveApp
          return (viTy, ({
            major := u[i]
            args := xs
            lctx := lctx
            targetTypeIdx := itIdx
            targetIndices := itIndices
            template := lctx.mkLambda xs <|
              (mkAppN (.bvar 0) itIndices).app (mkAppN u[i] xs) } :
              AddInductive.RecCallBlueprint))) c).WF
          (fun _ => True) := by
      intro _ _
      trivial
    refine hviTy.bind fun result _ => ?_
    rcases result with ⟨viTy, call⟩
    have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
        (fun lctx => lctx = c.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    apply withLocalDecl.continueRaw
    exact continueWith stats u recInfos k Hk (i + 1)
      (v.push (.fvar ⟨c.ngen.curr⟩)) (calls.push call) _
  · rw [dif_neg hnext]
    exact Hk v calls c
termination_by u.size - i

end mkRecInfos.loopUBlueprints

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

/-- Processing a constructor list preserves the number of family records and
appends exactly one minor premise per constructor to the selected owner. -/
theorem resultCount {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hidx : dIdx < recInfos.size)
    (Hk : ∀ out c,
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + ctors.length →
      { out[dIdx]! with minors := #[], ruleBlueprints := #[] } =
        { recInfos[dIdx]! with minors := #[], ruleBlueprints := #[] } →
      (∀ i, i < recInfos.size → dIdx ≠ i → out[i]! = recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simp only [AddInductive.mkRecInfos.loopCtors]
      apply Hk
      · rfl
      · simp
      · rfl
      · intros
        rfl
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      apply mkRecInfos.loopCtorArgs.selectedSublist stats
      intro t bu u cArgs _
      apply mkRecInfos.loopUBlueprints.continueWith stats u recInfos
      intro v calls cIH
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      apply withLocalDecl.continueRaw
      let blueprint : AddInductive.RecRuleBlueprint := {
        ctor := ctor.name
        fields := bu
        lctx := cIH.lctx
        recursiveCalls := calls
        targetTypeIdx := (AddInductive.getIIndices stats t).1
        targetIndices := (AddInductive.getIIndices stats t).2
        minor := .fvar ⟨cIH.ngen.curr⟩ }
      let next := recInfos.modify dIdx fun s => {
        s with
        minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩)
        ruleBlueprints := s.ruleBlueprints.push blueprint }
      apply ih next _
      · simpa [next]
      · intro out cOut houtSize houtCount houtFrame
          houtOther
        apply Hk out cOut
        · simpa [next] using houtSize
        · rw [houtCount]
          dsimp [next]
          have hnextIdx : dIdx < (recInfos.modify dIdx fun s =>
              { s with
                minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩)
                ruleBlueprints := s.ruleBlueprints.push blueprint }).size := by
            simpa using hidx
          have hbangModified :
              (recInfos.modify dIdx fun s =>
                { s with
                  minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩)
                  ruleBlueprints := s.ruleBlueprints.push blueprint })[dIdx]! =
              { recInfos[dIdx]! with
                minors := recInfos[dIdx]!.minors.push (.fvar ⟨cIH.ngen.curr⟩)
                ruleBlueprints := recInfos[dIdx]!.ruleBlueprints.push
                  blueprint } := by
            simp only [Array.getElem!_eq_getD]
            unfold Array.getD
            rw [dif_pos hnextIdx, dif_pos hidx]
            exact Array.getElem_modify_self _ hnextIdx
          rw [hbangModified]
          simp
          omega
        · rw [houtFrame]
          dsimp [next]
          rw [getElemBang_modify_self recInfos dIdx _ hidx]
        · intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          exact getElemBang_modify_ne recInfos dIdx i _ hi hine

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[], ruleBlueprints := #[] } =
    { b with minors := #[], ruleBlueprints := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

theorem SameFrame.trans (hab : SameFrame a b) (hbc : SameFrame b c) :
    SameFrame a c := Eq.trans hab hbc

theorem SameFrame.indices_eq (H : SameFrame a b) : a.indices = b.indices := by
  have h := congrArg AddInductive.RecInfo.indices H
  simpa [SameFrame] using h

/-- The second mutual pass finishes every family with exactly one minor per
owned constructor. The prefix/suffix formulation makes the mutation boundary
explicit and is directly initialized by `loopInd1`, whose minor arrays are
empty. -/
theorem resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (origin : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (horiginSize : origin.size = recInfos.size)
    (hframes : ∀ i, i < recInfos.size → SameFrame recInfos[i]! origin[i]!)
    (hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      out.size = origin.size →
      (∀ i, i < out.size → SameFrame out[i]! origin[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize houtCount houtFrame houtOther
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes (dIdx + 1)
      out origin k cOut
    · omega
    · simpa [hsize] using houtSize
    · omega
    · intro i hiout
      apply SameFrame.trans (b := recInfos[i]!)
      · by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
          exact SameFrame.refl _
      · exact hframes i (by simpa [houtSize] using hiout)
    · intro i hi hiout
      by_cases heq : i = dIdx
      · subst i
        rw [houtCount, hsuffix dIdx (by omega) (by simpa [hsize] using hidx)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
        exact hprefix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · intro i hi hiout
      rw [houtOther i (by simpa [hsize, houtSize] using hiout) (by omega)]
      exact hsuffix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · exact Hk
  · rw [dif_neg hidx]
    apply Hk recInfos c hsize
    · intro i hi
      exact hprefix i (by omega) hi
    · omega
    · exact hframes
termination_by indTypes.size - dIdx

/-- `loopInd2` changes only the `minors` field of each `RecInfo`; motives,
indices, and major premises remain those constructed by `loopInd1`. -/
theorem resultFrames {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (Hk : ∀ out c, out.size = recInfos.size →
      (∀ i, i < recInfos.size → SameFrame out[i]! recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize _ houtFrame houtOther
    apply mkRecInfos.loopInd2.resultFrames (Q := Q) stats indTypes (dIdx + 1)
      out k cOut
    · omega
    · simpa [hsize] using houtSize
    · intro final cFinal hfinalSize hfinalFrames
      apply Hk final cFinal
      · simpa [houtSize] using hfinalSize
      · intro i hi
        apply SameFrame.trans (hfinalFrames i (by simpa [houtSize] using hi))
        by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · have hsibling := houtOther i hi (Ne.symm heq)
          rw [hsibling]
          exact SameFrame.refl _
  · rw [dif_neg hidx]
    apply Hk recInfos c
    · rfl
    · intro i hi
      exact SameFrame.refl _
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end structural cardinality theorem for production `mkRecInfos`:
one record per mutual family, initialized by the first pass and populated with
one minor per source constructor by the second pass. -/
theorem mkRecInfos.resultStructure {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ (initial out : Array AddInductive.RecInfo)
        (c : AddInductive.Context),
      initial.size = indTypes.size →
      (∀ r ∈ initial.toList, r.minors.isEmpty) →
      (∀ i, i < initial.size →
        initial[i]!.indices.size = stats.nindices[i]!) →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (∀ i, i < out.size →
        mkRecInfos.loopInd2.SameFrame out[i]! initial[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultCount (Q := Q) stats indTypes elimLevel
    0 #[] (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) c
  · omega
  · simp
  · simp
  · simp
  · intro recInfos cRec hsize hempty harities
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes 0
      recInfos recInfos k cRec
    · omega
    · exact hsize
    · rfl
    · intro i hi
      exact mkRecInfos.loopInd2.SameFrame.refl _
    · intro i hi
      omega
    · intro i _ hi
      have he := hempty (recInfos[i]'hi) (Array.getElem_mem_toList hi)
      rw [Array.isEmpty_iff_size_eq_zero] at he
      simpa [Array.getElem!_eq_getD, Array.getD, hi] using he
    · intro out cOut houtSize houtCounts _ houtFrames
      exact Hk recInfos out cOut hsize hempty harities houtSize houtCounts
        houtFrames

/-- Cardinality-only projection of `resultStructure`. -/
theorem mkRecInfos.resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultStructure (Q := Q) stats indTypes elimLevel k c
  intro _ out cOut _ _ _ houtSize houtCounts _
  exact Hk out cOut houtSize houtCounts

/-- Per-family minor counts imply the corresponding flattened block count
used by production recursor types. -/
theorem mkRecInfos.flatMinors_size
    {recInfos : Array AddInductive.RecInfo}
    {indTypes : Array InductiveType}
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  rw [Array.size_flatMap, Array.size_flatMap]
  congr 1
  apply Array.ext
  · simp [hsize]
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    have hiRec : i < recInfos.size := by simpa using hiLeft
    have hiInd : i < indTypes.size := by omega
    have hc := hcounts i hiRec
    simpa [Array.getElem!_eq_getD, Array.getD, hiRec, hiInd] using hc

theorem ownedConstructors_length_eq_flattened_size
    (indTypes : Array InductiveType) :
    (ownedConstructors indTypes.toList).length =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  simp only [ownedConstructors, List.length_flatMap, List.length_map,
    Array.size_flatMap]
  rw [← Array.sum_toList, Array.toList_map]
  simp

/-- Number of constructors belonging to mutual families strictly before
`dIdx`. This is also the shared minor/rule state at the corresponding
iteration of `declareRecursors.loop`. -/
def recursorMinorOffset (indTypes : Array InductiveType) (dIdx : Nat) : Nat :=
  ((indTypes.toList.take dIdx).flatMap (fun type => type.ctors)).length

/-- The element at a flattened prefix offset is the selected element of the
current row.  Keeping this generic isolates the list arithmetic shared by
concrete and abstract owned-constructor enumerations. -/
theorem List.flatMap_getElem_prefix
    (rows : List α) (entries : α → List β)
    (owner i : Nat) (howner : owner < rows.length)
    (hi : i < (entries rows[owner]).length)
    (hindex : ((rows.take owner).flatMap entries).length + i <
      (rows.flatMap entries).length) :
    (rows.flatMap entries)[((rows.take owner).flatMap entries).length + i]'hindex =
      (entries rows[owner])[i]'hi := by
  have hsplit : rows = rows.take owner ++ rows[owner] ::
      rows.drop (owner + 1) := by
    calc
      rows = rows.take (owner + 1) ++ rows.drop (owner + 1) :=
        (List.take_append_drop (owner + 1) rows).symm
      _ = (rows.take owner ++ [rows[owner]]) ++
          rows.drop (owner + 1) := by
        rw [List.take_append_getElem howner]
      _ = rows.take owner ++ rows[owner] :: rows.drop (owner + 1) := by
        simp [List.append_assoc]
  have hrow : entries rows[owner] =
      (entries rows[owner]).take i ++
        (entries rows[owner])[i] ::
          (entries rows[owner]).drop (i + 1) := by
    calc
      entries rows[owner] =
          (entries rows[owner]).take (i + 1) ++
            (entries rows[owner]).drop (i + 1) :=
        (List.take_append_drop (i + 1) (entries rows[owner])).symm
      _ = ((entries rows[owner]).take i ++
            [(entries rows[owner])[i]]) ++
          (entries rows[owner]).drop (i + 1) := by
        rw [List.take_append_getElem hi]
      _ = (entries rows[owner]).take i ++
          (entries rows[owner])[i] ::
            (entries rows[owner]).drop (i + 1) := by
        simp [List.append_assoc]
  have houter : rows.flatMap entries =
      (rows.take owner).flatMap entries ++ entries rows[owner] ++
        (rows.drop (owner + 1)).flatMap entries := by
    simpa only [List.flatMap_append, List.flatMap_cons,
      List.append_assoc] using congrArg (List.flatMap entries) hsplit
  have hflat : rows.flatMap entries =
      ((rows.take owner).flatMap entries ++
        (entries rows[owner]).take i) ++
      (entries rows[owner])[i] ::
        ((entries rows[owner]).drop (i + 1) ++
          (rows.drop (owner + 1)).flatMap entries) := by
    calc
      rows.flatMap entries =
          (rows.take owner).flatMap entries ++ entries rows[owner] ++
            (rows.drop (owner + 1)).flatMap entries := houter
      _ = (rows.take owner).flatMap entries ++
          ((entries rows[owner]).take i ++
            (entries rows[owner])[i] ::
              (entries rows[owner]).drop (i + 1)) ++
          (rows.drop (owner + 1)).flatMap entries :=
        congrArg
          (fun xs => (rows.take owner).flatMap entries ++ xs ++
            (rows.drop (owner + 1)).flatMap entries) hrow
      _ = ((rows.take owner).flatMap entries ++
            (entries rows[owner]).take i) ++
          (entries rows[owner])[i] ::
            ((entries rows[owner]).drop (i + 1) ++
              (rows.drop (owner + 1)).flatMap entries) := by
        simp only [List.append_assoc, List.cons_append]
  exact List.getElem_of_append hflat (by
    simp [Nat.min_eq_left (Nat.le_of_lt hi)])

/-- The abstract owned-constructor enumeration uses the same owner-major,
constructor-minor order as its defining nested flattening. -/
theorem VInductDecl.ownedConstructors_getElem_prefix
    (decl : VInductDecl) (owner i : Nat)
    (howner : owner < decl.types.length)
    (hi : i < (decl.types[owner]).ctors.length)
    (hindex : ((decl.types.take owner).flatMap
      (fun type => type.ctors)).length + i < decl.ownedConstructors.length) :
    decl.ownedConstructors[
        ((decl.types.take owner).flatMap
          (fun type => type.ctors)).length + i]'hindex =
      (decl.types[owner], (decl.types[owner]).ctors[i]) := by
  have hiMapped : i <
      ((decl.types[owner]).ctors.map (decl.types[owner], ·)).length := by
    simpa using hi
  have hindexMapped :
      ((decl.types.take owner).flatMap
          (fun type => type.ctors.map (type, ·))).length + i <
        (decl.types.flatMap
          (fun type => type.ctors.map (type, ·))).length := by
    simpa [VInductDecl.ownedConstructors, List.length_flatMap] using hindex
  simpa [VInductDecl.ownedConstructors, List.length_flatMap] using
    List.flatMap_getElem_prefix decl.types
      (fun type => type.ctors.map (type, ·)) owner i howner hiMapped
      hindexMapped

/-- Translation preserves the number of constructors in every mutual-family
prefix, so production's running minor offset is the abstract flattening
offset for the same owner. -/
theorem TrInductDeclCore.recursorMinorOffset_eq_abstract
    (H : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe decl
      envTypes envCtors)
    (owner : Nat) (howner : owner ≤ indTypes.size) :
    recursorMinorOffset indTypes owner =
      ((decl.types.take owner).flatMap
        (fun type => type.ctors)).length := by
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
    have hsourceOwner : owner < indTypes.size := by omega
    have htypes : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length H
    have habstractOwner : owner < decl.types.length := by omega
    have hsourceList : owner < indTypes.toList.length := by
      simpa only [Array.length_toList] using hsourceOwner
    have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt H owner
      hsourceList habstractOwner
    unfold recursorMinorOffset at ih ⊢
    rw [← List.take_append_getElem hsourceList]
    rw [← List.take_append_getElem habstractOwner]
    simp only [List.flatMap_append, List.flatMap_singleton, List.length_append]
    rw [ih (by omega)]
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using
      Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner

/-- Select the canonical abstract owner/constructor at production's concrete
minor offset.  This is the pointwise bridge needed to package raw generated
equation translations as specification iota rules. -/
theorem TrInductDeclCore.ownedConstructorAtMinorOffset
    (H : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe decl
      envTypes envCtors)
    (owner i : Nat) (howner : owner < indTypes.size)
    (hi : i < indTypes[owner]!.ctors.length)
    (habstractOwner : owner < decl.types.length)
    (habstractCtor : i < (decl.types[owner]'habstractOwner).ctors.length)
    (hindex : recursorMinorOffset indTypes owner + i <
      decl.ownedConstructors.length) :
    decl.ownedConstructors[recursorMinorOffset indTypes owner + i]'hindex =
      (decl.types[owner]'habstractOwner,
        (decl.types[owner]'habstractOwner).ctors[i]'habstractCtor) := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length H
  let Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt H owner
    (by simpa using howner) habstractOwner
  have habstractCtor' : i < (decl.types[owner]).ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner]
    simpa [Array.getElem!_eq_getD, Array.getD, howner] using hi
  have hoffset :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.recursorMinorOffset_eq_abstract
      H owner (Nat.le_of_lt howner)
  have habstractIndex :
      ((decl.types.take owner).flatMap
        (fun type => type.ctors)).length + i <
        decl.ownedConstructors.length := by
    simpa [hoffset] using hindex
  simpa [hoffset] using
    Lean4Lean.VerifyInductive.VInductDecl.ownedConstructors_getElem_prefix
      decl owner i habstractOwner habstractCtor' habstractIndex

theorem recursorMinorOffset_step
    (indTypes : Array InductiveType) (dIdx : Nat)
    (hidx : dIdx < indTypes.size) :
    recursorMinorOffset indTypes (dIdx + 1) =
      recursorMinorOffset indTypes dIdx + indTypes[dIdx]!.ctors.length := by
  simp [recursorMinorOffset, List.take_add_one, hidx,
    List.length_flatMap]

theorem recursorMinorOffset_mono
    (indTypes : Array InductiveType) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ indTypes.size) :
    recursorMinorOffset indTypes a ≤
      recursorMinorOffset indTypes b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a ≤ b := by omega
        have hb' : b ≤ indTypes.size := by omega
        have hidx : b < indTypes.size := by omega
        calc
          recursorMinorOffset indTypes a ≤
              recursorMinorOffset indTypes b := ih a hab' hb'
          _ ≤ recursorMinorOffset indTypes (b + 1) := by
            rw [recursorMinorOffset_step indTypes b hidx]
            omega

theorem recursorMinorOffset_le_total
    (indTypes : Array InductiveType) (dIdx : Nat) :
    recursorMinorOffset indTypes dIdx ≤
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
  let pre := (indTypes.toList.take dIdx).flatMap (fun type => type.ctors)
  let suffix := (indTypes.toList.drop dIdx).flatMap (fun type => type.ctors)
  have hsplit : pre ++ suffix =
      indTypes.toList.flatMap (fun type => type.ctors) := by
    simp only [pre, suffix, ← List.flatMap_append,
      List.take_append_drop]
  change pre.length ≤ _
  rw [← hsplit, List.length_append]
  omega

theorem recursorMinorOffset_room
    (indTypes : Array InductiveType) (dIdx : Nat)
    (hidx : dIdx < indTypes.size) :
    recursorMinorOffset indTypes dIdx + indTypes[dIdx]!.ctors.length ≤
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
  rw [← recursorMinorOffset_step indTypes dIdx hidx]
  exact recursorMinorOffset_le_total indTypes (dIdx + 1)

theorem mkRecInfos.motives_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size) :
    (recInfos.map (·.motive)).size = decl.types.length := by
  simp only [Array.size_map]
  rw [hsize]
  simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl

theorem mkRecInfos.flatMinors_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size = decl.ownedConstructors.length := by
  rw [mkRecInfos.flatMinors_size hsize hcounts,
    ← ownedConstructors_length_eq_flattened_size]
  exact Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl

/-- Structural portion of the independent recursor shape, assembled before
the generated telescope itself is translated. -/
structure RecursorCardinalityCertificate
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (decl : VInductDecl) : Prop where
  records : recInfos.size = decl.types.length
  families : stats.indConsts.size = decl.types.length
  params : stats.params.size = decl.nparams
  motives : (recInfos.map (·.motive)).size = decl.types.length
  minors : (recInfos.flatMap (·.minors)).size =
    decl.ownedConstructors.length
  indices : ∀ i (hi : i < recInfos.size),
    recInfos[i]!.indices.size =
      (decl.types[i]'(by simpa [records] using hi)).numIndices

theorem RecursorCardinalityCertificate.ofResult
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (harities : ∀ i, i < recInfos.size →
      recInfos[i]!.indices.size = stats.nindices[i]!) :
    RecursorCardinalityCertificate stats recInfos decl where
  records := hsize.trans (by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl)
  families := by
    exact
      (checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader
        Hmaterialized).types_size
  params := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hmaterialized.narrowParams
    simpa [VInductDecl.paramVars] using hlen
  motives := mkRecInfos.motives_size_of_translation Hdecl hsize
  minors := mkRecInfos.flatMinors_size_of_translation Hdecl hsize hcounts
  indices := by
    let Hstats :=
      checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader Hmaterialized
    intro i hi
    have hiDecl : i < decl.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl]
      simpa [hsize] using hi
    have hn := Hstats.nindicesAt hiDecl
    have hstats : stats.nindices[i]! = decl.types[i].numIndices := by
      obtain ⟨hstatsBound, hnget⟩ := Array.getElem?_eq_some_iff.mp hn
      simpa [Array.getElem!_eq_getD, Array.getD, hstatsBound] using hnget
    exact (harities i hi).trans hstats

/-- Public `mkRecInfos` boundary carrying all independently specified
telescope cardinalities into the recursor-construction continuation. -/
theorem AddInductive.mkRecInfos.cardinalityWF
    {α : Type} {Q : α → Prop}
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (Hk : ∀ recInfos c,
      Nonempty (RecursorCardinalityCertificate stats recInfos decl) →
      (k recInfos c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultStructure (Q := Q) stats indTypes elimLevel k c
  intro initial out cOut hinitial _ hinitialArities hout hcounts hframes
  have houtArities : ∀ i, i < out.size →
      out[i]!.indices.size = stats.nindices[i]! := by
    intro i hi
    have hiInitial : i < initial.size := by omega
    rw [(hframes i hi).indices_eq]
    exact hinitialArities i hiInitial
  exact Hk out cOut ⟨RecursorCardinalityCertificate.ofResult
    Hdecl Hmaterialized hout hcounts houtArities⟩

/-- Constructor-tail refinement with the verified positivity traversal plugged
into every safe field. -/
theorem checkConstructors.loopCtor.tailRefinesFull
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  apply checkConstructors.loopCtor.tailRefines Hc Hstats hi htarget
    hparamAt hconsume hlit hctx hunsafe hbound
  · intro c' depth' posIdx type' type'' Hc' Hstats' hlit' hctx' htype'
    exact checkPositivity.refines Hc' Hstats' hconsume hlit' hctx' htype'
  · exact htr

/-- Regard a constructor constant as the root of a telescope synthesis.  The
existing narrow header certificate only uses the constant fields of its
`target`; the empty constructor list therefore lets the same, already proved
wrapping invariant serve constructor parameter prefixes without duplicating
it. -/
def constructorTelescopeTarget (ctorVal : VConstVal) :
    VInductiveTypeSkeleton where
  toVConstVal := ctorVal
  ctors := []

/-- Initialize constructor telescope synthesis from the independently
translated source constant. -/
noncomputable def ConstructorSynthesisState.initial
    (Hctor : TrSourceConstRaw env Us ctor type ctorVal)
    (htype : env.IsType Us.length [] ctorVal.type) :
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us (constructorTelescopeTarget ctorVal) [] ctorVal.type 0 0 := by
  let level := Classical.choose htype
  have htyped := Classical.choose_spec htype
  exact checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
    htype htype htyped

/-- Exact semantic record of the common-parameter comparisons performed
by `checkConstructors.loopCtor`.  Unlike `RecursorParamPrefix`, this trace
does not forget the translated concrete constructor domain or the
definitional equality returned by the executable `isDefEq` call.

The list of `sourceDomains` is in telescope order.  The scope is the cached
common-parameter scope after the same number of steps.  Keeping both sides
is essential for nested restoration: constructor parameter domains need only
be definitionally, not syntactically, equal to the family parameters. -/
inductive CheckedConstructorParameterPrefix
    (env : VEnv) (Us : List Name) (stats : AddInductive.InductiveStats)
    (original : Expr) :
    Nat → Expr → VLCtx → List VExpr → Prop where
  | zero : CheckedConstructorParameterPrefix env Us stats original
      0 original [] []
  | step
      (H : CheckedConstructorParameterPrefix env Us stats original
        i (.forallE name dom body bi) scope sourceDomains)
      (hparam : stats.params[i]? = some param)
      (hparamFVar : param = .fvar fv)
      (hdomain : TrExprS env Us scope dom sourceDomain)
      (hdomainType : env.IsType Us.length scope.toCtx sourceDomain)
      (hcompare : env.IsDefEqU Us.length scope.toCtx
        sourceDomain paramType) :
      CheckedConstructorParameterPrefix env Us stats original
        (i + 1) (body.instantiate1 param)
        ((some (fv, deps), .vlam paramType) :: scope)
        (sourceDomains ++ [sourceDomain])

/-- The retained pointwise comparisons assemble into the exact dependent
context conversion from translated concrete constructor domains to cached
family parameter domains. -/
theorem CheckedConstructorParameterPrefix.contextDefEq
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope sourceDomains) :
    env.IsDefEqCtx Us.length [] sourceDomains.reverse scope.toCtx := by
  induction H with
  | zero => exact .zero
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    have hcompareAtSort :=
      hcompare.of_l henv (ih.symm henv.ordered).isType
        (Classical.choose_spec hdomainType)
    have hcompareAtSource :=
      hcompareAtSort.defeqDFC henv.ordered (ih.symm henv.ordered)
    simpa [VLCtx.toCtx, List.reverse_append] using
      (VEnv.IsDefEqCtx.succ ih hcompareAtSource)

/-- Ordinary environment extension preserves the exact checked parameter
trace, including the executable comparison witnesses. -/
theorem CheckedConstructorParameterPrefix.mono
    (henv : env ≤ env')
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope sourceDomains) :
    CheckedConstructorParameterPrefix env' Us stats original
      i current scope sourceDomains := by
  induction H with
  | zero => exact .zero
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    exact .step ih hparam hparamFVar (hdomain.mono henv) (hdomainType.mono henv)
      (hcompare.mono henv)

/-- A successful cached-parameter comparison advances the semantic
constructor telescope directly.  The executable loop performs no
normalization in this branch: after converting the binder context from the
source domain to the cached parameter type, opening the source body with the
cached free variable supplies the next residual verbatim. -/
theorem checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.consumeConstructorParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom,
      TrExprS env Us scope dom sourceDom ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom paramType) :
    ∃ next,
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0) := by
  cases htype with
  | forallE hdomType _hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom, hsourceDom, hsourceDomEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    rcases hbody.defeqDFC henv hbodyCtx with ⟨next, hnext⟩
    have hopened : TrExprS env Us
        ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next :=
      hnext.inst_fvar henv.ordered hscopeWF
    have hbodyWF : VLCtx.WF env Us.length
        ((none, .vlam paramType) :: scope) :=
      ⟨H.scopeWF, nofun, ⟨_, hdomTyped.hasType.2⟩⟩
    have hnextRefl : env.IsDefEqU Us.length
        (paramType :: scope.toCtx) next next :=
      hnext.wf henv.ordered hbodyWF
    have hindices : H.indices = [] :=
      List.eq_nil_of_length_eq_zero H.indexCount
    have htype' : TrExprS env Us scope
        (.forallE name dom body bi) (.forallE _ _) :=
      .forallE hdomType _hbodyType hdom hbody
    rcases H.consumeParameter (name := name) (bi := bi)
        henv hindices htype' hscopeWF
        ⟨sourceDom, hsourceDom, hsourceDomEq⟩
        ⟨next, next, hnext, hopened, hnextRefl⟩ with
      ⟨next', hopened', Hnext⟩
    exact ⟨next', hopened', Hnext⟩

/-- Traverse the executable constructor's common-parameter prefix while
building its independent semantic telescope.  The two callbacks isolate the
control-flow boundaries: exact parameter coverage hands the synthesized tail
to the field verifier, while an early non-forall is discharged separately by
the invalid-result argument. -/
theorem checkConstructors.loopCtor.parameterSynthesisWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    {original : Expr}
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Q : Unit → Prop)
    (Hresult : ∀ {source' : Expr}
        {current' fullCurrent' : VExpr} {fuel' : Nat}
        {sourceDomains : List VExpr},
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0) →
      TrExprS Hc.venv c.lparams Hsuffix.parameterDecls source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      RecursorParamSegment stats 0 decl.nparams original source' →
      CheckedConstructorParameterPrefix Hc.venv c.lparams stats original
        decl.nparams source' Hsuffix.parameterDecls sourceDomains →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' decl.nparams (fuel' + 1) c).WF Q)
    (Hearly : ∀ {source' : Expr} {scope' : VLCtx}
        {current' fullCurrent' : VExpr} {i' fuel' : Nat}
        {sourceDomains : List VExpr},
      i' < decl.nparams →
      (¬ ∃ name dom body bi, source' = .forallE name dom body bi) →
      checkInductiveTypes.loopType.LaterParameterScope
        Hsuffix i' source' →
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          scope' current' i' 0) →
      TrExprS Hc.venv c.lparams scope' source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      CheckedConstructorParameterPrefix Hc.venv c.lparams stats original
        i' source' scope' sourceDomains →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' i' (fuel' + 1) c).WF Q)
    (hparams : stats.params.size = decl.nparams)
    (hbound : i ≤ decl.nparams)
    (Hsegment : RecursorParamSegment stats 0 i original source)
    (Hscope : ∀ h : i < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix i source)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = decl.nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      source fullCurrent)
    {sourceDomains : List VExpr}
    (Hcomparisons : CheckedConstructorParameterPrefix Hc.venv c.lparams
      stats original i source scope sourceDomains) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i fuel c).WF Q := by
  induction fuel generalizing source scope current fullCurrent i sourceDomains with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hi : i < decl.nparams
    · have histats : i < stats.params.size := by
        simpa [hparams] using hi
      by_cases hforall : ∃ name dom body bi,
          source = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        cases htypeNarrow with
        | @forallE narrowDom narrowBody _ _ _ _ _
            hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨fullDom, fullBody, hdomFull, hbodyFull,
              _hdomFullType, _hbodyFullType, _hfullCurrent⟩
          rcases Hcurrent.typing with
            ⟨paramTy, paramTy', param', hget, hparamTy,
              hparamTyEq, hparam, hparamType⟩
          have hparamAt : stats.params[i]? = some stats.params[i]! := by
            simp [Array.getElem!_eq_getD, histats]
          refine checkConstructors.loopCtor.parameter.sourceWF
            (Q := Q) Hc hparamAt hget hdomFull hbodyFull
              hparamTy hparam hparamType ?_
          intro heq hopenedFull
          rcases Hcurrent.domainDefEq hdomFull hparamTyEq heq with
            ⟨sourceDom, hsourceDom, hsourceDomEq⟩
          have hconsumedWF : VLCtx.WF Hc.venv c.lparams.length
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older) :=
            Hcurrent.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
          have htypeNarrow' : TrExprS Hc.venv c.lparams Hcurrent.older
              (.forallE name dom body bi) (.forallE narrowDom narrowBody) :=
            .forallE hdomNarrowType hbodyNarrowType
              hdomNarrow hbodyNarrow
          rcases Hsynthesis.consumeConstructorParameter
              (name := name) (bi := bi)
              Hc.checking.tr.wf
              htypeNarrow'
              hconsumedWF
              ⟨sourceDom, hsourceDom, hsourceDomEq⟩ with
            ⟨next, hopenedNarrow, ⟨Hsynthesis'⟩⟩
          have hopenedNarrow' : TrExprS Hc.venv c.lparams
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (body.instantiate1 stats.params[i]!) next := by
            simpa [Expr.instantiate1_eq, Hcurrent.parameter] using
              hopenedNarrow
          have hsourceDomType : Hc.venv.IsType c.lparams.length
              Hcurrent.older.toCtx sourceDom :=
            hdomNarrowType.defeqU_l Hc.checking.tr.wf
              Hsynthesis.scopeWF.toCtx
              (hdomNarrow.uniq Hc.checking.tr.wf
                (.refl Hc.checking.tr.wf Hsynthesis.scopeWF)
                hsourceDom)
          have Hcomparisons' : CheckedConstructorParameterPrefix
              Hc.venv c.lparams stats original (i + 1)
              (body.instantiate1 stats.params[i]!)
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (sourceDomains ++ [sourceDom]) :=
            .step Hcomparisons hparamAt Hcurrent.parameter hsourceDom hsourceDomType
              hsourceDomEq
          let Hbody :
              checkInductiveTypes.loopType.LaterParameterScope
                Hsuffix i body :=
            { Hcurrent with fvars := Hcurrent.fvars.2 }
          exact ih (i := i + 1)
            (scope := (some (Hcurrent.fv, Hcurrent.deps),
              .vlam Hcurrent.paramType) :: Hcurrent.older)
            (current := next) (fullCurrent := fullBody.inst param')
            (hbound := by omega)
            (Hscope := fun hlt => Hbody.next hlt (fun _ _ h => h))
            (hscopeEq := fun hlt =>
              Hbody.nextOlder (Hbody.next hlt (fun _ _ h => h)) hlt)
            (hcompleteScope := fun heq => by
              have hdone : i + 1 = stats.params.size := by
                rw [hparams]
                exact heq
              exact Hbody.completedScope hdone)
            (Hsegment := Hsegment.push hparamAt)
            Hsynthesis' hopenedNarrow'
            (hopenedFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            Hcomparisons'
      · exact Hearly hi hforall (Hscope histats)
          Hsynthesis htypeNarrow htypeFull Hcomparisons
    · have hieq : i = decl.nparams := by omega
      subst i
      have hscope := hcompleteScope rfl
      subst scope
      exact Hresult Hsynthesis htypeNarrow htypeFull Hsegment Hcomparisons

theorem _root_.Lean4Lean.FVarsIn.getAppArgsList
    (H : FVarsIn P e) (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  have H' : FVarsIn P
      (e.getAppFn.mkAppRevList e.getAppArgsRevList) := by
    rw [Expr.mkAppRevList_getAppArgsRevList]
    exact H
  have ha' : a ∈ e.getAppArgsRevList := by
    simpa [← Expr.getAppArgsList_reverse] using ha
  exact (FVarsIn.appRevList.mp H').2 a ha'

theorem _root_.Lean4Lean.FVarsIn.getAppFn
    (H : FVarsIn P e) : FVarsIn P e.getAppFn := by
  have H' : FVarsIn P (e.getAppFn.mkAppList e.getAppArgsList) := by
    rw [Expr.mkAppList_getAppArgsList]
    exact H
  exact (FVarsIn.mkAppList.mp H').1

/-- Abstracting a free variable removes precisely that variable from the
free-variable obligation. This is the structural lemma needed for nested
parameter replacement, whose runtime `Expr.abstract` boundary is opaque. -/
theorem _root_.Lean4Lean.FVarsIn.abstract1_of
    (H : FVarsIn (fun fv => fv = selected ∨ P fv) e) :
    FVarsIn P (Expr.abstract1 selected e k) := by
  induction e generalizing k <;>
    simp_all [Lean4Lean.FVarsIn, Expr.abstract1]
  case fvar fv =>
    split
    · trivial
    · rename_i hne
      rcases H with heq | hP
      · subst fv
        simp at hne
      · exact hP

/-- Abstracting a list of selected variables removes the entire selection
from the free-variable obligation. -/
theorem _root_.Lean4Lean.FVarsIn.abstractList_of
    (H : FVarsIn (fun fv => fv ∈ selected ∨ P fv) e) :
    FVarsIn P (e.abstractList selected k) := by
  induction selected generalizing e with
  | nil => simpa [Expr.abstractList] using H
  | cons selected rest ih =>
    simp only [Expr.abstractList]
    apply ih
    apply FVarsIn.abstract1_of
    exact H.mono fun fv hfv => by
      rcases hfv with hmem | hP
      · rcases List.mem_cons.mp hmem with heq | hrest
        · exact Or.inl heq
        · exact Or.inr (Or.inl hrest)
      · exact Or.inr (Or.inr hP)

/-- Closing a recent all-lambda prefix removes every free variable introduced
by that prefix.  The declaration typing stored in `MLCtx.WF` supplies the
induction step for binder domains; abstracting the current free variable
supplies it for the body. -/
theorem MLCtxOnlyLams.mkForall_fvarsIn_dropN
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us)
    (n : Nat) (hn : n ≤ m.length) (body : Expr)
    (Hbody : body.FVarsIn (· ∈ m.vlctx.fvars)) :
    (m.mkForall n hn body).FVarsIn
      (· ∈ (m.dropN n hn).vlctx.fvars) := by
  induction n generalizing m body with
  | zero => simpa using Hbody
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      have htail := Nat.le_of_succ_le_succ hn
      apply ih H.tail_vlam Hwf.1 htail
      constructor
      · exact Hwf.2.2.1.fvarsIn
      · apply FVarsIn.abstract1_of
        exact Hbody.mono fun current hcurrent => by
          simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
            List.mem_cons] at hcurrent
          exact hcurrent
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- A front retained by narrow index synthesis closes back to its narrow
base, even when the executable `MLCtx` contains an interleaved ambient
prefix below that front.  `FrontFVLift` retains the decisive fact that each
new concrete domain depends only on the preceding narrow scope, while the
context equality identifies those dependency lists with the executable
declarations selected by `MLCtx.mkForall`. -/
theorem _root_.Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift.mkForall_fvarsIn_sourceBase
    {sourceDomains expandedDomains : List VExpr}
    {scope expanded : VLCtx} {shift : Lift}
    {m : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift
      sourceDomains expandedDomains scope expanded shift)
    (Hm : MLCtxOnlyLams m) (Hmwf : m.WF env Us)
    (Hctx : VLCtx.IsDefEq env Us.length expanded m.vlctx)
    (hn : sourceDomains.length ≤ m.length) (body : Expr)
    (Hbody : body.FVarsIn (· ∈ scope.fvars)) :
    (m.mkForall sourceDomains.length hn body).FVarsIn
      (· ∈ VLCtx.fvars (scope.drop sourceDomains.length)) := by
  induction H generalizing m body with
  | zero => simpa using Hbody
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    cases m with
    | nil => cases Hctx
    | vlam current name type type' bi tail =>
      cases Hctx with
      | cons Htail _ _ =>
        have hnTail : sourceDomains.length ≤ tail.length := by
          apply Nat.le_of_succ_le_succ
          simpa using hn
        have Hdomain : type.FVarsIn (· ∈ scope.fvars) := by
          apply fvarsIn_iff.mpr
          refine ⟨hdeps, ?_⟩
          exact Hmwf.2.2.1.fvarsIn.mono fun _ _ => trivial
        have Habstract : (body.abstract1 fv).FVarsIn
            (· ∈ scope.fvars) := by
          apply FVarsIn.abstract1_of
          exact Hbody.mono fun current hcurrent => by
            simpa only [VLCtx.fvars_cons_some, List.mem_cons] using hcurrent
        simpa only [List.length_append, List.length_singleton,
          Nat.add_one, TypeChecker.MLCtx.mkForall,
          TypeChecker.MLCtx.dropN, List.drop_succ_cons] using
          ih Hm.tail_vlam Hmwf.1 Htail hnTail
            (.forallE name type (body.abstract1 fv) bi)
            ⟨Hdomain, Habstract⟩
    | vlet current name type value type' value' tail =>
      exact Hm.vlet_false.elim

theorem _root_.Lean4Lean.FVarsIn.abstract_fvarArray_of
    (fvars : List FVarId) (selected : Array Expr)
    (hselected : selected = (fvars.map Expr.fvar).toArray)
    (H : FVarsIn (fun fv => fv ∈ fvars ∨ P fv) e) :
    FVarsIn P (e.abstract selected) := by
  rw [hselected, Expr.abstract_eq]
  exact H.abstractList_of

/-- `instantiateRev` introduces no free variables beyond those already in
the body and substitution array. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRev
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRev subst) := by
  rw [Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply He.instantiateList
  intro a ha
  apply Hsubst a
  simpa using ha

/-- Range-restricted reverse instantiation has the same free-variable
discipline as the underlying simultaneous instantiation. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRevRange
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRevRange start stop subst) := by
  rw [Expr.instantiateRevRange_eq]
  apply He.instantiateRev
  intro a ha
  rcases Array.mem_iff_getElem.mp ha with ⟨i, hi, heq⟩
  have hi' : start + i < subst.size := by
    rw [Array.size_extract] at hi
    have hmin := Nat.min_le_right stop subst.size
    omega
  apply Hsubst a
  rw [← heq, Array.getElem_extract]
  exact Array.getElem_mem hi'

/-- Replacing universe parameters by universe expressions without metavariables
does not introduce a universe metavariable. -/
theorem _root_.Lean.Level.substParams'_hasMVar_false
    (Hu : u.hasMVar' = false)
    (Hs : ∀ name, (s name).hasMVar' = false) :
    (Lean.Level.substParams' s red u).hasMVar' = false := by
  induction u generalizing red with
  | zero | param | mvar => simp_all [Lean.Level.substParams', Lean.Level.hasMVar']
  | succ u ih =>
      simp only [Lean.Level.substParams', Lean.Level.hasMVar'] at Hu ⊢
      exact ih Hu
  | max u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]
  | imax u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelIMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]

/-- Universe-parameter instantiation preserves the expression free-variable
predicate when every supplied universe is metavariable-free. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateLevelParams
    (He : FVarsIn P e)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false) :
    FVarsIn P (e.instantiateLevelParams levelParams levels) := by
  rw [Expr.instantiateLevelParams_eq]
  have Hsubst : ∀ name,
      (((levelParams.idxOf? name).bind fun i => levels[i]?).getD
        (.param name)).hasMVar' = false := by
    intro name
    cases hidx : levelParams.idxOf? name with
    | none => simp [hidx, Lean.Level.hasMVar']
    | some i =>
      cases hget : levels[i]? with
      | none => simp [hidx, hget, Lean.Level.hasMVar']
      | some level =>
        simp only [hidx, Option.bind_some, hget, Option.getD_some]
        have hi : i < levels.length := by
          by_contra hnot
          have hnone := List.getElem?_eq_none (Nat.le_of_not_gt hnot)
          rw [hget] at hnone
          contradiction
        have heq : levels[i]'hi = level := by
          rw [← Option.some.injEq, ← hget]
          exact (List.getElem?_eq_getElem hi).symm
        exact Hlevels level (heq ▸ List.getElem_mem hi)
  induction e <;>
    simp_all [Expr.instantiateLevelParamsCore', Lean4Lean.FVarsIn,
      Lean.Level.substParams'_hasMVar_false]

theorem _root_.Lean4Lean.FVarsIn.mkAppRange_zero
    (hn : n ≤ args.size) (Hfn : FVarsIn P fn)
    (Hargs : ∀ arg ∈ args, FVarsIn P arg) :
    FVarsIn P (mkAppRange fn 0 n args) := by
  rw [Expr.mkAppRange_eq (l₁ := []) (l₂ := args.toList.take n)
    (l₃ := args.toList.drop n)]
  · rw [FVarsIn.mkAppList]
    refine ⟨Hfn, ?_⟩
    intro arg harg
    apply Hargs arg
    apply Array.mem_toList_iff.mp
    exact List.mem_of_mem_take harg
  · simpa using (List.take_append_drop n args.toList).symm
  · rfl
  · simp [List.length_take, Nat.min_eq_left (by simpa using hn)]

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl

/-- A constructor cannot reach its result before consuming every cached
parameter.  A valid result application would contain the current cached free
variable as argument `i`, whereas `LaterParameterScope` proves that the tail
can mention only the strictly older cached parameters. -/
theorem checkConstructors.loopCtor.earlyParameterResult.WF
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Hscope : checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix i source)
    (hi : i < stats.params.size)
    (hforall : ¬ ∃ name dom body bi,
      source = .forallE name dom body bi) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i (fuel + 1) c).WF Q := by
  cases hvalid : AddInductive.isValidIndAppIdx stats source targetIdx
  · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
  · have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hiArgs : i < source.getAppArgs.size := by omega
    have hparam : stats.params[i] = .fvar Hscope.fv := by
      have hparam' := Hscope.parameter
      simpa [hi] using hparam'
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hi
    rw [hparam] at hargEq
    have harg : source.getAppArgs[i] = .fvar Hscope.fv :=
      Expr.eqv_fvar_eq hargEq
    have hsourceArg : source.getAppArgsList[i]? =
        some source.getAppArgs[i] := by
      rw [← Expr.getAppArgs_toList]
      simp [hiArgs]
    have hmem : source.getAppArgs[i] ∈ source.getAppArgsList :=
      List.mem_of_getElem? hsourceArg
    have hargScope := Hscope.fvars.getAppArgsList hmem
    rw [harg] at hargScope
    have hsuffixWF := Hscope.lift.wf Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf
    have hfresh : Hscope.fv ∉ Hscope.older.fvars :=
      (hsuffixWF.2.1 Hscope.fv Hscope.deps rfl).1
    exact False.elim (hfresh hargScope)

/-- Constructor-tail refinement in the independent parameter/field scope.
The executable traversal remains in the retained mutual-header context, but
the resulting `CtorTailWF` never mentions those ambient declarations. -/
theorem checkConstructors.loopCtor.tailRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {scope : VLCtx} {depth : Nat} {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => ConstructorTailCertificate Hc.venv decl target
        scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : dom.consumeTypeAnnotationsVerified.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesNarrow
              (ctor := ctor) (idx := i) Hc Hruntime Hstats
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun _ => ConstructorTailCertificate Hc.venv decl target
                scope.toCtx depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull Hpos ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound hpositive bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotationsVerified.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotationsVerified.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats'
              (htargetLookup := by
                change Hc.venv.constants target.name = some target.toVConstant
                exact htargetLookup)
              (htargetWF := by
                change target.toVConstant.WF Hc.venv
                exact htargetWF)
              (htargetShape := by
                change decl.TypeShape Hc.venv params target
                exact htargetShape)
              hparamNext hlit hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              change ConstructorTailCertificate Hc.venv decl target
                (narrowDom :: scope.toCtx) (depth + 1) narrowBody at htail
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact {
                shape := .field
                  (by simpa [Hstats.uvars] using hfieldNarrow)
                  (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                  (Or.inr hpositive)
                  (by simpa [Hstats.uvars] using hfieldEq)
                  (by simpa [Hstats.uvars] using hbodyTyped)
                  htail.shape
                isType := VEnv.IsType.forallE
                  ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  htail.isType }
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun _ => ConstructorTailCertificate Hc.venv decl target
                scope.toCtx depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotationsVerified.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotationsVerified.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats'
              (htargetLookup := by
                change Hc.venv.constants target.name = some target.toVConstant
                exact htargetLookup)
              (htargetWF := by
                change target.toVConstant.WF Hc.venv
                exact htargetWF)
              (htargetShape := by
                change decl.TypeShape Hc.venv params target
                exact htargetShape)
              hparamNext hlit hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              change ConstructorTailCertificate Hc.venv decl target
                (narrowDom :: scope.toCtx) (depth + 1) narrowBody at htail
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact {
                shape := .field
                  (by simpa [Hstats.uvars] using hfieldNarrow)
                  (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                  (Or.inl (hunsafe rfl))
                  (by simpa [Hstats.uvars] using hfieldEq)
                  (by simpa [Hstats.uvars] using hbodyTyped)
                  htail.shape
                isType := VEnv.IsType.forallE
                  ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  htail.isType }
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · rcases htrNarrow.wf Hc.checking.tr.wf
          (Hruntime.scopeWF Hc.checking.tr.wf) with ⟨exprType, htype⟩
        have hisType := checkPositivityStep.isValidIndAppIdx.isType
          Hstats hi htrNarrow hvalid (by simpa [htarget] using htargetUvars)
          (by simpa [htarget] using htargetLookup)
          (by simpa [htarget] using htargetWF)
          (by simpa [htarget] using htargetShape)
          Hc.checking.tr.wf (Hruntime.scopeWF Hc.checking.tr.wf)
        have Hshape := checkConstructors.loopCtor.result.refines
          (c := c) (fuel := fuel) (i := i) (ctor := ctor)
          (isUnsafe := isUnsafe) Hstats hi htrNarrow
          hforall hvalid hlit
          (Hruntime.noIndConsts (decl.types.map (·.name)))
          (by simpa [Hstats.uvars] using htype)
        subst target
        exact Hshape.mono fun _ hshape =>
          ⟨hshape, by simpa [Hstats.uvars] using hisType⟩

/-- Aggregation boundary for constructors: once the common-parameter prefix
has supplied its independent `takeForalls` and parameter-conversion facts, the
verified executable tail establishes the public `CtorShape` judgment. -/
theorem checkConstructors.loopCtor.ctorShapeRefines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ownParams.reverse)
    (htailEq : type' = tail)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesFull
    (ctor := ctor) (fuel := fuel) Hc Hstats hi
    htarget hparamAt hconsume hlit hctx hunsafe hbound htr
  exact Htail.mono fun _ htail => by
    subst type'
    have hctxRefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        Hc.mlctx.vlctx.toCtx Hc.mlctx.vlctx.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hc.mlctx_wf.tr.wf.toCtx)
    exact ⟨normalized, ownParams, tail, exprType,
      Hc.mlctx.vlctx.toCtx, hctor, htake, hparams,
      by rw [← hctxEq]; exact hctxRefl, htail⟩

/-- Public constructor-shape refinement from the independent cached-parameter
scope.  `tailCtx` is allowed to be definitionally equal to the normalized
constructor parameters, which is the semantic relation supplied by mutual
header materialization. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType narrowType fullType : VExpr}
    {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      ownParams.reverse scope.toCtx)
    (htailEq : narrowType = tail)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type) := by
  have Htail := checkConstructors.loopCtor.tailRefinesNarrow
    (params := params) (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi
    htarget htargetUvars htargetLookup htargetWF htargetShape hparamAt
    hconsume hlit hunsafe hbound htrNarrow htrFull
  exact Htail.mono fun _ htail => by
    subst narrowType
    have hrebuild := (VExpr.takeForalls_rebuild htake).1
    have htailType : Hc.venv.IsType decl.uvars ownParams.reverse tail :=
      htail.isType.defeqDFC Hc.checking.tr.wf.ordered
        (htailCtx.symm Hc.checking.tr.wf.ordered)
    have hnormalizedType : Hc.venv.IsType decl.uvars [] normalized := by
      rw [hrebuild]
      exact VEnv.IsType.wrapForalls
        (by simpa using htailCtx.isType) (by simpa using htailType)
    have hctorType : Hc.venv.IsType decl.uvars [] ctorVal.type :=
      hnormalizedType.defeqU_l Hc.checking.tr.wf (by trivial)
        ⟨exprType, hctor.symm⟩
    exact ⟨⟨normalized, ownParams, tail, exprType, scope.toCtx,
      hctor, htake, hparams, htailCtx, htail.shape⟩, hctorType⟩

/-- Close a completely consumed constructor-parameter synthesis directly
against the verified field tail.  In particular, the normalized constructor
type and its `takeForalls` decomposition are outputs of the synthesis
certificate rather than assumptions reconstructed by the caller. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    {source : Expr} {current fullType : VExpr} {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current decl.nparams 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[decl.nparams]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hparams : decl.ParamsDefEq Hc.venv params Hsynthesis.params)
    (htrNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source decl.nparams fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type) := by
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have htake :
      (VExpr.wrapForalls Hsynthesis.params current).takeForalls decl.nparams =
        some (Hsynthesis.params, current) := by
    simpa [Hsynthesis.parameterCount] using
      VExpr.takeForalls_wrapForalls Hsynthesis.params current
  have htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      Hsynthesis.params.reverse scope.toCtx := by
    have hrefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        scope.toCtx scope.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hsynthesis.scopeWF.toCtx)
    simpa [Hsynthesis.scopeCtx, hindices] using hrefl
  apply checkConstructors.loopCtor.ctorShapeRefinesNarrow
    (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi htarget
    htargetUvars htargetLookup htargetWF htargetShape
    hparamAt hconsume hlit hunsafe hbound
    (normalized := VExpr.wrapForalls Hsynthesis.params current)
    (tail := current) (exprType := Hsynthesis.exprType)
    (ownParams := Hsynthesis.params)
  · simpa [constructorTelescopeTarget, hindices, Hstats.uvars] using
      Hsynthesis.header
  · exact htake
  · exact hparams
  · exact htailCtx
  · rfl
  · exact htrNarrow
  · exact htrFull

/-- End-to-end constructor telescope refinement in a single verifier
environment.  The source constructor is independently translated in the
empty scope; the executable closed-type result supplies its retained-runtime
translation.  Cached common parameters are consumed by
`parameterSynthesisWF`, and all remaining binders are checked by the narrow
positivity refinement. -/
theorem checkConstructors.loopCtor.refinesCtorShape
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (Hctor : TrSourceConstRaw Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun _ => ∃ tail tailTarget,
        RecursorParamPrefix stats 0 source tail ∧
        ∃ sourceDomains,
        CheckedConstructorParameterPrefix Hc.venv c.lparams stats source
          decl.nparams tail Hsuffix.parameterDecls sourceDomains ∧
        TrExprS Hc.venv c.lparams Hsuffix.parameterDecls tail tailTarget ∧
        ConstructorTailCertificate Hc.venv decl target
          Hsuffix.parameterDecls.toCtx 0 tailTarget ∧
        Nonempty
          (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls tailTarget stats.params.size 0) ∧
        decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  by_cases hzero : decl.nparams = 0
  ·
    have hscopeLength : Hsuffix.parameterDecls.length = 0 := by
      simpa [Hstats.params_size, hzero] using
        Hsuffix.parameterDecls_length
    have hscope : Hsuffix.parameterDecls = [] :=
      List.eq_nil_of_length_eq_zero hscopeLength
    have hparams : decl.ParamsDefEq Hc.venv params [] := by
      change VEnv.IsDefEqCtx Hc.venv decl.uvars [] params.reverse []
      simpa [hscope, VLCtx.toCtx] using hparamsCtx
    have hctorWF : Hc.venv.IsDefEqU c.lparams.length []
        ctorVal.type ctorVal.type :=
      Hctor.type.wf Hc.checking.tr.wf.ordered (by trivial)
    rcases hctorWF with ⟨exprType, hctorTyped⟩
    cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hparamAt : stats.params[0]? = none := by
        rw [Array.getElem?_eq_none_iff]
        rw [Hstats.params_size, hzero]
        omega
      have Hshape :
          (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor
            targetIdx source 0 (fuel + 1) c).WF
            (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
              Hc.venv.IsType decl.uvars [] ctorVal.type) := by
        exact checkConstructors.loopCtor.ctorShapeRefinesNarrow
          (decl := decl) (ctorVal := ctorVal) (params := params)
          (type := source) (i := 0) (ctor := ctor) (fuel := fuel + 1) Hc
          (narrowType := ctorVal.type) (fullType := fullType)
          (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix)
          Hstats hi htarget htargetUvars htargetLookup htargetWF htargetShape
          hparamAt
          hconsume hlit hunsafe hbound
          (normalized := ctorVal.type) (tail := ctorVal.type)
          (exprType := exprType) (ownParams := [])
          (by simpa [Hstats.uvars] using hctorTyped)
          (by rw [hzero]; rfl) hparams
          (by
            rw [hscope]
            change VEnv.IsDefEqCtx Hc.venv decl.uvars [] [] []
            exact VEnv.IsDefEqCtx.refl (by trivial))
          rfl (by simpa [hscope] using Hctor.type)
          (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      have Htail := checkConstructors.loopCtor.tailRefinesNarrow
        (params := params) (type := source) (i := 0) (ctor := ctor)
        (fuel := fuel + 1) Hc
        (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix)
        Hstats hi htarget htargetUvars htargetLookup htargetWF
        htargetShape hparamAt hconsume hlit hunsafe hbound
        (by simpa [hscope] using Hctor.type)
        (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      intro out hout
      have Hchecked := Hshape out hout
      have Htail' := Htail out hout
      let Hinitial := ConstructorSynthesisState.initial Hctor
        (by simpa [Hstats.uvars] using Hchecked.2)
      exact ⟨source, ctorVal.type,
        .done (by rw [Hstats.params_size, hzero]),
        [], by simpa [hzero, hscope] using
          (CheckedConstructorParameterPrefix.zero :
            CheckedConstructorParameterPrefix Hc.venv c.lparams stats source
              0 source [] []),
        by simpa [hscope] using Hctor.type,
        by simpa [hscope] using Htail',
        by simpa [hscope, Hstats.params_size, hzero] using
          (show Nonempty _ from ⟨Hinitial⟩),
        Hchecked⟩
  by_cases hforall : ∃ name dom body bi,
      source = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have htype : Hc.venv.IsType c.lparams.length [] ctorVal.type := by
      rcases TrExpr.forallE_source
          (Hctor.type.trExpr Hc.checking.tr.wf (by trivial)) with
        ⟨dom', body', _hdom, _hbody, hdomType, hbodyType, heq⟩
      exact (VEnv.IsType.forallE hdomType hbodyType).defeqU_l
        Hc.checking.tr.wf (by trivial) heq
    let Hinitial := ConstructorSynthesisState.initial Hctor htype
    apply checkConstructors.loopCtor.parameterSynthesisWF
      (decl := decl) (ctorVal := ctorVal) Hc
      (Q := fun _ => ∃ tail,
        ∃ tailTarget,
        RecursorParamPrefix stats 0 (.forallE name dom body bi) tail ∧
        ∃ sourceDomains,
        CheckedConstructorParameterPrefix Hc.venv c.lparams stats
          (.forallE name dom body bi) decl.nparams tail
          Hsuffix.parameterDecls sourceDomains ∧
        TrExprS Hc.venv c.lparams Hsuffix.parameterDecls tail tailTarget ∧
        ConstructorTailCertificate Hc.venv decl target
          Hsuffix.parameterDecls.toCtx 0 tailTarget ∧
        Nonempty
          (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls tailTarget stats.params.size 0) ∧
        decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type)
      (Hresult := by
        intro source' current' fullCurrent' fuel' sourceDomains
          Hsynthesis' htrNarrow htrFull Hsegment' Hcomparisons
        have hindices : Hsynthesis'.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis'.indexCount
        have hscopeCtx : Hsuffix.parameterDecls.toCtx =
            Hsynthesis'.indices.reverse ++ Hsynthesis'.params.reverse :=
          @checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.scopeCtx
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls current' decl.nparams 0 Hsynthesis'
        have hparams : decl.ParamsDefEq Hc.venv
            params Hsynthesis'.params := by
          change VEnv.IsDefEqCtx Hc.venv decl.uvars []
            params.reverse Hsynthesis'.params.reverse
          simpa [hscopeCtx, hindices] using hparamsCtx
        have hparamAt : stats.params[decl.nparams]? = none := by
          rw [Array.getElem?_eq_none_iff]
          exact Nat.le_of_eq Hstats.params_size
        have Hshape :
            (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor
              targetIdx source' decl.nparams (fuel' + 1) c).WF
              (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
                Hc.venv.IsType decl.uvars [] ctorVal.type) := by
          exact checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
            (ctor := ctor) (fuel := fuel' + 1) Hc
            (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
              Hc Hsuffix)
            Hstats Hsynthesis' hi htarget htargetUvars htargetLookup
            htargetWF htargetShape hparamAt hconsume hlit hunsafe
            hbound hparams htrNarrow htrFull
        have Htail := checkConstructors.loopCtor.tailRefinesNarrow
          (params := params) (type := source') (i := decl.nparams)
          (ctor := ctor) (fuel := fuel' + 1) Hc
          (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix)
          Hstats hi htarget htargetUvars htargetLookup htargetWF
          htargetShape hparamAt hconsume hlit hunsafe hbound
          htrNarrow htrFull
        intro out hout
        have Hchecked := Hshape out hout
        have Htail' := Htail out hout
        have HsegmentComplete : RecursorParamSegment stats 0
            stats.params.size (.forallE name dom body bi) source' := by
          simpa only [Hstats.params_size] using Hsegment'
        exact ⟨source', current', HsegmentComplete.complete rfl,
          sourceDomains, Hcomparisons, htrNarrow, Htail',
          by simpa [Hstats.params_size] using
            (show Nonempty _ from ⟨Hsynthesis'⟩),
          Hchecked⟩)
      (Hearly := by
        intro source' scope' current' fullCurrent' i' fuel' sourceDomains hi'
          hforall Hscope' _Hsynthesis' _htrNarrow _htrFull _Hcomparisons
        exact checkConstructors.loopCtor.earlyParameterResult.WF
          (fuel := fuel') Hc Hscope'
          (by simpa [Hstats.params_size] using hi') hforall)
      Hstats.params_size (by omega) (.done)
      (fun h =>
        checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars h hnoFVars)
      (fun h =>
        (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
          h hnoFVars).older_eq_nil h |>.symm)
      (by
        intro hdone
        have hlength := Hsuffix.parameterDecls_length
        have hempty : Hsuffix.parameterDecls = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [hlength, Hstats.params_size, hdone])
        exact hempty.symm)
      Hinitial Hctor.type
      (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      CheckedConstructorParameterPrefix.zero
  · cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hiStats : 0 < stats.params.size := by
        rw [Hstats.params_size]
        omega
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (Hsuffix := Hsuffix) (fuel := fuel) Hc
        (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
          (Hsuffix := Hsuffix) hiStats hnoFVars)
        (by omega) hforall

/-- Checked concrete parameter replays accumulated within one production
constructor array. -/
structure ConstructorParamPrefixRow
    (stats : AddInductive.InductiveStats) (ctors : List Constructor)
    (done : Nat) : Prop where
  covered : done ≤ ctors.length
  prefixes : ∀ i, i < done → (hi : i < ctors.length) →
    ∃ tail, RecursorParamPrefix stats 0 ctors[i].type tail

def ConstructorParamPrefixRow.empty
    (stats : AddInductive.InductiveStats) (ctors : List Constructor) :
    ConstructorParamPrefixRow stats ctors 0 where
  covered := Nat.zero_le _
  prefixes _ hi := by omega

def ConstructorParamPrefixRow.push
    (H : ConstructorParamPrefixRow stats ctors done)
    (hi : done < ctors.length)
    (Hprefix : RecursorParamPrefix stats 0 ctors[done].type tail) :
    ConstructorParamPrefixRow stats ctors (done + 1) where
  covered := by omega
  prefixes i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact ⟨tail, Hprefix⟩
    · exact H.prefixes i (by omega) hi'

/-- Completed replay rows accumulated across the production mutual-family
array. -/
structure ConstructorParamPrefixRows
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (done : Nat) : Prop where
  covered : done ≤ indTypes.size
  rows : ∀ i, i < done → (hi : i < indTypes.size) →
    ConstructorParamPrefixRow stats indTypes[i].ctors
      indTypes[i].ctors.length

def ConstructorParamPrefixRows.empty
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) :
    ConstructorParamPrefixRows stats indTypes 0 where
  covered := Nat.zero_le _
  rows _ hi := by omega

def ConstructorParamPrefixRows.push
    (H : ConstructorParamPrefixRows stats indTypes done)
    (hi : done < indTypes.size)
    (Hrow : ConstructorParamPrefixRow stats indTypes[done].ctors
      indTypes[done].ctors.length) :
    ConstructorParamPrefixRows stats indTypes (done + 1) where
  covered := by omega
  rows i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hrow
    · exact H.rows i (by omega) hi'

/-- Public completed concrete replay certificate selected by family and
constructor positions. -/
structure CheckedRecursorParameterPrefixes
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) : Prop where
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ∃ tail, RecursorParamPrefix stats 0
      indTypes[familyIdx].ctors[ctorIdx].type tail

def ConstructorParamPrefixRows.complete
    (H : ConstructorParamPrefixRows stats indTypes indTypes.size) :
    CheckedRecursorParameterPrefixes stats indTypes where
  replay familyIdx hfamily ctorIdx hctor :=
    (H.rows familyIdx hfamily hfamily).prefixes ctorIdx hctor hctor

/-- Full independently checked tail replay for one production constructor. -/
def CheckedConstructorTailReplayAt
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (source : Constructor) : Prop :=
  ∃ ctorVal tail tailTarget sourceDomains,
    ctorVal ∈ target.ctors ∧
    TrSourceConstRaw env Us source.name source.type ctorVal ∧
    RecursorParamPrefix stats 0 source.type tail ∧
    CheckedConstructorParameterPrefix env Us stats source.type
      stats.params.size tail scope sourceDomains ∧
    TrExprS env Us scope tail tailTarget ∧
    ConstructorTailCertificate env decl target scope.toCtx 0 tailTarget ∧
    Nonempty
      (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        env Us (constructorTelescopeTarget ctorVal) scope tailTarget
        stats.params.size 0)

structure ConstructorTailReplayRow
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (ctors : List Constructor)
    (done : Nat) : Prop where
  covered : done ≤ ctors.length
  replays : ∀ i, i < done → (hi : i < ctors.length) →
    CheckedConstructorTailReplayAt env Us scope stats decl target ctors[i]

def ConstructorTailReplayRow.empty
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (ctors : List Constructor) :
    ConstructorTailReplayRow env Us scope stats decl target ctors 0 where
  covered := Nat.zero_le _
  replays _ hi := by omega

def ConstructorTailReplayRow.push
    (H : ConstructorTailReplayRow env Us scope stats decl target ctors done)
    (hi : done < ctors.length)
    (Hreplay : CheckedConstructorTailReplayAt env Us scope stats decl target
      ctors[done]) :
    ConstructorTailReplayRow env Us scope stats decl target ctors (done + 1) where
  covered := by omega
  replays i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hreplay
    · exact H.replays i (by omega) hi'

structure ConstructorTailReplayRows
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (indTypes : Array InductiveType) (done : Nat) : Prop where
  size_eq : indTypes.size = decl.types.length
  covered : done ≤ indTypes.size
  rows : ∀ i, i < done → (hi : i < indTypes.size) →
    ConstructorTailReplayRow env Us scope stats decl decl.types[i]
      indTypes[i].ctors indTypes[i].ctors.length

def ConstructorTailReplayRows.empty
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (indTypes : Array InductiveType)
    (hsize : indTypes.size = decl.types.length) :
    ConstructorTailReplayRows env Us scope stats decl indTypes 0 where
  size_eq := hsize
  covered := Nat.zero_le _
  rows _ hi := by omega

def ConstructorTailReplayRows.push
    (H : ConstructorTailReplayRows env Us scope stats decl indTypes done)
    (hi : done < indTypes.size)
    (Hrow : ConstructorTailReplayRow env Us scope stats decl
      (decl.types[done]'(by rw [← H.size_eq]; exact hi))
      indTypes[done].ctors indTypes[done].ctors.length) :
    ConstructorTailReplayRows env Us scope stats decl indTypes (done + 1) where
  size_eq := H.size_eq
  covered := by omega
  rows i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hrow
    · exact H.rows i (by omega) hi'

structure CheckedRecursorConstructorTails
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (indTypes : Array InductiveType) : Prop where
  size_eq : indTypes.size = decl.types.length
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    CheckedConstructorTailReplayAt env Us scope stats decl
      decl.types[familyIdx] indTypes[familyIdx].ctors[ctorIdx]

def ConstructorTailReplayRows.complete
    (H : ConstructorTailReplayRows env Us scope stats decl indTypes
      indTypes.size) :
    CheckedRecursorConstructorTails env Us scope stats decl indTypes where
  size_eq := H.size_eq
  replay familyIdx hfamily ctorIdx hctor :=
    (H.rows familyIdx hfamily hfamily).replays ctorIdx hctor hctor


end VerifyInductive
end Lean4Lean
