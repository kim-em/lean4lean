import Init.Data.Array.Lemmas
import Init.Data.List.Sublist
import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Materializing a source declaration from a prefix of an expanded
declaration's recovered header metadata preserves the index count at every
source position.  This is the metadata-level fact needed after nested
lowering: original families retain their positions, while auxiliary families
are appended to the expanded declaration. -/
theorem VInductDeclSkeleton.materializePrefix_numIndices
    (skeleton : VInductDeclSkeleton) (expanded source : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length)
    (Hmaterialize : skeleton.materialize
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel)) = some source)
    (i : Nat) (hi : i < skeleton.types.length)
    (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).numIndices =
      (expanded.types[i]'hexpanded).numIndices := by
  rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hi with
    ⟨data, hdata, hsourceLookup⟩
  have hmetadata :
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel))[i]? =
        some (expanded.types[i].numIndices,
          expanded.types[i].resultLevel) := by
    simp [hi, hle]
  have hdataEq : data =
      (expanded.types[i].numIndices, expanded.types[i].resultLevel) := by
    rw [hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have hsourceEq : source.types[i] =
      skeleton.types[i].toVInductiveType expanded.types[i].numIndices
        expanded.types[i].resultLevel := by
    rw [List.getElem?_eq_getElem hsource] at hsourceLookup
    exact Option.some.inj hsourceLookup
  have hindices := congrArg VInductiveType.numIndices hsourceEq
  simpa [VInductiveTypeSkeleton.toVInductiveType] using hindices

/-- The original declaration is materialized from exactly the metadata prefix
of an expanded declaration.  Nested lowering appends auxiliary families, so
this is the declaration-level certificate connecting independently recovered
source metadata to the lowered checker result. -/
inductive MaterializedInductivePrefix
    (source expanded : VInductDecl) : Prop
  | intro (skeleton : VInductDeclSkeleton)
      (materialized : skeleton.materialize
        ((expanded.types.take skeleton.types.length).map fun type =>
          (type.numIndices, type.resultLevel)) = some source) :
      MaterializedInductivePrefix source expanded

theorem MaterializedInductivePrefix.numIndices
    {source expanded : VInductDecl}
    (H : MaterializedInductivePrefix source expanded)
    (hle : source.types.length ≤ expanded.types.length)
    (i : Nat) (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).numIndices =
      (expanded.types[i]'hexpanded).numIndices := by
  rcases H with ⟨skeleton, Hmaterialize⟩
  have hskeleton : skeleton.types.length = source.types.length :=
    (VInductDeclSkeleton.materialize_fields Hmaterialize).2.2.2.symm
  apply VInductDeclSkeleton.materializePrefix_numIndices skeleton expanded
    source
  · simpa [hskeleton] using hle
  · exact Hmaterialize
  · simpa [hskeleton] using hsource

/-- Every sufficiently long expanded declaration determines a unique-sized
source materialization from a metadata-free skeleton by taking the expanded
metadata prefix.  This is the constructor used by the outer nested verifier;
the source declaration is produced rather than supplied with unconstrained
semantic arities. -/
theorem VInductDeclSkeleton.materializeExpandedPrefix
    (skeleton : VInductDeclSkeleton) (expanded : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length) :
    ∃ source,
      skeleton.materialize
        ((expanded.types.take skeleton.types.length).map fun type =>
          (type.numIndices, type.resultLevel)) = some source ∧
      MaterializedInductivePrefix source expanded := by
  let metadata :=
    (expanded.types.take skeleton.types.length).map fun type =>
      (type.numIndices, type.resultLevel)
  have hmetadata : metadata.length = skeleton.types.length := by
    simp [metadata, List.length_take, Nat.min_eq_left hle]
  let source : VInductDecl := {
    uvars := skeleton.uvars
    nparams := skeleton.nparams
    types := List.zipWith (fun type data =>
      type.toVInductiveType data.1 data.2) skeleton.types metadata
    isUnsafe := skeleton.isUnsafe }
  have Hmaterialize : skeleton.materialize metadata = some source := by
    simp [VInductDeclSkeleton.materialize, hmetadata, source]
  exact ⟨source, Hmaterialize, ⟨skeleton, Hmaterialize⟩⟩

theorem OnCtx.append_right
    (H : OnCtx (xs ++ ys) P) : OnCtx ys P := by
  induction xs with
  | nil => exact H
  | cons x xs ih => exact ih H.1

/-- A declaration selected below a newer context prefix is looked up at the
prefix length, with one lift for its own binder and one for every newer
declaration. -/
theorem Lookup.append_zero (newer : List VExpr) (domain : VExpr)
    (older : List VExpr) :
    Lookup (newer ++ domain :: older) newer.length
      (domain.liftN (newer.length + 1) 0) := by
  induction newer with
  | nil => simpa [VExpr.liftN] using (Lookup.zero :
      Lookup (domain :: older) 0 domain.lift)
  | cons head newer ih =>
    simpa [VExpr.liftN_succ, Nat.add_assoc] using
      (Lookup.succ (A := head) ih)

theorem VExpr.getAppFnArgs_mkApps
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs =
      let (head, prior) := fn.getAppFnArgs
      (head, prior ++ args) := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args from rfl, ih]
      simp [List.append_assoc]

/-- Rebuilding an expression from its application head and left-to-right
argument list is exact. -/
theorem VExpr.mkApps_getAppFnArgs (e : VExpr) :
    let (fn, args) := e.getAppFnArgs
    VExpr.mkApps fn args = e := by
  have go : ∀ (e : VExpr) (suffix : List VExpr),
      let (fn, args) := VExpr.getAppFnArgs.go e suffix
      VExpr.mkApps fn args = VExpr.mkApps e suffix := by
    intro e
    induction e with
    | app fn arg ihFn _ =>
      intro suffix
      change (let (head, args) :=
        VExpr.getAppFnArgs.go fn (arg :: suffix)
        VExpr.mkApps head args = VExpr.mkApps (.app fn arg) suffix)
      simpa [VExpr.mkApps] using ihFn (arg :: suffix)
    | bvar | sort | const | proj => intro suffix; rfl
    | lam | forallE => intro suffix; rfl
  simpa [VExpr.getAppFnArgs, VExpr.mkApps] using go e []

/-- A dependent function type with exactly `arity` binders and a sort as its
final codomain.  Instantiating term variables preserves this shape because
universe levels do not depend on terms. -/
inductive VExpr.ForallAritySort : Nat → VExpr → Prop
  | zero (level : VLevel) : ForallAritySort 0 (.sort level)
  | succ (domain : VExpr) : ForallAritySort arity body →
      ForallAritySort (arity + 1) (.forallE domain body)

theorem VExpr.ForallAritySort.inst
    (H : ForallAritySort arity type) (arg : VExpr) (k : Nat := 0) :
    ForallAritySort arity (type.inst arg k) := by
  induction H generalizing k with
  | zero => exact .zero _
  | succ domain H ih =>
    simpa [VExpr.inst] using ForallAritySort.succ
      (domain.inst arg k) (ih (k + 1))

theorem VExpr.ForallAritySort.instL
    (H : ForallAritySort arity type) (levels : List VLevel) :
    ForallAritySort arity (type.instL levels) := by
  induction H with
  | zero => exact .zero _
  | succ domain H ih =>
    simpa [VExpr.instL] using ForallAritySort.succ
      (domain.instL levels) ih

theorem VExpr.ForallAritySort.wrapForalls
    (domains : List VExpr) (level : VLevel) :
    ForallAritySort domains.length
      (VExpr.wrapForalls domains (.sort level)) := by
  induction domains with
  | nil => exact .zero level
  | cons domain domains ih =>
    simpa [VExpr.wrapForalls] using ForallAritySort.succ domain ih

theorem VExpr.takeForalls_rebuild
    (H : type.takeForalls arity = some (domains, result)) :
    type = VExpr.wrapForalls domains result ∧ domains.length = arity := by
  induction arity generalizing type domains result with
  | zero =>
    change some ([], type) = some (domains, result) at H
    have hp : ([], type) = (domains, result) := Option.some.inj H
    cases hp
    exact ⟨rfl, rfl⟩
  | succ arity ih =>
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls arity with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rcases out with ⟨tailDomains, tailResult⟩
        rw [VExpr.takeForalls, htail] at H
        change some (domain :: tailDomains, tailResult) =
          some (domains, result) at H
        have hp : (domain :: tailDomains, tailResult) =
            (domains, result) := Option.some.inj H
        cases hp
        rcases ih htail with ⟨hrebuild, hlength⟩
        exact ⟨by simp [VExpr.wrapForalls, hrebuild], by simp [hlength]⟩
    | proj typeName index struct => simp [VExpr.takeForalls] at H
    | bvar | sort | const | app | lam => simp [VExpr.takeForalls] at H

/-- Split one successful telescope decomposition at an arbitrary intermediate
arity.  This lets a total translated recursor telescope be recovered as its
parameter, motive, minor, index, and major groups without inspecting binder
domains. -/
theorem VExpr.takeForalls_split
    {type result : VExpr} {domains : List VExpr}
    {leftArity rightArity : Nat}
    (H : type.takeForalls (leftArity + rightArity) =
      some (domains, result)) :
    ∃ left middle right,
      domains = left ++ right ∧
      type.takeForalls leftArity = some (left, middle) ∧
      middle.takeForalls rightArity = some (right, result) := by
  rcases VExpr.takeForalls_rebuild H with ⟨hrebuild, hlength⟩
  let left := domains.take leftArity
  let right := domains.drop leftArity
  have hleft : left.length = leftArity := by
    simp [left, hlength]
  have hright : right.length = rightArity := by
    simp [right, hlength]
  have hdomains : domains = left ++ right := by
    exact (List.take_append_drop leftArity domains).symm
  refine ⟨left, VExpr.wrapForalls right result, right, hdomains, ?_, ?_⟩
  · rw [hrebuild, hdomains, ← hleft]
    exact VExpr.takeForalls_wrapForalls_append left right result
  · rw [← hright]
    exact VExpr.takeForalls_wrapForalls right result

/-- The first `n` domains of a wrapped telescope are syntactically unique.
The residual bodies may differ, and the longer presentation may retain an
arbitrary suffix after the compared prefix. -/
theorem VExpr.wrapForalls_prefix_domains_eq
    (hleft : left.length = n) (hright : right.length = n)
    (H : VExpr.wrapForalls left leftBody =
      VExpr.wrapForalls (right ++ suffix) rightBody) :
    left = right := by
  have htake := congrArg (fun type => type.takeForalls n) H
  have htakeLeft :
      (VExpr.wrapForalls left leftBody).takeForalls n = some (left, leftBody) := by
    rw [← hleft]
    exact VExpr.takeForalls_wrapForalls left leftBody
  have htakeRight :
      (VExpr.wrapForalls (right ++ suffix) rightBody).takeForalls n =
        some (right, VExpr.wrapForalls suffix rightBody) := by
    rw [← hright]
    exact VExpr.takeForalls_wrapForalls_append right suffix rightBody
  rw [htakeLeft, htakeRight] at htake
  exact congrArg Prod.fst (Option.some.inj htake)

/-- Wrapping the same dependent domain list on both sides is injective in
the residual body. -/
theorem VExpr.wrapForalls_left_cancel
    (domains : List VExpr)
    (H : VExpr.wrapForalls domains left =
      VExpr.wrapForalls domains right) :
    left = right := by
  induction domains with
  | nil => simpa [VExpr.wrapForalls] using H
  | cons domain domains ih =>
    simp only [VExpr.wrapForalls] at H
    injection H with _ hbody
    exact ih hbody

/-- Lift a recent context prefix over a block inserted immediately beneath
it, starting at cutoff `k` below the whole prefix.  The cutoff decreases as
the prefix is traversed from newest to oldest. -/
def liftContextPrefixAt (n k : Nat) : List VExpr → List VExpr
  | [] => []
  | domain :: domains =>
    domain.liftN n (k + domains.length) ::
      liftContextPrefixAt n k domains

def liftContextPrefix (n : Nat) (domains : List VExpr) : List VExpr :=
  liftContextPrefixAt n 0 domains

@[simp] theorem liftContextPrefixAt_length
    (n k : Nat) (domains : List VExpr) :
    (liftContextPrefixAt n k domains).length = domains.length := by
  induction domains with
  | nil => rfl
  | cons domain domains ih => simp [liftContextPrefixAt, ih]

@[simp] theorem liftContextPrefix_length
    (n : Nat) (domains : List VExpr) :
    (liftContextPrefix n domains).length = domains.length := by
  exact liftContextPrefixAt_length n 0 domains

theorem liftContextPrefixAt_append_singleton
    (n k : Nat) (domains : List VExpr) (domain : VExpr) :
    liftContextPrefixAt n k (domains ++ [domain]) =
      liftContextPrefixAt n (k + 1) domains ++ [domain.liftN n k] := by
  induction domains with
  | nil => simp [liftContextPrefixAt]
  | cons head domains ih =>
    simp [liftContextPrefixAt, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- In outermost-to-innermost telescope order, the `j`th domain is weakened
below the `j` earlier binders. -/
theorem liftContextPrefixAt_reverse_getElem
    (n k : Nat) (domains : List VExpr) (j : Nat)
    (hj : j < domains.length) :
    ((liftContextPrefixAt n k domains.reverse).reverse)[j]! =
      domains[j]!.liftN n (k + j) := by
  induction domains generalizing k j with
  | nil => simp at hj
  | cons domain domains ih =>
    rw [List.reverse_cons, liftContextPrefixAt_append_singleton,
      List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append]
    cases j with
    | zero => simp [getElem!_pos]
    | succ j =>
      have hj' : j < domains.length := by simpa using hj
      simpa [getElem!_pos, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        ih (k := k + 1) (j := j) hj'

theorem liftContextPrefixAt_append
    (n k : Nat) (left right : List VExpr) :
    liftContextPrefixAt n k (left ++ right) =
      liftContextPrefixAt n (k + right.length) left ++
        liftContextPrefixAt n k right := by
  induction left with
  | nil => simp [liftContextPrefixAt]
  | cons domain left ih =>
    simp [liftContextPrefixAt, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

theorem liftContextPrefixAt_reverse_append
    (n k : Nat) (outer inner : List VExpr) :
    (liftContextPrefixAt n k (outer ++ inner).reverse).reverse =
      (liftContextPrefixAt n k outer.reverse).reverse ++
        (liftContextPrefixAt n (k + outer.length) inner.reverse).reverse := by
  rw [List.reverse_append, liftContextPrefixAt_append,
    List.reverse_append]
  simp [Nat.add_comm]

theorem liftContextPrefixAt_reverse_append_take_left
    (n k : Nat) (outer inner : List VExpr) :
    ((liftContextPrefixAt n k (outer ++ inner).reverse).reverse).take
        outer.length =
      (liftContextPrefixAt n k outer.reverse).reverse := by
  rw [liftContextPrefixAt_reverse_append]
  simp

/-- In outermost-to-innermost telescope order, inserting beneath a combined
outer/inner prefix splits into the lifted outer domains followed by the
inner domains lifted at the outer cutoff. -/
theorem liftContextPrefix_reverse_append
    (n : Nat) (outer inner : List VExpr) :
    (liftContextPrefix n (outer ++ inner).reverse).reverse =
      (liftContextPrefix n outer.reverse).reverse ++
        (liftContextPrefixAt n outer.length inner.reverse).reverse := by
  unfold liftContextPrefix
  rw [List.reverse_append, liftContextPrefixAt_append,
    List.reverse_append]
  simp

/-- Lifting a dependent forall telescope is dual to lifting its reversed
context prefix. -/
theorem VExpr.liftN_wrapForalls
    (domains : List VExpr) (body : VExpr) (n k : Nat) :
    (VExpr.wrapForalls domains body).liftN n k =
      VExpr.wrapForalls
        ((liftContextPrefixAt n k domains.reverse).reverse)
        (body.liftN n (k + domains.length)) := by
  induction domains generalizing k with
  | nil => simp [VExpr.wrapForalls, liftContextPrefixAt]
  | cons domain domains ih =>
    change VExpr.forallE (domain.liftN n k)
      ((VExpr.wrapForalls domains body).liftN n (k + 1)) = _
    rw [ih,
      List.reverse_cons, liftContextPrefixAt_append_singleton]
    simp [VExpr.wrapForalls, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- An arbitrary free-variable lift preserves the number of leading forall
binders.  Unlike `liftN_wrapForalls`, the transformed dependent domains do
not have a useful closed formula for a general `Lift`, so this shape lemma
retains them existentially. -/
theorem VExpr.lift'_wrapForalls_shape
    (domains : List VExpr) (body : VExpr) (shift : Lift) :
    ∃ liftedDomains liftedBody,
      liftedDomains.length = domains.length ∧
      (VExpr.wrapForalls domains body).lift' shift =
        VExpr.wrapForalls liftedDomains liftedBody := by
  induction domains generalizing shift with
  | nil =>
      exact ⟨[], body.lift' shift, rfl, by simp [VExpr.wrapForalls]⟩
  | cons domain domains ih =>
      rcases ih shift.cons with
        ⟨liftedDomains, liftedBody, hlength, hshape⟩
      exact ⟨domain.lift' shift :: liftedDomains, liftedBody,
        by simp [hlength], by
          change VExpr.forallE (domain.lift' shift)
              ((VExpr.wrapForalls domains body).lift' shift.cons) =
            VExpr.forallE (domain.lift' shift)
              (VExpr.wrapForalls liftedDomains liftedBody)
          rw [hshape]⟩

/-- The dependent domains produced by a free-variable lift.  Unlike the
bound-variable `liftContextPrefix`, the shift changes beneath every binder. -/
def liftForallDomains : List VExpr → Lift → List VExpr
  | [], _ => []
  | domain :: domains, shift =>
      domain.lift' shift :: liftForallDomains domains shift.cons

@[simp] theorem liftForallDomains_length
    (domains : List VExpr) (shift : Lift) :
    (liftForallDomains domains shift).length = domains.length := by
  induction domains generalizing shift with
  | nil => rfl
  | cons _ domains ih => simp [liftForallDomains, ih]

/-- Lifting a dependent forall telescope is prefix-stable: later domains do
not affect the translated representatives of an earlier prefix. -/
theorem liftForallDomains_append_take_left
    (left right : List VExpr) (shift : Lift) :
    (liftForallDomains (left ++ right) shift).take left.length =
      liftForallDomains left shift := by
  induction left generalizing shift with
  | nil => rfl
  | cons domain left ih =>
    simp [liftForallDomains, ih]

/-- Free-variable lifting of dependent domains distributes over telescope
concatenation, with the right block translated below every binder in the
left block. -/
theorem liftForallDomains_append
    (left right : List VExpr) (shift : Lift) :
    liftForallDomains (left ++ right) shift =
      liftForallDomains left shift ++
        liftForallDomains right (shift.consN left.length) := by
  induction left generalizing shift with
  | nil => rfl
  | cons domain left ih =>
    simp only [List.cons_append, liftForallDomains, ih, List.cons.injEq,
      true_and]
    have hconsN : shift.cons.consN left.length =
        (shift.consN left.length).cons := by
      generalize left.length = n
      induction n with
      | zero => rfl
      | succ n ihN => simpa [Lift.consN] using congrArg Lift.cons ihN
    rw [hconsN]
    simp [Lift.consN]

/-- Successive free-variable weakenings of a dependent telescope are the
single composite weakening.  The lift beneath each forall binder must be
composed at the same binder depth; `Lift.consN_comp` supplies precisely that
alignment. -/
theorem liftForallDomains_comp
    (domains : List VExpr) (first second : Lift) :
    liftForallDomains (liftForallDomains domains first) second =
      liftForallDomains domains (.comp first second) := by
  induction domains generalizing first second with
  | nil => rfl
  | cons domain domains ih =>
    simp only [liftForallDomains, VExpr.lift'_comp, ih]
    have hcomp : Lift.comp first.cons second.cons =
        (Lift.comp first second).cons := by
      simpa [Lift.consN] using
        (Lift.consN_comp (l₁ := first) (l₂ := second) (n := 1)).symm
    rw [hcomp]

/-- Retaining any finite source context and then inserting `inserted` newer
declarations acts on expressions exactly like ordinary de Bruijn weakening
at the corresponding cutoff.  The retained `cons` prefix has depth zero and
therefore contributes no numerical shift. -/
theorem VExpr.lift'_consN_skipN_consN_refl
    (e : VExpr) (retained inserted cutoff : Nat) :
    e.lift' ((Lift.skipN (Lift.consN .refl retained) inserted).consN cutoff) =
      e.liftN inserted cutoff := by
  have hshift : Lift.skipN (.consN .refl retained) inserted =
      Lift.comp (.consN .refl retained) (.skipN .refl inserted) := by
    simp [Lift.comp_skipN]
  rw [hshift, Lift.consN_comp, VExpr.lift'_comp]
  have hretained : e.lift' ((Lift.consN .refl retained).consN cutoff) =
      e := VExpr.lift'_depth_zero (by simp)
  rw [hretained]
  exact VExpr.lift'_consN_skipN

/-- Inserting a contiguous newer free-variable block into the scope of a
dependent telescope is the same transform as lifting its recent context
prefix over that block. -/
theorem liftForallDomains_skipN_consN_refl
    (domains : List VExpr) (retained inserted : Nat) :
    liftForallDomains domains
        (Lift.skipN (Lift.consN .refl retained) inserted) =
      (liftContextPrefix inserted domains.reverse).reverse := by
  have go : ∀ (domains : List VExpr) (cutoff : Nat),
      liftForallDomains domains
          ((Lift.skipN (Lift.consN .refl retained) inserted).consN cutoff) =
        (liftContextPrefixAt inserted cutoff domains.reverse).reverse := by
    intro telescope
    induction telescope with
    | nil => intro cutoff; rfl
    | cons domain telescope ih =>
      intro cutoff
      simp only [liftForallDomains, List.reverse_cons,
        liftContextPrefixAt_append_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append]
      rw [VExpr.lift'_consN_skipN_consN_refl]
      simpa [Lift.consN] using ih (cutoff + 1)
  simpa [liftContextPrefix] using go domains 0

/-- The suffix embedding used by a contiguous retained context is the same
ordinary dependent-prefix weakening (the retained `cons` count is zero). -/
theorem liftForallDomains_skipN_refl
    (domains : List VExpr) (inserted : Nat) :
    liftForallDomains domains (Lift.skipN .refl inserted) =
      (liftContextPrefix inserted domains.reverse).reverse := by
  simpa using liftForallDomains_skipN_consN_refl domains 0 inserted

/-- Exact form of `VExpr.lift'_wrapForalls_shape`, with a domain transform
independent of the residual.  This independence is what permits a context
conversion extracted from one translated residual to be closed around a
different (but equally shifted) residual. -/
theorem VExpr.lift'_wrapForalls_exact
    (domains : List VExpr) (body : VExpr) (shift : Lift) :
    (VExpr.wrapForalls domains body).lift' shift =
      VExpr.wrapForalls (liftForallDomains domains shift)
        (body.lift' (shift.consN domains.length)) := by
  induction domains generalizing shift with
  | nil => simp [VExpr.wrapForalls, liftForallDomains]
  | cons domain domains ih =>
      change VExpr.forallE (domain.lift' shift)
          ((VExpr.wrapForalls domains body).lift' shift.cons) = _
      rw [ih]
      have hconsN : shift.cons.consN domains.length =
          (shift.consN domains.length).cons := by
        generalize domains.length = n
        induction n with
        | zero => rfl
        | succ n ihN => simpa [Lift.consN] using congrArg Lift.cons ihN
      rw [hconsN]
      rfl

/-- Insert `inserted` below `prefix` and above `suffix`, lifting each
dependent prefix declaration at its exact de Bruijn cutoff. -/
theorem Ctx.LiftN.insertAfterPrefix
    (recent inserted suffix : List VExpr) :
    Ctx.LiftN inserted.length recent.length (recent ++ suffix)
      (liftContextPrefix inserted.length recent ++ inserted ++ suffix) := by
  induction recent with
  | nil =>
    simpa [liftContextPrefix, liftContextPrefixAt, List.append_assoc] using
      (Ctx.LiftN.zero (Γ := suffix) inserted)
  | cons domain recent ih =>
    simpa [liftContextPrefix, liftContextPrefixAt, List.append_assoc] using
      (Ctx.LiftN.succ (A := domain) ih)

/-- A well-formed recent context remains well formed when a separately
well-formed block is inserted beneath it and every recent declaration is
lifted at its dependent cutoff. -/
theorem _root_.Lean4Lean.OnCtx.insertAfterPrefix
    {env : VEnv} {uvars : Nat}
    {recent inserted outer : List VExpr}
    (henv : env.Ordered)
    (Hrecent : OnCtx (recent ++ outer) (env.IsType uvars))
    (Hinserted : OnCtx (inserted ++ outer) (env.IsType uvars)) :
    OnCtx
      (liftContextPrefix inserted.length recent ++ inserted ++ outer)
      (env.IsType uvars) := by
  induction recent with
  | nil => simpa [liftContextPrefix, liftContextPrefixAt] using Hinserted
  | cons domain recent ih =>
    have Hdomain := Hrecent.2.weakN henv
      (Ctx.LiftN.insertAfterPrefix recent inserted outer)
    exact ⟨ih Hrecent.1, by
      simpa [liftContextPrefix, liftContextPrefixAt] using Hdomain⟩

/-- Insert the same well-formed context block beneath two definitionally
equal recent prefixes.  Each dependent prefix declaration is lifted at the
cutoff determined by the older declarations, exactly as in
`Ctx.LiftN.insertAfterPrefix`. -/
theorem VEnv.IsDefEqCtx.insertSameMiddle
    {env : VEnv} {uvars : Nat}
    (henv : env.Ordered)
    (recent₁ recent₂ inserted outer : List VExpr)
    (H : VEnv.IsDefEqCtx env uvars []
      (recent₁ ++ outer) (recent₂ ++ outer))
    (hlength : recent₁.length = recent₂.length)
    (hctx : OnCtx (inserted ++ outer) (env.IsType uvars)) :
    VEnv.IsDefEqCtx env uvars []
      (liftContextPrefix inserted.length recent₁ ++ inserted ++ outer)
      (liftContextPrefix inserted.length recent₂ ++ inserted ++ outer) := by
  induction recent₁ generalizing recent₂ with
  | nil =>
    have hrefl := VEnv.IsDefEqCtx.refl hctx
    have hrecent₂ : recent₂ = [] :=
      List.eq_nil_of_length_eq_zero hlength.symm
    simpa [hrecent₂, liftContextPrefix, liftContextPrefixAt] using hrefl
  | cons domain₁ recent₁ ih =>
    cases recent₂ with
    | nil => simp at hlength
    | cons domain₂ recent₂ =>
      simp only [List.cons_append] at H
      cases H with
      | succ Hprior Hdomain =>
        have htailLength : recent₁.length = recent₂.length := by
          simpa using Nat.succ.inj hlength
        have Hprior' := ih recent₂ Hprior htailLength
        have W := Ctx.LiftN.insertAfterPrefix recent₁ inserted outer
        have Hdomain' := Hdomain.weakN henv W
        exact .succ Hprior' (by
          rw [← htailLength]
          simpa [liftContextPrefix, liftContextPrefixAt, VExpr.liftN] using
            Hdomain')

/-- A nonempty extension of the fixed base context must end in `succ`, so its
outermost declaration and prior conversion can be recovered without treating
the base context itself as a newly added declaration. -/
theorem VEnv.IsDefEqCtx.extensionConsInv
    {env : VEnv} {uvars : Nat} {outer Γ₁ Γ₂ : List VExpr}
    {domain₁ domain₂ : VExpr}
    (H : VEnv.IsDefEqCtx env uvars outer
      (domain₁ :: Γ₁) (domain₂ :: Γ₂))
    (hlength : outer.length < (domain₁ :: Γ₁).length) :
    ∃ level,
      VEnv.IsDefEqCtx env uvars outer Γ₁ Γ₂ ∧
      env.IsDefEq uvars Γ₁ domain₁ domain₂ (.sort level) := by
  cases H with
  | zero => simp at hlength
  | succ Hprior Hdomain => exact ⟨_, Hprior, Hdomain⟩

/-- Close a dependent context conversion back into a definitional equality
of forall telescopes.  `recent₁` and `recent₂` are stored in local-context
order, so reversing them restores source binder order for `wrapForalls`. -/
theorem VEnv.IsDefEqCtx.closeWrapForalls
    {env : VEnv} {uvars : Nat}
    (outer recent₁ recent₂ : List VExpr)
    (H : VEnv.IsDefEqCtx env uvars outer
      (recent₁ ++ outer) (recent₂ ++ outer))
    (Hbody : env.IsDefEq uvars (recent₁ ++ outer)
      body₁ body₂ (.sort bodyLevel)) :
    env.IsDefEqU uvars outer
      (VExpr.wrapForalls recent₁.reverse body₁)
      (VExpr.wrapForalls recent₂.reverse body₂) := by
  induction recent₁ generalizing recent₂ body₁ body₂ bodyLevel with
  | nil =>
    have hrecent₂ : recent₂ = [] := by
      have hlength := H.length_eq
      simp at hlength
      exact hlength
    subst recent₂
    exact ⟨_, by simpa [VExpr.wrapForalls] using Hbody⟩
  | cons domain₁ recent₁ ih =>
    cases recent₂ with
    | nil =>
      have hlength := H.length_eq
      simp at hlength
      omega
    | cons domain₂ recent₂ =>
      rcases
          Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extensionConsInv H (by
            simp
            omega) with
        ⟨domainLevel, Hprior, Hdomain⟩
      have Hclosed := VEnv.IsDefEq.forallEDF Hdomain Hbody
      have Hrest := ih recent₂ Hprior Hclosed
      simpa [List.reverse_cons, VExpr.wrapForalls_append,
        VExpr.wrapForalls] using Hrest

theorem VEnv.IsType.wrapForalls_inv
    {env : VEnv} (henv : env.Ordered)
    (hctx : OnCtx ctx (env.IsType uvars))
    (H : env.IsType uvars ctx (VExpr.wrapForalls domains result)) :
    OnCtx (domains.reverse ++ ctx) (env.IsType uvars) ∧
      env.IsType uvars (domains.reverse ++ ctx) result := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapForalls] using And.intro hctx H
  | cons domain domains ih =>
    have hinv := H.forallE_inv henv
    have hctx' : OnCtx (domain :: ctx) (env.IsType uvars) :=
      ⟨hctx, hinv.1⟩
    simpa [VExpr.wrapForalls, List.reverse_cons, List.append_assoc] using
      ih hctx' hinv.2

theorem VEnv.IsType.wrapForalls
    {env : VEnv} (hctx : OnCtx (domains.reverse ++ ctx)
      (env.IsType uvars))
    (H : env.IsType uvars (domains.reverse ++ ctx) result) :
    env.IsType uvars ctx (VExpr.wrapForalls domains result) := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (domain :: ctx))
        (env.IsType uvars) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hrest := ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using H)
    have hdomain : env.IsType uvars ctx domain :=
      (OnCtx.append_right hctx').2
    exact VEnv.IsType.forallE hdomain hrest

/-- Closing a term over a semantically well-formed telescope preserves its
typing.  The domains use the source binder order, while typing contexts use
the corresponding most-recent-first order. -/
theorem VEnv.HasType.wrapLams
    {env : VEnv} (hctx : OnCtx (domains.reverse ++ ctx)
      (env.IsType uvars))
    (H : env.HasType uvars (domains.reverse ++ ctx) body typeBody) :
    env.HasType uvars ctx (VExpr.wrapLams domains body)
      (VExpr.wrapForalls domains typeBody) := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapLams, VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (domain :: ctx))
        (env.IsType uvars) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hrest := ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using H)
    rcases (OnCtx.append_right hctx').2 with ⟨level, hdomain⟩
    simpa [VExpr.wrapLams, VExpr.wrapForalls] using hdomain.lam hrest

/-- Invert a lambda telescope whose type is the corresponding literal forall
telescope.  Strong lambda inversion initially recovers an arbitrary type for
the open body; uniqueness of typing and forall injectivity transport that
body back to the stated dependent residual before the induction continues.

This is the application-facing inverse of `VEnv.HasType.wrapLams`: canonical
recursive results are stored closed, while a dependent minor application
needs their exact open typing under the retained local domains. -/
theorem VEnv.HasType.wrapLams_inv
    {env : VEnv} (henv : env.WF)
    (hctx : OnCtx ctx (env.IsType uvars))
    (H : env.HasType uvars ctx (VExpr.wrapLams domains body)
      (VExpr.wrapForalls domains typeBody)) :
    OnCtx (domains.reverse ++ ctx) (env.IsType uvars) ∧
      env.HasType uvars (domains.reverse ++ ctx) body typeBody := by
  induction domains generalizing ctx with
  | nil =>
    simpa [VExpr.wrapLams, VExpr.wrapForalls] using And.intro hctx H
  | cons domain domains ih =>
    have Hlambda : env.HasType uvars ctx
        (.lam domain (VExpr.wrapLams domains body))
        (.forallE domain (VExpr.wrapForalls domains typeBody)) := by
      simpa [VExpr.wrapLams, VExpr.wrapForalls] using H
    rcases Hlambda.lam_inv henv.ordered hctx with
      ⟨HdomainType, actualBodyType, HactualBody⟩
    rcases HdomainType with ⟨domainLevel, Hdomain⟩
    have hctx' : OnCtx (domain :: ctx) (env.IsType uvars) :=
      ⟨hctx, ⟨domainLevel, Hdomain⟩⟩
    have HactualLambda : env.HasType uvars ctx
        (.lam domain (VExpr.wrapLams domains body))
        (.forallE domain actualBodyType) :=
      Hdomain.lam HactualBody
    have HfunctionType := Hlambda.uniqU henv hctx HactualLambda
    rcases (VEnv.IsDefEqU.forallE_inv henv hctx HfunctionType).2 with
      ⟨_bodyLevel, HbodyType⟩
    have HstatedBody : env.HasType uvars (domain :: ctx)
        (VExpr.wrapLams domains body)
        (VExpr.wrapForalls domains typeBody) :=
      HbodyType.defeq' HactualBody
    have Hrest := ih hctx' HstatedBody
    simpa [List.reverse_cons, List.append_assoc] using Hrest

/-- Package two equally typed residual bodies as one closed, well-formed
definitional equation.  This is the common specification-side endpoint for
ordinary and restored nested iota equations. -/
theorem VDefEq.wf_of_wrappedBodies
    {env : VEnv} {uvars : Nat} {domains : List VExpr}
    {lhsBody rhsBody typeBody : VExpr}
    (hctx : OnCtx domains.reverse (env.IsType uvars))
    (hlhs : env.HasType uvars domains.reverse lhsBody typeBody)
    (hrhs : env.HasType uvars domains.reverse rhsBody typeBody) :
    ({ uvars := uvars
       lhs := VExpr.wrapLams domains lhsBody
       rhs := VExpr.wrapLams domains rhsBody
       type := VExpr.wrapForalls domains typeBody } : VDefEq).WF env := by
  have hctx' : OnCtx (domains.reverse ++ []) (env.IsType uvars) := by
    simpa using hctx
  exact ⟨VEnv.HasType.wrapLams hctx' (by simpa using hlhs),
    VEnv.HasType.wrapLams hctx' (by simpa using hrhs)⟩

/-- Inject the next domain after two equally long definitionally equal forall
prefixes.  The result is stated in the left prefix context, matching the
narrow replay context built from already consumed family parameters. -/
theorem VEnv.IsDefEqU.wrapForalls_next
    (henv : VEnv.WF env)
    (hctx : OnCtx ctx (env.IsType uvars))
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls left (.forallE leftNext leftBody))
      (VExpr.wrapForalls right (.forallE rightNext rightBody))) :
    ∃ u, env.IsDefEq uvars (left.reverse ++ ctx)
      leftNext rightNext (.sort u) := by
  induction left generalizing right ctx with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa [VExpr.wrapForalls] using
      (VEnv.IsDefEqU.forallE_inv henv hctx H).1
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : OnCtx (leftHead :: ctx) (env.IsType uvars) :=
        ⟨hctx, ⟨headLevel, hhead.hasType.1⟩⟩
      have hnext := ih (right := rightTail) (ctx := leftHead :: ctx)
        hctx' hlength ⟨_, hbody⟩
      simpa [List.reverse_cons, List.append_assoc] using hnext

/-- Invert two equally long definitionally equal forall telescopes into a
conversion between their completed binder contexts.  The outer contexts may
already differ definitionally; each newly exposed domain extends that
conversion before the residual telescope is inspected. -/
theorem VEnv.IsDefEqU.wrapForalls_context
    (henv : VEnv.WF env)
    (hctx : VEnv.IsDefEqCtx env uvars [] leftCtx rightCtx)
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars leftCtx
      (VExpr.wrapForalls left leftBody)
      (VExpr.wrapForalls right rightBody)) :
    VEnv.IsDefEqCtx env uvars []
      (left.reverse ++ leftCtx) (right.reverse ++ rightCtx) := by
  induction left generalizing right leftCtx rightCtx leftBody rightBody with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa using hctx
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx.isType H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : VEnv.IsDefEqCtx env uvars []
          (leftHead :: leftCtx) (rightHead :: rightCtx) :=
        .succ hctx hhead
      have hbodyU : env.IsDefEqU uvars (leftHead :: leftCtx)
          (VExpr.wrapForalls leftTail leftBody)
          (VExpr.wrapForalls rightTail rightBody) :=
        ⟨.sort bodyLevel, hbody⟩
      have hrest := ih hctx' hlength hbodyU
      simpa [List.reverse_cons, List.append_assoc] using hrest

/-- Peel two equally long definitionally equal forall telescopes down to
their residual bodies.  The comparison is stated in the context generated by
the left telescope, matching `forallE_inv` and the dependent-context
convention used by the header checker. -/
theorem VEnv.IsDefEqU.wrapForalls_residual
    (henv : VEnv.WF env)
    (hctx : OnCtx ctx (env.IsType uvars))
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls left leftBody)
      (VExpr.wrapForalls right rightBody)) :
    env.IsDefEqU uvars (left.reverse ++ ctx) leftBody rightBody := by
  induction left generalizing right ctx with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa [VExpr.wrapForalls] using H
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : OnCtx (leftHead :: ctx) (env.IsType uvars) :=
        ⟨hctx, ⟨headLevel, hhead.hasType.1⟩⟩
      have hrest := ih (right := rightTail) (ctx := leftHead :: ctx)
        hctx' hlength ⟨_, hbody⟩
      simpa [List.reverse_cons, List.append_assoc] using hrest

/-- Compose two context conversions over the empty base.  The domain proof
of the second conversion is transported back across the already composed
prefix before transitivity is applied, so dependent domains remain in the
correct context.  This belongs with the generic dependent-context API rather
than any particular inductive phase. -/
theorem VEnv.IsDefEqCtx.transEmpty
    (henv : env.WF)
    (H₁ : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (H₂ : VEnv.IsDefEqCtx env U [] Γ₂ Γ₃) :
    VEnv.IsDefEqCtx env U [] Γ₁ Γ₃ := by
  induction H₁ generalizing Γ₃ with
  | zero => exact H₂
  | @succ Γ₁ Γ₂ A₁ A₂ u H₁ hdom ih =>
    cases H₂ with
    | succ H₂ hdom₂ =>
      have Hprefix := ih H₂
      have hdom₂' := hdom₂.defeqDFC henv.ordered (H₁.symm henv.ordered)
      exact .succ Hprefix
        (hdom.trans_r henv H₁.isType hdom₂')

/-- A dependency-ordered list of well-formed constants may be viewed as a
sequence of abstract axioms extending a well-formed environment.  Stating
the input typing in the original environment is sufficient because each
constant can be weakened through the preceding fresh additions. -/
theorem VEnv.WF.addConstVals
    {env env' : VEnv} {cis : List VConstVal}
    (Henv : env.WF)
    (Hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (Hadd : env.addConstVals cis = some env') : env'.WF := by
  induction cis generalizing env env' with
  | nil =>
    simp [VEnv.addConstVals] at Hadd
    subst env'
    exact Henv
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at Hadd
    | some next =>
      simp [VEnv.addConstVals, hci] at Hadd
      have hhead : ci.toVConstant.WF env := Hwf ci (by simp)
      have Hnext : next.WF := by
        rcases Henv with ⟨ds, Hds⟩
        exact ⟨.axiom ci :: ds, .decl (.axiom hhead hci) Hds⟩
      apply ih Hnext (env' := env')
      · intro ci' hmem
        exact (Hwf ci' (by simp [hmem])).mono (VEnv.addConst_le hci)
      · exact Hadd

/-- Repeated application syntax retains a well-typed prefix. -/
theorem VExpr.WF.mkApps_fn
    (henv : env.Ordered) (hctx : OnCtx ctx (env.IsType uvars))
    (H : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    VExpr.WF env uvars ctx fn := by
  induction args generalizing fn with
  | nil => simpa [VExpr.mkApps] using H
  | cons arg args ih =>
    have Hprefix := ih (fn := .app fn arg) H
    rcases Hprefix.app_inv henv hctx with ⟨domain, body, hfn, _harg⟩
    exact ⟨_, hfn⟩

/-- Pointwise convertible arguments preserve a well-formed application
spine.  The function heads may themselves merely be definitionally equal;
typing for each successive application is recovered by inversion from the
well-formed left spine. -/
theorem VEnv.IsDefEqU.mkApps
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.IsDefEqU uvars ctx fn₁ fn₂)
    (Hleft : VExpr.WF env uvars ctx (VExpr.mkApps fn₁ args₁))
    (Hargs : List.Forall₂
      (env.IsDefEqU uvars ctx) args₁ args₂) :
    env.IsDefEqU uvars ctx
      (VExpr.mkApps fn₁ args₁) (VExpr.mkApps fn₂ args₂) := by
  induction Hargs generalizing fn₁ fn₂ with
  | nil => simpa [VExpr.mkApps] using Hfn
  | @cons arg₁ arg₂ args₁ args₂ Harg Hargs ih =>
    have Hprefix := VExpr.WF.mkApps_fn henv.ordered hctx
      (fn := .app fn₁ arg₁) (args := args₁) Hleft
    rcases Hprefix.app_inv henv.ordered hctx with
      ⟨domain, body, HfnType, HargType⟩
    have HprefixEq : env.IsDefEqU uvars ctx
        (.app fn₁ arg₁) (.app fn₂ arg₂) :=
      (VEnv.IsDefEq.appDF (Hfn.of_l henv hctx HfnType)
        (Harg.of_l henv hctx HargType)).toU
    exact ih HprefixEq Hleft

/-- The first argument of a well-typed application spine has the declared
outer domain of the function.  Application inversion may initially recover
a different convertible domain; uniqueness and forall injectivity transport
the argument back to the stated telescope. -/
theorem VEnv.HasType.mkApps_head
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (hfn : env.HasType uvars ctx fn (.forallE domain body))
    (happs : VExpr.WF env uvars ctx
      (VExpr.mkApps fn (arg :: args))) :
    env.HasType uvars ctx arg domain := by
  have hprefix := VExpr.WF.mkApps_fn henv.ordered hctx
    (fn := .app fn arg) (args := args) happs
  rcases hprefix.app_inv henv.ordered hctx with
    ⟨actualDomain, actualBody, hfnActual, hargActual⟩
  have hfunctionEq := hfn.uniqU henv hctx hfnActual
  have hdomainEq :=
    (VEnv.IsDefEqU.forallE_inv henv hctx hfunctionEq).1
  rcases hdomainEq with ⟨domainLevel, hdomainEq⟩
  exact hdomainEq.defeq' hargActual

/-- A dependently typed application spine.  Each argument is checked against
the current outer forall domain, and the residual type is instantiated before
the rest of the spine is consumed.  This is the induction principle used for
the generated minor's fields followed by its recursive-result arguments. -/
inductive VEnv.TypedApplicationSpine
    (env : VEnv) (uvars : Nat) (ctx : List VExpr) :
    VExpr → VExpr → List VExpr → VExpr → Prop
  | nil (Hfn : env.HasType uvars ctx fn fnType) :
      TypedApplicationSpine env uvars ctx fn fnType [] fnType
  | cons
      (Hfn : env.HasType uvars ctx fn (.forallE domain body))
      (Harg : env.HasType uvars ctx arg domain)
      (Htail : TypedApplicationSpine env uvars ctx
        (.app fn arg) (body.inst arg) args resultType) :
      TypedApplicationSpine env uvars ctx fn (.forallE domain body)
        (arg :: args) resultType

/-- Add one dependent application when the argument's retained type is only
definitionally equal to the current forall domain.  Canonical recursive
results are built independently from the installed minor telescope, so this
is the application constructor used after their pointwise type alignment. -/
theorem VEnv.TypedApplicationSpine.cons_defeq
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.HasType uvars ctx fn (.forallE domain body))
    (Harg : env.HasType uvars ctx arg actualDomain)
    (Hdomain : env.IsDefEqU uvars ctx actualDomain domain)
    (Htail : VEnv.TypedApplicationSpine env uvars ctx
      (.app fn arg) (body.inst arg) args resultType) :
    VEnv.TypedApplicationSpine env uvars ctx fn (.forallE domain body)
      (arg :: args) resultType := by
  exact .cons Hfn (Harg.defeqU_r henv hctx Hdomain) Htail

theorem VEnv.TypedApplicationSpine.hasType
    (H : VEnv.TypedApplicationSpine env uvars ctx fn fnType args resultType) :
    env.HasType uvars ctx (VExpr.mkApps fn args) resultType := by
  induction H with
  | nil Hfn => simpa [VExpr.mkApps] using Hfn
  | cons Hfn Harg _ ih =>
      simpa [VExpr.mkApps] using ih

theorem VEnv.TypedApplicationSpine.wf
    (H : VEnv.TypedApplicationSpine env uvars ctx fn fnType args resultType) :
    VExpr.WF env uvars ctx (VExpr.mkApps fn args) :=
  ⟨resultType, H.hasType⟩

/-- Concatenate two dependent application phases.  The second phase starts at
the exact residual term and type produced by the first. -/
theorem VEnv.TypedApplicationSpine.append
    (Hinitial : VEnv.TypedApplicationSpine env uvars ctx
      fn fnType initial middleType)
    (Hsuffix : VEnv.TypedApplicationSpine env uvars ctx
      (VExpr.mkApps fn initial) middleType suffix resultType) :
    VEnv.TypedApplicationSpine env uvars ctx
      fn fnType (initial ++ suffix) resultType := by
  induction Hinitial with
  | nil Hfn => simpa [VExpr.mkApps] using Hsuffix
  | @cons fn domain body arg args resultType Hfn Harg Htail ih =>
      apply VEnv.TypedApplicationSpine.cons Hfn Harg
      apply ih
      simpa [VExpr.mkApps] using Hsuffix

/-- Extend an already checked dependent application prefix by one argument.
This is the left-to-right constructor used by executable argument folds. -/
theorem VEnv.TypedApplicationSpine.snoc
    (Hprefix : VEnv.TypedApplicationSpine env uvars ctx
      fn fnType args (.forallE domain body))
    (Harg : env.HasType uvars ctx arg domain) :
    VEnv.TypedApplicationSpine env uvars ctx fn fnType
      (args ++ [arg]) (body.inst arg) := by
  have Happ : env.HasType uvars ctx
      (.app (VExpr.mkApps fn args) arg) (body.inst arg) :=
    Hprefix.hasType.app Harg
  exact Hprefix.append <|
    .cons Hprefix.hasType Harg (.nil Happ)

/-- Left-to-right extension when the retained argument type is convertible
to the current dependent domain. -/
theorem VEnv.TypedApplicationSpine.snoc_defeq
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hprefix : VEnv.TypedApplicationSpine env uvars ctx
      fn fnType args (.forallE domain body))
    (Harg : env.HasType uvars ctx arg actualDomain)
    (Hdomain : env.IsDefEqU uvars ctx actualDomain domain) :
    VEnv.TypedApplicationSpine env uvars ctx fn fnType
      (args ++ [arg]) (body.inst arg) := by
  exact Hprefix.snoc (Harg.defeqU_r henv hctx Hdomain)

/-- Transport an entire dependent application spine across a definitionally
equal ambient context.  Every term and every successive instantiated type is
preserved literally; only the context in each typing derivation changes. -/
theorem VEnv.TypedApplicationSpine.defeqDFC
    (henv : env.Ordered)
    (Hctx : VEnv.IsDefEqCtx env uvars [] leftCtx rightCtx)
    (H : VEnv.TypedApplicationSpine env uvars leftCtx
      fn fnType args resultType) :
    VEnv.TypedApplicationSpine env uvars rightCtx
      fn fnType args resultType := by
  induction H with
  | nil Hfn =>
      exact .nil (Hfn.defeqDFC henv Hctx)
  | cons Hfn Harg _ ih =>
      exact .cons (Hfn.defeqDFC henv Hctx)
        (Harg.defeqDFC henv Hctx) ih

/-- Context conversion is reversible for dependent application spines. -/
theorem VEnv.TypedApplicationSpine.defeqDFC_iff
    (henv : env.Ordered)
    (Hctx : VEnv.IsDefEqCtx env uvars [] leftCtx rightCtx) :
    VEnv.TypedApplicationSpine env uvars leftCtx
        fn fnType args resultType ↔
      VEnv.TypedApplicationSpine env uvars rightCtx
        fn fnType args resultType := by
  constructor
  · exact VEnv.TypedApplicationSpine.defeqDFC henv Hctx
  · exact VEnv.TypedApplicationSpine.defeqDFC henv (Hctx.symm henv)

/-- Canonical variables for a telescope, in source binder order. -/
def recursorCanonicalVars (n : Nat) : List VExpr :=
  (List.range n).reverse.map .bvar

@[simp] theorem recursorCanonicalVars_zero : recursorCanonicalVars 0 = [] :=
  rfl

theorem recursorCanonicalVars_eq_ofFn (n : Nat) :
    recursorCanonicalVars n =
      List.ofFn fun i : Fin n => VExpr.bvar (n - 1 - i) := by
  apply List.ext_getElem
  · simp [recursorCanonicalVars]
  · intro i hleft hright
    simp [recursorCanonicalVars]

theorem recursorCanonicalVars_succ_cons (n : Nat) :
    recursorCanonicalVars (n + 1) =
      .bvar n :: recursorCanonicalVars n := by
  simp [recursorCanonicalVars, List.range_succ]

/-- Split canonical telescope variables into an older applied initial block,
weakened below the still-open suffix, followed by the suffix variables. -/
theorem recursorCanonicalVars_add (initialCount suffixCount : Nat) :
    recursorCanonicalVars (initialCount + suffixCount) =
      (recursorCanonicalVars initialCount).map
          (fun arg => arg.liftN suffixCount 0) ++
        recursorCanonicalVars suffixCount := by
  induction initialCount with
  | zero => simp
  | succ initialCount ih =>
    rw [show (initialCount + 1) + suffixCount =
        (initialCount + suffixCount) + 1 by omega,
      recursorCanonicalVars_succ_cons,
      recursorCanonicalVars_succ_cons, List.map_cons, ih]
    simp [VExpr.liftN, liftVar_base, List.append_assoc]

theorem VExpr.liftN_mkApps
    (fn : VExpr) (args : List VExpr) (n k : Nat) :
    (VExpr.mkApps fn args).liftN n k =
      VExpr.mkApps (fn.liftN n k) (args.map fun arg => arg.liftN n k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simpa [VExpr.mkApps, VExpr.liftN] using ih (.app fn arg)

theorem VExpr.mkApps_append (fn : VExpr) (initial suffix : List VExpr) :
    VExpr.mkApps fn (initial ++ suffix) =
      VExpr.mkApps (VExpr.mkApps fn initial) suffix := by
  simp [VExpr.mkApps, List.foldl_append]

/-- Applying all canonical variables factors through the canonical
application of any older initial block, weakened below the remaining suffix. -/
theorem VExpr.mkApps_canonical_add
    (fn : VExpr) (initialCount suffixCount : Nat) :
    VExpr.mkApps (fn.liftN (initialCount + suffixCount) 0)
        (recursorCanonicalVars (initialCount + suffixCount)) =
      VExpr.mkApps
        ((VExpr.mkApps (fn.liftN initialCount 0)
          (recursorCanonicalVars initialCount)).liftN suffixCount 0)
        (recursorCanonicalVars suffixCount) := by
  have hinitialApp :
      VExpr.mkApps (fn.liftN (initialCount + suffixCount) 0)
          ((recursorCanonicalVars initialCount).map
            (fun arg => arg.liftN suffixCount 0)) =
        (VExpr.mkApps (fn.liftN initialCount 0)
          (recursorCanonicalVars initialCount)).liftN suffixCount 0 := by
    rw [VExpr.liftN_mkApps]
    simp [VExpr.liftN_liftN]
  rw [recursorCanonicalVars_add]
  rw [VExpr.mkApps_append, hinitialApp]

/-- A well-typed complete canonical application retains every older partial
application after the unapplied dependent suffix is removed from the local
context. -/
theorem VExpr.WF.mkApps_canonical_prefix
    {fn : VExpr}
    (henv : env.WF)
    (actual : List VExpr) (outer : List VExpr)
    (hctx : OnCtx (actual.reverse ++ outer) (env.IsType uvars))
    (H : VExpr.WF env uvars (actual.reverse ++ outer)
      (VExpr.mkApps (fn.liftN actual.length 0)
        (recursorCanonicalVars actual.length)))
    (initialCount : Nat) (hinitial : initialCount ≤ actual.length) :
    VExpr.WF env uvars ((actual.take initialCount).reverse ++ outer)
      (VExpr.mkApps (fn.liftN initialCount 0)
        (recursorCanonicalVars initialCount)) := by
  let remaining := actual.drop initialCount
  have hsplit : actual = actual.take initialCount ++ remaining := by
    exact (List.take_append_drop initialCount actual).symm
  have hlength : actual.length = initialCount + remaining.length := by
    simp [remaining, hinitial]
  have Hsplit := H
  rw [hsplit] at Hsplit
  have H' : VExpr.WF env uvars
      (remaining.reverse ++ (actual.take initialCount).reverse ++ outer)
      (VExpr.mkApps (fn.liftN (initialCount + remaining.length) 0)
        (recursorCanonicalVars (initialCount + remaining.length))) := by
    simpa [hlength, List.reverse_append, List.append_assoc] using Hsplit
  rw [VExpr.mkApps_canonical_add] at H'
  have hctxSplit := hctx
  rw [hsplit] at hctxSplit
  have Hpartial := VExpr.WF.mkApps_fn henv.ordered (by
    simpa [List.reverse_append, List.append_assoc] using hctxSplit)
    H'
  have W : Ctx.LiftN remaining.length 0
      ((actual.take initialCount).reverse ++ outer)
      (remaining.reverse ++ (actual.take initialCount).reverse ++ outer) := by
    simpa [List.length_reverse] using
      (Ctx.LiftN.zero remaining.reverse
        (h := by simp)
        (Γ := (actual.take initialCount).reverse ++ outer))
  exact (VExpr.WF.weakN_iff henv (by
    simpa [List.reverse_append, List.append_assoc] using hctxSplit) W).mp
      (by simpa using Hpartial)

/-- A term whose type is a dependent forall telescope can be weakened beneath
that telescope and applied to the canonical variables for all of its binders.
The result has the unabstracted residual type in the completed telescope
context. -/
theorem VEnv.HasType.mkApps_wrapForalls_canonical
    {env : VEnv} {uvars : Nat} {ctx : List VExpr} {fn : VExpr}
    {domains : List VExpr} {body : VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.HasType env uvars ctx fn (VExpr.wrapForalls domains body)) :
    VEnv.HasType env uvars (domains.reverse ++ ctx)
      (VExpr.mkApps (fn.liftN domains.length 0)
        ((List.range domains.length).reverse.map .bvar)) body := by
  induction domains generalizing ctx fn with
  | nil => simpa [VExpr.mkApps, VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hfirst := (H.weakN henv (Ctx.LiftN.one (A := domain))).app
      (VEnv.HasType.bvar Lookup.zero)
    have hfirst' : VEnv.HasType env uvars (domain :: ctx)
        (.app (fn.liftN 1 0) (.bvar 0))
        (VExpr.wrapForalls domains body) := by
      simpa [VExpr.wrapForalls, VExpr.liftN, VExpr.instN_bvar0] using hfirst
    have hrest := ih hfirst'
    simpa [VExpr.wrapForalls, VExpr.mkApps, List.range_succ,
      List.reverse_cons, List.append_assoc, VExpr.liftN,
      VExpr.instN_bvar0, VExpr.liftN_liftN, Nat.add_comm] using hrest

/-- Applying only an initial segment of a dependent telescope leaves the
remaining suffix as the type of the canonical partial application. -/
theorem VEnv.HasType.mkApps_wrapForalls_prefix_canonical
    {env : VEnv} {uvars : Nat} {ctx : List VExpr} {fn : VExpr}
    {initial suffix : List VExpr} {body : VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.HasType env uvars ctx fn
      (VExpr.wrapForalls (initial ++ suffix) body)) :
    VEnv.HasType env uvars (initial.reverse ++ ctx)
      (VExpr.mkApps (fn.liftN initial.length 0)
        ((List.range initial.length).reverse.map .bvar))
      (VExpr.wrapForalls suffix body) := by
  rw [VExpr.wrapForalls_append] at H
  exact VEnv.HasType.mkApps_wrapForalls_canonical henv H

/-- Apply an initial forall prefix canonically and immediately transport the
result across the caller's ambient context conversion.  This is the exact
handoff used by generated minor applications: telescope inversion naturally
types the application in the installed field context, while the equation is
assembled in an independently checked field context. -/
theorem VEnv.HasType.mkApps_wrapForalls_prefix_canonical_defeqCtx
    {env : VEnv} {uvars : Nat} {outer actual : List VExpr} {fn : VExpr}
    {initial suffix : List VExpr} {body : VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.HasType env uvars outer fn
      (VExpr.wrapForalls (initial ++ suffix) body))
    (Hctx : VEnv.IsDefEqCtx env uvars []
      (initial.reverse ++ outer) actual) :
    VEnv.HasType env uvars actual
      (VExpr.mkApps (fn.liftN initial.length 0)
        (recursorCanonicalVars initial.length))
      (VExpr.wrapForalls suffix body) := by
  exact (VEnv.HasType.mkApps_wrapForalls_prefix_canonical henv H).defeqDFC
    henv Hctx

/-- Invert a well-typed canonical application of a declared forall
telescope into a conversion between the actual dependent argument context
and the declared domain context.  The residual body is arbitrary: in
particular, an initial field prefix may leave a recursive-hypothesis
telescope rather than a sort.  The proof grows the conversion from the
oldest binder outward, using partial-application typing at each step. -/
theorem VEnv.HasType.canonicalApplicationContext
    {fn body : VExpr}
    (henv : env.WF)
    (actual expected : List VExpr) (outer : List VExpr)
    (hctx : OnCtx (actual.reverse ++ outer) (env.IsType uvars))
    (hfn : env.HasType uvars outer fn
      (VExpr.wrapForalls expected body))
    (hlength : actual.length = expected.length)
    (happs : VExpr.WF env uvars (actual.reverse ++ outer)
      (VExpr.mkApps (fn.liftN actual.length 0)
        (recursorCanonicalVars actual.length))) :
    VEnv.IsDefEqCtx env uvars []
      (actual.reverse ++ outer) (expected.reverse ++ outer) := by
  have houter : OnCtx outer (env.IsType uvars) :=
    OnCtx.append_right hctx
  have go : ∀ initialCount, initialCount ≤ actual.length →
      VEnv.IsDefEqCtx env uvars []
        ((actual.take initialCount).reverse ++ outer)
        ((expected.take initialCount).reverse ++ outer) := by
    intro initialCount hinitial
    induction initialCount with
    | zero =>
      simpa using VEnv.IsDefEqCtx.refl houter
    | succ initialCount ih =>
      have hinitialLt : initialCount < actual.length := by omega
      have hexpectedLt : initialCount < expected.length := by omega
      have Hprior := ih (by omega)
      let actualDomain := actual[initialCount]
      let expectedDomain := expected[initialCount]
      let actualCtx := (actual.take initialCount).reverse ++ outer
      let expectedCtx := (expected.take initialCount).reverse ++ outer
      let partialApp := VExpr.mkApps (fn.liftN initialCount 0)
        (recursorCanonicalVars initialCount)
      have hexpectedSplit : expected = expected.take initialCount ++
          expected.drop initialCount :=
        (List.take_append_drop initialCount expected).symm
      have HpartialExpected : env.HasType uvars expectedCtx partialApp
          (VExpr.wrapForalls (expected.drop initialCount)
            body) := by
        have hfnSplit := hfn
        rw [hexpectedSplit] at hfnSplit
        have H := VEnv.HasType.mkApps_wrapForalls_prefix_canonical
          henv.ordered (initial := expected.take initialCount)
          (suffix := expected.drop initialCount) (by
            exact hfnSplit)
        simpa [expectedCtx, partialApp, recursorCanonicalVars,
          Nat.min_eq_left (Nat.le_of_lt hexpectedLt)] using H
      have Hpartial : env.HasType uvars actualCtx partialApp
          (VExpr.wrapForalls (expected.drop initialCount)
            body) :=
        HpartialExpected.defeqDFC henv.ordered
          (Hprior.symm henv.ordered)
      have hdrop : expected.drop initialCount = expectedDomain ::
          expected.drop (initialCount + 1) := by
        simpa [expectedDomain] using
          List.drop_eq_getElem_cons hexpectedLt
      rw [hdrop] at Hpartial
      have HpartialWeak := Hpartial.weakN henv.ordered
        (Ctx.LiftN.one (A := actualDomain))
      let expectedBody :=
        (VExpr.wrapForalls (expected.drop (initialCount + 1))
          body).liftN 1 1
      have HpartialForall : env.HasType uvars (actualDomain :: actualCtx)
          (partialApp.liftN 1 0)
          (.forallE expectedDomain.lift expectedBody) := by
        simpa [VExpr.wrapForalls, VExpr.lift, VExpr.liftN,
          expectedBody] using HpartialWeak
      have HnextWF₀ := VExpr.WF.mkApps_canonical_prefix henv actual outer
        hctx happs (initialCount + 1) (by omega)
      have HnextWF : VExpr.WF env uvars (actualDomain :: actualCtx)
          (VExpr.mkApps (partialApp.liftN 1 0)
            (recursorCanonicalVars 1)) := by
        have htake : actual.take (initialCount + 1) =
            actual.take initialCount ++ [actualDomain] := by
          simpa [actualDomain] using
            List.take_succ_eq_append_getElem hinitialLt
        simpa [actualCtx, partialApp, htake, List.reverse_append,
          VExpr.mkApps_canonical_add] using HnextWF₀
      have HexpectedArg := VEnv.HasType.mkApps_head henv (by
        have hactualPrefix : OnCtx (actualDomain :: actualCtx)
            (env.IsType uvars) := by
          have hactualSplit : actual = actual.take (initialCount + 1) ++
              actual.drop (initialCount + 1) :=
            (List.take_append_drop (initialCount + 1) actual).symm
          have hactualReverse : actual.reverse =
              (actual.drop (initialCount + 1)).reverse ++
                (actual.take (initialCount + 1)).reverse := by
            simpa [List.reverse_append] using
              congrArg List.reverse hactualSplit
          have hctxSplit := hctx
          rw [hactualReverse] at hctxSplit
          have Hopened := OnCtx.append_right (xs :=
            (actual.drop (initialCount + 1)).reverse) (by
              simpa [List.reverse_append, List.append_assoc] using hctxSplit)
          have htake : actual.take (initialCount + 1) =
              actual.take initialCount ++ [actualDomain] := by
            simpa [actualDomain] using
              List.take_succ_eq_append_getElem hinitialLt
          simpa [actualCtx, htake, List.reverse_append,
            List.append_assoc] using Hopened
        exact hactualPrefix)
        HpartialForall HnextWF
      have hactualCtx : OnCtx (actualDomain :: actualCtx)
          (env.IsType uvars) := by
        have hactualSplit : actual = actual.take (initialCount + 1) ++
            actual.drop (initialCount + 1) :=
          (List.take_append_drop (initialCount + 1) actual).symm
        have hactualReverse : actual.reverse =
            (actual.drop (initialCount + 1)).reverse ++
              (actual.take (initialCount + 1)).reverse := by
          simpa [List.reverse_append] using
            congrArg List.reverse hactualSplit
        have hctxSplit := hctx
        rw [hactualReverse] at hctxSplit
        have Hopened := OnCtx.append_right (xs :=
          (actual.drop (initialCount + 1)).reverse) (by
            simpa [List.reverse_append, List.append_assoc] using hctxSplit)
        have htake : actual.take (initialCount + 1) =
            actual.take initialCount ++ [actualDomain] := by
          simpa [actualDomain] using
            List.take_succ_eq_append_getElem hinitialLt
        simpa [actualCtx, htake, List.reverse_append,
          List.append_assoc] using Hopened
      have HactualArg : env.HasType uvars (actualDomain :: actualCtx)
          (.bvar 0) actualDomain.lift :=
        VEnv.HasType.bvar Lookup.zero
      have HdomainWeak := HactualArg.uniqU henv hactualCtx HexpectedArg
      have HdomainU := (VEnv.IsDefEqU.weakN_iff henv hactualCtx
        (Ctx.LiftN.one (A := actualDomain))).mp (by
          simpa [VExpr.lift] using HdomainWeak)
      rcases (hactualCtx.2) with ⟨domainLevel, HactualType⟩
      have Hdomain : env.IsDefEq uvars actualCtx
          actualDomain expectedDomain (.sort domainLevel) :=
        HdomainU.of_l henv Hprior.isType HactualType
      have Hnext := VEnv.IsDefEqCtx.succ Hprior Hdomain
      have hactualTake : actual.take (initialCount + 1) =
          actual.take initialCount ++ [actualDomain] := by
        simpa [actualDomain] using
          List.take_succ_eq_append_getElem hinitialLt
      have hexpectedTake : expected.take (initialCount + 1) =
          expected.take initialCount ++ [expectedDomain] := by
        simpa [expectedDomain] using
          List.take_succ_eq_append_getElem hexpectedLt
      simpa [actualCtx, expectedCtx, hactualTake, hexpectedTake,
        List.reverse_append, List.append_assoc] using Hnext
  have H := go actual.length (Nat.le_refl _)
  have hexpectedTakeAll : expected.take actual.length = expected := by
    rw [hlength, List.take_length]
  rw [List.take_length, hexpectedTakeAll] at H
  exact H

/-- Transport a canonical application from an independently reconstructed
argument context before inverting its declared forall telescope.  Keeping
the transport separate is useful when the application and the equation
frame come from different executable passes: only their ambient dependent
contexts must be related; the canonical application term is unchanged. -/
theorem VEnv.HasType.canonicalApplicationContext_of_defeqCtx
    {fn body : VExpr}
    (henv : env.WF)
    (actual expected : List VExpr) (outer applicationCtx : List VExpr)
    (hctx : OnCtx (actual.reverse ++ outer) (env.IsType uvars))
    (hfn : env.HasType uvars outer fn
      (VExpr.wrapForalls expected body))
    (hlength : actual.length = expected.length)
    (happlicationCtx : VEnv.IsDefEqCtx env uvars [] applicationCtx
      (actual.reverse ++ outer))
    (happs : VExpr.WF env uvars applicationCtx
      (VExpr.mkApps (fn.liftN actual.length 0)
        (recursorCanonicalVars actual.length))) :
    VEnv.IsDefEqCtx env uvars []
      (actual.reverse ++ outer) (expected.reverse ++ outer) := by
  rcases happs with ⟨applicationType, Happlication⟩
  have Htransported : env.HasType uvars (actual.reverse ++ outer)
      (VExpr.mkApps (fn.liftN actual.length 0)
        (recursorCanonicalVars actual.length)) applicationType :=
    Happlication.defeqDFC henv.ordered happlicationCtx
  exact VEnv.HasType.canonicalApplicationContext henv actual expected outer
    hctx hfn hlength ⟨applicationType, Htransported⟩

/-- Version of `canonicalApplicationContext` for a function already weakened
beneath the actual argument declarations.  This is the form exposed by a
bound selected minor in the completed equation context: removing the common
weakening recovers its declared telescope, after which canonical-application
inversion compares the actual equation fields with the installed fields. -/
theorem VEnv.HasType.canonicalApplicationContext_of_weakened
    {fn body : VExpr}
    (henv : env.WF)
    (actual expected : List VExpr) (outer : List VExpr)
    (hctx : OnCtx (actual.reverse ++ outer) (env.IsType uvars))
    (hfn : env.HasType uvars (actual.reverse ++ outer)
      (fn.liftN actual.length 0)
      ((VExpr.wrapForalls expected body).liftN actual.length 0))
    (hlength : actual.length = expected.length)
    (happs : VExpr.WF env uvars (actual.reverse ++ outer)
      (VExpr.mkApps (fn.liftN actual.length 0)
        (recursorCanonicalVars actual.length))) :
    VEnv.IsDefEqCtx env uvars []
      (actual.reverse ++ outer) (expected.reverse ++ outer) := by
  have W : Ctx.LiftN actual.length 0 outer
      (actual.reverse ++ outer) := by
    exact Ctx.LiftN.zero actual.reverse (by simp)
  have hfnBase : env.HasType uvars outer fn
      (VExpr.wrapForalls expected body) :=
    (VEnv.HasType.weakN_iff henv hctx W).mp hfn
  exact VEnv.HasType.canonicalApplicationContext henv actual expected outer
    hctx hfnBase hlength happs

/-- Applying every binder of a well-typed forall telescope ending in a sort
produces another type.  Argument typing is recovered from the independently
known well-typed application and transported to the specified telescope by
uniqueness and forall injectivity. -/
theorem VEnv.HasType.mkApps_isType
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (hfn : env.HasType uvars ctx fn fnType)
    (hshape : VExpr.ForallAritySort args.length fnType)
    (happs : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    env.IsType uvars ctx (VExpr.mkApps fn args) := by
  induction args generalizing fn fnType with
  | nil =>
    cases hshape with
    | zero level => exact ⟨level, by simpa [VExpr.mkApps] using hfn⟩
  | cons arg args ih =>
    cases hshape with
    | @succ arity body domain hbody =>
      have hprefix := VExpr.WF.mkApps_fn henv.ordered hctx
        (fn := .app fn arg) (args := args) happs
      rcases hprefix.app_inv henv.ordered hctx with
        ⟨actualDomain, actualBody, hfnActual, hargActual⟩
      have hfunctionEq := hfn.uniqU henv hctx hfnActual
      have hdomainEq :=
        (VEnv.IsDefEqU.forallE_inv henv hctx hfunctionEq).1
      rcases hdomainEq with ⟨domainLevel, hdomainEq⟩
      have harg : env.HasType uvars ctx arg domain :=
        hdomainEq.defeq' hargActual
      exact ih (fn := .app fn arg) (fnType := body.inst arg)
        (hfn.app harg) (hbody.inst arg) happs

/-- The concrete owner-result spine numbers the index variables followed by
the major exactly as the canonical variables of one combined telescope. -/
theorem concreteRecursorResultArgs_eq_canonical (numIndices : Nat) :
    ((List.range numIndices).reverse.map fun index =>
        VExpr.bvar (index + 1)) ++ [.bvar 0] =
      recursorCanonicalVars (numIndices + 1) := by
  induction numIndices with
  | zero => rfl
  | succ numIndices ih =>
    rw [List.range_succ, List.reverse_append, List.map_append]
    simpa [recursorCanonicalVars_succ_cons, List.append_assoc] using
      congrArg (VExpr.bvar (numIndices + 1) :: ·) ih

@[simp] theorem recursorCanonicalVars_liftN_at_length
    (n shift : Nat) :
    (recursorCanonicalVars n).map (fun arg => arg.liftN shift n) =
      recursorCanonicalVars n := by
  rw [recursorCanonicalVars_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_lt (by omega)]

theorem recursorCanonicalVars_liftN_comp
    (n inner outer : Nat) :
    ((recursorCanonicalVars n).map (fun arg => arg.liftN inner 0)).map
        (fun arg => arg.liftN outer inner) =
      (recursorCanonicalVars n).map
        (fun arg => arg.liftN (inner + outer) 0) := by
  rw [recursorCanonicalVars_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_base, liftVar_le (by omega), liftVar_base]
    congr 1
    omega

/-- Weakening the canonical variables for an outer telescope below an inner
block gives the direct de Bruijn numbering in the combined context. -/
theorem recursorCanonicalVars_liftN_zero_eq_ofFn
    (outer inner : Nat) :
    (recursorCanonicalVars outer).map
        (fun arg => arg.liftN inner 0) =
      List.ofFn fun i : Fin outer =>
        VExpr.bvar (outer + inner - 1 - i) := by
  rw [recursorCanonicalVars_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < outer := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_base]
    congr 1
    omega

/-- Two function types expose the same dependent domains while permitting
different residual result types.  This is the exact relation needed to use
a fully typed motive application as the argument certificate for a recursor
prefix whose result inhabits that motive application. -/
inductive SameTelescopeDomains : Nat → VExpr → VExpr → Prop
  | zero (left right : VExpr) : SameTelescopeDomains 0 left right
  | succ (domain left right : VExpr) {arity : Nat} :
      SameTelescopeDomains arity left right →
      SameTelescopeDomains (arity + 1)
        (.forallE domain left) (.forallE domain right)

/-- Two types expose the same number of forall binders, without requiring
their dependent domains to be literally identical.  This is the shape
relation used when an installed constructor parameter telescope is only
definitionally equal to the corresponding family telescope. -/
inductive SameTelescopeArity : Nat → VExpr → VExpr → Prop
  | zero (left right : VExpr) : SameTelescopeArity 0 left right
  | succ (leftDomain rightDomain left right : VExpr) {arity : Nat} :
      SameTelescopeArity arity left right →
      SameTelescopeArity (arity + 1)
        (.forallE leftDomain left) (.forallE rightDomain right)

theorem SameTelescopeArity.instN
    (H : SameTelescopeArity arity left right)
    (value : VExpr) (k : Nat) :
    SameTelescopeArity arity (left.inst value k) (right.inst value k) := by
  induction H generalizing k with
  | zero => exact .zero _ _
  | @succ leftDomain rightDomain left right arity H ih =>
      apply SameTelescopeArity.succ
      simpa [VExpr.inst] using ih (k + 1)

theorem SameTelescopeArity.wrapForalls
    (leftDomains rightDomains : List VExpr)
    (hlen : leftDomains.length = rightDomains.length)
    (left right : VExpr) :
    SameTelescopeArity leftDomains.length
      (VExpr.wrapForalls leftDomains left)
      (VExpr.wrapForalls rightDomains right) := by
  induction leftDomains generalizing rightDomains with
  | nil =>
    have hright : rightDomains = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst rightDomains
    exact .zero _ _
  | cons leftDomain leftDomains ih =>
    cases rightDomains with
    | nil => simp at hlen
    | cons rightDomain rightDomains =>
      apply SameTelescopeArity.succ
      exact ih rightDomains (by simpa using Nat.succ.inj hlen)

theorem SameTelescopeDomains.wrapForalls
    (domains : List VExpr) (left right : VExpr) :
    SameTelescopeDomains domains.length
      (VExpr.wrapForalls domains left)
      (VExpr.wrapForalls domains right) := by
  induction domains with
  | nil => exact .zero _ _
  | cons domain domains ih =>
    exact .succ domain _ _ ih

/-- Simultaneous substitution preserves a shared dependent-domain spine. -/
theorem SameTelescopeDomains.instN
    (H : SameTelescopeDomains arity left right)
    (value : VExpr) (k : Nat) :
    SameTelescopeDomains arity (left.inst value k) (right.inst value k) := by
  induction H generalizing k with
  | zero => exact .zero _ _
  | @succ domain left right arity H ih =>
    apply SameTelescopeDomains.succ
    simpa [VExpr.inst] using ih (k + 1)

/-- Consume a syntactic forall telescope with the supplied arguments and
return its instantiated residual type.  The fallback branch is irrelevant
for typed uses but keeps the operation total. -/
def VExpr.applyForallType : VExpr → List VExpr → VExpr
  | type, [] => type
  | .forallE _ body, arg :: args => applyForallType (body.inst arg) args
  | type, _ :: _ => type

/-- Definitional equality between two equally long dependent function types
survives consumption of the same well-typed argument spine.  The domains may
differ definitionally; `forallE_inv` transports each argument through the
left domain before substituting it into both residuals. -/
theorem VEnv.IsDefEqU.applyForallType
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hshape : SameTelescopeArity args.length leftType rightType)
    (Htypes : env.IsDefEqU uvars ctx leftType rightType)
    (Hleft : env.HasType uvars ctx fn leftType)
    (Happs : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    env.IsDefEqU uvars ctx
      (VExpr.applyForallType leftType args)
      (VExpr.applyForallType rightType args) := by
  induction args generalizing fn leftType rightType with
  | nil =>
    cases Hshape with
    | zero => simpa [VExpr.applyForallType] using Htypes
  | cons arg args ih =>
    cases Hshape with
    | @succ leftDomain rightDomain leftBody rightBody arity Htail =>
      have Harg : env.HasType uvars ctx arg leftDomain :=
        VEnv.HasType.mkApps_head henv hctx Hleft Happs
      rcases (VEnv.IsDefEqU.forallE_inv henv hctx Htypes).2 with
        ⟨bodyLevel, Hbody⟩
      have HbodyInst : env.IsDefEqU uvars ctx
          (leftBody.inst arg) (rightBody.inst arg) := by
        refine ⟨.sort bodyLevel, ?_⟩
        simpa [VExpr.inst] using
          Hbody.instN henv.ordered Harg .zero
      have HleftApp : env.HasType uvars ctx (.app fn arg)
          (leftBody.inst arg) := Hleft.app Harg
      have HappRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app fn arg) args) := by
        simpa [VExpr.mkApps] using Happs
      have Hrest := ih (fn := .app fn arg)
        (Htail.instN arg 0) HbodyInst HleftApp HappRest
      simpa [VExpr.applyForallType] using Hrest

/-- Source-side residual substitution matching complete application of a
forall telescope.  At each step the outer binder lies beneath all still-inner
binders in the already-open body, hence the decreasing `args.length` cutoff. -/
def Expr.instantiateForallBody : Expr → List Expr → Expr
  | body, [] => body
  | body, arg :: args =>
      instantiateForallBody (body.instantiate1' arg args.length) args

/-- The residual recorded by a typed application spine is the literal
result of consuming its initial forall type with the same arguments.  This
keeps later dependent application proofs from having to existentially forget
the result type they have already computed. -/
theorem VEnv.TypedApplicationSpine.result_eq_applyForallType
    (H : VEnv.TypedApplicationSpine env uvars ctx fn fnType args resultType) :
    resultType = VExpr.applyForallType fnType args := by
  induction H with
  | nil _ => rfl
  | cons _ _ _ ih =>
      simpa [VExpr.applyForallType] using ih

def VExpr.instForallDomains : List VExpr → VExpr → Nat → List VExpr
  | [], _, _ => []
  | domain :: domains, arg, k =>
      domain.inst arg k :: instForallDomains domains arg (k + 1)

@[simp] theorem VExpr.instForallDomains_length :
    (VExpr.instForallDomains domains arg k).length = domains.length := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
    simp [VExpr.instForallDomains, ih]

theorem VExpr.instForallDomains_append
    (left right : List VExpr) (arg : VExpr) (k : Nat) :
    VExpr.instForallDomains (left ++ right) arg k =
      VExpr.instForallDomains left arg k ++
        VExpr.instForallDomains right arg (k + left.length) := by
  induction left generalizing k with
  | nil => rfl
  | cons domain left ih =>
    simp [VExpr.instForallDomains, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

theorem VExpr.inst_wrapForalls
    (domains : List VExpr) (body arg : VExpr) (k : Nat) :
    (VExpr.wrapForalls domains body).inst arg k =
      VExpr.wrapForalls (VExpr.instForallDomains domains arg k)
        (body.inst arg (k + domains.length)) := by
  induction domains generalizing k with
  | nil => simp [VExpr.wrapForalls, VExpr.instForallDomains]
  | cons domain domains ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons,
      VExpr.instForallDomains, VExpr.inst]
    congr 1
    change (VExpr.wrapForalls domains body).inst arg (k + 1) =
      VExpr.wrapForalls (VExpr.instForallDomains domains arg (k + 1))
        (body.inst arg (k + (domains.length + 1)))
    rw [show k + (domains.length + 1) = k + 1 + domains.length by omega]
    exact ih (k + 1)

/-- Place independently typed closed domains into one dependent telescope.
The domain at chronological position `i` is weakened below the `i` earlier
binders, so substituting those binders recovers its original closed type. -/
def VExpr.liftClosedDomains : List VExpr → Nat → List VExpr
  | [], _ => []
  | domain :: domains, depth =>
      domain.liftN depth 0 :: liftClosedDomains domains (depth + 1)

@[simp] theorem VExpr.liftClosedDomains_length :
    (VExpr.liftClosedDomains domains depth).length = domains.length := by
  induction domains generalizing depth with
  | nil => rfl
  | cons domain domains ih =>
    simp [VExpr.liftClosedDomains, ih]

theorem VExpr.liftClosedDomains_getElem
    (domains : List VExpr) (depth i : Nat)
    (hi : i < domains.length) :
    (VExpr.liftClosedDomains domains depth)[i]'(by simpa using hi) =
      domains[i].liftN (depth + i) 0 := by
  induction domains generalizing depth i with
  | nil => simp at hi
  | cons domain domains ih =>
    cases i with
    | zero => simp [VExpr.liftClosedDomains]
    | succ i =>
      have hi' : i < domains.length := by simpa using hi
      simpa [VExpr.liftClosedDomains, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (depth + 1) i hi'

theorem VExpr.liftClosedDomains_take
    (domains : List VExpr) (depth count : Nat) :
    (VExpr.liftClosedDomains domains depth).take count =
      VExpr.liftClosedDomains (domains.take count) depth := by
  induction domains generalizing depth count with
  | nil => simp [VExpr.liftClosedDomains]
  | cons domain domains ih =>
    cases count with
    | zero => simp [VExpr.liftClosedDomains]
    | succ count =>
      simp [VExpr.liftClosedDomains, ih]

/-- Instantiating the next binder cancels one layer of the systematic
weakening in every later independent domain. -/
theorem VExpr.instForallDomains_liftClosedDomains_succ
    (domains : List VExpr) (arg : VExpr) (k : Nat) :
    VExpr.instForallDomains
        (VExpr.liftClosedDomains domains (k + 1)) arg k =
      VExpr.liftClosedDomains domains k := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
    simp only [VExpr.liftClosedDomains, VExpr.instForallDomains]
    have hhead : (domain.liftN (k + 1) 0).inst arg k =
        domain.liftN k 0 := by
      rw [show domain.liftN (k + 1) 0 =
          (domain.liftN k 0).liftN 1 k by
        simpa [Nat.add_comm] using
          (VExpr.liftN'_liftN_lo domain 1 k).symm]
      exact VExpr.inst_liftN (domain.liftN k 0) arg
    rw [hhead]
    congr 1
    simpa [Nat.add_assoc] using ih (k + 1)

/-- Consume a dependent telescope assembled from independently typed closed
arguments.  This packages the substitution bookkeeping needed by generated
minor hypotheses: after each application, `liftClosedDomains` and
`instForallDomains` reduce the remaining domains back to the same invariant. -/
theorem VEnv.TypedApplicationSpine.liftClosedDomains
    (henv : env.Ordered)
    (Hfn : env.HasType uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType))
    (Hargs : List.Forall₂
      (env.HasType uvars ctx) args types) :
    ∃ finalType, VEnv.TypedApplicationSpine env uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType)
      args finalType := by
  induction Hargs generalizing fn resultType with
  | nil =>
    exact ⟨resultType, by
      simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using
        (VEnv.TypedApplicationSpine.nil Hfn)⟩
  | @cons arg domain args types Harg Hargs ih =>
    have Hfn' : env.HasType uvars ctx fn
        (.forallE domain
          (VExpr.wrapForalls (VExpr.liftClosedDomains types 1)
            resultType)) := by
      simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using Hfn
    have Happ := Hfn'.app Harg
    have Happ' : env.HasType uvars ctx (.app fn arg)
        (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
          (resultType.inst arg types.length)) := by
      rw [VExpr.inst_wrapForalls] at Happ
      simpa [VExpr.instForallDomains_liftClosedDomains_succ] using Happ
    rcases ih Happ' with ⟨finalType, Htail⟩
    have Htail' : VEnv.TypedApplicationSpine env uvars ctx (.app fn arg)
        ((VExpr.wrapForalls (VExpr.liftClosedDomains types 1)
          resultType).inst arg) args finalType := by
      rw [VExpr.inst_wrapForalls,
        VExpr.instForallDomains_liftClosedDomains_succ]
      simpa using Htail
    refine ⟨finalType, ?_⟩
    simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using
      (VEnv.TypedApplicationSpine.cons Hfn' Harg Htail')

theorem VExpr.inst_mkApps
    (fn arg : VExpr) (args : List VExpr) (k : Nat) :
    (VExpr.mkApps fn args).inst arg k =
      VExpr.mkApps (fn.inst arg k) (args.map fun e => e.inst arg k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons head tail ih =>
    simpa [VExpr.mkApps, VExpr.inst] using ih (.app fn head)

theorem VExpr.liftN_succ_inst_at_length
    (fn arg : VExpr) (n : Nat) :
    (fn.liftN (n + 1) 0).inst arg n = fn.liftN n 0 := by
  rw [show fn.liftN (n + 1) 0 =
      (fn.liftN n 0).liftN 1 n by
    simpa [Nat.add_comm] using
      (VExpr.liftN'_liftN_lo fn 1 n).symm]
  exact VExpr.inst_liftN (fn.liftN n 0) arg

@[simp] theorem recursorCanonicalVars_inst_at_length
    (n : Nat) (arg : VExpr) :
    (recursorCanonicalVars n).map (fun e => e.inst arg n) =
      recursorCanonicalVars n := by
  rw [recursorCanonicalVars_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.inst,
      VExpr.instVar]
    rw [if_pos (by omega)]

theorem VExpr.inst_canonicalResult
    (fn arg : VExpr) (n : Nat) :
    (VExpr.mkApps (fn.liftN (n + 1) 0)
        (recursorCanonicalVars (n + 1))).inst arg n =
      VExpr.mkApps ((VExpr.app fn arg).liftN n 0)
        (recursorCanonicalVars n) := by
  rw [VExpr.inst_mkApps, recursorCanonicalVars_succ_cons,
    List.map_cons, recursorCanonicalVars_inst_at_length,
    VExpr.liftN_succ_inst_at_length]
  simp [VExpr.mkApps, VExpr.inst, VExpr.instVar, VExpr.liftN]

/-- Opening a canonical result spine and substituting one argument for each
telescope binder produces the same application with those concrete
arguments. -/
theorem VExpr.applyForallType_wrapForalls_canonical
    (domains args : List VExpr) (fn : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains
          (VExpr.mkApps (fn.liftN domains.length 0)
            (recursorCanonicalVars domains.length))) args =
      VExpr.mkApps fn args := by
  have go : ∀ n (domains args : List VExpr) (fn : VExpr),
      domains.length = n → args.length = n →
      VExpr.applyForallType
          (VExpr.wrapForalls domains
            (VExpr.mkApps (fn.liftN n 0)
              (recursorCanonicalVars n))) args =
        VExpr.mkApps fn args := by
    intro n
    induction n with
    | zero =>
      intro domains args fn hdomains hargs
      have hdomains' : domains = [] :=
        List.eq_nil_of_length_eq_zero hdomains
      have hargs' : args = [] :=
        List.eq_nil_of_length_eq_zero hargs
      subst domains
      subst args
      simp [VExpr.applyForallType, VExpr.wrapForalls, VExpr.mkApps]
    | succ n ih =>
      intro domains args fn hdomains hargs
      cases domains with
      | nil => simp at hdomains
      | cons domain domains =>
        cases args with
        | nil => simp at hargs
        | cons arg args =>
          have hdomainsTail : domains.length = n := by
            simpa using Nat.succ.inj hdomains
          have hargsTail : args.length = n := by
            simpa using Nat.succ.inj hargs
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (VExpr.mkApps (fn.liftN (n + 1) 0)
                (recursorCanonicalVars (n + 1)))).inst arg) args =
            VExpr.mkApps fn (arg :: args)
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [hdomainsTail]
          rw [VExpr.inst_canonicalResult]
          exact ih (VExpr.instForallDomains domains arg 0) args
            (VExpr.app fn arg) (by simpa using hdomainsTail) hargsTail
  exact go domains.length domains args fn rfl hlength

/-- A well-typed complete application of the right-hand function supplies
all dependent argument premises for the left-hand function when their types
have the same telescope domains.  No equality between the two residual
result types is required. -/
theorem VEnv.HasType.mkApps_sameTelescopeDomains
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hdomains : SameTelescopeDomains args.length leftType rightType)
    (Hleft : env.HasType uvars ctx left leftType)
    (Hright : env.HasType uvars ctx right rightType)
    (HrightApps : VExpr.WF env uvars ctx (VExpr.mkApps right args)) :
    VExpr.WF env uvars ctx (VExpr.mkApps left args) := by
  induction args generalizing left right leftType rightType with
  | nil =>
    cases Hdomains with
    | zero =>
      refine ⟨leftType, ?_⟩
      change env.IsDefEq uvars ctx left left leftType
      exact Hleft
  | cons arg args ih =>
    cases Hdomains with
    | @succ domain leftBody rightBody arity Htail =>
      have Harg := VEnv.HasType.mkApps_head henv hctx Hright HrightApps
      have HleftApp := Hleft.app Harg
      have HrightApp := Hright.app Harg
      have Htail' := Htail.instN arg 0
      have HrightRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app right arg) args) := by
        simpa [VExpr.mkApps] using HrightApps
      simpa [VExpr.mkApps] using
        ih Htail' HleftApp HrightApp HrightRest

/-- Exact-result strengthening of `mkApps_sameTelescopeDomains`.  Besides
recovering each argument from the independently typed right application, it
records the residual type obtained by instantiating the left forall
telescope. -/
theorem VEnv.HasType.mkApps_sameTelescopeDomains_exact
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hdomains : SameTelescopeDomains args.length leftType rightType)
    (Hleft : env.HasType uvars ctx left leftType)
    (Hright : env.HasType uvars ctx right rightType)
    (HrightApps : VExpr.WF env uvars ctx (VExpr.mkApps right args)) :
    env.HasType uvars ctx (VExpr.mkApps left args)
      (VExpr.applyForallType leftType args) := by
  induction args generalizing left right leftType rightType with
  | nil =>
    cases Hdomains with
    | zero => simpa [VExpr.mkApps, VExpr.applyForallType] using Hleft
  | cons arg args ih =>
    cases Hdomains with
    | @succ domain leftBody rightBody arity Htail =>
      have Harg := VEnv.HasType.mkApps_head henv hctx Hright HrightApps
      have HleftApp := Hleft.app Harg
      have HrightApp := Hright.app Harg
      have Htail' := Htail.instN arg 0
      have HrightRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app right arg) args) := by
        simpa [VExpr.mkApps] using HrightApps
      simpa [VExpr.mkApps, VExpr.applyForallType] using
        ih Htail' HleftApp HrightApp HrightRest

/-- Parallel telescope relation between an inductive family and its motive.
Both functions consume the same dependent domains.  Once all domains have
been consumed, the motive expects an inhabitant of the corresponding family
application and returns the selected elimination sort. -/
inductive RecursorMotiveTelescope (resultLevel : VLevel) :
    Nat → VExpr → VExpr → VExpr → Prop
  | zero (family familyType : VExpr) :
      RecursorMotiveTelescope resultLevel 0 family familyType
        (.forallE family (.sort resultLevel))
  | succ (family domain familyType motiveType : VExpr) {arity : Nat} :
      RecursorMotiveTelescope resultLevel arity
        (.app (family.liftN 1 0) (.bvar 0)) familyType motiveType →
      RecursorMotiveTelescope resultLevel (arity + 1) family
        (.forallE domain familyType) (.forallE domain motiveType)

/-- Closing the same dependent domains over a family result and over the
corresponding family-major proposition produces a parallel motive
telescope. -/
theorem RecursorMotiveTelescope.wrapForalls
    (domains : List VExpr) (family familyResult : VExpr)
    (resultLevel : VLevel) :
    RecursorMotiveTelescope resultLevel domains.length family
      (VExpr.wrapForalls domains familyResult)
      (VExpr.wrapForalls domains
        (.forallE
          (VExpr.mkApps (family.liftN domains.length 0)
            (recursorCanonicalVars domains.length))
          (.sort resultLevel))) := by
  induction domains generalizing family with
  | nil =>
    simpa [VExpr.wrapForalls, VExpr.mkApps] using
      (RecursorMotiveTelescope.zero (resultLevel := resultLevel)
        family familyResult)
  | cons domain domains ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.wrapForalls, recursorCanonicalVars_succ_cons,
      VExpr.mkApps, VExpr.liftN, VExpr.liftN_liftN, Nat.add_comm] using
      ih (.app (family.liftN 1 0) (.bvar 0))

/-- Weakening all three expressions preserves a parallel motive telescope. -/
theorem RecursorMotiveTelescope.liftN
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (n k : Nat) :
    RecursorMotiveTelescope resultLevel arity
      (family.liftN n k) (familyType.liftN n k)
      (motiveType.liftN n k) := by
  induction H generalizing k with
  | zero => simp [VExpr.liftN, RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.liftN, VExpr.lift, VExpr.lift_liftN'] using ih (k + 1)

/-- Weakening a parallel motive telescope by an arbitrary context embedding
preserves the relation.  The embedding is extended below each shared binder,
exactly as `VExpr.lift'` traverses a dependent forall. -/
theorem RecursorMotiveTelescope.lift'
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (shift : Lift) :
    RecursorMotiveTelescope resultLevel arity
      (family.lift' shift) (familyType.lift' shift)
      (motiveType.lift' shift) := by
  induction H generalizing shift with
  | zero => simp [RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.liftN, VExpr.lift, VExpr.lift_eq_lift',
      ← VExpr.lift'_comp] using ih shift.cons

/-- Simultaneous term substitution preserves the parallel family/motive
telescope relation.  The explicit cutoff is needed under dependent binders. -/
theorem RecursorMotiveTelescope.instN
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (value : VExpr) (k : Nat) :
    RecursorMotiveTelescope resultLevel arity
      (family.inst value k) (familyType.inst value k)
      (motiveType.inst value k) := by
  induction H generalizing k with
  | zero => simp [VExpr.inst, RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
      apply RecursorMotiveTelescope.succ
      simpa [VExpr.inst, VExpr.lift, VExpr.lift_instN_lo] using
        ih (k + 1)

/-- Consuming the outer shared domain advances a parallel telescope to the
family application at that argument. -/
theorem RecursorMotiveTelescope.consume
    (H : RecursorMotiveTelescope resultLevel (arity + 1) family
      (.forallE domain familyType) (.forallE domain motiveType))
    (arg : VExpr) :
    RecursorMotiveTelescope resultLevel arity (.app family arg)
      (familyType.inst arg) (motiveType.inst arg) := by
  cases H with
  | @succ _ _ _ _ _ Htail =>
      simpa [VExpr.inst, VExpr.instN_bvar0, VExpr.inst_liftN] using
        RecursorMotiveTelescope.instN Htail arg 0

/-- Apply a family and a parallel motive to the same argument spine, then
apply the resulting motive to a major premise of the family application.
Typing of the shared arguments is recovered from the independently typed
family application and transported to the declared telescope by uniqueness.
The exact result sort is retained for consumers that must type an equation
body rather than merely prove that it is a type. -/
theorem RecursorMotiveTelescope.applyMajorTyped
    {args : List VExpr} {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {motive major : VExpr}
    (H : RecursorMotiveTelescope resultLevel args.length family
      familyType motiveType)
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfamily : env.HasType uvars ctx family familyType)
    (Hmotive : env.HasType uvars ctx motive motiveType)
    (Hmajor : env.HasType uvars ctx major (VExpr.mkApps family args)) :
    env.HasType uvars ctx
      (.app (VExpr.mkApps motive args) major) (.sort resultLevel) := by
  induction args generalizing family familyType motive motiveType with
  | nil =>
      cases H with
      | zero =>
          simpa [VExpr.mkApps, VExpr.inst] using
            VEnv.HasType.app Hmotive Hmajor
  | cons arg args ih =>
      cases H with
      | @succ _ domain familyBody motiveBody _ Htail =>
        have HfamilyAppType := Hmajor.isType henv hctx
        have HfamilyAppWF : VExpr.WF env uvars ctx
            (VExpr.mkApps family (arg :: args)) := by
          rcases HfamilyAppType with ⟨level, Htype⟩
          exact ⟨.sort level, Htype⟩
        have Hprefix := VExpr.WF.mkApps_fn henv.ordered hctx
          (fn := .app family arg) (args := args) HfamilyAppWF
        rcases Hprefix.app_inv henv.ordered hctx with
          ⟨actualDomain, actualBody, HfamilyActual, HargActual⟩
        have HfunctionEq := Hfamily.uniqU henv hctx HfamilyActual
        have HdomainEq :=
          (VEnv.IsDefEqU.forallE_inv henv hctx HfunctionEq).1
        rcases HdomainEq with ⟨domainLevel, HdomainEq⟩
        have Harg : env.HasType uvars ctx arg domain :=
          HdomainEq.defeq' HargActual
        have Hfamily' : env.HasType uvars ctx (.app family arg)
            (familyBody.inst arg) := Hfamily.app Harg
        have Hmotive' : env.HasType uvars ctx (.app motive arg)
            (motiveBody.inst arg) := Hmotive.app Harg
        have Htail' := Htail.instN arg 0
        have Htail'' : RecursorMotiveTelescope resultLevel args.length
            (.app family arg) (familyBody.inst arg)
            (motiveBody.inst arg) := by
          simpa [VExpr.inst, VExpr.instN_bvar0, VExpr.inst_liftN] using Htail'
        exact ih Htail'' Hfamily' Hmotive' Hmajor

/-- Typehood wrapper around `applyMajorTyped`. -/
theorem RecursorMotiveTelescope.applyMajor
    {args : List VExpr} {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {motive major : VExpr}
    (H : RecursorMotiveTelescope resultLevel args.length family
      familyType motiveType)
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfamily : env.HasType uvars ctx family familyType)
    (Hmotive : env.HasType uvars ctx motive motiveType)
    (Hmajor : env.HasType uvars ctx major (VExpr.mkApps family args)) :
    env.IsType uvars ctx
      (.app (VExpr.mkApps motive args) major) :=
  ⟨resultLevel, H.applyMajorTyped henv hctx Hfamily Hmotive Hmajor⟩

@[simp] theorem VExpr.getAppFnArgs_mkApps_bvar
    (index : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar index) args).getAppFnArgs = (.bvar index, args) := by
  simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using
    VExpr.getAppFnArgs_mkApps (.bvar index) args

theorem VExpr.IsFieldApp.mkApps
    (hfield : field ∈ fieldVars) (args : List VExpr) :
    (VExpr.mkApps (.bvar (field + depth)) args).IsFieldApp fieldVars depth := by
  exact ⟨field, hfield, args, VExpr.getAppFnArgs_mkApps_bvar _ _⟩

theorem VExpr.lift'_mkApps
    (fn : VExpr) (args : List VExpr) (shift : Lift) :
    (VExpr.mkApps fn args).lift' shift =
      VExpr.mkApps (fn.lift' shift)
        (args.map fun arg => arg.lift' shift) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simpa [VExpr.mkApps] using ih (.app fn arg)

theorem VExpr.IsFieldApp.lift
    {e : VExpr}
    (H : e.IsFieldApp fieldVars depth) (n : Nat) :
    (e.liftN n 0).IsFieldApp fieldVars (depth + n) := by
  rcases H with ⟨field, hfield, args, hspine⟩
  have hrebuild := VExpr.mkApps_getAppFnArgs e
  rw [hspine] at hrebuild
  rw [← hrebuild, VExpr.liftN_mkApps]
  have hhead : (VExpr.bvar (field + depth)).liftN n 0 =
      .bvar (field + (depth + n)) := by
    simp [VExpr.liftN, liftVar]
    omega
  rw [hhead]
  exact VExpr.IsFieldApp.mkApps hfield _

theorem VExpr.IsFieldApp.appendApps
    {e : VExpr}
    (H : e.IsFieldApp fieldVars depth) (more : List VExpr) :
    (VExpr.mkApps e more).IsFieldApp fieldVars depth := by
  rcases H with ⟨field, hfield, args, hspine⟩
  refine ⟨field, hfield, args ++ more, ?_⟩
  simpa [hspine] using VExpr.getAppFnArgs_mkApps e more

theorem VExpr.bvarHead?_eq_some
    {e : VExpr} {field : Nat}
    (h : e.bvarHead? = some field) :
    ∃ args, e.getAppFnArgs = (.bvar field, args) := by
  unfold VExpr.bvarHead? at h
  cases hspine : e.getAppFnArgs with
  | mk head args =>
    rw [hspine] at h
    cases head <;> simp at h
    rename_i index
    cases h
    exact ⟨args, rfl⟩

/-- Every recursive argument whose application head is a de Bruijn variable
is, by construction, designated by `IotaRule.fieldVars`. -/
theorem VExpr.IsFieldApp.ofRecursiveArg
    {arg : VExpr} {recursiveArgs : List VExpr} {field : Nat}
    (harg : arg ∈ recursiveArgs)
    (hhead : arg.bvarHead? = some field) :
    arg.IsFieldApp (recursiveArgs.filterMap VExpr.bvarHead?) 0 := by
  rcases VExpr.bvarHead?_eq_some hhead with ⟨args, hspine⟩
  refine ⟨field, ?_, args, by simpa using hspine⟩
  exact List.mem_filterMap.mpr ⟨arg, harg, hhead⟩

/-- Expressions containing none of the installed recursor names satisfy the
iota guard structurally. This is the ordinary-expression half of the guard;
actual recursive calls are introduced only through `GuardedIota.recCall`. -/
theorem VExpr.GuardedIota.ofContainsAnyConstFalse
    {e : VExpr} {recursors : List Name} {fieldVars : List Nat}
    {depth : Nat}
    (h : e.containsAnyConst recursors = false) :
    e.GuardedIota recursors fieldVars depth := by
  induction e generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const name levels =>
      apply VExpr.GuardedIota.const
      intro hmem
      simp [VExpr.containsAnyConst] at h
      exact h hmem
  | app fn arg ihFn ihArg =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .app (ihFn h.1) (ihArg h.2)
  | proj typeName index major ihMajor =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .proj (ihMajor h.2)
  | lam dom body ihDom ihBody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .lam (ihDom h.1) (ihBody h.2)
  | forallE dom body ihDom ihBody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .forallE (ihDom h.1) (ihBody h.2)

/-- The guarded-iota judgment follows source-visible constant support.
Primitive projection nodes contribute the support of their source major. -/
theorem VExpr.SourceConstFree.guardedIota
    (H : VExpr.SourceConstFree recursors e) :
    VExpr.GuardedIota recursors fieldVars depth e := by
  induction H generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const name levels fresh => exact .const fresh
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | proj _ _ _ ihMajor => exact .proj ihMajor
  | lam _ _ ihDomain ihBody =>
      exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody =>
      exact .forallE ihDomain ihBody

/-- Closing a guarded body over recursor-free domains preserves the guard,
with the body checked beneath exactly the number of introduced binders. -/
theorem VExpr.GuardedIota.wrapLams
    {recursors : List Name} {fieldVars : List Nat}
    {domains : List VExpr} {body : VExpr} {depth : Nat}
    (hdomains : ∀ dom ∈ domains, dom.SourceConstFree recursors)
    (hbody : body.GuardedIota recursors fieldVars
      (depth + domains.length)) :
    (VExpr.wrapLams domains body).GuardedIota recursors fieldVars depth := by
  induction domains generalizing depth with
  | nil => simpa [VExpr.wrapLams] using hbody
  | cons dom domains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons]
      apply VExpr.GuardedIota.lam
      · exact VExpr.SourceConstFree.guardedIota
          (hdomains dom (by simp))
      · apply ih
        · intro inner hinner
          exact hdomains inner (by simp [hinner])
        · simpa [Nat.add_assoc, Nat.add_comm 1 domains.length] using hbody

/-- If a lambda telescope contains none of the selected constants, neither
its binder domains nor its residual body contain one. -/
theorem VExpr.containsAnyConst_wrapLams_false
    {domains : List VExpr} {body : VExpr} {names : List Name}
    (hfree : (VExpr.wrapLams domains body).containsAnyConst names = false) :
    (∀ dom ∈ domains, dom.containsAnyConst names = false) ∧
      body.containsAnyConst names = false := by
  induction domains with
  | nil => simpa [VExpr.wrapLams] using hfree
  | cons dom domains ih =>
    simp only [VExpr.wrapLams, List.foldr_cons, VExpr.containsAnyConst,
      Bool.or_eq_false_iff] at hfree
    rcases ih hfree.2 with ⟨hdomains, hbody⟩
    exact ⟨by
      intro current hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hfree.1
      · exact hdomains current hmem, hbody⟩

theorem VExpr.GuardedIota.mkApps
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {fn : VExpr} {args : List VExpr}
    (hfn : fn.GuardedIota recursors fieldVars depth)
    (hargs : ∀ arg ∈ args,
      arg.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps fn args).GuardedIota recursors fieldVars depth := by
  induction args generalizing fn with
  | nil => simpa [VExpr.mkApps] using hfn
  | cons arg args ih =>
      rw [VExpr.mkApps]
      apply ih
      · exact .app hfn (hargs arg (by simp))
      · intro inner hinner
        exact hargs inner (by simp [hinner])

/-- The executable iota RHS applies a minor variable first to every
constructor field and then to the generated recursive results. Once those
two argument groups are guarded, the complete spine is guarded. -/
theorem VExpr.GuardedIota.minorRhs
    {recursors : List Name} {fieldVars : List Nat} {depth minorVar : Nat}
    {fieldArgs recursiveResults : List VExpr}
    (hfields : ∀ arg ∈ fieldArgs,
      arg.GuardedIota recursors fieldVars depth)
    (hresults : ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps (.bvar minorVar) (fieldArgs ++ recursiveResults)).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.mkApps .bvar
  intro arg harg
  rcases List.mem_append.mp harg with hfield | hresult
  · exact hfields arg hfield
  · exact hresults arg hresult

/-- Canonical guarded shape of a generated higher-order recursive result:
zero or more recursor-free lambda domains close a recursor application whose
major premise is an application of a designated constructor field. -/
theorem VExpr.GuardedIota.recCallWrapped
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {domains : List VExpr} {recursor : Name} {levels : List VLevel}
    {init : List VExpr} {major : VExpr}
    (hdomains : ∀ dom ∈ domains, dom.SourceConstFree recursors)
    (hrecursor : recursor ∈ recursors)
    (hargs : ∀ arg ∈ init ++ [major],
      arg.GuardedIota recursors fieldVars (depth + domains.length))
    (hmajor : major.IsFieldApp fieldVars (depth + domains.length)) :
    (VExpr.wrapLams domains <|
      VExpr.mkApps (.const recursor levels) (init ++ [major])).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.wrapLams hdomains
  exact .recCall hrecursor hargs hmajor

/-- Semantic image of one higher-order recursive result emitted by
`mkRecRules.loopU`.  This is deliberately independent of the executable
syntax: the generator-facing proof only has to show that translating one
`GeneratedRecursiveCall` produces this shape. -/
structure IotaRecursiveResultCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (_recursiveArg result : VExpr) where
  domains : List VExpr
  recursor : Name
  levels : List VLevel
  init : List VExpr
  major : VExpr
  result_eq : result = (VExpr.wrapLams domains <|
    VExpr.mkApps (.const recursor levels) (init ++ [major]))
  domains_recursor_free : ∀ dom ∈ domains,
    dom.SourceConstFree recursors
  recursor_mem : recursor ∈ recursors
  arguments_guarded : ∀ arg ∈ init ++ [major],
    arg.GuardedIota recursors fieldVars domains.length
  major_is_field : major.IsFieldApp fieldVars domains.length

theorem IotaRecursiveResultCertificate.guarded
    (H : IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) :
    result.GuardedIota recursors fieldVars 0 := by
  rw [H.result_eq]
  exact VExpr.GuardedIota.recCallWrapped H.domains_recursor_free
    H.recursor_mem (by simpa using H.arguments_guarded)
      (by simpa using H.major_is_field)

/-- Pointwise alignment of selected recursive constructor arguments with the
translated recursive results supplied to the minor premise. -/
structure IotaRecursiveResultsCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (recursiveArgs recursiveResults : List VExpr) : Prop where
  aligned : List.Forall₂ (fun major result =>
    Nonempty (IotaRecursiveResultCertificate
      recursors fieldVars major result)) recursiveArgs recursiveResults

theorem IotaRecursiveResultsCertificate.length
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    recursiveResults.length = recursiveArgs.length := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem IotaRecursiveResultsCertificate.results_guarded
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars 0 := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => simp
  | cons hhead _ ih =>
    intro result hresult
    simp only [List.mem_cons] at hresult
    rcases hresult with rfl | htail
    · rcases hhead with ⟨cert⟩
      exact cert.guarded
    · exact ih result htail

/-- Once ordinary constructor arguments are recursor-free, the aligned
recursive-result certificate discharges guardedness of the complete minor
application used on an iota right-hand side. -/
theorem IotaRecursiveResultsCertificate.minorRhs
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults)
    (hfields : ∀ arg ∈ fieldArgs,
      arg.SourceConstFree recursors) :
    (VExpr.mkApps (.bvar minorVar)
      (fieldArgs ++ recursiveResults)).GuardedIota
        recursors fieldVars 0 := by
  apply VExpr.GuardedIota.minorRhs
  · intro arg harg
    exact VExpr.SourceConstFree.guardedIota (hfields arg harg)
  · exact H.results_guarded

/-- Complete right-hand-side fragment of an iota rule. The executable minor
application is represented once; its spine, field/result split, cardinality,
and guardedness are derived below. -/
structure IotaRhsCertificate
    (recursors : List Name) (domains fieldArgs recursiveArgs : List VExpr)
    (rhsBody : VExpr) where
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  recursiveResults : List VExpr
  rhs_eq : rhsBody = VExpr.mkApps (.bvar minorVar)
    (fieldArgs ++ recursiveResults)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  fields_recursor_free : ∀ arg ∈ fieldArgs,
    arg.SourceConstFree recursors
  recursive_results : IotaRecursiveResultsCertificate
    recursors fieldVars recursiveArgs recursiveResults

theorem IotaRhsCertificate.rhs_spine
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.getAppFnArgs =
      (.bvar H.minorVar, fieldArgs ++ H.recursiveResults) := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.getAppFnArgs =
    (.bvar minorVar, fieldArgs ++ results)
  rw [hrhs]
  exact VExpr.getAppFnArgs_mkApps_bvar _ _

theorem IotaRhsCertificate.field_args
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    (fieldArgs ++ H.recursiveResults).take fieldArgs.length = fieldArgs := by
  simp

theorem IotaRhsCertificate.results_length
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    ((fieldArgs ++ H.recursiveResults).drop fieldArgs.length).length =
      recursiveArgs.length := by
  simpa using H.recursive_results.length

theorem IotaRhsCertificate.guarded
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.GuardedIota recursors H.fieldVars 0 := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.GuardedIota recursors fieldVars 0
  rw [hrhs]
  exact hresults.minorRhs hfieldsFree


end VerifyInductive
end Lean4Lean
