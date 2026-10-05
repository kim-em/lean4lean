import Lean4Lean.Theory.Typing.NativeCaptureTransport
import Lean4Lean.Theory.Typing.SplitProofFrame
import Lean4Lean.Theory.Typing.SharedProofInterleaving

/-!
Canonical fresh proof captures for a fixed constructor-field plan.

`CapturePlan` fixes every index position and every proof allocation. Its
context and capture expressions are independent of the original proof
witnesses. `abstractReplay` derives an actual native replay in that context,
related captures, and a split proof frame from the existing replay evidence.
The typed retraction recovers an actual replay in the original context.

This is not yet a canonical native reduction strategy. Constructing the
initial replay and the plan from installed metadata, proving full trace
stability, and establishing logical-relation adequacy remain obligations.
No caller-supplied equality or computation callback is introduced here.
-/

/-!
Scratch proof of the fixed-field-plan abstraction for the actual
`NativeCaptureReplay` relation. A plan fixes every field to either an index
position or a proof capture. Canonical context/capture syntax depends only
on this plan, the declared telescope, and the original arguments.

The input `Compatible` records an actual replay derivation obeying the plan.
It supplies exactly the domain formation and alignment already demanded by
`NativeCaptureReplay`; it supplies no equality/computation callbacks.
Constructing those premises from a declaration remains an upstream task.

Induction consumes the finite plan. Newly obtained proof/cast derivations
are never recursive arguments. No inverse weakening or type uniqueness is
used. This is one replay abstraction, not deterministic whole exposure.
-/
namespace Lean4Lean.VEnv
open VExpr

@[simp] theorem comp_tail (a b : Subst) : (a.comp b).tail = a.tail.comp b := rfl
@[simp] theorem comp_head (a b : Subst) : (a.comp b).head = a.head.subst b := rfl
@[simp] theorem raised_tail (a : Subst) (n : Nat) : (raisedSubst a n).tail = raisedSubst a.tail n := rfl
@[simp] theorem raised_head (a : Subst) (n : Nat) : (raisedSubst a n).head = a.head.liftN n := rfl

/-- Substitute every stored conversion edge into a different target context. -/
theorem TypeConversion.substTarget
    (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ σ σ Γ)
    (H : TypeConversion env U Γ A B) :
    TypeConversion env U Δ (A.subst σ) (B.subst σ) := by
  induction H with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (by simpa only [VExpr.subst] using edge.subst henv W hΔ)

/-- Whole-replay target substitution, including arbitrary proof witnesses. -/
theorem NativeCaptureReplay.substTarget
    (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ σ σ Γ)
    (H : NativeCaptureReplay env U Γ source arguments declared captures) :
    NativeCaptureReplay env U Δ source (arguments.comp σ) declared (captures.comp σ) := by
  induction H with
  | nil => exact .nil
  | index previous hd hi he hp ih =>
    refine .index ih hd hi ?_ ?_
    · exact congrArg (fun e => e.subst σ) he
    · simpa only [subst_subst, comp_tail] using hp.substTarget henv hΔ W
  | proof previous hd hq ih =>
    refine .proof ih hd ?_
    simpa only [subst_subst, comp_tail, comp_head] using hq.subst henv W hΔ

theorem TypeConversion.weakTarget
    (henv : env.Ordered) (W : Ctx.LiftN n 0 Γ Δ)
    (H : TypeConversion env U Γ A B) :
    TypeConversion env U Δ (A.liftN n) (B.liftN n) := by
  induction H with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (by simpa only [VExpr.liftN] using edge.weakN henv W)

theorem NativeCaptureReplay.weakTarget
    (henv : env.Ordered) (W : Ctx.LiftN n 0 Γ Δ)
    (H : NativeCaptureReplay env U Γ source arguments declared captures) :
    NativeCaptureReplay env U Δ source (raisedSubst arguments n) declared
      (raisedSubst captures n) := by
  induction H with
  | nil => exact .nil
  | index previous hd hi he hp ih =>
    refine .index ih hd hi ?_ ?_
    · exact congrArg (fun e => e.liftN n) he
    · simpa only [raised_tail, subst_raised] using hp.weakTarget henv W
  | proof previous hd hq ih =>
    refine .proof ih hd ?_
    simpa only [raised_tail, raised_head, subst_raised] using hq.weakN henv W

/-- Every field role and every data index position is fixed by the plan. -/
inductive CapturePlan : List VExpr → Type where
  | nil : CapturePlan []
  | index : CapturePlan declared → Nat → CapturePlan (domain :: declared)
  | proof : CapturePlan declared → CapturePlan (domain :: declared)

namespace CapturePlan

def count : CapturePlan declared → Nat
  | .nil => 0
  | .index p _ => p.count
  | .proof p => p.count + 1

def captures (arguments : Subst) : CapturePlan declared → Subst
  | .nil => .id
  | .index p i => (p.captures arguments).cons ((arguments i).liftN p.count)
  | .proof p => (raisedSubst (p.captures arguments) 1).cons (.bvar 0)

def added (arguments : Subst) : CapturePlan declared → List VExpr
  | .nil => []
  | .index p _ => p.added arguments
  | @proof _ domain p => domain.subst (p.captures arguments) :: p.added arguments

/-- A refinement of the actual replay relation with its fixed field plan.
The raw replay is proposition-valued, so the plan is supplied separately;
it is not extracted as data by inspecting a proof. -/
inductive Compatible (env : VEnv) (U : Nat) (Γ source : List VExpr)
    (arguments : Subst) : {declared : List VExpr} → (p : CapturePlan declared) →
    {actual : Subst} → NativeCaptureReplay env U Γ source arguments declared actual → Prop where
  | nil : Compatible env U Γ source arguments .nil (.nil (captures := actual))
  | index {actual : Subst}
      {H : NativeCaptureReplay env U Γ source arguments declared actual.tail}
      (previous : Compatible env U Γ source arguments p H)
      (hd : HasType env U declared domain (.sort level))
      (hi : Lookup source position naturalDomain)
      (he : actual.head = arguments position)
      (hp : TypeConversion env U Γ (naturalDomain.subst arguments) (domain.subst actual.tail)) :
      Compatible env U Γ source arguments (p.index position) (.index H hd hi he hp)
  | proof {actual : Subst}
      {H : NativeCaptureReplay env U Γ source arguments declared actual.tail}
      (previous : Compatible env U Γ source arguments p H)
      (hd : HasType env U declared domain (.sort .zero))
      (hq : HasType env U Γ actual.head (domain.subst actual.tail)) :
      Compatible env U Γ source arguments p.proof (.proof H hd hq)

@[simp] theorem raised_raised (a : Subst) (n m : Nat) :
    raisedSubst (raisedSubst a n) m = raisedSubst a (n + m) := by
  funext i
  exact liftN_liftN _ _ _

@[simp] theorem skip_raised (a : Subst) :
    a.lift_r (.skip .refl) = raisedSubst a 1 := by
  funext i
  exact lift_eq_lift'.symm

/-- Abstract every proof capture and retain the actual proof-allocation
history. This history is produced by the replay induction; it is not inferred
from an arbitrary split-frame record. It lets a subsequent head comparison
interleave these private proof binders with a shared native trace. -/
theorem abstractReplay_withHistory {declared : List VExpr} {actual : Subst}
    {p : CapturePlan declared}
    {H : NativeCaptureReplay env U Γ source arguments declared actual}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (Wargs : Ctx.SubstEq env U Γ arguments arguments source)
    (HC : Compatible env U Γ source arguments p H) :
    ∃ _F : SplitProofFrame env U Γ (p.added arguments ++ Γ) p.count,
      Nonempty (SharedProofInterleaving env U Γ []
        (p.added arguments ++ Γ) (.skipN .refl p.count)) ∧
      NativeCaptureReplay env U (p.added arguments ++ Γ) source
        (raisedSubst arguments p.count) declared (p.captures arguments) ∧
      Ctx.SubstEq env U (p.added arguments ++ Γ)
        (raisedSubst actual p.count) (p.captures arguments) declared := by
  induction HC with
  | nil => exact ⟨.refl henv hΓ, ⟨.base hΓ⟩, .nil, .nil⟩
  | index previous hd hi he hp ih =>
    obtain ⟨F, history, Hr, Wr⟩ := ih
    have hdomain := hd.substDF henv Wr.wf F.targetWF Wr
    have hpath := hp.weakTarget henv F.weakening
    simp only [← subst_raised] at hpath
    have hactual := (hp.cast (Wargs.lookup hi)).hasType.1
    have hactual' := hactual.weakN henv F.weakening
    refine ⟨F, history, .index Hr hd hi rfl (.tail hpath hdomain), .cons Wr hd ?_⟩
    simpa only [HasType, captures, count, added, raised_head, Subst.cons_head, ← he, subst_raised,
      raised_tail] using hactual'
  | proof previous hd hq ih =>
    rename_i D plan A cap Hr0
    obtain ⟨F, ⟨history⟩, Hr, Wr⟩ := ih
    have hdomain := hd.substDF henv Wr.wf F.targetWF Wr
    have hq' := hq.weakN henv F.weakening
    rw [← subst_raised] at hq'
    have hq'' := IsDefEq.defeqDF hdomain hq'
    let F' := F.cons henv hdomain.hasType.2 hq''
    have Hr' := Hr.weakTarget henv (Ctx.LiftN.one (A := A.subst (plan.captures arguments)))
    have Wr' := Wr.skip (B := A.subst (plan.captures arguments)) henv
    simp only [captures, count, added, List.cons_append]
    refine ⟨F', ⟨history.privateStep hdomain.hasType.2 hq''⟩, ?_, ?_⟩
    · apply NativeCaptureReplay.proof (by simpa only [raised_raised, Subst.cons_tail] using Hr') hd
      simpa only [subst_raised, Subst.cons_head, Subst.cons_tail] using
        (show env.HasType U (A.subst (plan.captures arguments) :: _) (.bvar 0)
          (A.subst (plan.captures arguments)).lift from .bvar .zero)
    · apply Ctx.SubstEq.cons ?_ hd ?_
      · simpa only [raised_tail, skip_raised, raised_raised, Subst.cons_tail] using Wr'
      · have hp' := hdomain.hasType.1.weak (B := A.subst (plan.captures arguments)) henv
        have heq := IsDefEq.proofIrrel hp' (hq'.weak henv)
          (IsDefEq.defeqDF (hdomain.symm.weak henv) (.bvar .zero))
        simpa only [captures, count, added, Subst.cons_head, raised_head,
          raised_tail, subst_raised, liftN_succ (n := plan.count)] using heq

/-- Forget only the allocation history when a caller needs the original
replay interface. Contexts and captures still do not depend on chosen proof
witnesses; those witnesses certify the typed retraction. -/
theorem abstractReplay {declared : List VExpr} {actual : Subst}
    {p : CapturePlan declared}
    {H : NativeCaptureReplay env U Γ source arguments declared actual}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (Wargs : Ctx.SubstEq env U Γ arguments arguments source)
    (HC : Compatible env U Γ source arguments p H) :
    ∃ _F : SplitProofFrame env U Γ (p.added arguments ++ Γ) p.count,
      NativeCaptureReplay env U (p.added arguments ++ Γ) source
        (raisedSubst arguments p.count) declared (p.captures arguments) ∧
      Ctx.SubstEq env U (p.added arguments ++ Γ)
        (raisedSubst actual p.count) (p.captures arguments) declared := by
  obtain ⟨F, _, Hr, Wr⟩ := abstractReplay_withHistory henv hΓ Wargs HC
  exact ⟨F, Hr, Wr⟩

end CapturePlan

/-- Retraction of the canonical replay restores the original arguments
literally. Its reconstructed capture tuple can then be compared to the raw
one by the capture equality provided by `abstractReplay`. -/
theorem SplitProofFrame.retractReplay (F : SplitProofFrame env U Γ Δ n)
    (henv : env.Ordered)
    (H : NativeCaptureReplay env U Δ source (raisedSubst arguments n) declared canonical) :
    NativeCaptureReplay env U Γ source arguments declared (canonical.comp F.retract) := by
  have h := H.substTarget henv F.baseWF F.typed
  have he : (raisedSubst arguments n).comp F.retract = arguments := by
    funext i
    exact F.leftInv (arguments i)
  rwa [he] at h


end Lean4Lean.VEnv
