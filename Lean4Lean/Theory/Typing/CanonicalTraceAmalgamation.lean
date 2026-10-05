import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.SharedProofInterleaving
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

/-!
Identify the corresponding binders of two syntax-selected head traces.

Unrelated preliminary proof frames are interleaved by `commonTarget`. Fresh
slots selected by the SAME computation must instead be shared: sending them
to distinct variables would destroy literal agreement of the resulting Pi
displays. The construction below consumes actual typing of both telescopes
and literal agreement after the initial renamings. It produces the extended
split embeddings; it assumes neither type injectivity nor inverse weakening.

The syntactic agreement premise is supplied by deterministic trace comparison,
not inferred from equality of the two whole Pi types.
-/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
open private addShared from Lean4Lean.Theory.Typing.SharedProofInterleaving

namespace SharedProofInterleaving.CommonTarget
variable {env : VEnv} {U : Nat} {leftTarget rightTarget : List VExpr}
  {leftMap rightMap : Lift}

/-- Allocate a corresponding trace slot once in the common target. The
domains need only agree after the existing forward embeddings; no canonical
domain typing in an earlier context is requested. Data binders are allowed. -/
theorem synchronizeBinder
    (C : SharedProofInterleaving.CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered)
    (hL : env.HasType U leftTarget QL (.sort uL))
    (hR : env.HasType U rightTarget QR (.sort uR))
    (he : QR.lift' C.right.liftMap = QL.lift' C.left.liftMap) :
    ∃ D : SharedProofInterleaving.CommonTarget env U (QL :: leftTarget) (QR :: rightTarget)
        leftMap.cons rightMap.cons,
      D.left.liftMap = C.left.liftMap.cons ∧
      D.right.liftMap = C.right.liftMap.cons := by
  let F := addShared C.left henv hL
  let G₀ := addShared C.right henv hR
  let G : {G : SplitTypedEmbedding env U (QR :: rightTarget)
      (QL.lift' C.left.liftMap :: C.target) //
      G.liftMap = C.right.liftMap.cons} :=
    Eq.mp (congrArg (fun X => {G : SplitTypedEmbedding env U
      (QR :: rightTarget) (X :: C.target) //
      G.liftMap = C.right.liftMap.cons}) he) G₀
  refine ⟨⟨QL.lift' C.left.liftMap :: C.target, F.1, G.1,
    ?_, ?_, ?_, ?_⟩, F.2, G.2⟩
  · rw [F.2, G.2]
    exact congrArg Lift.cons C.agreement
  · intro i j hij
    rw [F.2, G.2] at hij
    cases i with
    | zero =>
      cases j with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ j => simp only [Lift.liftVar] at hij; cases hij
    | succ i =>
      cases j with
      | zero => simp only [Lift.liftVar] at hij; cases hij
      | succ j =>
        simp only [Lift.liftVar] at hij
        obtain ⟨k, hk, hk'⟩ := C.overlap i j (Nat.succ.inj hij)
        exact ⟨k + 1, by simp only [Lift.liftVar, hk],
          by simp only [Lift.liftVar, hk']⟩
  · rw [F.2]
    exact C.leftInsertion.cons hL
  · rw [G.2, ← he]
    exact C.rightInsertion.cons hR

/-- Merge the complete generated telescopes. Every corresponding new slot is
identified, while the initial common target preserves the separation of its
private variables. The returned map equations are needed to transport the
actual final terms and their semantic evidence into this context. -/
theorem synchronizeTelescope
    (C : SharedProofInterleaving.CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered) (leftDomains rightDomains : List VExpr)
    (hL : OnCtx (leftDomains ++ leftTarget) (env.IsType U))
    (hR : OnCtx (rightDomains ++ rightTarget) (env.IsType U))
    (he : renameAdded C.left.liftMap leftDomains =
      renameAdded C.right.liftMap rightDomains) :
    ∃ D : SharedProofInterleaving.CommonTarget env U
        (leftDomains ++ leftTarget) (rightDomains ++ rightTarget)
        (leftMap.consN leftDomains.length) (rightMap.consN rightDomains.length),
      D.left.liftMap = C.left.liftMap.consN leftDomains.length ∧
      D.right.liftMap = C.right.liftMap.consN rightDomains.length := by
  induction leftDomains generalizing rightDomains with
  | nil =>
    cases rightDomains with
    | nil => exact ⟨C, rfl, rfl⟩
    | cons Q domains => cases he
  | cons QL leftDomains ih =>
    cases rightDomains with
    | nil => cases he
    | cons QR rightDomains =>
      have ⟨hQ, htail⟩ := List.cons.inj he
      obtain ⟨uL, hQL⟩ := hL.2
      obtain ⟨uR, hQR⟩ := hR.2
      obtain ⟨D, hdL, hdR⟩ := ih rightDomains hL.1 hR.1 htail
      have hQ' : QR.lift' D.right.liftMap = QL.lift' D.left.liftMap := by
        rw [hdL, hdR]
        exact hQ.symm
      obtain ⟨E, heL, heR⟩ := D.synchronizeBinder henv hQL hQR hQ'
      exact ⟨E, heL.trans (congrArg Lift.cons hdL),
        heR.trans (congrArg Lift.cons hdR)⟩

/-- Literal agreement of final expressions survives the typed telescope
amalgamation, so a Pi display's components can be compared syntactically. -/
theorem synchronizeTelescope_result
    (C : SharedProofInterleaving.CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered) (leftDomains rightDomains : List VExpr)
    (hL : OnCtx (leftDomains ++ leftTarget) (env.IsType U))
    (hR : OnCtx (rightDomains ++ rightTarget) (env.IsType U))
    (he : renameAdded C.left.liftMap leftDomains =
      renameAdded C.right.liftMap rightDomains)
    {leftResult rightResult : VExpr}
    (ht : leftResult.lift' (C.left.liftMap.consN leftDomains.length) =
      rightResult.lift' (C.right.liftMap.consN rightDomains.length)) :
    ∃ D : SharedProofInterleaving.CommonTarget env U
        (leftDomains ++ leftTarget) (rightDomains ++ rightTarget)
        (leftMap.consN leftDomains.length) (rightMap.consN rightDomains.length),
      D.left.liftMap = C.left.liftMap.consN leftDomains.length ∧
      D.right.liftMap = C.right.liftMap.consN rightDomains.length ∧
      leftResult.lift' D.left.liftMap = rightResult.lift' D.right.liftMap := by
  obtain ⟨D, hdL, hdR⟩ := C.synchronizeTelescope henv leftDomains rightDomains hL hR he
  exact ⟨D, hdL, hdR, by rwa [hdL, hdR]⟩

end SharedProofInterleaving.CommonTarget
end Lean4Lean.VEnv
