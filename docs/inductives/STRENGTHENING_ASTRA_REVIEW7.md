The main finding is that **core standardisation exists, but the required full head-exposure theorem is still missing**. Also, the checked repository reduction still has projection and eliminator obligations.

I wrote the detailed [report](/home/kim/worktrees/lean4lean/strengthening-context/round9/REPORT.txt), [design lemmas](/home/kim/worktrees/lean4lean/strengthening-context/round9/Round9.lean), and [regression tests](/home/kim/worktrees/lean4lean/strengthening-context/round9/Regression.lean). Both Lean files compile with `lake env lean` from this worktree; audited theorems have no `sorryAx` or new axioms. I did not modify repository files.

1. **Standardisation and the induction measure.**

   [`ParRedS.standard`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/HeadReduction.lean:745) gives core standardisation. I checked this consequence:

   ```lean
   theorem core_exposure_standard [VEnv.Params]
       (hΓ : OnCtx Γ (Params.env.IsType univs))
       (ht : Params.env.HasType univs Γ F (.sort u))
       (hr : ParRedS Γ F (.forallE A B)) :
       ∃ A₀ B₀, WHRedS Γ F (.forallE A₀ B₀)
   ```

   It does **not** apply to `FullReduction`. Existing [`WHRed`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/HeadReduction.lean:93) omits singleton/quotient prefix unfolding and projection iota. I checked a conditional projection example admitting full Π exposure but no `WHRedS` Π exposure. The levelled machinery supplies [full joins](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/LevelledReduction.lean:4593), without a head strategy or path-length bound.

   Your root-eta exclusion is correct; I checked it for arbitrary sort-typed `F`. But **the demanded major need not itself be a type**. For example, with `structure Box where field : Type`, Lean checks:

   ```lean
   example (s : Box) :
       Box.rec (motive := fun _ => Type)
         (fun _ => Prop → Prop) s = (Prop → Prop) := rfl
   ```

   A neutral structure major needs structure-eta computation before iota. The checker explicitly implements this in [`toCtorWhenStruct`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Inductive/Reduce.lean:54). Thus excluding eta at the outer type does not justify an entirely eta-free demanded-head strategy.

   The useful invariant is **typing of the current reduct below**, maintained by subject reduction. The exact sufficient local interface I stated is:

   ```lean
   ∀ ⦃k Γ Γ' e T out⦄, Ctx.LiftN 1 k Γ Γ' →
     OnCtx Γ (Params.env.IsType univs) →
     OnCtx Γ' (Params.env.IsType univs) →
     Params.env.HasType univs Γ e T →
     HeadStep Γ' (e.liftN 1 k) out →
     ∃ e', out = e'.liftN 1 k ∧ FullStep Γ e e'
   ```

   **Given this interface**, ordinary induction on the remaining above path suffices—no size component. This is proved as [`head_path_replay`](/home/kim/worktrees/lean4lean/strengthening-context/round9/Round9.lean:183). Replay plus an appropriate full-to-head exposure bridge implies `PiExposureRedN`; that implication is checked. The interfaces themselves remain unproved.

   Without local replay, strengthening a guard is a different recursive problem, not the tail of the exposure path. Its subsidiary exposure may come from [`exposure_reduces`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/TypingFront.lean:561), with no bound by the current head-step count. That is the missing inequality for `(head steps, size)`. This diagnoses that proposed recursion; it does not rule out every possible measure.

   One concrete case already closes: [`HasType.projIota_field`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/LevelledReduction.lean:3172) reconstructs the field typing from a saturated constructor projection typed below. I checked the resulting projection replay without any strengthening hypothesis.

2. **`TypedFront`, `Cancel`, and exposure.**

   I proved:

   ```lean
   theorem typeFrontN_iff_typeFront (henv : env.WF) :
     TypeFrontN env ↔ TypeFront env

   theorem typeFrontN_iff_typedFront
       (henv : env.WF) (heq : env.HasCanonicalEq) :
     TypeFrontN env ↔ StrengtheningKripke.TypedFront env

   theorem piExposureRed_iff_piExposure
       (henv : env.WF) (heq : env.HasCanonicalEq) :
     PiExposureRedN henv ↔ PiExposureN env
   ```

   Consequently, under those assumptions:

   ```text
   Cancel ⇒ TypeFrontN ⇔ TypeFront ⇔ TypedFront ⇔ KeyFaithful
   PiExposureRedN ⇔ PiExposureN
   PiExposureN + TypeFrontN ⇒ AppFrontN
   ```

   The last two repository connections are [`keyFaithful_iff_typedFront`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/Kripke.lean:189) and [`AppFrontN.of_piExposure`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/TypingFront.lean:456).

   **I found no reduction of `Cancel` to `TypedFront` alone, and did not establish strict weakness.** Strictness requires separation, not merely a missing implication. Nor did I prove `TypedFront ⇒ PiExposureN`.

   Your proposed comparison identifies the obstruction exactly: besides `F : Sort u`, one needs a **Π representative typed below**, whose lift is convertible to `F↑`. The above-exposed Π need not be a lift, as the checked [`headType_bad_reduct`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/TypingFront.lean:208) demonstrates. Comparing `F` with itself supplies no Π shape.

   There is also a qualification to “exactly two obligations.” [`cancel_of_piExposureRed`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/TypingFront.lean:595) still requires `ProjFrontN` and `ElimFrontN`. The latter’s supplied discharge requires [`GenericTypesTyped`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/TypingFront.lean:786), explicitly not yet a library theorem. I checked the exact formulation:

   ```lean
   Cancel env ↔
     StrengtheningKripke.TypedFront env ∧
     AppFrontN env ∧ ProjFrontN env ∧ ElimFrontN env
   ```

3. **A small concrete regression.**

   The test needs no declaration beyond the `Eq` block. In readable notation, its exact `VExpr` definitions are:

   ```text
   D   = Prop → Prop
   b X = (fun Y : Type => Y) X
   M X = fun (Y : Type) (_ : @Eq Type X Y) => Type
   R X = @Eq.rec.{2,2} Type X (M X) D (b X) (@Eq.refl.{2} Type X)
   F   = (fun X : Type => R X) D
   ```

   After `F →β R D`, the five-argument singleton prefix reconstructs `Eq.refl Type D` beneath a major binder of type `Eq Type D (b D)`. Its constructor guard therefore requires the nonliteral conversion `b D ≡ D`.

   [Checked facts](/home/kim/worktrees/lean4lean/strengthening-context/round9/Regression.lean:101) include:

   - The reconstructed proof and `b D` occur in `R D`, but neither occurs syntactically in `F`.
   - `sizeOf F < sizeOf (R D)`.
   - Both types are lifts of themselves.
   - The **complete `UnfoldingCheck`**, including capture typing, major typing, and spine alignment, holds below and above.
   - `F` is typed, inhabited, and fully exposes below to a Π.

   The executable regression builds an empty environment, installs only `Eq`, checks the original, reduct, and converted guard, and verifies that checker `whnf` exposes `D`.

   **Certification limit:** I did not construct a separate closed `VEnv.WF` certificate for that executable output or discharge its chosen registry/generation equations. [`prefix_step`](/home/kim/worktrees/lean4lean/strengthening-context/round9/Regression.lean:186) retains those equations explicitly. Thus this supplies a fully checked abstract guard regression and an Eq-only executable test, not a fully instantiated minimal `VEnv` head-path certificate. It defeats the proposed subterm/size argument; it is not a typing-gap counterexample.

4. **The most useful reorganisation.**

   Prove local replay from the current below typing, separately for each computation rule. For fixed lifted guard types, I checked the useful bridge:

   ```text
   TypeFrontN + (e : T below) + (A : Sort u below)
     + (e↑ : A↑ above)
     ⇒ e : A below.
   ```

   This exposes precisely what remains for generated programs: establish the independent below typings of their captures and expected types. Scope preservation alone does not establish them. The required premises are visible in [`UnfoldingCheck`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/PrefixUnfolding/Rule.lean:25) and [`CaseRedex`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/CaseReduction.lean:316).

   Replacing full reduction with checker `whnf` still needs an exposure-completeness bridge. [`whnf.WF`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Verify/TypeChecker.lean:473) preserves translation and free-variable bounds **on successful execution**; [`M.WF`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Verify/TypeChecker/Basic.lean:716) does not assert success. It therefore does not prove “full Π exposure implies checker Π exposure.” Using it requires adequacy for the quantified abstract environments, successful exposure, and replay below—substantial additional lemmas.
