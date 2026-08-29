import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner

open Lean hiding Environment Exception
open Kernel

/-- The graph of the executable projection-result computation at one exact
checker context and state.  This is proof data obtained from evaluation, not a
caller-supplied projection resolver. -/
structure ProjectionResultTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (result : ProjectionResult) where
  finalState : State
  run : inferProjResult typeName index struct structType
      methods c.toContext s.toState = .ok (result, finalState)

namespace ProjectionResultTrace

theorem family_single
    (H : ProjectionResultTrace methods c s typeName index struct structType result) :
    result.expansion.familyInfo.ctors =
      [result.expansion.constructorName] :=
  result.expansion.familySingle

/-- One executable projection-result run has only one result.  In particular,
the inferred type and every retained expansion component are literally equal;
no type-theoretic injectivity or projection compatibility hypothesis is used. -/
theorem result_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult = rightResult := by
  cases left with
  | mk leftState leftRun =>
    cases right with
    | mk rightState rightRun =>
      rw [leftRun] at rightRun
      cases rightRun
      rfl

theorem type_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult.type = rightResult.type :=
  congrArg ProjectionResult.type (left.result_eq right)

theorem expansion_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult.expansion = rightResult.expansion :=
  congrArg ProjectionResult.expansion (left.result_eq right)

end ProjectionResultTrace

/-- The exact accepted certificate produced by one executable projection
inference run.  `inferProj` returns only `certificate.projection.type`; this
trace retains the certificate that the executable code actually computed. -/
structure ProjectionCertificateTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (certificate : ProjectionCertificate) where
  finalState : State
  run : inferProjCertified typeName index struct structType
      methods c.toContext s.toState = .ok (certificate, finalState)

/-- Decomposition of certification into the exact generated proposal and
the subsequent validation run.  These are the producer/blueprint objects
that semantic projection refinement must replay; neither is supplied by a
caller. -/
structure ProjectionCertificationTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (certificate : ProjectionCertificate) where
  proposal : ProjectionProposal typeName index struct structType
  proposalState : State
  proposalRun : generateProjectionProposal typeName index struct structType
      methods c.toContext s.toState = .ok (proposal, proposalState)
  finalState : State
  validationRun : validateProjectionResult
      proposal.exactProjection.toProjectionResult
      proposal.generated.candidate methods c.toContext proposalState =
        .ok (certificate, finalState)

/-- Exact-result phase of a generated projection proposal. -/
structure ExactProjectionResultTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (result : ExactProjectionResult typeName index struct structType) where
  finalState : State
  run : inferProjResultExact typeName index struct structType
      methods c.toContext s.toState = .ok (result, finalState)

/-- Candidate-generation phase at the state left by exact inference. -/
structure GeneratedProjectionCandidateTrace
    (methods : Methods) (c : VContext) (state : State)
    (projection : ProjectionResult)
    (generated : GeneratedProjectionCandidate projection) where
  finalState : State
  run : generateProjectionCandidate projection methods c.toContext state =
    .ok (generated, finalState)

/-- Exact decomposition of the proposal-producing bind. -/
structure ProjectionProposalTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (proposal : ProjectionProposal typeName index struct structType) where
  exactState : State
  exactRun : inferProjResultExact typeName index struct structType
      methods c.toContext s.toState =
        .ok (proposal.exactProjection, exactState)
  finalState : State
  generatedRun : generateProjectionCandidate
      proposal.exactProjection.toProjectionResult methods c.toContext
        exactState = .ok (proposal.generated, finalState)

/-- Exact decomposition of the validation phase.  In particular, the
certificate's candidate type is the literal result of checked inference and
the final state is reached only after the executable definitional-equality
test returned `true`. -/
structure ProjectionValidationTrace
    (methods : Methods) (c : VContext) (state : State)
    (projection : ProjectionResult) (candidate : Expr)
    (certificate : ProjectionCertificate) where
  scopeRun : projectionCandidateScopeValid c.lctx candidate = true
  inferenceState : State
  inferenceRun : inferType candidate (inferOnly := false) methods c.toContext
      state = .ok (certificate.candidateType, inferenceState)
  finalState : State
  defeqRun : isDefEq certificate.candidateType projection.type methods
      c.toContext inferenceState = .ok (true, finalState)
  projection_eq : certificate.projection = projection
  candidate_eq : certificate.candidate = candidate

namespace ProjectionCertificateTrace

/-- A successful validation run exposes the two checker calls whose results
justify acceptance.  The parser witness remains in `certificate.shellRun`;
the equations below prevent replacing either the proposal or candidate after
the fact. -/
theorem validationTrace
    (Hrun : validateProjectionResult projection candidate methods c.toContext
      state = .ok (certificate, outputState)) :
    Nonempty (ProjectionValidationTrace methods c state projection candidate
      certificate) := by
  cases hparsed : projection.expansion.parsedShell? candidate with
  | none =>
      unfold validateProjectionResult at Hrun
      simp only [hparsed] at Hrun
      change Except.error _ = Except.ok _ at Hrun
      contradiction
  | some parsed =>
      unfold validateProjectionResult at Hrun
      simp only [hparsed] at Hrun
      cases hscope : projectionCandidateScopeValid c.lctx candidate with
      | false =>
          simp only [hscope, Bool.false_eq_true, ↓reduceIte] at Hrun
          change Except.error _ = Except.ok _ at Hrun
          contradiction
      | true =>
        simp only [hscope, ↓reduceIte] at Hrun
        cases hinference : inferType candidate (inferOnly := false) methods
            c.toContext state with
        | error error =>
            rw [hinference] at Hrun
            contradiction
        | ok inferencePair =>
            rcases inferencePair with ⟨candidateType, inferenceState⟩
            rw [hinference] at Hrun
            simp only at Hrun
            cases hdefeq : isDefEq candidateType projection.type methods
                c.toContext inferenceState with
            | error error =>
                rw [hdefeq] at Hrun
                contradiction
            | ok defeqPair =>
                rcases defeqPair with ⟨accepted, validationState⟩
                rw [hdefeq] at Hrun
                cases accepted with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at Hrun
                    contradiction
                | true =>
                    simp only [↓reduceIte] at Hrun
                    rcases Hrun with ⟨rfl, rfl⟩
                    exact ⟨{
                      scopeRun := hscope
                      inferenceState := inferenceState
                      inferenceRun := hinference
                      finalState := outputState
                      defeqRun := hdefeq
                      projection_eq := rfl
                      candidate_eq := rfl }⟩

/-- The accepted certificate is literal producer output, hence unique for a
fixed checker method/context/state triple. -/
theorem certificate_eq
    (left : ProjectionCertificateTrace methods c s typeName index struct
      structType leftCertificate)
    (right : ProjectionCertificateTrace methods c s typeName index struct
      structType rightCertificate) :
    leftCertificate = rightCertificate := by
  cases left with
  | mk leftState leftRun =>
      cases right with
      | mk rightState rightRun =>
          rw [leftRun] at rightRun
          cases rightRun
          rfl

/-- Every retained certificate trace exposes the exact proposal and
validation phases executed by `inferProjCertified`. -/
theorem certification
    (H : ProjectionCertificateTrace methods c s typeName index struct
      structType certificate) :
    Nonempty (ProjectionCertificationTrace methods c s typeName index struct
      structType certificate) := by
  cases H with
  | mk outputState Hrun =>
      cases hproposal : generateProjectionProposal typeName index struct
          structType methods c.toContext s.toState with
      | error error =>
          unfold inferProjCertified at Hrun
          change Except.bind
              (generateProjectionProposal typeName index struct structType
                methods c.toContext s.toState)
              (fun pair => validateProjectionResult
                pair.1.exactProjection.toProjectionResult
                pair.1.generated.candidate methods c.toContext pair.2) =
            Except.ok (certificate, outputState) at Hrun
          rw [hproposal] at Hrun
          contradiction
      | ok pair =>
          rcases pair with ⟨proposal, proposalState⟩
          unfold inferProjCertified at Hrun
          change Except.bind
              (generateProjectionProposal typeName index struct structType
                methods c.toContext s.toState)
              (fun pair => validateProjectionResult
                pair.1.exactProjection.toProjectionResult
                pair.1.generated.candidate methods c.toContext pair.2) =
            Except.ok (certificate, outputState) at Hrun
          rw [hproposal] at Hrun
          exact ⟨{
            proposal := proposal
            proposalState := proposalState
            proposalRun := hproposal
            finalState := outputState
            validationRun := Hrun }⟩

/-- The proposal retained by certification is itself the literal pair of the
exact projection-result run and candidate-generation run. -/
theorem certificationProposalTrace
    (H : ProjectionCertificationTrace methods c s typeName index struct
      structType certificate) :
    Nonempty (ProjectionProposalTrace methods c s typeName index struct
      structType H.proposal) := by
  cases H with
  | mk proposal proposalState Hproposal outputState Hvalidation =>
      cases hexact : inferProjResultExact typeName index struct structType
          methods c.toContext s.toState with
      | error error =>
          unfold generateProjectionProposal at Hproposal
          change Except.bind
              (inferProjResultExact typeName index struct structType methods
                c.toContext s.toState)
              (fun pair => Except.bind
                (generateProjectionCandidate pair.1.toProjectionResult methods
                  c.toContext pair.2)
                (fun generatedPair => Except.ok
                  (({ exactProjection := pair.1
                      generated := generatedPair.1 } :
                    ProjectionProposal typeName index struct structType),
                    generatedPair.2))) =
            Except.ok (proposal, proposalState) at Hproposal
          rw [hexact] at Hproposal
          contradiction
      | ok pair =>
          rcases pair with ⟨exactProjection, exactState⟩
          cases hgenerated : generateProjectionCandidate
              exactProjection.toProjectionResult methods c.toContext
                exactState with
          | error error =>
              unfold generateProjectionProposal at Hproposal
              change Except.bind
                  (inferProjResultExact typeName index struct structType
                    methods c.toContext s.toState)
                  (fun pair => Except.bind
                    (generateProjectionCandidate pair.1.toProjectionResult
                      methods c.toContext pair.2)
                    (fun generatedPair => Except.ok
                      (({ exactProjection := pair.1
                          generated := generatedPair.1 } :
                        ProjectionProposal typeName index struct structType),
                        generatedPair.2))) =
                Except.ok (proposal, proposalState) at Hproposal
              rw [hexact] at Hproposal
              simp only [Except.bind] at Hproposal
              rw [hgenerated] at Hproposal
              simp only [Except.bind] at Hproposal
              contradiction
          | ok generatedPair =>
              rcases generatedPair with ⟨generated, generatedState⟩
              unfold generateProjectionProposal at Hproposal
              change Except.bind
                  (inferProjResultExact typeName index struct structType
                    methods c.toContext s.toState)
                  (fun pair => Except.bind
                    (generateProjectionCandidate pair.1.toProjectionResult
                      methods c.toContext pair.2)
                    (fun generatedPair => Except.ok
                      (({ exactProjection := pair.1
                          generated := generatedPair.1 } :
                        ProjectionProposal typeName index struct structType),
                        generatedPair.2))) =
                Except.ok (proposal, proposalState) at Hproposal
              rw [hexact] at Hproposal
              simp only [Except.bind] at Hproposal
              rw [hgenerated] at Hproposal
              simp only [Except.bind] at Hproposal
              cases Hproposal
              exact ⟨{
                exactState := exactState
                exactRun := hexact
                finalState := proposalState
                generatedRun := hgenerated }⟩

/-- The retained certification trace also exposes the exact checked
inference and successful definitional-equality runs used by validation. -/
theorem certificationValidationTrace
    (H : ProjectionCertificationTrace methods c s typeName index struct
      structType certificate) :
    Nonempty (ProjectionValidationTrace methods c H.proposalState
      H.proposal.exactProjection.toProjectionResult
      H.proposal.generated.candidate certificate) :=
  validationTrace H.validationRun

/-- A successful `inferProj` run is definitionally a successful certified
run followed by projection of the retained inferred type. -/
theorem ofInferProjRun
    (Hrun : inferProj typeName index struct structType
      methods c.toContext s.toState = .ok (inferredType, outputState)) :
    ∃ certificate,
      Nonempty (ProjectionCertificateTrace methods c s typeName index struct
        structType certificate) ∧
      certificate.projection.type = inferredType := by
  cases hcertificate : inferProjCertified typeName index struct structType
      methods c.toContext s.toState with
  | error error =>
      unfold inferProj at Hrun
      change Except.bind
          (inferProjCertified typeName index struct structType methods
            c.toContext s.toState)
          (fun pair => Except.ok
            (pair.1.projection.type, pair.2)) =
        Except.ok (inferredType, outputState) at Hrun
      rw [hcertificate] at Hrun
      contradiction
  | ok pair =>
      rcases pair with ⟨certificate, state⟩
      unfold inferProj at Hrun
      change Except.bind
          (inferProjCertified typeName index struct structType methods
            c.toContext s.toState)
          (fun pair => Except.ok
            (pair.1.projection.type, pair.2)) =
        Except.ok (inferredType, outputState) at Hrun
      rw [hcertificate] at Hrun
      rcases Hrun with ⟨rfl, rfl⟩
      exact ⟨certificate, ⟨⟨state, hcertificate⟩⟩, rfl⟩

/-- One-step public recovery of every retained producer phase from the type
returned by `inferProj`. -/
theorem phasesOfInferProjRun
    (Hrun : inferProj typeName index struct structType
      methods c.toContext s.toState = .ok (inferredType, outputState)) :
    ∃ certificate,
      certificate.projection.type = inferredType ∧
      Nonempty (ProjectionCertificateTrace methods c s typeName index struct
        structType certificate) ∧
      Nonempty (ProjectionCertificationTrace methods c s typeName index struct
        structType certificate) ∧
      ∃ certification : ProjectionCertificationTrace methods c s typeName
          index struct structType certificate,
        Nonempty (ProjectionProposalTrace methods c s typeName index struct
          structType certification.proposal) ∧
        Nonempty (ProjectionValidationTrace methods c
          certification.proposalState
          certification.proposal.exactProjection.toProjectionResult
          certification.proposal.generated.candidate certificate) := by
  rcases ofInferProjRun Hrun with ⟨certificate, ⟨Hcertificate⟩, htype⟩
  have Hcertification := Hcertificate.certification
  rcases Hcertification with ⟨certification⟩
  exact ⟨certificate, htype, ⟨Hcertificate⟩, ⟨certification⟩,
    certification, certificationProposalTrace certification,
    certificationValidationTrace certification⟩

end ProjectionCertificateTrace

end Lean4Lean.TypeChecker.Inner
