# TMS2 clean-room formalization

This directory is an isolated Lean formalization of `FROZEN_STATEMENT.md`.

## Independence boundary

The formalization was produced from the frozen statement and ordinary finite probability mathematics. It does not import the pre-existing MDSI/Telos Python, Go, SMT, paper-proof, or Lean sources.

It is still generated within the same conversational programme, so provenance separation is incomplete until an independent human or separately governed formalizer reviews the statement and source.

## Status

Work in progress. The draft pull request must not be merged or cited as a kernel theorem until:

1. every required obligation is formalized without `sorry`, `admit`, or new axioms;
2. the pinned Lean build succeeds;
3. the valid control is accepted;
4. false and malformed controls are decisively rejected;
5. the axiom audit is clean;
6. the Lean environment checker and an independently implemented checker succeed;
7. a statement-fidelity comparison against the frozen statement is completed.

## Toolchain

- Lean: `leanprover/lean4:v4.31.0`
- mathlib: tag `v4.31.0`

The CI workflow records exact resolved commits and build logs.
