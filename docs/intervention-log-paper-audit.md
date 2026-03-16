# Intervention Log: Paper Claims Audit (2026-03-16)

## Task
Audit formal verification claims from three hs-to-coq papers against the
current codebase (GHC 9.10.3, Coq 8.20, containers v0.7). Fix gaps where
possible. Document findings.

## Changes Made

### 1. MonoidLaws_Map proof (NEW)
**File**: `examples/containers/theories/MapProofs/TypeclassProofs.v`
- Added `unions_foldr_union` helper lemma
- Added `MonoidLaws_Map` instance (4 laws: left identity, right identity,
  semigroup compatibility, mconcat)
- This closes a gap vs JFP 2021 paper Fig 4 which lists "Map Instances:
  Eq, Eq1, Monoid, Semigroup" but the codebase only had SemigroupLaws

### 2. Gap analysis document (NEW)
**File**: `docs/paper-claims-audit.md`
- Claim-by-claim audit of all three papers
- Status for each: HOLDS / REGRESSED / IMPROVED / CHANGED
- Admitted counts per file for both containers and GHC theories
- List of unfixable regressions with explanations

### 3. CLAUDE.md updated
**File**: `CLAUDE.md`
- Added "Paper claims audit" section referencing the gap analysis document
- Updated containers description to note MonoidLaws for Map

## Attempted but Not Completed

### FromListProofs.v (2 Admitted)
- Attempted to fix `fromList_create_Desc` and `fromList_go_Desc` obligations
- Root cause confirmed: Coq 8.20 pre-introduces ALL obligation variables
  (including CPS continuation P and H1), breaking proofs that start with
  `intros X HX`
- Fix approach: `revert dependent P` recovers the original proof structure
- However, the Map version additionally requires pair destructuring (`destruct p`)
  before pattern matching, unlike the Set version. This cascading difference
  affects `destruct_match` behavior (picks up wrong matches in hypotheses)
- Estimated effort: 2-4 hours of careful proof engineering
- Reverted to preserve the working Admitted state

## No Interventions Needed
- All other paper claims verified against codebase as documented
