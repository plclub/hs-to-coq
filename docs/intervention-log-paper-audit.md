# Intervention Log: Paper Claims Audit (2026-03-16)

## Task
Audit formal verification claims from three hs-to-coq papers against the
current codebase (GHC 9.10.3, Coq 8.20, containers v0.7). Fix gaps where
possible. Document findings.

## Changes Made

### 1. MonoidLaws_Map proof (NEW)
**File**: `examples/containers/theories/MapProofs/TypeclassProofs.v`
**Lines added**: 395-461 (helper lemma + instance)

Added `unions_foldr_union` helper lemma and `MonoidLaws_Map` instance proving
all 4 monoid laws for `WFMap e a` (the well-formedness-carrying Map wrapper):

1. **Left identity** (`mappend mempty x == x`):
   CPS-style via `empty_Desc` + `union_Desc` + `strong_eq1`.
   Key step: `sem (union empty s) i = None ||| sem s i = sem s i` (by computation).

2. **Right identity** (`mappend x mempty == x`):
   Same CPS pattern; key step: `sem (union s empty) i = sem s i ||| None = sem s i`
   (via `oro_None_r` lemma).

3. **Semigroup compatibility** (`mappend x y == x <<>> y`):
   Since `mappend = <<>> = union` for Maps, both occurrences unify via single
   `union_Desc` CPS application. Then `strong_eq1` with `reflexivity`.

4. **mconcat** (`mconcat xs == foldr mappend mempty xs`):
   Two-part proof: (a) `replace` the WFMap-level `foldr` with the Map-level
   `Base.foldr union empty (List.map unpack xs)`, proved by induction with
   `unfold_Monoid_Map` to unwrap the `Program Instance` packaging; (b) apply
   `unions_foldr_union` which shows `unions` and `foldr union empty` agree
   semantically via `unions_Desc` + `strong_eq1`.

This closes a gap vs JFP 2021 paper Fig 4 which lists "Map Instances:
Eq, Eq1, Monoid, Semigroup" but the codebase previously only had SemigroupLaws.

### 2. Gap analysis document (NEW)
**File**: `docs/paper-claims-audit.md`

Comprehensive claim-by-claim audit of all three papers with:
- Status for each claim: HOLDS / REGRESSED / IMPROVED / CHANGED
- Exact line numbers and theorem names verified against source
- Admitted counts verified by grep (distinguishing actual Admitted from comment mentions)
- Axiom inventory for GHC theories
- Corrected GHC Admitted total: 31 actual (was incorrectly estimated as 36 due to
  comment-embedded occurrences in CSE.v, Exitify.v, UniqSetInv.v)
- Corrected UniqSetInv.v: 0 actual Admitted (the one grep match is inside a comment)

### 3. CLAUDE.md updated
**File**: `CLAUDE.md`
- Added "Paper claims audit" section referencing `docs/paper-claims-audit.md`
- Updated containers description to note MonoidLaws for Map

## Attempted but Not Completed

### FromListProofs.v (2 Admitted)
**File**: `examples/containers/theories/MapProofs/FromListProofs.v`
**Lines**: 1775 (`fromList_create_Desc`), 1861 (`fromList_go_Desc`)

**Investigation findings**:
- Root cause confirmed: Coq 8.20 `Program Fixpoint` pre-introduces ALL obligation
  variables, including the CPS continuation `P` and its argument `H1`. This breaks
  the original proof pattern `intros X HX. apply HX.`

- **Fix approach discovered**: `revert dependent P` after renaming `H`/`H0` recovers
  the original CPS goal structure. The `rewrite fromList_create_eq` side condition
  also works after this revert.

- **Remaining obstacle**: After recovering the CPS structure, the Map proof diverges
  from the Set proof at pair destructuring. In the `2^sz = 1` case:
  - Set: `fromList_create_f` matches on `not_ordered e0 xs` directly
  - Map: `fromList_create_f` first destructures `let '(kx, vx) := p in ...`,
    then matches on `not_ordered kx xs`
  - The generic `destruct_match` tactic picks up matches in hypotheses (e.g.,
    `Z.pow` matching on `sz`) before the intended goal match
  - Fix requires explicit `destruct p as [kx vx]; destruct (not_ordered kx xs) eqn:Hord`
    followed by adapting all subsequent `apply HX` calls for the Map pair structure

- **Why reverted**: The cascading differences between Set and Map proofs require
  adapting ~100 lines of intricate proof script. Each `intros X HX. apply HX.`
  pattern needs conversion to either `apply HX` (with pre-introduced HX) or
  local `intros/apply` blocks within IH callbacks. The `insertMax_Desc`,
  `link_Desc`, and nested `eapply IH` calls all need Map-specific type annotations
  (e.g., `@insertMax_Desc e a` vs bare `insertMax_Desc`).

## Verification Methodology

All claims in the audit document were verified by:
1. `grep -c 'Admitted\.' <file>` for Admitted counts (raw)
2. Manual inspection to distinguish proof-ending Admitted from comment mentions
3. `grep 'Qed\.' <file>` to confirm key theorems are complete
4. `grep '^Axiom ' <file>` for axiom inventory
5. `coq_makefile && make` to confirm all files compile

## No Interventions Needed
- All other paper claims verified against codebase as documented
- 25 of 30 GHC theory files confirmed as zero-Admitted
- All container proof files (Set, IntSet, Map) confirmed zero-Admitted
  except FromListProofs (2), IntMapProofs (12), IntSetWordProofs (80)
