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

### 4. fromList_create_Desc proof fixed (was Admitted)
**File**: `examples/containers/theories/MapProofs/FromListProofs.v`

Fixed the `fromList_create_Desc` obligation (was Admitted since Coq 8.20 upgrade).
Key techniques:
- `revert dependent P` to recover the CPS structure after Coq 8.20 pre-introduction
- Explicit `destruct p as [kx vx]; destruct (not_ordered kx xs) eqn:Hord` instead of
  generic `destruct_match` (which picks up wrong matches in hypotheses)
- `change (match 2^x with 0=>0|Z.pos p=>Z.pos p~0|Z.neg p=>Z.neg p~0 end) with (2*2^x)`
  to normalize Z multiplication that Coq 8.20 reduces to match form
- Map-specific tactic annotations: `applyDesc e (@link_Desc e a)`, `solve_Bounded e`

This reduces containers Admitted from 94 to 93.

### 5. fromList_go_Desc proof COMPLETED (was Admitted)
**File**: `examples/containers/theories/MapProofs/FromListProofs.v`

Fixed the `fromList_go_Desc` obligation (was Admitted since Coq 8.20 upgrade).
This required solving 6 distinct technical issues across 5 sessions:

1. **Coq 8.20 pre-introduction**: `revert dependent P` not needed (Desc' return
   type is NOT pre-introduced), but scalar hypotheses H/H0/H1 are
2. **Pair destructuring**: `destruct p as [kx vx]` + explicit `destruct (not_ordered ...)`
   instead of generic `destruct_match`
3. **Z multiplication normalization**: `change (match 2^x with ...) with (2*2^x)` +
   `Z.pow_add_r` for size proofs
4. **`order e` + `==` incompatibility**: Convert `(i == kx) = true` to `(kx <= i) = true`
   via `Eq_le_r` lemma before `order e`
5. **`SomeIf` opacity**: `unfold SomeIf` before `destruct` to enable `simpl` reduction
6. **Residual oro chain**: `rewrite sem_list_app; destruct p` to close the final case
   where `sem_for_lists (rev zs ++ p :: nil)` didn't match `sem_for_lists (rev zs) ||| ...`

Key architectural insight: use `eapply (@fromList'_Desc). exact HB.` for the zs<>nil
case (manual CPS) + `apply showDesc'. split; [assumption|].` to preserve the outer
Desc' structure, avoiding `applyDesc` which would consume it via `try assumption`.

This reduces containers Admitted from 94 to 92.

## No Remaining Unfinished Tasks

All tasks from the paper claims audit are now complete.

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
