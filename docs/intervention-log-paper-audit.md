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

## Attempted but Not Completed

### FromListProofs.v: fromList_go_Desc (1 remaining Admitted)
**File**: `examples/containers/theories/MapProofs/FromListProofs.v`
**Line**: 1965 (`fromList_go_Desc`)

**Extensive investigation (2026-03-16, continued)**:

The proof structure is 90% complete. Working approach discovered:
1. **Nil/singleton cases**: work directly with `solve_Desc e` + manual semantic proofs
2. **2+ case, not_ordered=true**: `applyDesc e (@fromList'_Desc)` + `solve_Desc e` + semantic
3. **2+ case, not_ordered=false**: `pose proof (fromList_create_Desc ...) + apply` to
   eliminate the `fromList_create` call, then `applyDesc e (@link_Desc e a)`, then:
   - **zs=nil subcase**: `assert HIH : Desc' ...` with `eapply IH; [measure|lia|assumption|
     size proof with change/lia|]` works. Semantic reconciliation via `rewrite Hsem_go,
     Hsem, Hlist_l'; simpl rev; rewrite rev_app_distr, !sem_list_app; erewrite
     sem_toList_reverse, <- toList_sem''`.
   - **zs<>nil subcase**: `eapply (@fromList'_Desc)` + semantic reconciliation.

**Progress (2026-03-16, session 3)**: The IH recursion case (zs=nil) is now FULLY
proved. Key breakthroughs:
- `unfold isLB, isUB` → `simpl isLB, isUB` to normalize boolean ordering facts
- `assert (compare i kx = Eq) by (rewrite Ord_compare_Eq; exact Hieq)` to convert
  `==` to `compare` before `order e` (which can't handle `Eq_` class `==` directly)
- `eapply sem_inside; eassumption` with `eassumption`-based Bounded matching
  (instead of naming specific hypotheses)

**Discovery (session 4)**: The zs<>nil subcase's goal is NOT `Desc'` — the
`applyDesc e (@link_Desc e a)` consumed the outer Desc' via `try assumption`.
The remaining goal is a side condition from `replace`. This explains why
`rewrite Hlist_l'` couldn't find `(ky,vy)::xss` — the goal doesn't contain the
original semantic function. Needs MCP/interactive tool to inspect the actual goal.

**Historical blocker (zs<>nil subcase only)**: The semantic reconciliation step requires
proving that `sem s i`, `SomeIf (i==kx) vx`, and `sem l' i` have disjoint key
domains, making `|||` (oro) order-irrelevant. After `destruct (sem s i), (i==kx),
(sem l' i)`, most cases close by `reflexivity`. The impossible cases (where two
sources both have `Some`) need `exfalso` via:
```
apply (sem_inside HBounded_l') in Hl'_i; destruct Hl'_i;
apply (sem_inside H0) in Hs_i; destruct Hs_i; order e.
```
But `order e` fails because it can't combine boolean `isUB`/`isLB` facts with
`==` to derive ordering contradictions. The `solve_Bounds e` tactic also fails.
Possible fix: unfold `isUB`/`isLB` before calling `order e`, or add a dedicated
tactic for combining Eq_ and Ord bounds.

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
