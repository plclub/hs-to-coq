# New hs-to-coq Example

Create a new hs-to-coq example that translates a Haskell library to Coq. This skill sets up the directory structure, configures the build system, and iteratively translates the library following the Translation Principles from CLAUDE.md.

## Arguments

The argument should be the library name and its Git repository URL, e.g.:
```
/new-example mtl https://github.com/haskell/mtl.git
```

If only a name is given, ask the user for the repository URL.

## Phase 1: Setup

### 1.1 Create directory structure

```
examples/<name>/
├── Makefile
├── README.md
├── edits                    # Start empty
├── <name>/                  # Git submodule
├── lib/                     # Generated output (created by make)
├── module-edits/            # Per-module edits (created as needed)
└── theories/                # Proofs (created later if needed)
```

### 1.2 Add Git submodule

```bash
git submodule add <REPO_URL> examples/<name>/<name>
```

Pin to a specific tag/commit if the user specifies one. Ask:
- "Which version/tag/commit of the library should I use?"

### 1.3 Identify Haskell source files

Explore the submodule to find:
- The `src/` or `lib/` directory containing Haskell sources
- The `.cabal` file to understand module structure and dependencies
- Which modules are "exposed" (public API) vs internal

Ask the user:
- "I found N modules. Should I translate all of them, or start with a subset?"

### 1.4 Create Makefile

Use the graph/containers Makefile as a template. The Makefile must:

```makefile
include ../../common.mk

ifeq (,$(wildcard <name>))
$(error Please run git submodule update --init examples/<name>/<name>)
endif

OUT=lib

MODULES = \
  Module/Path/One \
  Module/Path/Two

VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES = $(VFILES_GEN)

all: vfiles coq

vfiles: $(OUT)/edits $(OUT)/_CoqProject $(OUT)/README.md $(VFILES)

$(OUT)/_CoqProject: Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo '-Q ../../../base ""' >> $@
	$(foreach f,$(addsuffix .v,$(MODULES)),echo '$(f)' >> $@;)

$(OUT)/edits:
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains generated Coq files. Do not edit directly.' >> $@

coq: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT) && coq_makefile -f _CoqProject -o Makefile
	$(MAKE) -C $(OUT)

HS_TO_COQ_OPTS := \
  -e ../../base/edits \
  -e edits \
  --iface-dir ../../base/ \
  --iface-dir $(OUT) \
  -N \
  -i <name>/<src-path>

.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) \
                            $$(wildcard module-edits/$$*/midamble.v) \
                            $$(wildcard module-edits/$$*/edits) \
                            $$(wildcard module-edits/$$*/flags) \
                            edits $(OUT)/README.md
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             $(HS_TO_COQ_OPTS) \
	             -o $(OUT) \
	             <name>/<src-path>/$*.hs
	test -e $@

clean:
	rm -rf $(OUT) hs-spec

theories: coq
	@if test -f theories/_CoqProject; then \
	  cd theories && coq_makefile -f _CoqProject -o Makefile && $(MAKE); \
	fi
```

### 1.5 Create minimal edits file

Start with an EMPTY edits file. Do not presume any edits are needed.

### 1.6 Create README.md

```markdown
# <Name> Example

Coq translation of the [<name>](REPO_URL) Haskell library using hs-to-coq.

## Building

```bash
git submodule update --init examples/<name>/<name>
make -C examples/<name>
```

## Structure

- `lib/` — Generated Coq files (do not edit directly)
- `edits` — Translation directives
- `module-edits/` — Per-module customization
- `theories/` — Hand-written proofs
```

## Phase 2: Translation (iterative)

### Translation Principles (from CLAUDE.md)

Follow this strict priority order for handling translation issues:

1. **Auto-generate** — try `make vfiles` first with no edits
2. **Use edits** — `skip`, `rename`, `rewrite`, `order`, `termination`, `equations`, etc.
3. **Fix hs-to-coq** — if the tool should handle a case but can't
4. **`redefine`** — only when translation is fundamentally wrong
5. **`midamble.v`** — only for mid-file definitions that can't be expressed via edits
6. **Manual files** — absolute last resort

### 2.1 First translation attempt

Run translation with no edits:

```bash
make -C examples/<name> vfiles 2>&1
```

Capture ALL errors. Do NOT add any edits preemptively.

### 2.2 Diagnose and fix errors iteratively

For each error, follow this decision tree:

**"Could not find module X"** or **"skip declarations that mention X"**
→ Add `skip module X` to the global edits file. This is the lightest edit.

**"Cannot translate data family / type family"**
→ Add `skip <qualified_name>` for the specific declaration.

**Type mismatch or constructor name conflicts**
→ Try `rename value` or `rename type` first (lightweight).
→ If that fails, try `rewrite` to fix specific subexpressions.
→ Only use `redefine` if the above don't work.

**Termination / recursion issues**
→ For structural recursion: try `equations <name>` first (preferred over Program Fixpoint).
→ For well-founded recursion: use `equations <name>` + `termination <name> {measure ...}`.
→ For complex mutual recursion: try `inline mutual` before resorting to midamble.
→ Use `termination <name> deferred` only as a last resort (produces deferredFix).

**"skipping a binding" or ordering issues**
→ Try `order <name1> <name2>` to fix topological sort.

**Typeclass issues**
→ Try `skip class <ClassName>` if the class is from an untranslated module.
→ Try `skip method <ClassName> <methodName>` for individual methods.

### 2.3 Verify before editing

Before adding ANY edit, verify the issue exists:

1. Read the actual error message
2. Check if the issue is in the Haskell source or the translation
3. Try the simplest fix first
4. If you believe something can't be translated, show the user the error and ask:
   ```
   "Module X.Y.Z fails to translate because [reason].
   I've tried [what you tried]. Options:
   a) skip the entire module
   b) skip just the problematic definition
   c) redefine it manually
   d) fix hs-to-coq to handle this case
   Which would you prefer?"
   ```

### 2.4 Ask user about each non-trivial decision

Never silently:
- Skip a module that contains definitions other modules depend on
- Redefine a definition (always show what you'd redefine it to)
- Add a midamble (always explain why it's needed)
- Use `termination deferred` (explain the deferredFix implications)

### 2.5 Compile generated Coq

After translation succeeds:

```bash
(cd examples/<name>/lib; coq_makefile -f _CoqProject -o Makefile)
make -C examples/<name>/lib
```

Fix Coq compilation errors by adjusting edits, preambles, or midambles.

## Phase 3: Finalization

### 3.1 Ask about convenience copies

Ask the user:
```
"Should I commit the generated lib/*.v files to Git as convenience copies?
This lets people build without running hs-to-coq, but means the files
need to stay in sync with edits changes. (The base/, containers/, ghc/,
and graph/ examples all do this.)"
```

If yes:
- `git add examples/<name>/lib/`
- Commit with a descriptive message

### 3.2 Ask about CI integration

Ask the user:
```
"Should I add this example to the CI pipeline?
This would add it to:
- test-coq job (compile lib/ and theories/)
- test-translation job (regenerate and verify convenience copies match)
"
```

If yes, update `.github/workflows/hs-to-coq.yml`.

### 3.3 Ask about theories

Ask the user:
```
"Would you like to set up a theories/ directory for hand-written proofs?
This is useful if you plan to prove properties about the translated code."
```

If yes, create `theories/_CoqProject` with appropriate `-Q` paths.

### 3.4 Final verification

Run the full build chain:

```bash
make -C examples/<name> clean
make -C examples/<name>
```

### 3.5 Commit

Commit the new example with a descriptive message:

```
Add <name> example: <brief description>

Translated from <repo> (<tag/commit>).
<N> modules translated, <M> skipped.
Key edits: <brief summary of non-trivial edits>.
```

## Important Rules

- **Never presume** an edit is needed before seeing the error
- **Always verify** that a definition truly can't be translated before skipping/redefining
- **Ask the user** about non-trivial decisions (skip vs redefine vs fix)
- **Prefer equations** over Program Fixpoint for non-trivial recursion
- **Follow Translation Principles** priority order strictly
- **Show your work** — explain what failed and what you tried before asking
- **Start minimal** — empty edits, add only what's needed
- **Test incrementally** — translate one module at a time if the library is large
