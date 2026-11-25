---
title: "A1. Setting up Yamma"
---

<nav class="nav">
    <span class="inactivenav" aria-disabled="true">← Previous</span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

<h1 id="a01-yamma" style="border-bottom: none;">A1. Setting up Yamma</h1>

> [!WARNING]
> This appendix is AI-generated and has not been reviewed. It was written from Yamma's README,
> `package.json`, and parser source (version 0.0.19, March 2025). It has not been tried in a running
> editor. Where the docs were silent, the text says so.

@toc(hn)

## Why bother

> [!WARNING]
> This section is AI-generated and has not been reviewed.

The built-in proof assistant works from the goal backwards, one `assign` at a time. That's fine for
chapter 4. In chapter 6 the hints keep saying "write down the intermediate line first": the dummy
variable in `abbi`, the middle formula in a `3bitr4g`, the element in `ssrdv`. In MM-PA that means
`let step` and `let variable`. In a worksheet you just type the line, and the tool fills in or checks
everything else as you go.

[Yamma](https://github.com/glacode/yamma) is a VS Code extension for exactly this. It reads `.mmp`
*proof worksheets*, a text format inherited from mmj2, and checks them live against a `.mm` database.
It unifies steps, suggests labels, searches the database, and generates the finished proof.
[mmj2](https://github.com/digama0/mmj2) is the older Java tool that introduced the worksheet format.
It's covered briefly at the end.

You don't need a new file per proof. Keep one `scratch.mmp`, prove something, copy the result out,
clear it, and start the next one.

## Install and point it at a database

> [!WARNING]
> This section is AI-generated and has not been reviewed.

1. In VS Code, open Extensions, search for **Yamma** (publisher `glacode`, ID `glacode.yamma`), and
   install it. It needs VS Code 1.69 or later.
2. Tell Yamma which database to load. If a file named `set.mm` is in the same folder as the `.mmp`
   you open, Yamma loads it automatically. Otherwise set `yamma.mmFileFullPath`, either through
   *Extension Settings* (gear icon on the extension) or in the workspace's `.vscode/settings.json`:

   ```json
   {
       "yamma.mmFileFullPath": "path/to/myset.mm"
   }
   ```

   This repository's `.vscode/settings.json` currently points at chapter 4's `src/code-04/myset.mm`.
   For chapter 6, point it at your working copy of the chapter 5 database (the `myset.mm` the
   chapter 6 introduction tells you to make).
3. Open or create a file ending in `.mmp`. Yamma parses and verifies the whole database when it
   loads it. For `set.mm` (about 50 MB) expect that to take a while the first time. If the database
   has errors, it loads a valid partial theory anyway.

The other settings can stay at their defaults. The two worth knowing about:

| Setting | Default | What it does |
|---|---|---|
| `yamma.disjVarAutomaticGeneration` | `GenerateDummy` | Adds `$d` lines for dummy variables automatically. `GenerateAll` also adds the mandatory ones. `GenerateNone` turns it off. |
| `yamma.proofMode` | `normal` | Format of the generated proof (`normal`, `packed`, `compressed`). The `.mmt` export below always uses compressed. |

## The worksheet format

> [!WARNING]
> This section is AI-generated and has not been reviewed.

A worksheet is a list of statements. Each statement starts in column 0, and an indented line
continues the previous one. This is a complete worksheet for chapter 4's `mp2`, taken from Yamma's
test suite:

```text
$theorem testname
* A double modus ponens inference.
h50::mp2.1           |- ph
h51::mp2.2           |- ps
h52::mp2.3           |- ( ph -> ( ps -> ch ) )
53:50,52:ax-mp       |- ( ps -> ch )
qed:51,53:ax-mp      |- ch
```

- `$theorem LABEL` names the theorem. If `LABEL` already exists in the database (as every exercise
  in these notes does), Yamma checks your worksheet against it. The hypothesis labels must match,
  for example `mp2.1`.
- A line starting with `*` is the theorem's comment.
- A proof step is `REF:HYPS:LABEL |- formula`.
  - `REF` is the step's name, usually a number.
  - `HYPS` is a comma-separated list of the steps it uses, in the order of `LABEL`'s hypotheses.
  - `LABEL` is the theorem or axiom applied.
  - Any of the three parts can be left empty while you work: `53::ax-mp`, or `53:: |- ( ps -> ch )`
    with no label yet.
- `h` in front of the ref marks a hypothesis of the theorem being proved (`h50::mp2.1`).
- The last step must have ref `qed`.
- `$d x y` declares two variables distinct (exactly two per line).
- Working variables, the worksheet's version of MM-PA's `$1`, `$2`, are written `&W1` (wff),
  `&S1` (setvar), `&C1` (class). They appear where a label doesn't determine part of a formula. You
  replace them by typing the expression you want.

Steps can be written in any order, but a step must appear below the steps it cites, and `qed` goes
last. **Unify and Renumber** (below) tidies the order and numbering for you.

## Keys and commands

> [!WARNING]
> This section is AI-generated and has not been reviewed.

| Key | Command | Use |
|---|---|---|
| `Ctrl+U` | Unify | Check every step, fill in what the labels determine, derive missing hypothesis steps. Press it constantly. |
| `Ctrl+R` | Unify and Renumber | Same, then renumber and reorder the steps. |
| `Ctrl+H` | Search theorems in the theory | Search the database. |
| `Ctrl+Space` | (completion) | Label and step suggestions at the cursor. |

On a Mac the README says you may need `Cmd` instead of `Ctrl`. Everything is also in the command
palette and in the right-click menu of an `.mmp` file.

Searching can also be done inline with a line in the worksheet:

```text
SearchSymbols: ( x e. ( A i^i B ) -> x e. A )
```

`SearchComment:` searches comment text instead. Chapter 5's advice about `search` applies here as
well. Search for the *shape* you need, with the class and wff variables you expect.

## Worked example: `inss1`

> [!WARNING]
> This section is AI-generated and has not been reviewed.

This is the first proof in 6.2, `|- ( A i^i B ) C_ A`. Start with only the goal and the label you
want to apply to it:

```text
$theorem inss1
qed::ssriv |- ( A i^i B ) C_ A
```

Press `Ctrl+U`. Yamma unifies `ssriv`'s conclusion with the goal and adds a step for its hypothesis.
`ssriv`'s hypothesis mentions an element variable that its conclusion doesn't, so that position comes
back as a working variable, something like `&S1`. This is the moment where MM-PA needed
`let variable`. Here you overwrite `&S1` with `x`:

```text
$theorem inss1
50:: |- ( x e. ( A i^i B ) -> x e. A )
qed:50:ssriv |- ( A i^i B ) C_ A
```

Give step 50 the label `simplbi`. `Ctrl+U` again adds its hypothesis,
`( x e. ( A i^i B ) <-> ( x e. A /\ &W1 ) )` or similar. Label that step `elin` and unify once more.
The worksheet is complete:

```text
$theorem inss1
51::elin           |- ( x e. ( A i^i B ) <-> ( x e. A /\ x e. B ) )
50:51:simplbi      |- ( x e. ( A i^i B ) -> x e. A )
qed:50:ssriv       |- ( A i^i B ) C_ A
```

The exact refs and the working variable names Yamma generates may differ from these. The steps and
labels are the ones in the chapter 6 hint.

## Worked example: `abbi`, writing the middle line yourself

> [!WARNING]
> This section is AI-generated and has not been reviewed.

`abbi` is `|- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } )`. The hint says to assign `eqrdv`
with a fresh element `y`, then `3bitr4g`. In a worksheet, type the line you're aiming for and let
unification check that it fits:

```text
$theorem abbi
51:: |- ( A. x ( ph <-> ps ) -> ( y e. { x | ph } <-> y e. { x | ps } ) )
qed:51:eqrdv |- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } )
```

Then put `3bitr4g` on step 51 and fill in its three hypotheses:

```text
$theorem abbi
52::spsbbi         |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) )
53::df-clab        |- ( y e. { x | ph } <-> [ y / x ] ph )
54::df-clab        |- ( y e. { x | ps } <-> [ y / x ] ps )
51:52,53,54:3bitr4g |- ( A. x ( ph <-> ps ) -> ( y e. { x | ph } <-> y e. { x | ps } ) )
qed:51:eqrdv       |- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } )
```

`y` is a dummy variable: it appears in the proof but not in the statement. `eqrdv` requires `y`
distinct from `x`, `ph`, and `ps`. With the default `GenerateDummy` setting, Yamma adds those `$d`
lines itself. Otherwise it reports them as missing and offers a quick fix. (In `set.mm`, `abbi`'s
scope already declares them. The worksheet just has to agree.)

## Getting the proof back into the database

> [!WARNING]
> This section is AI-generated and has not been reviewed.

When the worksheet is complete, run **Unify + Store in MMT Folder** from the right-click menu.
Despite the name, the code writes the result next to the worksheet: `scratch.mmp` produces
`scratch.mmt`. It contains the theorem as a block ready for a `.mm` file:

```text
  ${
    $d ... $.
    abbi $p |- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } ) $=
      ( ... compressed proof ... ) $.
  $}
```

For an exercise, the statement is already in `myset.mm`. You only need the proof: replace the text
between `$=` and `$.` of the existing `abbi $p` with the one from the `.mmt` file. Then check it with
the verifier:

```sh
metamath 'read myset.mm' 'verify proof abbi' quit
```

Don't skip this step. Yamma checks a step label only by looking it up in the whole database. Its
source has no rule that you may cite only *earlier* statements, the way MM-PA's `prove` does. In
`scratch.mmp` you can happily use `abbii`, which comes after `abbi` and is proved from it.
`verify proof` in `metamath.exe` rejects that, because a proof may only refer to statements before it
in the file. It also catches any `$d` problem, as in chapter 6's `elabg`.

Two other things to avoid in exercises:

- `$getproof LABEL` loads the database's existing proof of `LABEL` into the worksheet. That's useful
  for reading library proofs, but it shows you the answer.
- Labels tagged "New usage is discouraged" give a warning, and Yamma won't generate a proof that uses
  them unless the worksheet contains the line `$allowdiscouraged`. For the exercises, take the
  warning as a sign to find another lemma.

## mmj2, briefly

> [!WARNING]
> This section is AI-generated and has not been reviewed.

[mmj2](https://github.com/digama0/mmj2) is a Java application with its own editor window, and the
origin of the worksheet format above. Its worksheets start with a header naming the theorem and,
via `LOC_AFTER`, where in the database the proof lives. That lets it restrict a proof to earlier
statements. It has search, a unification engine, and macros. Upstream `set.mm`'s CI runs it as one
of several verifiers. The cost is setup: a Java install, a run script, and an interface from another
era. For working through these notes, Yamma inside the editor you already use is the easier choice.
Use mmj2 if you start contributing upstream, or if you want `LOC_AFTER`'s ordering check while you
work.
