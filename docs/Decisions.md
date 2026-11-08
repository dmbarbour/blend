# Decisions

Why Blend is the way it is. Each decision is a small record in
[`decisions/`](decisions/), grouped here under the larger decisions they
belong to. The rules themselves live in Blend's standing docs (the
guide's model above all, `LAWS.bend`): a record says why, and names
where its rule lives. Blend grew in glam-in-bend, whose records some of
these cite by slug (`generated-sources`, `shadowing-is-an-error`).

## Records

A record is `decisions/<slug>.md`, its slug its stable name, cited as
`` `slug` `` in docs, plans, code comments and commits.

    # <Descriptive title>

    `<slug>` · maintainer|agent · rev <short hash>

    **Context.** …
    **Decision.** …
    **Consequences.** …
    **Rule lives in:** <doc and section>   (omit if none)

- **rev** names the commit a record's last substantive revision was made
  on top of (`HEAD` while editing); `git log <rev>` gives the context it
  was decided in. Typo fixes leave it alone.
- **Revise in place**: a record states the current decision only; git
  keeps the old versions. **Delete what no longer holds**, with its index
  line, once nothing cites its slug.
- **maintainer** marks a decision the maintainer made or ratified;
  **agent** one an agent made, open to revision.
- Plans extract their durable decisions here, at the latest before they
  retire ([`plans/README.md`](plans/README.md)).

This index stays an index: a short paragraph per larger decision, then
one linked line per record. The docs check (`check.sh`) holds every
record's header and rev, that this index lists it, and that no record's
body moves in here.

## The repository

- [`blend-own-repository`](decisions/blend-own-repository.md): Blend is
  a repository of its own, its history filtered from glam-in-bend's,
  which uses it as a submodule.

## The command

Blend is a command of its own, shaped as Bend's and installed beside it.

- [`blend-command-mirrors-bend`](decisions/blend-command-mirrors-bend.md):
  `blend` takes a file first as
  `bend` does and hands the emitted module to Bend; errors in Bend's
  shape; `deps` lists what `emit` reaches and whether each is current;
  `blend` a launcher in `$BEND_HOME/bin` running the tool built natively,
  else through Bend; installed from a checkout or a release, which it
  reports but never takes unasked.
- [`blend-stamps`](decisions/blend-stamps.md): each written file's
  stamp, Blend's version stamp and a hash of its tree, says whether it is
  current; `deps` reads it, `emit` leaves a current import as it is.
- [`blend-guide`](decisions/blend-guide.md): the guide, `GUIDE.md`,
  which `blend guide` prints, describes the language, what Blend writes
  and the command; the README motivates and gets a user started; their
  examples whole modules the gate emits and checks.

## Failures

Blend reports what it cannot do.

- [`blend-no-silent-failures`](decisions/blend-no-silent-failures.md): a
  failure no law prevents is reported as an error, never handled
  silently; a law may then claim its property where none is reported,
  and a report a law proves unreachable may go.

## The model

Blend translates static objects into Bend and adds no logic of its own;
its modules, namespaces and emitted names are Bend's.

- [`blend-adds-no-bend-logic`](decisions/blend-adds-no-bend-logic.md):
  Blend translates objects and adds no Bend logic of its own; mutual
  recursion is an error as in Bend; types, laws and proofs are members,
  emitted as Bend.
- [`blend-module-is-bend`](decisions/blend-module-is-bend.md): a Blend
  module is no object; its own definitions are plain Bend, as Bend's
  static modules are.
- [`blend-namespaces-as-bends`](decisions/blend-namespaces-as-bends.md):
  Blend's namespaces are Bend's, a file's own names and its imports' by
  local aliases, the same however imports reach them; `extend` stays out
  of the top level.
- [`blend-imports-local`](decisions/blend-imports-local.md): a `.blend`
  file's imports are local, never `../` or `/`, or a package's on Bend's
  hub, passed to Bend as written.
- [`blend-paths-no-newline`](decisions/blend-paths-no-newline.md): a path
  holding a newline is refused, as it would break each line naming it.
- [`blend-locations`](decisions/blend-locations.md): a place in the
  source is a location, its module and its line, read only through its
  API.
- [`blend-c3`](decisions/blend-c3.md): inheritance is linearized by C3,
  an error where no order keeps every list it merges.
- [`blend-frozen-host`](decisions/blend-frozen-host.md): `^` sees the host a
  nested object is made for, and inheritance never binds it again.
- [`blend-copies-keep-their-name`](decisions/blend-copies-keep-their-name.md):
  a copied definition is always emitted by its own name, and once more
  for each use.
- [`blend-units-keyed`](decisions/blend-units-keyed.md): the units' table
  keys each entry by its position, a lookup comparing it, so that it is
  provably the list's.
- [`blend-declares-witnessed`](decisions/blend-declares-witnessed.md): a
  typed declaration is bound in each concrete object to its own types
  and checked by a witness Bend checks, in the module's own file.
- [`blend-templates-affine`](decisions/blend-templates-affine.md): a
  template is affine by default, as any definition; the guide explains
  `shared` against `copied` for templates.
- [`blend-emit-verifies-imports`](decisions/blend-emit-verifies-imports.md):
  emission writes the modules named and every import they reach short
  of a package, or with `--alone` the modules named alone.
- [`blend-laws-in-module`](decisions/blend-laws-in-module.md): a module's
  laws and proofs written into its own file after its code, `Obj.LAW.name`
  and `LAW.name`; a law a claim stated once, its proof a member `upd
  proof` may replace, a lemma its own keyword, a law unproven only an
  abstract object's.
- [`blend-do-self`](decisions/blend-do-self.md): `do self<R>:` is a use
  of the concrete object's `bind` and `pure`, bound late; a header naming
  an object, of that object's, bound early; the two `shared`; `self`
  elsewhere an error.
- [`blend-no-shadowing`](decisions/blend-no-shadowing.md): within a
  `.blend` file or object, a bare name is a local or a definition, never
  both, as glam's `shadowing-is-an-error` has it.
