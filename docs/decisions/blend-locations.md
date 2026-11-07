# A place in the source is a location, its module and its line

`blend-locations` · maintainer · rev 9431ac3

**Context.** Every node, line and error carried one U32, `no`, packing
its module and line as `k * 1000000 + line`, decoded by `loc.mod` and
`loc.line`: an early shortcut, with no record, that capped a module at
999,999 lines and a tree at 4,294 modules, both silent until reported
(`blend-laws2.lines-bound`), and that printed a raw packed number in
two messages.

**Decision.** The maintainer (2026-11-07): the clear pair, `(module,
line)`, preferred; numbering lines consecutively across the tree, with
a table of each module's first line, acceptable if the pair costs
severely at run time; and the location records abstracted. A location
is a `Loc{mod, line}`, read and made only through its API:
`loc.at`, `loc.top(k)` (module k itself, line 0), `loc.mod`,
`loc.line`, `loc.next` (the next line of a module), `loc.eq`,
`loc.le` (module, then line) and `locs.has`. The reader numbers a
module's lines from its `loc.top`; the proofs reason through four
lemmas (`loc_eq_refl`, `loc_eq_eq`, `loc_succ_ne`, with the API's
definitions), so that a later change of shape changes those alone.

**Consequences.**
- No limit on a module's lines or the modules of a tree but U32's; the
  errors that reported the old limits are gone.
- The emitted files, the errors and their order are as before, byte
  for byte; the families' instructions 1.4 to 1.5% fewer (chain, fan
  and copies at N to 4N), a scan of every module's bytes for its lines
  gone with the limits.
- A line Bend reports back, in the checks of a written file, stays a
  plain number: it is no place in Blend's sources.

**Rule lives in:** `blend.bend`, the lines (`Loc` and its API).
