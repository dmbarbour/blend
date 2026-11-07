# The guide describes Blend; the README motivates it

`blend-guide` · maintainer · rev 4e94f31

**Context.** The README had grown to hold everything: why Blend, the
command line, the model, what Blend writes, every sample, open
questions, most of it dense and some of it stale. `blend guide` was
planned to print a guide as `bend guide` does (`blend-cli.guide`), its
contents to be discussed first.

**Decision.** The maintainer (2026-11-07):
- The guide is for someone who knows Bend and writes `.blend` files.
  It owns the description of the language, of what Blend writes and of
  the command; the README links to it.
- The README motivates Blend and gets a user started, assuming Bend:
  why, one example, how to install and run.
- Both pare away the unnecessary, aggressively and concisely; examples
  demonstrate, the samples keeping the fuller cases.
- A fenced `blend` block in either is a sample, whole, and the output
  shown after it the sample's: the examples are a curated subset of the
  samples, run and checked as every sample is (2026-11-07, after the
  first cut checked them only by emitting); a fragment goes in an
  indented block.
- The guide is `GUIDE.md` at Blend's root, which `blend guide` prints.

**Consequences.**
- The records' rules live in the guide's sections now, not the README's.
- Open questions and known issues live in the plan's steps, a limit the
  user meets in the guide's Limits.
- `examples_check.sh` (a gate section) compares each block with the
  sample its fence names (```` ```blend samples/override.blend ````), and
  each run shown, an indented `$ blend NAME.blend` and the lines below,
  with the sample's `.out`: the section list and this convention are
  the agent's.

**Rule lives in:** `GUIDE.md`; `README.md`; `examples_check.sh`.
