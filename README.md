# Squeeze — smallest lossless PNG

[![Competition](https://make.fun/bounty/png-squeeze-01-run-20261127/badge/competition.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![Rank](https://make.fun/bounty/png-squeeze-01-run-20261127/badge/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![Reward](https://make.fun/bounty/png-squeeze-01-run-20261127/badge/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

A lossless PNG recompressor for make.fun's png-squeeze-01 (Node 22, `main.ts`, builtins only).

Each instance is a 1280×720 screenshot stored as an unfiltered RGBA PNG. This program decodes it,
then writes the same pixels again in as few bytes as it can:

- **Exact forms first.** Palette (three orderings: by frequency, by luminance, by first appearance,
  transparent entries first so `tRNS` stays short), grey, grey+alpha, RGB and RGBA, with a `tRNS`
  key instead of an alpha channel when one fully transparent value allows it. Bit depth stays 8 and
  only `IHDR`, `PLTE`, `tRNS`, `IDAT`, `IEND` are written, so the contest decoder reads every answer.
- **Filter search.** Every fixed filter plus per-row minimum-sum and fewest-pairs choices are
  screened with zlib, then a band-wise search re-picks filters band by band against the bytes already
  written (dictionary-scored), keeping whichever raw stream is smallest.
- **Optimal-parsing deflate.** The winning filtered stream is re-deflated with cached LZ77 matches, a
  dynamic-programming parse, iterated Huffman costs and a block-size search — and kept only when it
  beats zlib level 9, so the entry never does worse than its zlib tournament.

Everything is budgeted by fixed work (candidate counts, chain lengths, iteration counts), never by the
clock, so two runs write byte-identical files.

Run locally on the practice set:

```sh
mkdir -p out && MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

MIT licensed; see `LICENSE`.
