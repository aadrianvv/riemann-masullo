# Transcription (reading aid)

Verbatim readable transcription of A. M. Masullo, *The Music of the Primes*,
split by chapter. Each file preserves the physical PDF page markers
(`## PDF page N`, printed number = PDF number).

- Source: `paper/the-music-of-the-primes.pdf`, sha256
  `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`
  (see `paper/README.md`). 940 physical pages, including 11 verified blanks
  (2, 8, 10, 56, 116, 154, 286, 380, 654, 822, 932).
- The manuscript belongs to its author and is **not** covered by this
  repository's Apache-2.0 license, exactly like `paper/`.
- Verbatim, not corrected: printed errors, placeholders and unfinished text
  are preserved. No figure artwork is reconstructed; diagrams are label text
  plus LaTeX arrays. Typography (bold/small-caps, color, spacing) is collapsed.
- The PDF is the reference. Check any formula against the page image
  (`scripts/paper.sh --png N`) before formalizing it.

## Contents

See `chapters/README.md` for the per-chapter page ranges.
`front-matter.md` covers pp. 1–10 through `bibliography.md` pp. 933–940.

## Quick checks (no render needed)

```sh
python3 -c "
import re, pathlib
ms = []
for p in sorted(pathlib.Path('transcription/chapters').glob('*.md')):
    if p.name == 'README.md':
        continue
    t = p.read_text(encoding='utf-8')
    assert '\ufffd' not in t, p
    ns = list(map(int, re.findall(r'^## PDF page (\d+)\s*$', t, flags=re.M)))
    assert ns == sorted(ns), p
    ms += ns
assert sorted(ms) == list(range(1, 941)) and len(ms) == 940, 'all 940 pages present exactly once'
print('pages:', len(ms), 'FFFD: 0')
"
```

Full verification (assembly, tag sweep, glyph/hat checks, random visual probe)
is reported in the tracking issue. A page-by-page final visual review is in
progress; findings go to `ERRATA.md` and the issue, never silently into this text.
