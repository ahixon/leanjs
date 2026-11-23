Argument builders for `JSProofs/ReactCompleteUnit.lean` (zippy docs/react-proofs.md).

`args.py` parses a callee theorem's binders and builds its named arguments at a caller's state: implicits by name
(renamed), premises transferred by the shape of their type (heap bounds, kinds and properties through the stage's
facts `gZk`/`gKk`/`gPk`, fuel `gFk`, envs `gEk`, module bindings `gBk`). `stage1.py`–`stage3.py` inserted the three
`completeWork` calls into the proof one at a time (each replaces the proof's `trace_state; all_goals sorry`); the
committed proof is their result plus hand edits, so rerunning them is not needed to build it.
