# Proof

HEEEEEEEELLO!

Date: Aug 26
Next steps:
~~1. Actually read LessThanInv to make sure it works~~
2. Prove Cycle.lean (Deps can be reused)
3. Prove EndsInFixPoint (maybe I should try this before 2, I'm so tired of these Deps, honestly)

Date: Sept 18
Looked at LessThanInv. It makes sense.
Added a termination theorem in Termination.lean
Started EndsInFixPoint by first proving that every state G in the fixpoint is
stable, which gives us Grow, and thus FixPoint
We also need the helper that every_object_is_in_fixpoint, by virtue to config.start
(This is probably different from what the algorithm actually does though...

If Instead, config.start doesn't have a queue at all. We only suspend and resume...
Then we need to say that every object that Main depends on (the algorithm's Dep) is InFixPoint
...but how?
)