# Proof

HEEEEEEEELLO! (like claude.md, but for me. how amazing)

Date: Aug 26
Next steps:
~~1. Actually read LessThanInv to make sure it works~~
2. Prove Cycle.lean (Deps can be reused)
3. Prove EndsInFixPoint (maybe I should try this before 2, I'm so tired of these Deps, honestly)

Date: Sept 18
Looked at LessThanInv. It makes sense.
Added a termination theorem in Termination.lean

Date: Sept 19
Per yesterday: Should probably change my algorithm. Config shouldn't have a queue at all.
We start with G\_main and only suspend and resume when necessary

For the fixpoint argument, we need something that says if G is InFixPoint,
THEN we satisfy FixPoint.
We need this addition to prove that every iteration of the algorithm
fixpoint IS a fixpoint.
Otherwise, consider config.start.fixpoints = \emptyset.
A G that we haven't considered will break the theorem.

With this addition, can change the algorithm to satisfy

Added Conclusion.lean.

Next step, do Cycle.lean.

Date: Sept 20
I think I know how to fix the FixPoint argument. We declare a new L with only
G's within the Algo's FixPoints list.

Date: Sept 23
One month from the project and it seems I had forgotten the point of
the fucking algorithm...

Idea: when the program runs, obviously it starts with Main and only goes
to global objects reachable from Main. However, our analysis will look at each individual global object, and find cyclic dependencies that way. It is meant to be faster and to look at less code because only a subset of the whole program starts from the global objects.

Part 2:
discharge sorries in report_cycle_then_dep and clean it up. Then
we might be good for LessThanInv and Cycle

Date Sept 24
Go to Cycle and READ THIS THING