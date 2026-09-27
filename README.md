# Proof

When the program runs, it starts from Main and only goes
to global objects reachable from Main. However, our analysis will look at each individual global object, and find cyclic dependencies that way. This analysis is faster because it looks at less code since only a subset of the whole program is reachable from the global objects. In this project, we seek to prove that our approach to only look at code reachable from the global objects is sound for finding cyclic dependencies between global objects.

## Daisy's Notes
In stack_dep_step, finish suspend and resume. For resume, need to write Config.all_data_resume