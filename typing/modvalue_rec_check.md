Module/Value Rec Check/Compiler
---

Idea: Extend the mode system of the value rec check to all compilation of both
recursive values and modules.


Extending the mode system
--
We have to extend the mode system to have modes for record projections (a kind of "Return",
used for accessing members of a module or record), and record lifting (a kind of "Guard",
used when creating modules and records).

In addition, "Delay" should gain a description of what we are delaying, so that we can
add its inverse "Apply", since "Dereference" is much too restrictive.


Handling ill-founded recursive modules
--

We may encounter ill-founded recursive modules of possibly two kinds:
1. Those currently rejected by the safe-module check (not all are ill-founded)
2. Those that would cause an exception at runtime, due to reading a dummy value

Our graph algorithm has a more detailed analysis, so it should accept well-founded modules
rejected by (1).
Those that would currently raise at runtime have a true cycle. If we want to maintain similar
behavior, we could extract the feedback arc set from the dependency graphs, and replace
those links with exception-throwing functions. It's not clear if there is any point to this,
since if a program unconditionally throws, it's not useful.
Maybe in combination with functors?
