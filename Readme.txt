This directory contains Murphi files for the submission to VMCAI.

1. flashNoMutex.m This is flash protocol for verifying deadlock
freedom with no mutual exclusion or data properties. Thus, the
abstract model is more unconstrained, leading to a larger runtime.

2. flashWithMutex.m This file also verifies mutual exclusion and data
property, along with deadlock freedom. Thus a shorter runtime due to
more constrained abstract model.

3. germanNoMutex.m: German code for verifying deadlock freedom without
mutual exclusion or data properties. No non-interference lemmas needed
for this.

4. germanWithMutex.m: German code for verifying deadlock freedom with
mutual exclusion.

5. germanBuggy.m: Injected bug in german protocol -- invack
dropped. Leads to a deadlock caught by the skolemization method.
