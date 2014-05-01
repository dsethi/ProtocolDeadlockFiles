This directory contains Murphi files for the submission to VMCAI.

1. flashWithMutex.m This file verifies s-deadlock freedom along with
mutual exclusion and data properties. 

3. germanNoMutex.m: German code for verifying s-deadlock freedom without
mutual exclusion or data properties. No non-interference lemmas needed
for this.

4. germanWithMutex.m: German code for verifying s-deadlock freedom
with mutual exclusion. Non-interference lemmas needed, more
constrained abstraction, and so faster run time.

5. germanBuggy.m: Injected bug in german protocol -- invack
dropped by agent. Leads to an s-deadlock bug.
