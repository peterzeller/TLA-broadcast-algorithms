# TLA+ models

To ckeck the TLA+ models with the TLA toolbox.
When configuring the model you should disable deadlock checks, since the model will only check finite executions and then stop, which will be detected as a deadlock otherwise.

You need to configure the set of messages and the set of processes to use. For example:

    Process = {"p1", "p2"}
    Message = {"m1", "m2"}
