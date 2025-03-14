# Semaphore Protocol
This is a Raft-based key value store, extending upon our [Raft model](../Raft).
This directory includes the specification, a configuration file for the TLC model-checker, and the generated Erlang translation.

### Generated Implementation
The file was generated using the arguments ```-erlang -genMain```.
To execute the generated implementation:
1. Compile the implementation (e.g. by executing ```c(locksvc.erl).``` in the Erlang shell).
2. Compile all erla_libs_* library files (currently found [here](../../tlatools/src/pcal/erla_libs/)).
3. Initialize all processes via the _init_ function.
4. Finally, execute the protocol via the _run_ function.

To change the number of nodes in the Raft cluster, you can either modify the corresponding constant in the PlusCal model
and recompile to generate a new implementation or adjust the constant directly in the Erlang code itself
and modify the process initialization code to fit your needs.