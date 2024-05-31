# Semaphore Protocol #
This is a simple semaphore protocol, inspired by the [locksvc spec by PGo](https://github.com/DistCompiler/pgo/blob/main/systems/locksvc/locksvc.tla) [1] where a central server manages
a lock, while several clients can concurrently request to acquire and release
the lock. 

This directory includes the specification, a configuration file for the TLC model-checker, and the generated Erlang translation.

### Generated Implementation ###
The file was generated using the arguments ```-erlang -genMain```.
To execute the generated implementation:
1. Compile the implementation (e.g. by executing ```c(locksvc.erl).``` in the Erlang shell).
2. Compile all erla_libs_* library files (currently found [here](../../tlatools/src/pcal/erla_libs/)).
3. Initialize all processes via the _init_ function.
4. Finally, execute the protocol via the _run_ function.

### References ###
[1] Hackett, Finn, et al. "Compiling distributed system models with PGo." Proceedings of the 28th ACM International Conference on Architectural Support for Programming Languages and Operating Systems, Volume 2. 2023.