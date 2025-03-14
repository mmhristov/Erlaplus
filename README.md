<h1> <img src="logo_transparent.png" alt="Erla+ logo" style="height: 2em; display: block;
    margin: 0 auto;" /></h1>
Erla+ is a tool that translates models written in a subset of PlusCal into Erlang implementations.
Additionally, Erla+ provides new PlusCal primitives for actor-style modeling,
thus clearly separating the modeled system from its environment. 

To learn more about Erla+, you can dive into the research behind our work in our [paper](https://doi.org/10.1145/3677995.3678190), a copy of which can be found [here](./Documents/icfpws24erlangmain-p12-p-d11fcb0eab-94820-final.pdf).
If you prefer a video presentation, feel free to watch our [talk](https://www.youtube.com/watch?v=idQS5Fb-Kpg).

The project is based on the original [PlusCal translator](https://github.com/tlaplus/tlaplus).

### Motivation
Our goal is to automatically translate verified formal distributed system models written in a subset of the PlusCal
language into Erlang programs, which exhibit the formal
model’s behavior. To achieve this, we created a translator
called Erla+, which is built upon the original PlusCal translator, adding an Erlang translation functionality and extending the PlusCal language with additional PlusCal primitives
for actor-style modeling. This extension enables a clear separation between the modeled system and its environment.
It enables developers to express distributed algorithms close
to their implementation but on a higher level of abstraction.

### Usage
#### Compile:
``` shell
cd tlatools

ant -f customBuild.xml compile
ant -f customBuild.xml compile-test
ant -f customBuild.xml dist
```

#### Run:
``` shell
java -cp tlatools/dist/tla2tools.jar pcal.trans -erlang [-genMain] my_spec.tla
```

- Providing the optional ```-genMain``` parameter allows the compiler to generate a process initialization and start function,
ensuring that all processes are registered before system execution. This helps prevent errors where early-initialized processes attempt
to communicate with peers that have not yet been registered. 
It is generally recommended to enable this option unless the model's processes are independent and do not interact.

### Running the Generated Erlang Implementations:
To run a generated implementation, follow these steps:

1. **Compile the Implementation**
  - In the Erlang shell, compile the specification by running:
    ```erlang
    c(my_spec.erl).
    ```

2. **Compile Erla+ Library Files**
  - Compile all `erla_libs_*` library files, which can currently be found [here](tlatools/src/pcal/erla_libs/).

3. **Initialize and Start Processes**
  - If the `-genMain` parameter was provided to the Erla+ compiler:
    - Initialize all processes using the `_init_` function.
    - Start protocol execution with the `_run_` function.
  - Otherwise, manually start the processes by calling the appropriate main functions, which follow the `start_` prefix.

### Examples
In directory [Examples](./Examples/) you will find examples of models that we have successfully modeled and translated, including:
- **Raft**: A model of the Raft consensus algorithm based on the authors' [original TLA+ specification](https://github.com/ongardie/raft.tla). 
- **RaftKVS**: A Raft-based key-value store.
- **Semaphore protocol**:  A simple semaphore protocol where a central server manages a lock, while several clients can concurrently
  request to acquire and release the lock.

