![Erlaplus Logo](logo.png)
# Erla+

Erla+ is a tool that translates PlusCal specifications into Erlang implementations.
An extension of PlusCal for actor-based modeling,
which includes new primitives for message-passing
and error simulation    

The project is based on the original [PlusCal translator](https://github.com/tlaplus/tlaplus).
### Goal
Our goal is to automatically translate verified formal distributed system models written in a subset of the PlusCal
language into Erlang programs, which exhibit the formal
model’s behavior. To achieve this, we created a translator
called Erla+, which is built upon the original PlusCal translator, adding an Erlang translation functionality and extending the PlusCal language with additional PlusCal primitives
for actor-style modeling. This extension enables a clear separation between the modeled system and its environment.
It enables developers to express distributed algorithms close
to their implementation but on a higher level of abstraction

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
java -cp tlatools/dist/tla2tools.jar pcal.trans -erlang my_spec.tla
```

Refer to directory [Examples](./Examples/) for examples on how to execute the generated Erlang implementations.