# PlusCal translator #

## Compile: ##

``` shell
ant -f customBuild.xml compile
ant -f customBuild.xml compile-test
ant -f customBuild.xml dist
```

## Run: ##

``` shell
java -cp dist/tla2tools.jar pcal.trans -erlang ../Examples/TLA/Test_Print.tla
``` 

[//]: # (## Long term to-dos: ##)

[//]: # ()
[//]: # (    1. Complete overhaul of network semantics: change primitives to resemble Erlang's semantics more closely;)

[//]: # (        change broadcast&#40;&#41; to send&#40;&#41; one message at a time, possibly failing.)

[//]: # ()
[//]: # ()
[//]: # (    2. Re-implement functions and records: functions should not be evaluated by Erla, )

[//]: # ()
[//]: # (        but in the Erlang implementation &#40;i.e. no hardcoded functions&#41;. )

[//]: # ()
[//]: # (        Records should levarage functions' implementation &#40;i.e. represented as functions over a domain of their keys&#41;. )

[//]: # ()
[//]: # (    )
[//]: # (    3. Complete set functionality: )

[//]: # ()
[//]: # (	    -> mapping: {x \in 1..4 : x * x })