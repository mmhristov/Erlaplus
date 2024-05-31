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