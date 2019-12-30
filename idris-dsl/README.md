Idris back end to compile to a R1CS system
------------------------------------------

Restricted use cases only at the moment

Installation
------------

to install the backend

```
git clone https://github.com/onai/idris-dsl.git
cd idris-dsl.git
cabal install
```

to run it on file `Example.idr` use


```
idris Example.idr --codegen R1CS-DSL -o Example.dsl
```
