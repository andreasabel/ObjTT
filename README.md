# Type checker prototype for objective type theory (ObjTT)

Build requirements:
- BNFC
- Stack

Build instruction:
```
bnfc -d -m ObjTT.cf
stack build
```

Test:
```
stack run -- test/ex1.ott
```
