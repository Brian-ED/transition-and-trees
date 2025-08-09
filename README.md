#  Proving the book Transition and Trees by Hans Hüttel in Agda
INCOMPLETE.
Progress is page 32 out of 267.

This repository assumes you have a agda-lib.agda-lib file on the directory which contains this repository.
This is the contents:
```
name: agda-lib
depend: standard-library
include: .
```

## Conventions
All files are camel-case (HereIsAnExample), except that the first character's case has meaning:
1. Uppercase: This file is a library file, intented to be imported.
2. Lowercase: This file is an examples file, not intended to be imported.

## TODO
1. Split Bims code into big-step semantics and small step semantics.

## Mistakes found in the book
Author uses PLUS and SUB in tandom in the small-step transition rules for Aexp, when it should be ADD and SUB, or PLUS and MINUS. Found at Table 3.2.
