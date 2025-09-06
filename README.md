#  Proving the book Transition and Trees by Hans Hüttel in Agda
INCOMPLETE.
Progress is page 47 out of 267.

This repository assumes you have a agda-lib.agda-lib file on the directory which contains this repository.
This is the contents:
```
name: agda-lib
depend: standard-library
include: .
```

## Conventions
All files are camel-case (HereIsAnExample), except that the first character's case has meaning:
1. Uppercase: This file is a library file, meaning it can not import example files.
2. Lowercase: This file is an example file, meaning it can import anything and can be imported by other example files.

## TODO
1. Split Bims code into big-step semantics and small step semantics.

## Mistakes found in the book
Author uses PLUS and SUB in tandom in the small-step transition rules for Aexp, when it should be ADD and SUB, or PLUS and MINUS. Found at Table 3.2.

Bexp on Table 3.4 defines the rule EQUALS-1BSS. Bexp on Table 4.2 defines EQUAL-1BSS. There is a leading S after EQUAL in one case, and not the other.

In Table 4.2, the rule PARENT-BBSS has 2 'B's, which could be intentional but I doubt it.
