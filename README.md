#  Proving the book Transition and Trees by Hans Hüttel in Agda
INCOMPLETE.
Progress is page 49 out of 267.

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

In page 31, under `3.3 Big-step vs small-step semantics`, it states that a small-step semantics's transition rule does not need to result in a terminal configuration, which is not a restriction. Therefore the set of semantics that are SmallStepSemantics is equal to the set of all transition systems.
