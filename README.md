#  Proving the book Transition and Trees by Hans Hüttel in Agda
INCOMPLETE.
Progress is page 57 out of 267.

## Conventions
All files are camel-case (HereIsAnExample), except that the first character's case has meaning:
1. Uppercase: This file is a library file, meaning it can not import example files.
2. Lowercase: This file is an example file, meaning it can import anything and can be imported by other example files.

## Contribution
Feel free to contribute. I'm going through the book in order. To contribute, you can look for the latest page. Since page numbers are commented above and below (hopefully) all code, you can look for the biggest page number and prove/define the next thing that isn't proven/defined.

## Mistakes found in the book
Mistakes mentioned in the [errata](http://www.operationalsemantics.net/errata.pdf) (meaning the official corrections) won't be repeated here.

Author uses PLUS and SUB in tandom in the small-step transition rules for Aexp, when it should be ADD and SUB, or PLUS and MINUS. Found at Table 3.2.

Bexp on Table 3.4 defines the rule EQUALS-1BSS. Bexp on Table 4.2 defines EQUAL-1BSS. There is a leading S after EQUAL in one case, and not the other.

In Table 4.2, the rule PARENT-BBSS has 2 'B's, which could be intentional but I doubt it.

In page 31, under `3.3 Big-step vs small-step semantics`, it states that a small-step semantics's transition rule does not need to result in a terminal configuration, which is not a restriction. Therefore the set of semantics that are SmallStepSemantics is equal to the set of all transition systems.

Problem 4.9 uses `>`, which is not defined, only `<` is defined.

Lemma 4.12 assumes that the transition sequence `a⇒b⇒ᵏc` can be rewritten as `a⇒⟨S,s⟩⇒ᵏc`, which is a mistake, `b` can also be a state. Trivially fixed by proving this case.

Theorem 4.13 at the start of page 59 assumes that the transition sequence `a⇒b⇒ᵏc` can be rewritten as `a⇒⟨S,s⟩⇒ᵏc`, which is a mistake, `b` can also be a state. Trivially fixed by proving this case.

Lemma 4.14 has ⟨S₁;S₂⟩⇒ᵏs˝, which isn't a valid statement, state in left side is ommitted.

Lemma 4.14, sentence "k₂ = k₂₂". k₂₂ is never defined, only k₂₁, which I have assumed the author meant.

### Opinionated
The generic transition ⇒ᵏ in transition systems I believe would be simpler if instead of defining it using step 0 and step suc k, and defining ⇒* afterwards, you could just define ⇒* first. Every induction, instead of being reliant on an intiger, could just rely on the length of the transition sequence itself. The reason I believe this is simpler is that it avoids the duplicate information from k, since it's determined by the transition sequence anyways. Duplicate information is annoying when unifying things. It could be that I only believe this because Agda proves by construction, and needs unification a lot.
