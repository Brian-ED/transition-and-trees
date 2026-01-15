module BigAndSmallStepSemantics where

open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟; Γ₁; _⇒₁_; T₁_)
open import Data.Product using (∃; ∃₂) renaming (_×_ to _and_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

-- Section Start Page 31

record BigStepSemantics (TS : TransitionSystem) : Set₁ where
    constructor ⌈>
    open TransitionSystem TS
    field
        BigStepping : (x y : Γ) → x ⇒ y → T y

-- TODO: Complain to book maker that a SmallStepSemantic is a big step semantic too.
SmallStepSemantics = TransitionSystem

-- Section End Page 31
