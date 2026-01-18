module BigAndSmallStepSemantics where

open import TransitionSystems using (TransitionSystem)

-- Section Start Page 31

record BigStepSemantics (TS : TransitionSystem) : Set₁ where
    constructor ⌈>
    open TransitionSystem TS
    field
        BigStepping : (x y : Γ) → x ⇒ y → T y

-- TODO: Complain to book maker that a SmallStepSemantic is a big step semantic too.

-- Section End Page 31
