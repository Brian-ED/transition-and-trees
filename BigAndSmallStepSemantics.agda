module BigAndSmallStepSemantics where

open import TransitionSystems using (TransitionSystem)
open import Level using (Level) renaming (suc to lsuc)

-- Section Start Page 31

record BigStepSemantics {ℓ : Level} (TS : TransitionSystem {ℓ}) : Set ℓ where
    constructor ⌈>
    open TransitionSystem TS
    field
        BigStepping : (x y : Γ) → x ⇒ y → T y

-- Section End Page 31
