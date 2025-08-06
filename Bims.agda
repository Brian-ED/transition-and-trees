module transition-and-trees.Bims where
open import Data.Integer using (+_) renaming (ℤ to Num)
open import Data.Integer.Literals
open import Data.String using () renaming (String to Var)


-- Section Start Page 29

data Aexp : Set where
    N_ : Num → Aexp
    V_ : Var → Aexp
    _+_ : Aexp → Aexp → Aexp
    _*_ : Aexp → Aexp → Aexp
    _-_ : Aexp → Aexp → Aexp
    [_] : Aexp → Aexp

data Bexp : Set where
    _==_ : Aexp → Aexp → Bexp
    _<_ : Aexp → Aexp → Bexp
    ¬_ : Bexp → Bexp
    _∧_ : Bexp → Bexp → Bexp
    ⟨_⟩ : Bexp → Bexp

data Stm : Set where
    skip : Stm
    _←_ : Var → Aexp → Stm
    _Å_ : Stm → Stm → Stm
    if_then_else_ : Bexp → Stm → Stm → Stm
    _while_ : Stm → Bexp → Stm

infixr 5 N_
infixr 5 V_

exprPg29 : Aexp
exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)

-- TODO: complain to book owner: Bims in the book doesn't define n like I've done. I don't understand what the syntactic catagory of 3 is, Aexp or Num or both?

-- Section End Page 29

-- Section Start Page 30

infixl 2 _Å_
infixr 3 _*_
infixr 4 _+_
infixr 4 _-_

_≠_ : Aexp → Aexp → Bexp
_≠_ a b = ¬ (a == b)

-- Section End Page 30

-- Section Start Page 32-33

-- 3.4.1 A big-step semanticcs of Aexp

open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟; False; True)
open import transition-and-trees.BigAndSmallStepSemantics using (BigStepSemantics)

open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Turn subtype in argument to sumtype
⭆⇛ : (Aexp → ℤ) → (ℤ ⊎ Aexp → ℤ ⊎ Aexp → Set)
⭆⇛ x (inj₁ x₁) (inj₁ z) = False
⭆⇛ x (inj₂ y) (inj₁ z) = True
⭆⇛ x y (inj₂ z) = False

T : (ℤ ⊎ Aexp → Set)
T (inj₁ x) = True
T (inj₂ y) = False

Transition : Aexp → Num
Transition (N x) = x
Transition (V x) = + 0
Transition (x + y) = (Transition x) +ℤ (Transition y)
Transition (x * y) = (Transition x) *ℤ (Transition y)
Transition (x - y) = (Transition x) -ℤ (Transition y)
Transition [ x ] = Transition x

AExpSemantic : TransitionSystem
AExpSemantic .TransitionSystem.Γ = ℤ ⊎ Aexp
AExpSemantic .TransitionSystem._⇛_ = ⭆⇛ Transition
AExpSemantic .TransitionSystem.T = T

ProofOfBigStep : BigStepSemantics AExpSemantic  -- ∀ (x y : Γ) → (x ⇛ y) → (T y)
ProofOfBigStep .BigStepSemantics.BigStepping x (inj₁ y) z = True.unit
ProofOfBigStep .BigStepSemantics.BigStepping (inj₁ x) (inj₂ y) ()
ProofOfBigStep .BigStepSemantics.BigStepping (inj₂ x) (inj₂ y) ()

-- Section End Page 32-33