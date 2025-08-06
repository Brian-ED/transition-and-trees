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

-- Section Start Page 32

-- 3.4.1 A big-step semanticcs of Aexp

open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟; False; True)
open import transition-and-trees.BigAndSmallStepSemantics using (BigStepSemantics)

AExpSemantic : TransitionSystem
AExpSemantic .TransitionSystem.Γ = Aexp
(AExpSemantic TransitionSystem.⇛ x) (N x₁) = True
(AExpSemantic TransitionSystem.⇛ x) (V x₁) = False
(AExpSemantic TransitionSystem.⇛ x) (y + y₁) = False
(AExpSemantic TransitionSystem.⇛ x) (y * y₁) = False
(AExpSemantic TransitionSystem.⇛ x) (y - y₁) = False
(AExpSemantic TransitionSystem.⇛ x) [ y ] = False
AExpSemantic .TransitionSystem.T (N x) = True
AExpSemantic .TransitionSystem.T (V x) = False
AExpSemantic .TransitionSystem.T (x + x₁) = False
AExpSemantic .TransitionSystem.T (x * x₁) = False
AExpSemantic .TransitionSystem.T (x - x₁) = False
AExpSemantic .TransitionSystem.T [ x ] = False

ProofOfBigStep : BigStepSemantics AExpSemantic  -- ∀ (x y : Γ) → (x ⇛ y) → (T y)
ProofOfBigStep .BigStepSemantics.BigStepping x (N y) z = True.unit

open import Data.Integer using () renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Nat using (ℕ) renaming (_*_ to _*ℕ_)

Transition : Aexp → Num
Transition (N x) = x
Transition (V x) = + 0
Transition (x + y) = (Transition x) +ℤ (Transition y)
Transition (x * y) = (Transition x) *ℤ (Transition y)
Transition (x - y) = (Transition x) -ℤ (Transition y)
Transition [ x ] = Transition x

-- Section End Page 32