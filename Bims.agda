module transition-and-trees.Bims where
open import Data.Integer using (+_) renaming (ℤ to Num)
open import Data.String using (toList) renaming (String to Var)
open import Data.Char.Base using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃; ∃₂; _,_; _×_)
open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import transition-and-trees.BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤) renaming (tt to ttt)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Nullary.Negation using () renaming (¬_ to not_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_; _<_ to _<ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- Section Start Page 29

data Aexp₁ : Set where
    N_ : Num → Aexp₁
    -- V_ : Var → Aexp₁ -- The book decides to not define variables yet
    _+_ : Aexp₁ → Aexp₁ → Aexp₁
    _*_ : Aexp₁ → Aexp₁ → Aexp₁
    _-_ : Aexp₁ → Aexp₁ → Aexp₁
    [_] : Aexp₁ → Aexp₁

data Bexp : Set where
    tt : Bexp
    ff : Bexp
    _==_ : Aexp₁ → Aexp₁ → Bexp
    _<_ : Aexp₁ → Aexp₁ → Bexp
    ¬_ : Bexp → Bexp
    _∧_ : Bexp → Bexp → Bexp
    ⟨_⟩ : Bexp → Bexp

data Stm : Set where
    skip : Stm
    _←_ : Var → Aexp₁ → Stm
    _Å_ : Stm → Stm → Stm
    ifStm_then_else : Bexp → Stm → Stm → Stm
    _while_ : Stm → Bexp → Stm

infixr 5 N_
infixr 5 ++_

-- Section End Page 29

-- Section Start Page 30

infixl 2 _Å_
infixr 3 _*_
infixr 4 _+_
infixr 4 _-_

open import Data.Bool using (Bool; true; false; if_then_else_) renaming (_∧_ to _∧B_; _∨_ to _∨B_)

-- Section End Page 30

-- Section Start Page 32-33
-- 3.4.1 A big-step semantics of Aexp₁

data _⇒₁_ : ℤ ⊎ Aexp₁ → ℤ ⊎ Aexp₁ → Set where
    _PLUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
               → inj₂ α₁ ⇒₁ inj₁ v₁  →  inj₂ α₂ ⇒₁ inj₁ v₂
               → inj₂ (α₁ + α₂) ⇒₁ inj₁ (v₁ +ℤ v₂)

    _MULT-BSS_ : ∀ {α₁ α₂ v₁ v₂}
               → inj₂ α₁ ⇒₁ inj₁ v₁  →  inj₂ α₂ ⇒₁ inj₁ v₂
               → inj₂ (α₁ * α₂) ⇒₁ inj₁ (v₁ *ℤ v₂)

    _MINUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                → inj₂ α₁ ⇒₁ inj₁ v₁  →  inj₂ α₂ ⇒₁ inj₁ v₂
                → inj₂ ( α₁ - α₂ ) ⇒₁ inj₁ (v₁ -ℤ v₂)

    PARENT-BSS_ : ∀ {α₁ v₁}
                → inj₂ α₁ ⇒₁ inj₁ v₁
                → inj₂ [ α₁ ] ⇒₁ inj₁ v₁

    NUM-BSS_ : ∀ {n}
             → inj₂ (N n) ⇒₁ inj₁ n


-- Section End Page 32-33

-- Section Start Page 36-37
-- A small-step semantics of Aexp₁

-- Need to redefine Aexp to support non-literals too...
-- "The presentation becomes a little easier if we can let values appear directly
-- in our intermediate results. We do this by extending the formation rules for
-- Aexp such that values become elements of Aexp"
data Aexp₂ : Set where
    N_ : Num → Aexp₂ -- Number literals
    ++_  : Num → Aexp₂ -- Parsed number
    -- V_ : Var → Aexp₂ -- The book decides to not define variables yet
    _+_ : Aexp₂ → Aexp₂ → Aexp₂
    _*_ : Aexp₂ → Aexp₂ → Aexp₂
    _-_ : Aexp₂ → Aexp₂ → Aexp₂
    [_] : Aexp₂ → Aexp₂

_or_ = _⊎_

infix 4 _⇒₂_

infixr 5 PLUS-1ₛₛₛ_
infixr 5 PLUS-2ₛₛₛ_
infixr 5 PLUS-3ₛₛₛ
infixr 5 MULT-1ₛₛₛ_
infixr 5 MULT-2ₛₛₛ_
infixr 5 MULT-3ₛₛₛ
infixr 5 SUB-1ₛₛₛ_
infixr 5 SUB-2ₛₛₛ_
infixr 5 SUB-3ₛₛₛ
infixr 5 PARENT-1ₛₛₛ_
infixr 5 NUMₛₛₛ_

infixr 5 _PLUS-BSS_
infixr 5 _MULT-BSS_
infixr 5 _MINUS-BSS_
infixr 5 PARENT-BSS_
infixr 5 NUM-BSS_

data _⇒₂_ : Aexp₂ → Aexp₂ → Set where

    -- PLUS
    PLUS-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
               → α₁ ⇒₂ α₁´
               → (α₁ + α₂) ⇒₂ (α₁´ + α₂)

    PLUS-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
               → α₂ ⇒₂ α₂´
               → (α₁ + α₂) ⇒₂ (α₁ + α₂´)

    PLUS-3ₛₛₛ : ∀ {x y}
              → (++ x + ++ y) ⇒₂ ++ x +ℤ y

    -- MULT
    MULT-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
               → α₁ ⇒₂ α₁´
               → (α₁ * α₂) ⇒₂ (α₁´ * α₂)

    MULT-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
               → α₂ ⇒₂ α₂´
               → (α₁ * α₂) ⇒₂ (α₁ * α₂´)

    MULT-3ₛₛₛ : ∀ {x y}
              → (++ x * ++ y) ⇒₂ ++ x *ℤ y

    -- SUB
    SUB-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
              → α₁ ⇒₂ α₁´
              → (α₁ - α₂) ⇒₂ (α₁´ - α₂)

    SUB-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
              → α₂ ⇒₂ α₂´
              → (α₁ - α₂) ⇒₂ (α₁ - α₂´)

    SUB-3ₛₛₛ : ∀ {x y}
             → (++ x - ++ y) ⇒₂ ++ x -ℤ y

    -- PARENTHESES
    PARENT-1ₛₛₛ_ : ∀ {x y}
                 → x ⇒₂ y
                 → [ x ] ⇒₂ [ y ]

    PARENT-2ₛₛₛ_ : ∀ {x y}
                 → x ≡ y
                 → [ ++ x ] ⇒₂ ++ y

    -- NUM
    NUMₛₛₛ_ : ∀ {x y}
            → x ≡ y
            → N x ⇒₂ ++ y

-- Section End Page 36-37

-- Section Begin Page 40

data _⇒b_ : (Bool ⊎ Bexp) → (Bool ⊎ Bexp) → Set where

    _EQUALS-1-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₂ α₁ ⇒₁ inj₁ v₁  → inj₂ α₂ ⇒₁ inj₁ v₂
                   → v₁ ≡ v₂
                   → inj₂ (α₁ == α₂) ⇒b inj₁ true

    _EQUALS-2-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₂ α₁ ⇒₁ inj₁ v₁  → inj₂ α₂ ⇒₁ inj₁ v₂
                   → not (v₁ ≡ v₂)
                   → inj₂ (α₁ == α₂) ⇒b inj₁ false

    _GREATERTHAN-1-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                         → inj₂ α₁ ⇒₁ inj₁ v₁  → inj₂ α₂ ⇒₁ inj₁ v₂
                         → v₁ <ℤ v₂
                         → inj₂ (α₁ < α₂) ⇒b inj₁ false

    _GREATERTHAN-2-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                         → inj₂ α₁ ⇒₁ inj₁ v₁  → inj₂ α₂ ⇒₁ inj₁ v₂
                         → not (v₁ <ℤ v₂)
                         → inj₂ (α₁ < α₂) ⇒b inj₁ false

    NOT-1-BSS_ : ∀ {b}
               → inj₂ b ⇒b inj₁ false
               → inj₂ (¬ b) ⇒b inj₁ true

    NOT-2-BSS_ : ∀ {b}
               → inj₂ b ⇒b inj₁ true
               → inj₂ (¬ b) ⇒b inj₁ false

    PARENTH-B-BSS : ∀ {b v}
               → inj₂ b ⇒b v
               → inj₂ ⟨ b ⟩ ⇒b v

    AND-1-BSS : ∀ {b₁ b₂}
              → inj₂ b₁ ⇒b inj₁ true
              → inj₂ b₂ ⇒b inj₁ true
              → inj₂ (b₁ ∧ b₂) ⇒b inj₁ true

    AND-2-BSS : ∀ {b₁ b₂}
              → (inj₂ b₁ ⇒b inj₁ false)
              ⊎ (inj₂ b₂ ⇒b inj₁ false)
              → inj₂ (b₁ ∧ b₂) ⇒b inj₁ false

-- Section End Page 40

-- Section Start Page 44-45

open import transition-and-trees.State using (State; _[_↦_]; lookup; emptyState)

data Aexp₃ : Set where
    N_ : Num → Aexp₃ -- Number literals
    ++_  : Num → Aexp₃ -- Parsed number
    V_ : Var → Aexp₃
    _+_ : Aexp₃ → Aexp₃ → Aexp₃
    _*_ : Aexp₃ → Aexp₃ → Aexp₃
    _-_ : Aexp₃ → Aexp₃ → Aexp₃
    [_] : Aexp₃ → Aexp₃


data _⊢_⇒₃_ : State → ℤ ⊎ Aexp₃ → ℤ ⊎ Aexp₃ → Set where
    _PLUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
               → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
               → s ⊢ inj₂ (α₁ + α₂) ⇒₃ inj₁ (v₁ +ℤ v₂)

    _MULT-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
               → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
               → s ⊢ inj₂ (α₁ * α₂) ⇒₃ inj₁ (v₁ *ℤ v₂)

    _MINUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                → s ⊢ inj₂ ( α₁ - α₂ ) ⇒₃ inj₁ (v₁ -ℤ v₂)

    PARENT-BSS_ : ∀ {s α₁ v₁}
                → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                → s ⊢ inj₂ [ α₁ ] ⇒₃ inj₁ v₁

    NUM-BSS : ∀ {s n}
            → s ⊢ inj₂ (N n) ⇒₃ inj₁ n

    Var-BSS_ : ∀ {s x v}
             → (lookup x s) ≡ just v
             → s ⊢ inj₂ (V x) ⇒₃ inj₁ v

-- The book states this transition system is a big-step-semantic, though does not prove it.
-- To make it easier to prove for myself, I have assumed you start out with no state on a given program.

T₃ : (ℤ ⊎ Aexp₃ → Set)
T₃ (inj₁ x) = ⊤
T₃ (inj₂ x) = ⊥

Aexp₃Semantic : TransitionSystem
Aexp₃Semantic = ⌞ (ℤ ⊎ Aexp₃) , (_⊢_⇒₃_ emptyState) , T₃ ⌟

Aexp₃-is-big-step-proof : ∀ x y → emptyState ⊢ x ⇒₃ y → T₃ y
Aexp₃-is-big-step-proof (inj₁ x) (inj₁ x₁) = λ _ → ttt
Aexp₃-is-big-step-proof (inj₁ x) (inj₂ y) ()
Aexp₃-is-big-step-proof (inj₂ y₁) (inj₁ x) = λ _ → ttt
Aexp₃-is-big-step-proof (inj₂ y₁) (inj₂ y) ()
Aexp₃big-semantic : BigStepSemantics Aexp₃Semantic
Aexp₃big-semantic = ⌈> Aexp₃-is-big-step-proof


--    EQUAL-1-BSS_       : ∀ (s α₁ α₂ v₁ v₂) → (s ⊢ ink₂ α₁ ⇒₃b inj₁ v₁ ) → (s ⊢ ink₂ α₂ ⇒₃b inj₁ v₂ ) →     (v₁ ≡ v₂) → s ⊢ α₁ ⇒₃b α₂
--    EQUAL-2-BSS_       : ∀ (s α₁ α₂ v₁ v₂) → (s ⊢ ink₂ α₁ ⇒₃b inj₁ v₁ ) → (s ⊢ ink₂ α₂ ⇒₃b inj₁ v₂ ) → not (v₁ ≡ v₂) → s ⊢ α₁ ⇒₃b α₂
--    GREATERTHAN-1-BSS_ : ∀ (s α₁ α₂ v₁ v₂) → (s ⊢ ink₂ α₁ ⇒₃b inj₁ v₁ ) → (s ⊢ ink₂ α₂ ⇒₃b inj₁ v₂ ) → 
--    GREATERTHAN-2-BSS_ : ∀ (s α₁ α₂ v₁ v₂) → (s ⊢ ink₂ α₁ ⇒₃b inj₁ v₁ ) → (s ⊢ ink₂ α₂ ⇒₃b inj₁ v₂ ) → 
--    NOT-1-BSS_         : ∀ (s α₁ α₂ v₁ v₂) → ()
--    NOT-2-BSS_         : ∀ (s α₁ α₂ v₁ v₂) → ()
--    PARENT-B-BSS_      : ∀ (s α₁ α₂ v₁ v₂) → ()
--    AND-1-BSS_         : ∀ (s α₁ α₂ v₁ v₂) → ()
--    AND-2-BSS_         : ∀ (s α₁ α₂ v₁ v₂) → ()

-- Section End Page 44-45

-- Section Begin Page 46

data Bexp₃ : Set where
    tt₃ : Bexp₃
    ff₃ : Bexp₃
    _==₃_ : Aexp₃ → Aexp₃ → Bexp₃
    _<₃_ : Aexp₃ → Aexp₃ → Bexp₃
    ¬₃_ : Bexp₃ → Bexp₃
    _∧₃_ : Bexp₃ → Bexp₃ → Bexp₃
    ⟨_⟩₃ : Bexp₃ → Bexp₃

data _⊢_⇒₃b_ : State → Bool ⊎ Bexp₃ → Bool ⊎ Bexp₃ → Set where

    _EQUAL-1-BSS_ : ∀ {s α₁ α₂ v}
                   → s ⊢ inj₂ α₁ ⇒₃ inj₁ v  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v
                   → s ⊢ (inj₂ (α₁ ==₃ α₂)) ⇒₃b inj₁ true

    EQUALS-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                   → not (v₁ ≡ v₂)
                   → s ⊢ inj₂ (α₁ ==₃ α₂) ⇒₃b inj₁ false

    _GREATERTHAN-1-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                         → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                         → v₁ <ℤ v₂
                         → s ⊢ inj₂ (α₁ <₃ α₂) ⇒₃b inj₁ false

    _GREATERTHAN-2-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                         → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁  →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                         → not (v₁ <ℤ v₂)
                         → s ⊢ inj₂ (α₁ <₃ α₂) ⇒₃b inj₁ false

    NOT-1-BSS_ : ∀ {s b}
               → s ⊢ inj₂ b ⇒₃b inj₁ false
               → s ⊢ inj₂ (¬₃ b) ⇒₃b inj₁ true

    NOT-2-BSS_ : ∀ {s b}
               → s ⊢ inj₂ b ⇒₃b inj₁ true
               → s ⊢ inj₂ (¬₃ b) ⇒₃b inj₁ false

    PARENTH-B-BSS : ∀ {s b v}
               → s ⊢ inj₂ b ⇒₃b v
               → s ⊢ inj₂ ⟨ b ⟩₃ ⇒₃b v

    AND-1-BSS : ∀ {s b₁ b₂}
              → s ⊢ inj₂ b₁ ⇒₃b inj₁ true
              → s ⊢ inj₂ b₂ ⇒₃b inj₁ true
              → s ⊢ inj₂ (b₁ ∧₃ b₂) ⇒₃b inj₁ true

    AND-2-BSS : ∀ {s b₁ b₂}
              → (s ⊢ inj₂ b₁ ⇒₃b inj₁ false)
             or (s ⊢ inj₂ b₂ ⇒₃b inj₁ false)
              → s ⊢ inj₂ (b₁ ∧₃ b₂) ⇒₃b inj₁ false

-- Section End Page 46

-- Section Begin Page 47

data Stm₃ : Set where
    skip₃ : Stm₃
    _←₃_ : Var → Aexp₃ → Stm₃
    _Å₃_ : Stm₃ → Stm₃ → Stm₃
    ifStm₃_then_else : Bexp₃ → Stm₃ → Stm₃ → Stm₃
    while_do₃_ : Bexp₃ → Stm₃ → Stm₃

data ⟨_,_⟩⇒₃_ : Stm₃ → State → State → Set where
    ASS-BSS         : ∀ {x a s v}
                    → s ⊢ inj₂ a ⇒₃ inj₁ v
                    → ⟨ (x ←₃ a) , s ⟩⇒₃ (s [ x ↦ v ])

    SKIP-BSS        : ∀ {s}
                    → ⟨ skip₃ , s ⟩⇒₃ s

    COMP-BSS        : ∀ {S₁ S₂ s s´ s˝}
                    → ⟨ S₁ , s ⟩⇒₃ s˝  →  ⟨ S₂ , s˝ ⟩⇒₃ s´
                    → ⟨ (S₁ Å₃ S₂) , s ⟩⇒₃ s´

    IF-TRUE-BSS     : ∀ {S₁ S₂ s s´ b}
                    → ⟨ S₁ , s ⟩⇒₃ s´  →  s ⊢ inj₂ b ⇒₃b inj₁ true
                    → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₃ s´

    IF-FALSE-BSS    : ∀ {S₁ S₂ s s´ b}
                    → ⟨ S₂ , s ⟩⇒₃ s´  →  s ⊢ inj₂ b ⇒₃b inj₁ false
                    → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₃ s´

    WHILE-TRUE-BSS  : ∀ {S s s´ s˝ b}
                    → s ⊢ inj₂ b ⇒₃b inj₁ true
                    → ⟨ S , s ⟩⇒₃ s˝  →  ⟨ (while b do₃ S) , s˝ ⟩⇒₃ s´
                    → ⟨ (while b do₃ S) , s ⟩⇒₃ s´

    WHILE-FALSE-BSS : ∀ {S s s´ b}
                    → s ⊢ inj₂ b ⇒₃b inj₁ false
                    → s´ ≡ s
                    → ⟨ (while b do₃ S) , s ⟩⇒₃ s´

-- Section End Page 47


-- Section Begin Page 48-49


S2 = ("i" ←₃ (N + 6)) Å₃ (while ¬₃ ((V "i") ==₃ (N + 0)) do₃ (("x" ←₃ (V "x" + V "i")) Å₃ ("i" ←₃ ((V "i") - (N + 2)))))
s2 = emptyState [ "x" ↦ + 5 ]
r2 = (emptyState [ "x" ↦ + 17 ]) [ "i" ↦ + 0 ]
P2 : ⟨ S2 , s2 ⟩⇒₃ r2
P2 = COMP-BSS
    (ASS-BSS NUM-BSS)
    (WHILE-TRUE-BSS
        (NOT-1-BSS EQUALS-2-BSS (Var-BSS refl) NUM-BSS λ())
        (COMP-BSS (ASS-BSS ((Var-BSS refl) PLUS-BSS (Var-BSS refl))) (ASS-BSS ((Var-BSS refl) MINUS-BSS NUM-BSS)))
        (WHILE-TRUE-BSS
            (NOT-1-BSS EQUALS-2-BSS (Var-BSS refl) NUM-BSS λ())
            (COMP-BSS (ASS-BSS ((Var-BSS refl) PLUS-BSS (Var-BSS refl))) (ASS-BSS ((Var-BSS refl) MINUS-BSS NUM-BSS)))
            (WHILE-TRUE-BSS
                (NOT-1-BSS EQUALS-2-BSS (Var-BSS refl) NUM-BSS λ())
                (COMP-BSS (ASS-BSS ((Var-BSS refl) PLUS-BSS (Var-BSS refl))) (ASS-BSS ((Var-BSS refl) MINUS-BSS NUM-BSS)))
                (WHILE-FALSE-BSS (NOT-2-BSS ((Var-BSS refl) EQUAL-1-BSS NUM-BSS)) refl)
            )
        )
    )

-- Section End Page 48-49
