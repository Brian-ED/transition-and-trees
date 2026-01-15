module bims where

-- Section Start Page 29
module Aexp₁-example-expr where
    open import Data.Integer using (+_)
    open import Bims
    open Aexp₁-bigstep-semantic using (Aexp₁; _+_; N_; _*_)

    exprPg29 : Aexp₁
    exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)
-- Section End Page 29

-- Section Start Page 32-33
-- 3.4.1 A big-step semantics of Aexp₁
module Aexp₁-is-big-step where
    open import Bims
    open Aexp₁-bigstep-semantic
    open import Data.Integer using () renaming (ℤ to Num)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)

    -- The book doesn't define Transition on Nums. I assume there is no transition, so the extension is simply False
    -- Turn subtype in argument to sumtype
    ⭆⇒ : (Aexp₁ → Num) → (Num ⊎ Aexp₁ → Num ⊎ Aexp₁ → Set)
    ⭆⇒ x (inj₁ x₁) (inj₁ z) = ⊥
    ⭆⇒ x (inj₂ y) (inj₁ z) = ⊤
    ⭆⇒ x y (inj₂ z) = ⊥

    T₁ : (Num ⊎ Aexp₁ → Set)
    T₁ (inj₁ x) = ⊤
    T₁ (inj₂ x) = ⊥

    Aexp₁Semantic : TransitionSystem
    Aexp₁Semantic = ⌞ (Num ⊎ Aexp₁) , _⇒₁_ , T₁ ⌟

    Aexp₁-is-big-step : Set
    Aexp₁-is-big-step = (x y : (Num ⊎ Aexp₁)) → (x ⇒₁ y) → (T₁ y)
    Aexp₁-is-big-step-proof : Aexp₁-is-big-step
    Aexp₁-is-big-step-proof (inj₁ x) (inj₁ y) = λ z → ttt
    Aexp₁-is-big-step-proof (inj₂ x) (inj₁ y) = λ z → ttt
    Aexp₁-is-big-step-proof x (inj₂ y) ()

    Aexp₁big-semantic : BigStepSemantics Aexp₁Semantic
    Aexp₁big-semantic = ⌈> Aexp₁-is-big-step-proof

-- Section End Page 32-33


-- Section Start Page 36-37
-- A small-step semantics of Aexp₁
module Aexp₂-small-step-semantic where
    open import Bims
    open Aexp₁-smallstep-semantic
    open import Data.Unit using (⊤)
    open import Data.Empty using (⊥)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)

    T₂ : (Aexp₂ → Set)
    T₂ (++ x) = ⊤
    T₂ _ = ⊥

    Aexp₂Semantic : TransitionSystem
    Aexp₂Semantic = ⌞ Aexp₂ , _⇒₂_ , T₂ ⌟

-- Section End Page 36-37

-- Section Begin Page 40

-- Test for solution to problem 3.16, small-step transition for Bexp
module Bexp-small-step-example where
    open import Data.Integer using (+_)
    open import Agda.Builtin.Equality using (refl)
    open import Bims
    open Bexp-smallstep-transition
    open Aexp₁-smallstep-semantic using (ff; tt; N_; _*_; _+_; _∧_; _==_; ++_)

    code1 = ((ff ∧ tt ) ∧ ((N + 6) == (N + 5)))
    code2 = ff ∧ ((N + 6) == (N + 5))
    code3 = ff ∧ ((++ + 6) == (N + 5))
    code4 = ff ∧ ((++ + 6) == (++ + 5))
    code5 = ff ∧ ff
    code6 = ff

    a : code1 ⇒b code2
    a = AND-1-BSS AND-4-BSS
    b : code2 ⇒b code3
    b = AND-2-BSS (EQUALS-1-BSS (Aexp₁-smallstep-semantic.NUMₛₛₛ refl))
    c : code3 ⇒b code4
    c = AND-2-BSS (EQUALS-2-BSS (Aexp₁-smallstep-semantic.NUMₛₛₛ refl))
    d : code4 ⇒b code5
    d = AND-2-BSS (EQUALS-4-BSS (λ ()))
    e : code5 ⇒b code6
    e = AND-5-BSS

-- Section End Page 40

-- Section Begin Page 48-49
module Aexp₃-state-transition-example where
    open import State using (State; _[_↦_]; emptyState)
    open import Relation.Binary.PropositionalEquality using (refl)
    open import Bims
    open Aexp₃-semantic
    open import Data.Integer using (+_)

    code = ("i" ←₃ (N + 6)) Å₃
        (while ¬₃ ((V "i") ==₃ (N + 0)) do₃ (
            ("x" ←₃ (V "x" + V "i")) Å₃
            ("i" ←₃ (V "i" - N + 2))
        ))

    beginState = emptyState [ "x" ↦ + 5 ]
    endState = (emptyState [ "x" ↦ + 17 ]) [ "i" ↦ + 0 ]
    P2 : ⟨ code , beginState ⟩⇒₃ endState
    P2 = COMP-BSS
        (ASS-BSS NUM-BSS)
        (WHILE-TRUE-BSS
            (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
            (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
            (WHILE-TRUE-BSS
                (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
                (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
                (WHILE-TRUE-BSS
                    (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
                    (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
                    (WHILE-FALSE-BSS (NOT-2-BSS ((VAR-BSS refl) EQUAL-1-BSS NUM-BSS)) refl)
                )
            )
        )

-- Section End Page 48-49
