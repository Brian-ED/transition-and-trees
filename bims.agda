module bims where

-- Section Start Page 29
module Aexp₁-example-expr where
    open import Data.Integer using (+_)
    import Bims
    open Bims.Aexp₁-bigstep-semantic using (Aexp₁; _+_; N_; _*_)

    exprPg29 : Aexp₁
    exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)
-- Section End Page 29

-- Section Start Page 32-33
-- 3.4.1 A big-step semantics of Aexp₁
module Aexp₁-is-big-step where
    import Bims
    open Bims.Aexp₁-bigstep-semantic
    open import Data.Integer using () renaming (ℤ to Num)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)

    Γ₁ = Aexp₁ ⊎ Num

    T₁ : (Aexp₁ ⊎ Num → Set)
    T₁ (inj₁ x) = ⊥
    T₁ (inj₂ x) = ⊤

    Aexp₁Semantic : TransitionSystem
    Aexp₁Semantic = ⌞ Γ₁ , _⇒₁_ , T₁ ⌟

    Aexp₁-is-big-step : Set
    Aexp₁-is-big-step = (x y : Γ₁) → (x ⇒₁ y) → (T₁ y)
    Aexp₁-is-big-step-proof : Aexp₁-is-big-step
    Aexp₁-is-big-step-proof (inj₂ x) (inj₂ y) = λ z → ttt
    Aexp₁-is-big-step-proof (inj₁ x) (inj₂ y) = λ z → ttt
    Aexp₁-is-big-step-proof x (inj₁ y) ()

    Aexp₁big-semantic : BigStepSemantics Aexp₁Semantic
    Aexp₁big-semantic = ⌈> Aexp₁-is-big-step-proof

-- Section End Page 32-33


-- Section Start Page 36-37
-- A small-step semantics of Aexp₁
module Aexp₁-small-step-semantic where
    open import Bims
    open Aexp₁-smallstep-semantic
    open import Data.Unit using (⊤)
    open import Data.Empty using (⊥)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Integer using () renaming (ℤ to Num)

    Aexp₁ssSemantic : TransitionSystem
    Aexp₁ssSemantic = ⌞ Aexp₁ss ⊎ Num , _⇒₂_ , T₁ ⌟
        where
            Γ₁ = Aexp₁ss ⊎ Num
            T₁ : Γ₁ → Set
            T₁ (inj₂ x) = ⊤
            T₁ (inj₁ x) = ⊥

-- Section End Page 36-37

-- Section Begin Page 40
-- Test for solution to problem 3.16, small-step transition for Bexp
module Bexp-small-step-example where
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Bexp-smallstep-transition
    open Bims.Aexp₁-smallstep-semantic using (Aexp₁ss; Bexp; N_; _*_; _+_; NUMₛₛₛ_; _∧_; _==_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff; _∧_ to _∧b_)
    open import Data.Integer using (+_) renaming (ℤ to Num)
    open import Data.Nat using (ℕ)

    infixl 40 _ₙ==_
    _ₙ==_ : ℕ → ℕ → Bexp ⊎ Bool
    x ₙ== y = inj₁ ((inj₂ (+ x)) == (inj₂ (+ y)))

    infixl 40 _ₛ==_
    _ₛ==_ : ℕ → ℕ → Bexp ⊎ Bool
    x ₛ== y = inj₁ ((inj₁ (N (+ x))) == (inj₁ (N (+ y))))

    infixl 39 _ₛ∧_
    _ₛ∧_ : Bexp ⊎ Bool → Bexp ⊎ Bool → Bexp ⊎ Bool
    x ₛ∧ y = inj₁ (x ∧ y)

    ᵥtt : Bexp ⊎ Bool
    ᵥtt = inj₂ tt
    ᵥff : Bexp ⊎ Bool
    ᵥff = inj₂ ff

    code1 = 0 ₙ== 1 ₛ∧ 0 ₙ== 0 ₛ∧ 6 ₛ== 5
    code2 = ᵥff     ₛ∧ 0 ₙ== 0 ₛ∧ 6 ₛ== 5
    code3 = ᵥff     ₛ∧ ᵥtt     ₛ∧ 6 ₛ== 5
    code4 = ᵥff     ₛ∧ ᵥtt     ₛ∧ inj₁ (inj₁ (N + 6) == inj₂ (+ 5))
    code5 = ᵥff     ₛ∧ ᵥtt     ₛ∧ 6 ₙ== 5
    code6 = ᵥff     ₛ∧ ᵥtt     ₛ∧ ᵥff
    code7 = ᵥff

    a : code1 ⇒b code2
    a = AND-1-BSS (AND-1-BSS (EQUALS-4-BSS λ ()))
    b : code2 ⇒b code3
    b = AND-1-BSS (AND-2-BSS (EQUALS-3-BSS refl))
    c : code3 ⇒b code4
    c = AND-2-BSS (EQUALS-2-BSS (NUMₛₛₛ refl))
    d : code4 ⇒b code5
    d = AND-2-BSS (EQUALS-1-BSS (NUMₛₛₛ refl))
    e : code5 ⇒b code6
    e = AND-2-BSS (EQUALS-4-BSS (λ ()))
    g : code6 ⇒b code7
    g = AND-5-BSS refl

-- Section End Page 40

-- Section Begin Page 48-52
module Aexp₂-state-transition-example where
    open import State using (State; _[_↦_]; emptyState)
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic
    open import Data.Nat using (ℕ)
    open import Data.Integer using (+_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    code = ("i" ←₃ (inj₁ (N + 6))) Å₃
        (while inj₁(¬₃ inj₁((inj₁(V "i")) ==₃ (inj₁ (N + 0)))) do₃ (
            ("x" ←₃ inj₁(inj₁(V "x") + (inj₁(V "i")))) Å₃
            ("i" ←₃ inj₁(inj₁(V "i") - inj₁(N + 2)))
        ))

    beginState = emptyState [ "x" ↦ + 5 ]
    endState = (emptyState [ "x" ↦ + 17 ]) [ "i" ↦ + 0 ]
    P2 : ⟨ code , beginState ⟩⇒₂ endState
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

    -- Section Begin Page 52
    -- Problem 4.8
    open import Data.Product using (∃; _,_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Empty using (⊥)

    S = while inj₁(inj₁(N + 0) ==₃ inj₁(N + 0)) do₃ skip₃

    neverTerminates : ∀ s → ∃ λ s´ → not ⟨ S , s ⟩⇒₂ s´
    neverTerminates s = emptyState , f
        where
            f : {s : State} → ⟨ S , s ⟩⇒₂ emptyState → ⊥
            f (WHILE-TRUE-BSS _ _ x₂) = f x₂
            f (WHILE-FALSE-BSS (EQUALS-2-BSS NUM-BSS NUM-BSS x₃) x₁) = x₃ refl

    -- Section End Page 52

-- Section End Page 48-52

-- Section Begin Page 54
-- Problem 4.9

module Aexp₂-smallstep-example where
    open import State using (State; _[_↦_]; emptyState)
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic
    import TransitionSystems as TS
    open import Data.Nat using (ℕ; z≤n) renaming (s≤s to s≤s_)
    open import Data.Integer using (+_) renaming (+<+ to +<+_)
    open import Data.String using (String)
    open import Data.Product using (_×_; _,_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    S =
        ifStm₂
            inj₁(inj₁(N + 3) <₃ inj₁(V "x"))
        then
            (
                ("x" ←₃ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₃
                ("y" ←₃ inj₁(N + 4))
            )
        else skip₃
    s = emptyState [ "x" ↦ + 4 ]

    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

    open TS.TransitionSystem ⟨_⟩⇒₂⟨_⟩-transition using (_⇒⟨_⟩_)
    open TS.TransitionSystem using (_⇒∘⇒_; x⇒x)
    open import Data.Bool using (true)

    -- Problem 4.9
    -- There's only one transition from the starte state
    transition1 :
        inj₁ (S , s )
        ⇒⟨ 1 ⟩
        inj₁ ((
            ("x" ←₃ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₃
            ("y" ←₃ inj₁(N + 4))
        ) , s)
    transition1 = IF-TRUEₛₛₛ (GREATERTHAN-1-BSS NUM-BSS (VAR-BSS refl) (+<+ s≤s s≤s s≤s s≤s z≤n)) ⇒∘⇒ x⇒x

    -- There's only one transition from the start state
    f : s ⊢ inj₁ (inj₁ (N + 3) + inj₁ (V "x")) ⇒ₐ inj₂ (+ 7)
    f = NUM-BSS PLUS-BSS (VAR-BSS refl)
    transition2 :
        inj₁ (
            ("x" ←₃ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₃
            ("y" ←₃ inj₁(N + 4))
            , s
        )
        ⇒⟨ 1 ⟩
        inj₁ (
            ("y" ←₃ inj₁(N + 4))
            , (s [ "x" ↦ + 7 ])
        )
    transition2 = COMP-2ₛₛₛ (ASSₛₛₛ (NUM-BSS PLUS-BSS (VAR-BSS refl))) ⇒∘⇒ x⇒x --step-suc outExpr , (COMP-2ₛₛₛ (ASSₛₛₛ f) , x⇒x)

    transition3 :
        inj₁ (
            ("y" ←₃ inj₁(N + 4))
            , (s [ "x" ↦ + 7 ])
        )
        ⇒⟨ 1 ⟩
        inj₂ (
            s [ "x" ↦ + 7 ] [ "y" ↦ + 4 ]
        )
    transition3 = ASSₛₛₛ NUM-BSS ⇒∘⇒ x⇒x

-- Section End Page 54

-- Section Begin Page 55

module SmallStep-BigStep-Equivalence where
    open import State using (State; _[_↦_]; emptyState)
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic
    open Bims.Aexp₁-bigstep-semantic
    import TransitionSystems as TS
    open import Data.Nat using (ℕ; suc; zero)
    open import Data.Integer using (+_)
    open import Data.String using (String)
    open import Data.Product using (_×_; _,_; proj₁; proj₂)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    open TS.TransitionSystem ⟨_⟩⇒₂⟨_⟩-transition using (_⇒∘⇒_; x⇒x; _⇒*_; _⇒⟨_⟩_; _∘⇒_)

    open import Data.Product using (∃)

    L4-12 : {S₁ S₂ : Stm₂} {s s´ : State}
          → inj₁(S₁ , s) ⇒* inj₂ s´
          → inj₁(S₁ Å₃ S₂ , s) ⇒* inj₁(S₂ , s´)
    L4-12 (suc fst , fst₁ ⇒∘⇒ x⇒x) = 1 , COMP-2ₛₛₛ fst₁ ⇒∘⇒ x⇒x
    L4-12 (suc k , (_⇒∘⇒_ {γ˝ = inj₁ S₁´,s˝} premise⟨S₁,s⟩⇒⟨S₁´,s˝⟩ ⟨S₁´,s˝⟩⇒ᵏy)) = COMP-1ₛₛₛ premise⟨S₁,s⟩⇒⟨S₁´,s˝⟩ ∘⇒ L4-12 (k , ⟨S₁´,s˝⟩⇒ᵏy)

    -- Theorem 4.11 -- Apparently this should be hard to prove, and needs the lemma, though agda figures it out without the lemma
    T4-11 : {S : Stm₂} → {s s' : State} → ⟨ inj₁(S , s) ⟩⇒₂⟨ inj₂ s' ⟩ → inj₁(S , s) ⇒* inj₂ s'
    T4-11 x = 1 , x ⇒∘⇒ x⇒x

    -- Theorem 4.13
    T4-13 : {S : Stm₂} → {s s' : State} → inj₁(S , s) ⇒* inj₂ s' → ⟨ inj₁(S , s) ⟩⇒₂⟨ inj₂ s' ⟩
    T4-13 x = {!   !}

-- Section End Page 55
