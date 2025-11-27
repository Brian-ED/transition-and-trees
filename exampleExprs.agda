{-# OPTIONS --allow-unsolved-metas #-}
module transition-and-trees.exampleExprs where
open import Data.Integer using (+_) renaming (ℤ to Num)
open import Function using (_∘_)
open import Data.String using () renaming (String to Var)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃; ∃₂; _,_) renaming (_×_ to _and_)
open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import transition-and-trees.BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; zero) renaming ()

open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_)
open import transition-and-trees.Bims
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; sym; trans)
open import transition-and-trees.Bims using (Aexp₂; _⇒₂_; ++_)
open import transition-and-trees.bims using (T₂; Aexp₂Semantic)

-- Section Start Page 38. This label is place 1
-- page 28 is also done in TransitionSystems.agda
open TransitionSystem Aexp₂Semantic using () renaming (_⇒⟨_⟩_ to _⇒₂⟨_⟩_; step-zero to step-zero₂; _step-suc_ to _step-suc₂_; _⇒*_ to _⇒₂*_)

exampleAexp₂1 : (((N + 3) + (N + 12)) * ((N + 4)*((N + 5)*(N + 8))))
        ⇒₂⟨ 3 ⟩ ((++ + 15)            * ((N + 4)*((N + 5)*(N + 8))))
exampleAexp₂1 = MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
      step-suc₂ MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
      step-suc₂ MULT-1ₛₛₛ PLUS-3ₛₛₛ
      step-suc₂ step-zero₂

-- Problem 3.12
exampleAexp₂2 : (((N + 2) + (N + 3))*((N + 4) + (N + 9))) ⇒₂* (++ + 65)
exampleAexp₂2 = 7 , MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
          step-suc₂ MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
          step-suc₂ MULT-1ₛₛₛ PLUS-3ₛₛₛ
          step-suc₂ MULT-2ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
          step-suc₂ MULT-2ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
          step-suc₂ MULT-2ₛₛₛ PLUS-3ₛₛₛ
          step-suc₂ MULT-3ₛₛₛ
          step-suc₂ step-zero₂
-- Section End Page 38
