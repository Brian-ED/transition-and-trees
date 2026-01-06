module determinacy-proofs where
-- Section Begin Page 39

open import Data.Integer using (+_) renaming (ℤ to Num)
open import Function using (_∘_)
open import Data.String using () renaming (String to Var)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃; ∃₂; _,_) renaming (_×_ to _and_)
open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; zero) renaming ()
open import TransitionSystems using (TransitionSystem)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; sym; trans)
open import bims using (Aexp₂Semantic)

open TransitionSystem Aexp₂Semantic using () renaming (_⇒⟨_⟩_ to _⇒₂⟨_⟩_; step-zero to step-zero₂; _step-suc_ to _step-suc₂_; _⇒*_ to _⇒₂*_)

{-
-- Determinacy for big step (TODO: Apparently it's supposed to be proven in chapter 5, so might want to move this at some point)
-- Proof for Theorem 3.13
Determinacy₁ : {v1 v2 : Num} → {α : ℤ ⊎ Aexp₁} → α ⇒₁ inj₁ v1 → α ⇒₁ inj₁ v2 → v1 ≡ v2
Determinacy₁ (x PLUS-BSS x₁) (y PLUS-BSS y₁) = cong₂ _+ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
Determinacy₁ (x MULT-BSS x₁) (y MULT-BSS y₁) = cong₂ _*ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
Determinacy₁ (x MINUS-BSS x₁) (y MINUS-BSS y₁) = cong₂ _-ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
Determinacy₁ (PARENT-BSS x) (PARENT-BSS y) = Determinacy₁ x y
Determinacy₁ NUM-BSS_ NUM-BSS_ = refl

-- Determinacy for eventual small step (TODO: Apparently it's supposed to be proven in chapter 5, so might want to move this at some point)
-- Proof for Theorem 3.15
Determinacy₂ : {v1 v2 : Num} → {α : Aexp₂} → α ⇒₂* (++ v1) → α ⇒₂ (++ v2) → v1 ≡ v2
Determinacy₂ (suc n       , PLUS-3ₛₛₛ step-suc₂ step-zero₂) PLUS-3ₛₛₛ = refl
Determinacy₂ (suc n       , MULT-3ₛₛₛ step-suc₂ step-zero₂) MULT-3ₛₛₛ = refl
Determinacy₂ (suc n       , SUB-3ₛₛₛ step-suc₂ step-zero₂) SUB-3ₛₛₛ = refl
Determinacy₂ (suc zero    , (PARENT-2ₛₛₛ refl) step-suc₂ step-zero₂) (PARENT-2ₛₛₛ refl) = refl
Determinacy₂ (suc zero    , NUMₛₛₛ refl step-suc₂ step-zero₂) (NUMₛₛₛ refl) = refl

Determinacy₂ (suc (suc n) , MULT-3ₛₛₛ       step-suc₂ () step-suc₂ snd) MULT-3ₛₛₛ
Determinacy₂ (suc (suc n) , SUB-3ₛₛₛ        step-suc₂ () step-suc₂ snd) SUB-3ₛₛₛ
Determinacy₂ (suc (suc n) , (PARENT-2ₛₛₛ x) step-suc₂ () step-suc₂ r) (PARENT-2ₛₛₛ y)

Determinacy₂ (suc (suc n) , PLUS-1ₛₛₛ   () step-suc₂ x) PLUS-3ₛₛₛ
Determinacy₂ (suc (suc n) , PLUS-2ₛₛₛ   () step-suc₂ x) PLUS-3ₛₛₛ
Determinacy₂ (suc (suc n) , MULT-1ₛₛₛ   () step-suc₂ x) MULT-3ₛₛₛ
Determinacy₂ (suc (suc n) , MULT-2ₛₛₛ   () step-suc₂ x) MULT-3ₛₛₛ
Determinacy₂ (suc (suc n) , SUB-1ₛₛₛ    () step-suc₂ x) SUB-3ₛₛₛ
Determinacy₂ (suc (suc n) , SUB-2ₛₛₛ    () step-suc₂ x) SUB-3ₛₛₛ
Determinacy₂ (suc (suc n) , PARENT-1ₛₛₛ () step-suc₂ x) (PARENT-2ₛₛₛ refl)
-}
-- Section End Page 39
