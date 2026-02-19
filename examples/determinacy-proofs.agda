module examples.determinacy-proofs where
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
open import Bims using (module Aexp₁-bigstep-semantic; module Aexp₁-smallstep-semantic)

module Aexp₁-bigstep-determinacy where
  open Aexp₁-bigstep-semantic

  -- Determinacy for big step (TODO: Apparently it's supposed to be proven in chapter 5, so might want to move this at some point)
  -- Proof for Theorem 3.13
  Determinacy₁ : {v1 v2 : Num} → {α : Aexp₁ ⊎ ℤ} → α ⇒₁ inj₂ v1 → α ⇒₁ inj₂ v2 → v1 ≡ v2
  Determinacy₁ (x PLUS-BSS x₁) (y PLUS-BSS y₁) = cong₂ _+ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
  Determinacy₁ (x MULT-BSS x₁) (y MULT-BSS y₁) = cong₂ _*ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
  Determinacy₁ (x MINUS-BSS x₁) (y MINUS-BSS y₁) = cong₂ _-ℤ_ (Determinacy₁ x y) (Determinacy₁ x₁ y₁)
  Determinacy₁ (PARENT-BSS x) (PARENT-BSS y) = Determinacy₁ x y
  Determinacy₁ NUM-BSS NUM-BSS = refl

module Aexp₁-smallstep-determinacy where
  -- Determinacy for eventual small step (TODO: Apparently it's supposed to be proven in chapter 5, so might want to move this at some point)
  -- Proof for Theorem 3.15
  open Aexp₁-smallstep-semantic
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

  -- TODO unfinished, finish it at chapter 5
  --Determinacy₂ : {v1 v2 α : Aexp₁ss ⊎ Num} → α ⇒* v1 → α ⇒* v2 → v1 ≡ v2
  --Determinacy₂ x y = ?
  -- Section End Page 39
