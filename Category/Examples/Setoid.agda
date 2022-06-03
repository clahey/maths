module clahey.maths.Category.Examples.Setoid where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import clahey.maths.Category using (Category; Functor)
open import clahey.maths.Category.Properties using (mono; epi)
open import clahey.maths.Group using (Group; Group-Morphism)
open import clahey.maths.Monoid using (Monoid)
open import clahey.maths.Monoid.Examples using (Nat-monoid-+; Nat-monoid-*)
open import Relation.Binary using (Rel; IsPreorder; IsDecEquivalence; IsEquivalence)
open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Data.Unit using (⊤; tt)
open import Function.Base using (flip)
open import Data.Product using (∃-syntax; Σ; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Empty using (⊥)

Set-Category : { l : Level } → Category (lsuc l) l l
Set-Category {l} = record
                     { Obj = Set l
                     ; _⇒_ = λ A B → A → B
                     ; _≈_ = λ {A} {B} f g → ∀ (a : A) → f a ≡ g a
                     ; isEquivalence = record { refl = λ a → refl ; sym = λ fa≡ga a → sym (fa≡ga a) ; trans = λ fa≡ga ga≡ha a → trans (fa≡ga a) (ga≡ha a) }
                     ; id = Function.Base.id
                     ; _∘_ = λ f g a → f (g a)
                     ; assoc = λ a → refl
                     ; sym-assoc = λ a → refl
                     ; idˡ = λ a → refl
                     ; idʳ = λ a → refl
                     ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} f≈g h≈i a → trans (cong f (h≈i a)) (f≈g (i a))
                     }

𝓟 : {l : Level} → Functor (Set-Category {l}) (Set-Category {l})
𝓟 = record { obj = λ s → {!!}
            ; morph = {!!}
            ; identity = {!!}
            ; resp-∘ = {!!}
            }

inj : { l : Level } → {A B : Set l} → (A → B) → Set l
inj {A = A} f = ∀ (a₁ a₂ : A) → f a₁ ≡ f a₂ → a₁ ≡ a₂

inj→mono : {l : Level} → {A B : Set l} → {f : A → B} → inj f → mono {c = Set-Category {l}} f
inj→mono {A = A} {B = B} if = λ g₁ g₂ f∘g₁≈f∘g₂ a → if (g₁ a) (g₂ a) (f∘g₁≈f∘g₂ a)

data Singleton {l : Level} : Set l where
  * : Singleton

singleton-function : {l : Level} {A : Set l} → A → (Singleton {l} → A)
singleton-function a * = a

mono→inj : {l : Level} → {A B : Set l} → {f : A → B} → (∀ (A : Set l) → ¬ ¬ A → A) → mono {c = Set-Category {l}} f → inj f
mono→inj {A = A} {B = B} {f = f} lem mf a₁ a₂ fa₁≡fa₂ = lem (a₁ ≡ a₂) λ ¬a₁≡a₂ → contraposition (mf g₁ g₂) (λ g₁≈g₂ → ¬a₁≡a₂ (g₁≈g₂ *)) λ * → {!!}
-- lem (f (singleton-function a₁ *) ≡ f (singleton-function a₂ *)) (λ _ → ¬a₁≡a₂ (mf (λ _ → a₁) (λ _ → a₂) (λ a → a) fa₁≡fa₂))
--   begin
--     f (g₁ *)
--     ≡⟨ cong f (lem (singleton-function a₁ * ≡ a₁)
--                  (λ _ → ¬a₁≡a₂ (mf (λ _ → a₁) (λ _ → a₂) (λ a → a) fa₁≡fa₂))) ⟩
--     f a₁
--     ≡⟨ fa₁≡fa₂ ⟩
--     f a₂
--     ≡⟨ lem (f a₂ ≡ f (singleton-function a₂ *))
--          (λ _ → ¬a₁≡a₂ (mf (λ _ → a₁) (λ _ → a₂) (λ a → a) fa₁≡fa₂)) ⟩
--     f (g₂ *)
--   ∎
--   
  where
    g₁ = singleton-function a₁
    g₂ = singleton-function a₂
    ¬g₁≈g₂ : ¬ a₁ ≡ a₂ → (∀ (a : Singleton) → ¬ g₁ a ≡ g₂ a)
    ¬g₁≈g₂ ¬a₁≡a₂ * g₁a≡g₂a = ¬a₁≡a₂ g₁a≡g₂a

surj : { l : Level } → {A B : Set l} → (A → B) → Set l
surj {A = A} {B = B} f = ∀ (b : B) → ∃[ a ] (f a ≡ b) 

surj→epi : {l : Level} → {A B : Set l} → {f : A → B} → surj f → epi {c = Set-Category {l}} f
surj→epi {A = A} {B = B} {f = f} sf f₁ f₂ f₁∘g≈f₂∘g b =
  begin
    f₁ b
  ≡⟨ cong f₁ (sym fa≡b) ⟩
    f₁ (f a)
  ≡⟨ f₁∘g≈f₂∘g a ⟩
    f₂ (f a)
  ≡⟨ cong f₂ fa≡b ⟩
    f₂ b
  ∎
  where
    a : A
    a = Σ.proj₁ (sf b)

    fa≡b : f a ≡ b
    fa≡b = Σ.proj₂ (sf b)
