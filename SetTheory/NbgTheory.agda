module clahey.maths.SetTheory.NbgTheory where

open import Agda.Primitive using (Level; lsuc; lzero)
open import Function.Base using (case_of_; _$_; _∘_; id; const)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; _≢_; sym; trans; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product using (∃-syntax; _×_; proj₁; proj₂; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; [_,_])
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _⊔_; _+_; _∸_; _≥_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; n≤m⊔n; suc-injective; +-suc; n∸n≡0; +-identityʳ; +-comm; ⊔-idem; m≤n⇒n⊔m≡n; ⊔-comm)
open import Data.Vec using (Vec; lookup; []; _∷_; _++_; initLast; init; last; foldl₁; foldl; head; tail)
open import Data.Fin using (fromℕ<; Fin)
open import clahey.maths.Whole using (ℕ⁺; toℕ)


-- Missing from standard-library version
-- Take the first 'm' elements of a vector.
truncate : {A : Set} → {m n : ℕ} → m ≤ n → Vec A n → Vec A m
truncate z≤n      _        = []
truncate (s≤s le) (x ∷ xs) = x ∷ (truncate le xs)


record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
infix 3 _⇔_

open _⇔_

LEM : {l : Level} → Set (lsuc l)
LEM {l} = (A : Set l) → Dec A

⇔-trans : {A B C : Set} → (A ⇔ B) → (B ⇔ C) → (A ⇔ C)
⇔-trans record { to = to₁ ; from = from₁ } record { to = to₂ ; from = from₂ } =
   record { to = to₂ ∘ to₁
   ; from = from₁ ∘ from₂
   }

⇔-×-dist : {A B C D : Set} → (A ⇔ C) → (B ⇔ D) → ((A × B) ⇔ (C × D))
⇔-×-dist record { to = to₁ ; from = from₁ } record { to = to₂ ; from = from₂ } = record { to = λ (a , b) → to₁ a , to₂ b ; from = λ (c , d) → from₁ c , from₂ d }

⇔-refl : {A : Set} → A ⇔ A
⇔-refl = record { to = id ; from = id }

⇔-transport : {A : Set} → {a b : A} → {P : A → Set} → a ≡ b → P a ⇔ P b
⇔-transport refl = record { to = id ; from = id }

⇔-converse : {A B : Set} → A ⇔ B → (¬ A) ⇔ (¬ B)
⇔-converse record { to = to ; from = from } = record { to = contraposition from ; from = contraposition to }

⇔-comm : {A B : Set} → A ⇔ B → B ⇔ A
⇔-comm record { to = to; from = from } = record { to = from ; from = to }

A→¬¬A : {A : Set} → A → ¬ ¬ A
A→¬¬A a = λ ¬a → ¬a a

postulate
  NbgClass : Set
  _∈_ : (X A : NbgClass) → Set
infix  8 _∈_

isSet : NbgClass → Set
isSet x = ∃[ C ] (x ∈ C)

NbgSet = Σ[ c ∈ NbgClass ] (isSet c)

_!∈_ : NbgSet → NbgClass → Set
x !∈ A = proj₁ x ∈ A
infix  7 _!∈_

_!!∈_ : NbgSet → NbgSet → Set
x !!∈ A = proj₁ x ∈ proj₁ A 
infix  7 _!!∈_

_⊆_ : NbgClass → NbgClass → Set
A ⊆ B = (x : NbgSet) → x !∈ A → x !∈ B
infix  8 _⊆_

_!⊆_ : NbgSet → NbgClass → Set
A !⊆ B = proj₁ A ⊆ B
infix  8 _!⊆_

_!!⊆_ : NbgSet → NbgSet → Set
A !!⊆ B = proj₁ A ⊆ proj₁ B
infix  8 _!!⊆_

transport : {Type : Set} → {P : Type → Set} → {A B : Type} → A ≡ B → P A → P B
transport refl pa = pa


record NbgTheory : Set (lsuc lzero) where
  field
    lem : LEM {lzero}
    extensionality : ∀ (A B : NbgClass) → (∀ (x : NbgSet) → x !∈ A ⇔ x !∈ B) → A ≡ B
    pairing : ∀ (x y : NbgSet) → Σ[ p ∈ NbgSet ] (∀ (z : NbgSet) → z !!∈ p ⇔ (z ≡ x ⊎ z ≡ y))

  ¬¬A→A : {A : Set} → ¬ ¬ A → A
  ¬¬A→A {A} ¬¬a = case lem A of λ
      { (yes a) → a
      ; (no ¬a) → ⊥-elim $ ¬¬a ¬a
      }
  pair : (x y : NbgSet) → NbgSet
  pair x y = proj₁ (pairing x y)

  pair-rule : (x y z : NbgSet) → z !!∈ pair x y ⇔ (z ≡ x ⊎ z ≡ y)
  pair-rule x y = proj₂ (pairing x y)

  pair-ruleᵢ : (x y z : NbgSet) → z !!∈ pair x y → (z ≡ x ⊎ z ≡ y)
  pair-ruleᵢ x y z = to (pair-rule x y z)

  pair-ruleₗ : (x y : NbgSet) → x !!∈ pair x y
  pair-ruleₗ x y = from (pair-rule x y x) (_⊎_.inj₁ refl)

  pair-ruleᵣ : (x y : NbgSet) → y !!∈ pair x y
  pair-ruleᵣ x y = from (pair-rule x y y) (_⊎_.inj₂ refl)

  singleton : (x : NbgSet) → NbgSet
  singleton x = pair x x

  orderedPair : (x y : NbgSet) → NbgSet
  orderedPair x y = pair x (pair x y)

  orderedTriple : (x y z : NbgSet) → NbgSet
  orderedTriple x y z = orderedPair (orderedPair x y) z
    
  field
    membership : Σ[ E ∈ NbgClass ] (∀ (x y : NbgSet) → orderedPair x y !∈ E ⇔ x !!∈ y)
    intersection : ∀ (A B : NbgClass) → Σ[ C ∈ NbgClass ] (∀ (x : NbgSet) → x !∈ C ⇔ (x !∈ A × x !∈ B))
    complement : ∀ (A : NbgClass) → Σ[ B ∈ NbgClass ] (∀ (x : NbgSet) → x !∈ A ⇔ (¬ x !∈ B))
    domain : ∀ (A : NbgClass) → Σ[ B ∈ NbgClass ] (∀ (x : NbgSet) → x !∈ B ⇔ (Σ[ y ∈ NbgSet ] orderedPair x y !∈ A))

  _∩_ : NbgClass → NbgClass → NbgClass
  A ∩ B = proj₁ (intersection A B)

  _!!∩_ : NbgSet → NbgSet → NbgClass
  A !!∩ B = proj₁ A ∩ proj₁ B

  infix  9 _∩_
  infix  9 _!!∩_

  ∩-rule : (A B : NbgClass) → (x : NbgSet) → x !∈ A ∩ B ⇔ (x !∈ A × x !∈ B)
  ∩-rule A B = proj₂ (intersection A B)

  ∩-ruleᵢ : (A B : NbgClass) → (x : NbgSet) → x !∈ A → x !∈ B → x !∈ A ∩ B
  ∩-ruleᵢ A B x x∈A x∈B = from (∩-rule A B x) (x∈A , x∈B)

  ∁ : NbgClass → NbgClass
  ∁ A = proj₁ (complement A)

  ∁-rule : (A : NbgClass) → (x : NbgSet) → x !∈ A ⇔ (¬ x !∈ ∁ A)
  ∁-rule A = proj₂ (complement A)

  Dom : NbgClass → NbgClass
  Dom A = proj₁ (domain A)

  Dom-rule : (A : NbgClass) → (x : NbgSet) → x !∈ (Dom A) ⇔ (Σ[ y ∈ NbgSet ] orderedPair x y !∈ A)
  Dom-rule A = proj₂ (domain A)
  
  Dom-rule-to : (A : NbgClass) → (x : NbgSet) → x !∈ (Dom A) → Σ[ y ∈ NbgSet ] orderedPair x y !∈ A
  Dom-rule-to A x = to (Dom-rule A x)

  Dom-rule-from : (A : NbgClass) → (x : NbgSet) → Σ[ y ∈ NbgSet ] orderedPair x y !∈ A → x !∈ (Dom A)
  Dom-rule-from A x = from (Dom-rule A x)

  ⊘-class : NbgClass
  ⊘-class = proj₁ membership ∩ (∁ (proj₁ membership))

  V : NbgClass
  V = ∁ ⊘-class

  field
    productByV : ∀ (A : NbgClass) → Σ[ B ∈ NbgClass ] (∀ (u : NbgSet) → (u !∈ B) ⇔ (Σ[ (x , y) ∈ (NbgSet × NbgSet) ] (u ≡ orderedPair x y × x !∈ A)))
    circularPerm : ∀ (A : NbgClass) → Σ[ B ∈ NbgClass ] (∀ (x y z : NbgSet) → (orderedTriple x y z !∈ B ⇔ orderedTriple y z x !∈ A))
    transposition : ∀ (A : NbgClass) → Σ[ B ∈ NbgClass ] (∀ (x y z : NbgSet) → (orderedTriple x y z !∈ B ⇔ orderedTriple x z y !∈ A))
    regularity : ∀ (a : NbgSet) → proj₁ a ≢ ⊘-class → Σ[ u ∈ NbgSet ] (u !!∈ a × (u !!∩ a) ≡ ⊘-class)

  ×V : NbgClass → NbgClass
  ×V A = proj₁ (productByV A)

  ×V-rule : (A : NbgClass) → (∀ (u : NbgSet) → (u !∈ ×V A) ⇔ (Σ[ (x , y) ∈ (NbgSet × NbgSet) ] (u ≡ orderedPair x y × x !∈ A)))
  ×V-rule A = proj₂ (productByV A)

  V^2 = ×V V

  isFunction : NbgClass → Set
  isFunction F = (F ⊆ V^2) × (∀ (x y z : NbgSet) → orderedPair x y !∈ F × orderedPair x z !∈ F → y ≡ z)

  field
    replacement : ∀ (F : NbgClass) → (a : NbgSet) → isFunction F → Σ[ b ∈ NbgSet ] (∀ (y : NbgSet) → y !!∈ b ⇔ (Σ[ x ∈ NbgSet ] (x !!∈ a × orderedPair x y !∈ F)))
  
  field
    union : ∀ (a : NbgSet) → Σ[ b ∈ NbgSet ] (∀ (x : NbgSet) → (Σ[ y ∈ NbgSet ] (x !!∈ y × y !!∈ a)) → x !!∈ b)
    powerSet : ∀ (a : NbgSet) → Σ[ b ∈ NbgSet ] (∀ (x : NbgSet) → x !!⊆ a ⇔ x !!∈ b)
    infinity : Σ[ a ∈ NbgSet ] ((Σ[ u ∈ NbgSet ] (u !!∈ a)) × (∀ (x : NbgSet) → (x !!∈ a) → Σ[ y ∈ NbgSet ] (y !!∈ a × x !!⊆ a)))
--    globalChoice

postulate
  nbg : NbgTheory

open NbgTheory nbg

ω : NbgSet
ω = proj₁ infinity

⊘-empty-helper : (x : NbgSet) → x !∈ ⊘-class → ⊥
⊘-empty-helper x x∈⊘ = ¬x∈∁E x∈∁E
  where
    E = proj₁ membership
    x∈E×x∈∁E : x !∈ E × x !∈ ∁ E
    x∈E×x∈∁E = to (∩-rule E (∁ E) x) x∈⊘
    x∈E : x !∈ E
    x∈E = proj₁ x∈E×x∈∁E
    ¬x∈∁E : ¬ x !∈ ∁ E
    ¬x∈∁E = to (∁-rule E x) x∈E
    x∈∁E : x !∈ ∁ E
    x∈∁E = proj₂ x∈E×x∈∁E

⊘-class-empty : (x : NbgSet) → ¬ x !∈ ⊘-class
⊘-class-empty x = λ x∈⊘ → ⊘-empty-helper x x∈⊘

⊘isFunction : isFunction ⊘-class
⊘isFunction = (λ x x∈⊘ → ⊥-elim (⊘-class-empty x x∈⊘)) , λ x y z x,y∈⊘×x,z∈⊘ → ⊥-elim (⊘-class-empty (orderedPair x y) (proj₁ x,y∈⊘×x,z∈⊘))

⊘-existence : Σ[ ⊘ ∈ NbgSet ] (∀ (y : NbgSet) → y !!∈ ⊘ ⇔ (Σ[ x ∈ NbgSet ] (x !!∈ ω × orderedPair x y !∈ ⊘-class)))
⊘-existence = replacement ⊘-class ω ⊘isFunction

⊘ : NbgSet
⊘ = proj₁ ⊘-existence

⊘-rule : (x : NbgSet) → ¬ x !!∈ ⊘
⊘-rule x x∈⊘ = ⊘-class-empty (orderedPair y x) y,x∈⊘
  where
    ⊘-rule' : Σ[ y ∈ NbgSet ] (y !!∈ ω × orderedPair y x !∈ ⊘-class)
    ⊘-rule' = to (proj₂ ⊘-existence x) x∈⊘

    y : NbgSet
    y = proj₁ ⊘-rule'

    y,x∈⊘ : orderedPair y x !∈ ⊘-class
    y,x∈⊘ = proj₂ (proj₂ ⊘-rule')

⊘-empty : (x : NbgSet) → ¬ x !!∈ ⊘
⊘-empty = ⊘-rule

A⊎A⇒A : {A : Set} → A ⊎ A → A
A⊎A⇒A (_⊎_.inj₁ a) = a
A⊎A⇒A (_⊎_.inj₂ a) = a

X∩X≡X : (X : NbgClass) → X ∩ X ≡ X
X∩X≡X X = extensionality (X ∩ X) X λ x → record { to = λ x∈X∩X → proj₁ (to (∩-rule X X x) x∈X∩X)
                                                 ; from = λ x∈X → from (∩-rule X X x) (x∈X , x∈X)
                                                 }

x∉x : (x : NbgSet) → ¬ x !!∈ x
x∉x x x∈x with regularity (singleton x) ¬xx≡⊘
  where
    x∈xx : x !!∈ singleton x
    x∈xx = pair-ruleₗ x x
    ¬xx≡⊘ : proj₁ (singleton x) ≢ ⊘-class
    ¬xx≡⊘ xx≡⊘ = ⊘-class-empty x (subst (x !∈_) xx≡⊘ x∈xx)
... | u , u∈xx , u∩xx≡⊘ = ⊘-class-empty x (subst (x !∈_) u∩xx≡⊘ x∈u∩xx)
  where
    u≡x : u ≡ x
    u≡x = A⊎A⇒A (pair-ruleᵢ x x u u∈xx)
    x∈u∩xx : x !∈ (u !!∩ singleton x)
    x∈u∩xx = ∩-ruleᵢ (proj₁ u) (proj₁ (singleton x)) x (subst (x !!∈_) (sym u≡x) x∈x) (pair-ruleₗ x x)

¬x∈y×y∈x : (x y : NbgSet) → ¬ (x !!∈ y × y !!∈ x)
¬x∈y×y∈x x y x∈y×y∈x with regularity (pair x y) ¬xy≡⊘
  where
    x∈xy : x !!∈ pair x y
    x∈xy = pair-ruleₗ x y
    ¬xy≡⊘ : proj₁ (pair x y) ≢ ⊘-class
    ¬xy≡⊘ xy≡⊘ = ⊘-class-empty x (subst (x !∈_) xy≡⊘ x∈xy)
... | u , u∈xy , u∩xy≡⊘ with u≡x⊎u≡y
  where
    u≡x⊎u≡y : u ≡ x ⊎ u ≡ y
    u≡x⊎u≡y = pair-ruleᵢ x y u u∈xy
... | _⊎_.inj₁ u≡x = ⊘-class-empty y (subst (y !∈_) u∩xy≡⊘ y∈u∩xy)
  where
    y∈u∩xy : y !∈ (u !!∩ pair x y)
    y∈u∩xy = ∩-ruleᵢ (proj₁ u) (proj₁ (pair x y)) y (subst (y !!∈_) (sym u≡x) (proj₂ x∈y×y∈x)) (pair-ruleᵣ x y)
... | _⊎_.inj₂ u≡y = ⊘-class-empty x (subst (x !∈_) u∩xy≡⊘ x∈u∩xy)
  where
    x∈u∩xy : x !∈ (u !!∩ pair x y)
    x∈u∩xy = ∩-ruleᵢ (proj₁ u) (proj₁ (pair x y)) x (subst (x !!∈_) (sym u≡y) (proj₁ x∈y×y∈x)) (pair-ruleₗ x y)

A⊎B×¬A⇒B : {A B : Set} → A ⊎ B → ¬ A → B
A⊎B×¬A⇒B (_⊎_.inj₁ a) ¬a = ⊥-elim (¬a a)
A⊎B×¬A⇒B (_⊎_.inj₂ b) ¬a = b

A⊎B×¬B⇒A : {A B : Set} → A ⊎ B → ¬ B → A
A⊎B×¬B⇒A (_⊎_.inj₁ a) ¬b = a
A⊎B×¬B⇒A (_⊎_.inj₂ b) ¬b = ⊥-elim (¬b b)

pair-inverseₗ : (a₁ b₁ a₂ b₂ : NbgSet) → pair a₁ b₁ ≡ pair a₂ b₂ → a₁ ≡ a₂ ⊎ a₁ ≡ b₂
pair-inverseₗ a₁ b₁ a₂ b₂ a₁b₁≡a₂b₂ = to (pair-rule a₂ b₂ a₁) (subst (a₁ !!∈_) a₁b₁≡a₂b₂ (pair-ruleₗ a₁ b₁))

pair-inverseᵣ : (a₁ b₁ a₂ b₂ : NbgSet) → pair a₁ b₁ ≡ pair a₂ b₂ → b₁ ≡ a₂ ⊎ b₁ ≡ b₂
pair-inverseᵣ a₁ b₁ a₂ b₂ a₁b₁≡a₂b₂ = to (pair-rule a₂ b₂ b₁) (subst (b₁ !!∈_) a₁b₁≡a₂b₂ (pair-ruleᵣ a₁ b₁))

orderedPair-inverse : (a₁ b₁ a₂ b₂ : NbgSet) → orderedPair a₁ b₁ ≡ orderedPair a₂ b₂ → a₁ ≡ a₂ × b₁ ≡ b₂
orderedPair-inverse a₁ b₁ a₂ b₂ a₁b₁≡a₂b₂ = a₁≡a₂ , b₁≡b₂
  where
    a₁∉a₁ : ¬ (a₁ !!∈ a₁)
    a₁∉a₁ = x∉x a₁
    a₁∈pair₁ : a₁ !!∈ pair a₁ b₁
    a₁∈pair₁ = from (pair-rule a₁ b₁ a₁) (_⊎_.inj₁ refl)
    a₁≢pair₁ : ¬ (a₁ ≡ pair a₁ b₁)
    a₁≢pair₁ = λ a₁≡pair₁ → a₁∉a₁ (subst (a₁ !!∈_) (sym a₁≡pair₁) a₁∈pair₁)

    pair₁≡a₂⊎pair₁≡pair₂ : pair a₁ b₁ ≡ a₂ ⊎ pair a₁ b₁ ≡ pair a₂ b₂
    pair₁≡a₂⊎pair₁≡pair₂ = pair-inverseᵣ a₁ (pair a₁ b₁) a₂ (pair a₂ b₂) a₁b₁≡a₂b₂

    a₁≡a₂⊎a₁≡pair₂ : a₁ ≡ a₂ ⊎ a₁ ≡ pair a₂ b₂
    a₁≡a₂⊎a₁≡pair₂ = pair-inverseₗ a₁ (pair a₁ b₁) a₂ (pair a₂ b₂) a₁b₁≡a₂b₂

    ¬a₁≡a₂×pair₁≡a₂ : ¬ (a₁ ≡ a₂ × pair a₁ b₁ ≡ a₂)
    ¬a₁≡a₂×pair₁≡a₂ (a₁≡a₂ , pair₁≡a₂) = a₁≢pair₁ (trans a₁≡a₂ (sym pair₁≡a₂))

    ¬a₁≡pair₂×pair₁≡pair₂ : ¬ (a₁ ≡ pair a₂ b₂ × pair a₁ b₁ ≡ pair a₂ b₂)
    ¬a₁≡pair₂×pair₁≡pair₂ (a₁≡pair₂ , pair₁≡pair₂) = a₁≢pair₁ (trans a₁≡pair₂ (sym pair₁≡pair₂))

    ¬a₁≡pair₂×pair₁≡a₂ : ¬ (a₁ ≡ pair a₂ b₂ × pair a₁ b₁ ≡ a₂)
    ¬a₁≡pair₂×pair₁≡a₂ (a₁≡pair₂ , pair₁≡a₂) = ¬x∈y×y∈x a₁ a₂ (a₁∈a₂ , a₂∈a₁)
      where
        a₁∈a₂ : a₁ !!∈ a₂
        a₁∈a₂ = subst (a₁ !!∈_) pair₁≡a₂ (pair-ruleₗ a₁ b₁)
        a₂∈a₁ : a₂ !!∈ a₁
        a₂∈a₁ = subst (a₂ !!∈_) (sym a₁≡pair₂) (pair-ruleₗ a₂ b₂)

    ¬a₁≡pair₂ : ¬ (a₁ ≡ pair a₂ b₂)
    ¬a₁≡pair₂ = [ (λ pair₁≡a₂ a₁≡pair₂ → ¬a₁≡pair₂×pair₁≡a₂ (a₁≡pair₂ , pair₁≡a₂)) , (λ pair₁≡pair₂ a₁≡pair₂ → ¬a₁≡pair₂×pair₁≡pair₂ ( a₁≡pair₂ , pair₁≡pair₂)) ] pair₁≡a₂⊎pair₁≡pair₂

    a₁≡a₂ : a₁ ≡ a₂
    a₁≡a₂ = A⊎B×¬B⇒A a₁≡a₂⊎a₁≡pair₂ ¬a₁≡pair₂

    ¬pair₁≡a₂ : ¬ (pair a₁ b₁ ≡ a₂)
    ¬pair₁≡a₂ = [ (λ a₁≡a₂ pair₁≡a₂ → ¬a₁≡a₂×pair₁≡a₂ (a₁≡a₂ , pair₁≡a₂)) , (λ a₁≡pair₂ pair₁≡a₂ → ¬a₁≡pair₂×pair₁≡a₂ (a₁≡pair₂ , pair₁≡a₂)) ] a₁≡a₂⊎a₁≡pair₂

    pair₁≡pair₂ : pair a₁ b₁ ≡ pair a₂ b₂
    pair₁≡pair₂ = A⊎B×¬A⇒B pair₁≡a₂⊎pair₁≡pair₂ ¬pair₁≡a₂

    b₂≡a₁⊎b₂≡b₁ : b₂ ≡ a₁ ⊎ b₂ ≡ b₁
    b₂≡a₁⊎b₂≡b₁ = pair-inverseᵣ a₂ b₂ a₁ b₁ (sym pair₁≡pair₂)
    
    b₁≡b₂ : b₁ ≡ b₂
    b₁≡b₂ = [ (λ b₁≡a₂ → [ (λ b₂≡a₁ → trans (trans b₁≡a₂ (sym a₁≡a₂)) (sym b₂≡a₁)) , sym ] b₂≡a₁⊎b₂≡b₁) , id ] (pair-inverseᵣ a₁ b₁ a₂ b₂ pair₁≡pair₂)

⊘≡⊘-class : proj₁ ⊘ ≡ ⊘-class
⊘≡⊘-class = extensionality (proj₁ ⊘) ⊘-class λ x → record { to = λ x∈⊘ → ⊥-elim (⊘-empty x x∈⊘) ; from = λ x∈⊘-class → ⊥-elim (⊘-class-empty x x∈⊘-class) }

∁-involutory : (A : NbgClass) → A ≡ ∁ (∁ A)
∁-involutory A = extensionality A (∁ (∁ A))
  λ x → record { to = λ x∈A → ¬¬A→A λ ¬x∈∁∁A → to (∁-rule A x) x∈A (from (∁-rule (∁ A) x) ¬x∈∁∁A)
                ; from = λ x∈∁∁A → ¬¬A→A λ ¬x∈A → contraposition (to (∁-rule (∁ A) x)) (A→¬¬A x∈∁∁A) (¬¬A→A (contraposition (from (∁-rule A x)) ¬x∈A))
                }

data NbgVariable : (xᵒ : ℕ) →  Set where
  x' : (i : ℕ) → NbgVariable (suc i)

data NbgExpression : (xᵒ Yᵒ : ℕ) → Set where
  _∈'_ : {xᵒ₁ xᵒ₂ Yᵒ : ℕ} → NbgVariable xᵒ₁ → NbgVariable xᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) Yᵒ
  _='_ : {xᵒ₁ xᵒ₂ Yᵒ : ℕ} → NbgVariable xᵒ₁ → NbgVariable xᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) Yᵒ
  _∧'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgExpression xᵒ₁ Yᵒ₁ → NbgExpression xᵒ₂ Yᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _∨'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgExpression xᵒ₁ Yᵒ₁ → NbgExpression xᵒ₂ Yᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _⇔'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgExpression xᵒ₁ Yᵒ₁ → NbgExpression xᵒ₂ Yᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _⇒'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgExpression xᵒ₁ Yᵒ₁ → NbgExpression xᵒ₂ Yᵒ₂ → NbgExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  ∃' : {Yᵒ : ℕ} → (i : ℕ) → NbgExpression (suc i) Yᵒ → NbgExpression i Yᵒ
  ∀' : {Yᵒ : ℕ} → (i : ℕ) → NbgExpression (suc i) Yᵒ → NbgExpression i Yᵒ
  ¬' : {xᵒ Yᵒ : ℕ} → NbgExpression xᵒ Yᵒ → NbgExpression xᵒ Yᵒ
infix  8 _∈'_
infix  3 _⇔'_
NbgExpression-transport : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → xᵒ₁ ≡ xᵒ₂ → Yᵒ₁ ≡ Yᵒ₂ → NbgExpression xᵒ₁ Yᵒ₁ → NbgExpression xᵒ₂ Yᵒ₂
NbgExpression-transport refl refl exp = exp

data NbgIntermediateExpression : (xᵒ Yᵒ : ℕ) → Set where
  _∈'_ : {xᵒ₁ xᵒ₂ Yᵒ : ℕ} → NbgVariable xᵒ₁ → NbgVariable xᵒ₂ → NbgIntermediateExpression (xᵒ₁ ⊔ xᵒ₂) Yᵒ
  _∧'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgIntermediateExpression xᵒ₁ Yᵒ₁ → NbgIntermediateExpression xᵒ₂ Yᵒ₂ → NbgIntermediateExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _∨'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgIntermediateExpression xᵒ₁ Yᵒ₁ → NbgIntermediateExpression xᵒ₂ Yᵒ₂ → NbgIntermediateExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _⇔'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgIntermediateExpression xᵒ₁ Yᵒ₁ → NbgIntermediateExpression xᵒ₂ Yᵒ₂ → NbgIntermediateExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  _⇒'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgIntermediateExpression xᵒ₁ Yᵒ₁ → NbgIntermediateExpression xᵒ₂ Yᵒ₂ → NbgIntermediateExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  ∃' : {Yᵒ : ℕ} → (i : ℕ) → NbgIntermediateExpression (suc i) Yᵒ → NbgIntermediateExpression i Yᵒ
  ∀' : {Yᵒ : ℕ} → (i : ℕ) → NbgIntermediateExpression (suc i) Yᵒ → NbgIntermediateExpression i Yᵒ
  ¬' : {xᵒ Yᵒ : ℕ} → NbgIntermediateExpression xᵒ Yᵒ → NbgIntermediateExpression xᵒ Yᵒ
NbgIntermediateExpression-transport : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → xᵒ₁ ≡ xᵒ₂ → Yᵒ₁ ≡ Yᵒ₂ → NbgIntermediateExpression xᵒ₁ Yᵒ₁ → NbgIntermediateExpression xᵒ₂ Yᵒ₂
NbgIntermediateExpression-transport refl refl exp = exp

data NbgSimpleExpression : (xᵒ Yᵒ : ℕ) → Set where
  _∈'_ : {xᵒ₁ xᵒ₂ Yᵒ : ℕ} → NbgVariable xᵒ₁ → NbgVariable xᵒ₂ → NbgSimpleExpression (xᵒ₁ ⊔ xᵒ₂) Yᵒ
  _∧'_ : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → NbgSimpleExpression xᵒ₁ Yᵒ₁ → NbgSimpleExpression xᵒ₂ Yᵒ₂ → NbgSimpleExpression (xᵒ₁ ⊔ xᵒ₂) (Yᵒ₁ ⊔ Yᵒ₂)
  ∃' : {Yᵒ : ℕ} → (i : ℕ) → NbgSimpleExpression (suc i) Yᵒ → NbgSimpleExpression i Yᵒ
  ¬' : {xᵒ Yᵒ : ℕ} → NbgSimpleExpression xᵒ Yᵒ → NbgSimpleExpression xᵒ Yᵒ
NbgSimpleExpression-transport : {xᵒ₁ Yᵒ₁ xᵒ₂ Yᵒ₂ : ℕ} → xᵒ₁ ≡ xᵒ₂ → Yᵒ₁ ≡ Yᵒ₂ → NbgSimpleExpression xᵒ₁ Yᵒ₁ → NbgSimpleExpression xᵒ₂ Yᵒ₂
NbgSimpleExpression-transport refl refl exp = exp

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

convert-to-intermediate : {xᵒ Yᵒ : ℕ} → NbgExpression xᵒ Yᵒ → NbgIntermediateExpression xᵒ Yᵒ
convert-to-intermediate (x ∈' x₁) = x ∈' x₁
convert-to-intermediate {xᵒ = .(suc (i₁ ⊔ i₂))} {Yᵒ = Yᵒ} (x' i₁ =' x' i₂) = ∃' (suc (i₁ ⊔ i₂)) (transport-function (_⇔'_ {Yᵒ₁ = Yᵒ} {Yᵒ₂ = Yᵒ} (x' (suc (i₁ ⊔ i₂)) ∈' x' i₁) (x' (suc (i₁ ⊔ i₂)) ∈' x' i₂)))
 where
  transport-function = NbgIntermediateExpression-transport (cong suc (trans (cong₂ _⊔_ (m≤n⇒n⊔m≡n (≤-step (m≤m⊔n i₁ i₂))) (m≤n⇒n⊔m≡n (≤-step (n≤m⊔n i₁ i₂)))) (⊔-idem (suc (i₁ ⊔ i₂))))) (⊔-idem Yᵒ)
convert-to-intermediate (exp ∧' exp₁) = convert-to-intermediate exp ∧' convert-to-intermediate exp₁
convert-to-intermediate (exp ∨' exp₁) = convert-to-intermediate exp ∨' convert-to-intermediate exp₁
convert-to-intermediate (exp ⇔' exp₁) = convert-to-intermediate exp ⇔' convert-to-intermediate exp₁
convert-to-intermediate (exp ⇒' exp₁) = convert-to-intermediate exp ⇒' convert-to-intermediate exp₁
convert-to-intermediate (∃' _ exp) = ∃' _ (convert-to-intermediate exp)
convert-to-intermediate (∀' _ exp) = ∀' _ (convert-to-intermediate exp)
convert-to-intermediate (¬' exp) = ¬' (convert-to-intermediate exp)

int-to-simple : {xᵒ Yᵒ : ℕ} → NbgIntermediateExpression xᵒ Yᵒ → NbgSimpleExpression xᵒ Yᵒ
int-to-simple {.(suc (i ⊔ i₁))} {Yᵒ} (x' i ∈' x' i₁) = x' i ∈' x' i₁
int-to-simple {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} (_∧'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) = int-to-simple exp₁ ∧' int-to-simple exp₂
int-to-simple {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} (_∨'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) = ¬' ((¬' (int-to-simple exp₁)) ∧' (¬' (int-to-simple exp₂)))
int-to-simple {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} (_⇔'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) = idem-transport (_∧'_ {xᵒ₁ ⊔ xᵒ₂} {Yᵒ₁ ⊔ Yᵒ₂} {xᵒ₁ ⊔ xᵒ₂} {Yᵒ₁ ⊔ Yᵒ₂} (¬' (_∧'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} (int-to-simple exp₁) (¬' (int-to-simple exp₂)))) (¬' (comm-transport (_∧'_ {xᵒ₂} {Yᵒ₂} {xᵒ₁} {Yᵒ₁} (int-to-simple exp₂) (¬' (int-to-simple exp₁))))))
 where
  idem-transport = NbgSimpleExpression-transport (⊔-idem (xᵒ₁ ⊔ xᵒ₂)) (⊔-idem (Yᵒ₁ ⊔ Yᵒ₂))
  comm-transport = NbgSimpleExpression-transport (⊔-comm xᵒ₂ xᵒ₁) (⊔-comm Yᵒ₂ Yᵒ₁)
int-to-simple {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} (_⇒'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) = ¬' ((int-to-simple exp₁) ∧' (¬' (int-to-simple exp₂)))
int-to-simple {xᵒ} {Yᵒ} (∃' .xᵒ exp) = ∃' xᵒ (int-to-simple exp)
int-to-simple {xᵒ} {Yᵒ} (∀' .xᵒ exp) = ¬' (∃' xᵒ (¬' (int-to-simple exp)))
int-to-simple {xᵒ} {Yᵒ} (¬' exp) = ¬' (int-to-simple exp)

convert-to-simple : {xᵒ Yᵒ : ℕ} → NbgExpression xᵒ Yᵒ → NbgSimpleExpression xᵒ Yᵒ
convert-to-simple exp = int-to-simple (convert-to-intermediate exp)

infixr 5 _+~_
_+~_ : {n : ℕ} → {A : Set} → Vec A n → A → Vec A (suc n)
_+~_ [] x = x ∷ []
_+~_ (x₁ ∷ xs) x = x₁ ∷ xs +~ x

infixr 5 _++'_
_++'_ : {m n : ℕ} → {A : Set} → Vec A m → Vec A n → Vec A (n + m)
_++'_ {m} {n} {A} xs ys = subst (Vec A) (+-comm m n) (xs ++ ys)


last' : {n-1 : ℕ} → {A : Set} → Vec A (suc n-1) → A
last' (x ∷ []) = x
last' (x ∷ x₁ ∷ xs) = last' (x₁ ∷ xs)

init' : {n-1 : ℕ} → {A : Set} → Vec A (suc n-1) → Vec A n-1
init' (x ∷ []) = []
init' (x ∷ x₁ ∷ xs) = x ∷ (init' (x₁ ∷ xs))

last-rule : {n : ℕ} → {A : Set} → (xs : Vec A n) → (x : A) → x ≡ last' (xs +~ x)
last-rule [] x = refl
last-rule (x₁ ∷ []) x = refl
last-rule (x₁ ∷ x₂ ∷ xs) x = last-rule (x₂ ∷ xs) x

init-rule : {n-1 : ℕ} → {A : Set} → (xs : Vec A n-1) → (x : A) → xs ≡ init' (xs +~ x)
init-rule [] x = refl
init-rule (x₁ ∷ []) x = refl
init-rule (x₁ ∷ x₂ ∷ xs) x = cong (x₁ ∷_) (init-rule (x₂ ∷ xs) x)

n-tuple : {n-1 : ℕ} → Vec NbgSet (suc n-1) → NbgSet
n-tuple (x ∷ []) = x
n-tuple {suc n-1} (xs) = orderedPair (n-tuple (init' xs)) (last' xs)

n-tuple-suc : {n-1 : ℕ} → (xs : Vec NbgSet (suc n-1)) → (x : NbgSet) → orderedPair (n-tuple xs) x ≡ n-tuple (xs +~ x)
n-tuple-suc {.0} (x₁ ∷ []) x = refl
n-tuple-suc {.(suc _)} (x₁ ∷ x₂ ∷ xs) x = cong₂ orderedPair (
  begin
    orderedPair (n-tuple (x₁ ∷ init' (x₂ ∷ xs))) (last' (x₂ ∷ xs))    
  ≡⟨⟩
    orderedPair (n-tuple (init' (x₁ ∷ x₂ ∷ xs))) (last' (x₁ ∷ x₂ ∷ xs))
  ≡⟨⟩
    n-tuple (x₁ ∷ x₂ ∷ xs)
  ≡⟨ cong (λ v → n-tuple (x₁ ∷ v)) (init-rule (x₂ ∷ xs) x) ⟩
    n-tuple (x₁ ∷ init' (x₂ ∷ xs +~ x))
  ∎)
  ((last-rule (x₂ ∷ xs) x))

≤-helper : (m n : ℕ) → m ≤ n → suc m ≤ n + 1
≤-helper m n m≤n rewrite +-comm n 1 = s≤s m≤n

≤⇒≤s : {m n : ℕ} → m ≤ n → m ≤ suc n
≤⇒≤s z≤n = z≤n
≤⇒≤s (s≤s m≤n) = s≤s (≤⇒≤s m≤n)


expression-set : {|x| |Y| xᵒ Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ |x|} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} → NbgExpression xᵒ Yᵒ → Vec NbgSet |x| → Vec NbgClass |Y| → Set
expression-set {|x|} {|Y|} {.(suc (i₁ ⊔ i₂))} {Yᵒ} {xᵒ≤|x|} {Yᵒ≤|Y|} (x' i₁ ∈' x' i₂) xs Ys =
  lookup xs (fromℕ< {i₁} {|x|} (≤-trans (m≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|)) !!∈
  lookup xs (fromℕ< {i₂} {|x|} (≤-trans (n≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|))
expression-set {|x|} {|Y|} {.(suc (i₁ ⊔ i₂))} {Yᵒ} {xᵒ≤|x|} {Yᵒ≤|Y|} (x' i₁ =' x' i₂) xs Ys =
  lookup xs (fromℕ< {i₁} {|x|} (≤-trans (m≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|)) ≡
  lookup xs (fromℕ< {i₂} {|x|} (≤-trans (n≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|))
expression-set {|x|} {|Y|} {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x|} {Yᵒ≤|Y|} (_∧'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
  expression-set {|x|} {|Y|} {xᵒ₁} {Yᵒ₁} {≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys ×
  expression-set {|x|} {|Y|} {xᵒ₂} {Yᵒ₂} {≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys
expression-set {|x|} {|Y|} {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x|} {Yᵒ≤|Y|} (_∨'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
  expression-set {|x|} {|Y|} {xᵒ₁} {Yᵒ₁} {≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys ⊎
  expression-set {|x|} {|Y|} {xᵒ₂} {Yᵒ₂} {≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys
expression-set {|x|} {|Y|} {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x|} {Yᵒ≤|Y|} (_⇔'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
  expression-set {|x|} {|Y|} {xᵒ₁} {Yᵒ₁} {≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys ⇔
  expression-set {|x|} {|Y|} {xᵒ₂} {Yᵒ₂} {≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys
expression-set {|x|} {|Y|} {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x|} {Yᵒ≤|Y|} (_⇒'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
  expression-set {|x|} {|Y|} {xᵒ₁} {Yᵒ₁} {≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys →
  expression-set {|x|} {|Y|} {xᵒ₂} {Yᵒ₂} {≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys
expression-set {|x|} {|Y|} {xᵒ} {Yᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (∃' _ exp) xs Ys =
  Σ[ xᵢ ∈ NbgSet ] expression-set  {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs +~ xᵢ) Ys
expression-set {|x| = |x|} {xᵒ = xᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (∀' _ exp) xs Ys =
  ∀ (xᵢ : NbgSet) → expression-set {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs +~ xᵢ) Ys
expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (¬' exp) xs Ys =
  ¬ expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys

simple-expression-set : {|x| |Y| xᵒ Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ |x|} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} → NbgSimpleExpression xᵒ Yᵒ → Vec NbgSet |x| → Vec NbgClass |Y| → Set
simple-expression-set {|x|} {|Y|} {.(suc (i₁ ⊔ i₂))} {Yᵒ} {xᵒ≤|x|} {Yᵒ≤|Y|} (x' i₁ ∈' x' i₂) xs Ys =
  lookup xs (fromℕ< {i₁} {|x|} (≤-trans (m≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|)) !!∈
  lookup xs (fromℕ< {i₂} {|x|} (≤-trans (n≤m⊔n (suc i₁) (suc i₂)) xᵒ≤|x|))
simple-expression-set {|x|} {|Y|} {.(xᵒ₁ ⊔ xᵒ₂)} {.(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x|} {Yᵒ≤|Y|} (_∧'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
  (simple-expression-set {|x|} {|Y|} {xᵒ₁} {Yᵒ₁} {≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys) ×
  (simple-expression-set {|x|} {|Y|} {xᵒ₂} {Yᵒ₂} {≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys)
simple-expression-set {|x|} {|Y|} {xᵒ} {Yᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (∃' _ exp) xs Ys =
  Σ[ xᵢ ∈ NbgSet ] simple-expression-set {suc |x|} {|Y|} {suc xᵒ} {Yᵒ} {s≤s xᵒ≤|x|} {Yᵒ≤|Y|} exp (xs +~ xᵢ) Ys
simple-expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (¬' exp) xs Ys = ¬ simple-expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys

-- simple-equiv-full : {|x| |Y| xᵒ Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ |x|} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} →
--   (exp : NbgSimpleExpression xᵒ Yᵒ) →
--   (xs : Vec NbgSet |x|) →
--   (Ys : Vec NbgClass |Y|) →
--   (simple-expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys ⇔
--     expression-set {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (convert-simple exp) xs Ys)
-- simple-equiv-full {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (x' i₁ ∈' x' i₂) xs Ys = ⇔-refl
-- simple-equiv-full {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (_∧'_ {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) xs Ys =
--   record { to = λ (proof₁ , proof₂) →
--              to (simple-equiv-full {xᵒ≤|x| = ≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys) proof₁ ,
--              to (simple-equiv-full {xᵒ≤|x| = ≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys) proof₂
--          ; from = λ (proof₁ , proof₂) →
--              (from (simple-equiv-full  {xᵒ≤|x| = ≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs Ys) proof₁) ,
--              (from (simple-equiv-full  {xᵒ≤|x| = ≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ xs Ys) proof₂)
--          }
-- simple-equiv-full {|x| = |x|} {xᵒ = xᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (∃' _ exp) xs Ys =
--   record { to = λ (set , proof) → set , to (simple-equiv-full {xᵒ≤|x| = ≤-helper xᵒ |x| xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs ++ [ set ]) Ys) proof
--          ; from = λ (set , proof) → set , from (simple-equiv-full {xᵒ≤|x| = ≤-helper xᵒ |x| xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs ++ [ set ]) Ys) proof
--          }
-- simple-equiv-full {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (¬' exp) xs Ys =
--   record { to = λ ¬sset set → ¬sset (from (simple-equiv-full {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys) set)
--          ; from = λ ¬set sset → ¬set (to (simple-equiv-full {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys) sset)
--          }

module tuple-lemma where

  lemma₁ : ∀ (A : NbgClass) → Σ[ B₁ ∈ NbgClass ] (∀ (x y z : NbgSet) → n-tuple (z ∷ x ∷ y ∷ []) !∈ B₁ ⇔ n-tuple (x ∷ y ∷ []) !∈ A)
  class₁ : NbgClass → NbgClass
  proof₁ : (A : NbgClass) → ∀ (x y z : NbgSet) → n-tuple (z ∷ x ∷ y ∷ []) !∈ (class₁ A) ⇔ n-tuple (x ∷ y ∷ []) !∈ A
  lemma₂ : ∀ (A : NbgClass) → Σ[ B₂ ∈ NbgClass ] (∀ (x y z : NbgSet) → n-tuple (x ∷ z ∷ y ∷ []) !∈ B₂ ⇔ n-tuple (x ∷ y ∷ []) !∈ A)
  class₂ : NbgClass → NbgClass
  proof₂ : (A : NbgClass) → ∀ (x y z : NbgSet) → n-tuple (x ∷ z ∷ y ∷ []) !∈ (class₂ A) ⇔ n-tuple (x ∷ y ∷ []) !∈ A
  lemma₃ : ∀ (A : NbgClass) → Σ[ B₃ ∈ NbgClass ] (∀ (x y z : NbgSet) → n-tuple (x ∷ y ∷ z ∷ []) !∈ B₃ ⇔ n-tuple (x ∷ y ∷ []) !∈ A)
  class₃ : NbgClass → NbgClass
  proof₃ : (A : NbgClass) → ∀ (x y z : NbgSet) → n-tuple (x ∷ y ∷ z ∷ []) !∈ (class₃ A) ⇔ n-tuple (x ∷ y ∷ []) !∈ A
  lemma₄ : ∀ (A : NbgClass) → Σ[ B₄ ∈ NbgClass ] (∀ (x y : NbgSet) → n-tuple (y ∷ x ∷ []) !∈ B₄ ⇔ n-tuple (x ∷ y ∷ []) !∈ A)
  class₄ : NbgClass → NbgClass
  proof₄ : (A : NbgClass) → ∀ (x y : NbgSet) → n-tuple (y ∷ x ∷ []) !∈ (class₄ A) ⇔ n-tuple (x ∷ y ∷ []) !∈ A
  
  
  lemma₁ A = (class₁ A) , (proof₁ A)
  class₁ A = proj₁ (circularPerm (class₃ A))
  proof₁ A x y z = ⇔-trans (proj₂ (circularPerm (class₃ A)) z x y) (proof₃ A x y z)

  lemma₂ A = (class₂ A) , (proof₂ A)
  class₂ A = proj₁ (transposition (class₃ A))
  proof₂ A x y z = ⇔-trans (proj₂ (transposition (class₃ A)) x z y) (proof₃ A x y z)
  
  lemma₃ A = (class₃ A) , (proof₃ A)
  class₃ A = (×V A)
  proof₃ A x y z = record { to = λ xyz∈A×V → to-helper2 x y z (to-helper x y z xyz∈A×V)
                          ; from = λ xy∈A → from-helper x y z (from-helper2 x y z xy∈A)
                          }
    where
      to-helper : (x y z : NbgSet) → orderedPair (orderedPair x y) z !∈ ×V A → Σ[ (xy' , z') ∈ (NbgSet × NbgSet) ] (orderedPair (orderedPair x y) z ≡ orderedPair xy' z' × xy' !∈ A)
      to-helper x y z = (to (×V-rule A (n-tuple (x ∷ y ∷ z ∷ []))))
      to-helper2 : (x y z : NbgSet) → (Σ[ (xy' , z') ∈ (NbgSet × NbgSet) ] (orderedPair (orderedPair x y) z ≡ orderedPair xy' z' × xy' !∈ A)) → orderedPair x y !∈ A
      to-helper2 x y z ((xy' , z') , xyz≡xy'z' , xy'∈A) = subst (_!∈ A) (sym (proj₁ (orderedPair-inverse (orderedPair x y) z xy' z' xyz≡xy'z'))) xy'∈A
      from-helper : (x y z : NbgSet) → Σ[ (xy' , z') ∈ (NbgSet × NbgSet) ] (orderedPair (orderedPair x y) z ≡ orderedPair xy' z' × xy' !∈ A) → orderedPair (orderedPair x y) z !∈ ×V A
      from-helper x y z = (from (×V-rule A (n-tuple (x ∷ y ∷ z ∷ []))))
      from-helper2 : (x y z : NbgSet) → orderedPair x y !∈ A → (Σ[ (xy' , z') ∈ (NbgSet × NbgSet) ] (orderedPair (orderedPair x y) z ≡ orderedPair xy' z' × xy' !∈ A))
      from-helper2 x y z xy∈A = (orderedPair x y , z) , refl , xy∈A

  yxz : NbgClass → NbgClass
  yxz A = proj₁ (circularPerm (class₂ A))
  yxz-proof : (A : NbgClass) → ∀ (x y z : NbgSet) → n-tuple (y ∷ x ∷ z ∷ []) !∈ (yxz A) ⇔ n-tuple (x ∷ y ∷ []) !∈ A
  yxz-proof A x y z = ⇔-trans (proj₂ (circularPerm (class₂ A)) y x z) (proof₂ A x y z)

  lemma₄ A = class₄ A , proof₄ A
  class₄ A = Dom (yxz A)
  proof₄ A x y = record { to = to-helper
                        ; from = from-helper
                        }
    where
      dom-rule : orderedPair y x !∈ Dom (yxz A) ⇔ (Σ[ z ∈ NbgSet ] (orderedPair (orderedPair y x) z !∈ yxz A))
      dom-rule = Dom-rule (yxz A) (orderedPair y x)
      to-helper : orderedPair y x !∈ class₄ A → orderedPair x y !∈ A
      to-helper yx∈B₄ = to (yxz-proof A x y z) yxz∈yxzA
        where
          ∃z⇒yxz∈yxzA : Σ[ z ∈ NbgSet ] (orderedPair (orderedPair y x) z !∈ yxz A)
          ∃z⇒yxz∈yxzA = to dom-rule yx∈B₄
          z = proj₁ ∃z⇒yxz∈yxzA
          yxz∈yxzA = proj₂ ∃z⇒yxz∈yxzA
      from-helper : orderedPair x y !∈ A → orderedPair y x !∈ class₄ A
      from-helper xy∈A = (from dom-rule) (z , z-rule)
        where
          z : NbgSet
          z = x
          z-rule : orderedPair (orderedPair y x) z !∈ yxz A
          z-rule = from (yxz-proof A x y x) xy∈A 

_is-suc_tuples-satisfying_ : NbgClass → (n-1 : ℕ) → (R : Vec NbgSet (suc n-1) → Set) → Set
_is-suc_tuples-satisfying_ P n-1 R = ∀ (u : NbgSet) → (u !∈ P) ⇔ (Σ[ v ∈ Vec NbgSet (suc n-1) ] (u ≡ n-tuple v × R v))

<⇒≤ : {a b : ℕ} → (a < b) → (a ≤ b)
<⇒≤ (s≤s z≤n) = z≤n
<⇒≤ (s≤s (s≤s a<b)) = s≤s (<⇒≤ (s≤s a<b))

<ss : {a : ℕ} → a < suc (suc a)
<ss {zero} = s≤s z≤n
<ss {suc a} = s≤s <ss

<s : {a : ℕ} → a < suc a
<s {zero} = s≤s z≤n
<s {suc a} = s≤s <s

<⇒<s : {a b : ℕ} → (a < b) → (a < suc b)
<⇒<s (s≤s z≤n) = s≤s z≤n
<⇒<s (s≤s (s≤s a<b)) = s≤s (<⇒<s (s≤s a<b))

expansion-lemma : {i j n-1 : ℕ} → (i<j : i < j) → (j<n : j < suc n-1) → (P : NbgClass) → (R : (x₁ x₂ : NbgSet) → Set) →
  (P is-suc 1 tuples-satisfying (λ (v) → R (head v) (head (tail v)))) →
  Σ[ Q ∈ NbgClass ] (Q is-suc n-1 tuples-satisfying (λ v → R (lookup v (fromℕ< (≤-trans i<j (<⇒≤ j<n)))) (lookup v (fromℕ< j<n))))
expansion-lemma {i} {j} {n-1} i<j j<n P R P-is-2-tuples-satisfying-R = {!!}
  where
    lemma₁ : Σ[ P₁ ∈ NbgClass ] (P₁ is-suc (suc i) tuples-satisfying (λ v → R (lookup v (fromℕ< {i} <ss)) (lookup v (fromℕ< {suc i} <s))))
    lemma₁ = {!!} , {!!}
      where
        P₁ = {!tuple-lemma.lemma₁ P!}

    lemma₂ : Σ[ P₁ ∈ NbgClass ] (P₁ is-suc j tuples-satisfying (λ v → R (lookup v (fromℕ< {i} (<⇒<s i<j))) (lookup v (fromℕ< {j} <s))))
    lemma₂ = {!!}

simple-class-existence-theorem : {|x|-1 xᵒ |Y| Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ suc |x|-1} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} → (exp : NbgSimpleExpression (xᵒ) Yᵒ) → (Ys : Vec NbgClass |Y|) →
  Σ[ X ∈ NbgClass ] (∀ (xs : Vec NbgSet (suc |x|-1)) → n-tuple xs !∈ X ⇔ (simple-expression-set {suc |x|-1} {|Y|} {xᵒ} {Yᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys))

simple-class-existence-theorem {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (x' i ∈' x' i₁) Ys = {!!}
simple-class-existence-theorem {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (_∧'_  {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) Ys =
  (class₁ ∩ class₂) , λ xs → ⇔-trans (∩-rule class₁ class₂ (n-tuple xs)) (⇔-×-dist (proof₁ xs) (proof₂ xs))
  where
    class-proof₁ = simple-class-existence-theorem {xᵒ≤|x| = ≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ Ys
    class-proof₂ = simple-class-existence-theorem {xᵒ≤|x| = ≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ Ys
    class₁ = proj₁ class-proof₁
    class₂ = proj₁ class-proof₂
    proof₁ = proj₂ class-proof₁
    proof₂ = proj₂ class-proof₂

simple-class-existence-theorem {|x|-1 = |x|-1} {xᵒ = xᵒ}  {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (∃' _ exp) Ys =
  Dom class , λ xs → simple-exists-helper xs
  where
    class-proof = simple-class-existence-theorem  {|x|-1 = suc |x|-1} {xᵒ = suc xᵒ} {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys
    class = proj₁ class-proof
    proof = proj₂ class-proof
    simple-exists-helper : (xs : Vec NbgSet (suc |x|-1)) → ((n-tuple xs !∈ Dom class) ⇔ (Σ[ x ∈ NbgSet ] (simple-expression-set {|x| = suc (suc |x|-1)} {xᵒ = suc xᵒ} {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs +~ x) Ys))) -- 
    simple-exists-helper xs = record { to = to-helper
                                     ; from = from-helper
                                     }
      where
        from-helper : Σ[ x ∈ NbgSet ] (simple-expression-set {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|}  exp (xs +~ x) Ys) → n-tuple xs !∈ Dom class
        from-helper (y , exp-set) = Dom-rule-from class (n-tuple xs) ((y) , subst (_!∈ class) (sym (n-tuple-suc xs y)) (from (proof (xs +~ y)) exp-set))
        to-helper : n-tuple xs !∈ Dom class → Σ[ x ∈ NbgSet ] simple-expression-set {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp (xs +~ x) Ys
        to-helper xs∈Dom = y , to (proof (xs +~ y)) ((subst (_!∈ class) (n-tuple-suc xs y) Dom-rule-detail))
          where
            y : NbgSet
            y = (proj₁ (Dom-rule-to class (n-tuple xs) xs∈Dom))
            Dom-rule-detail : orderedPair (n-tuple xs) y !∈ class
            Dom-rule-detail = (proj₂ (Dom-rule-to class (n-tuple xs) xs∈Dom))

simple-class-existence-theorem {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (¬' exp) Ys = ∁ class , λ xs →
  ⇔-trans (∁-rule (∁ class) (n-tuple xs)) (
  ⇔-trans ((⇔-transport {P = λ x → (¬ n-tuple xs !∈ x)} (sym (∁-involutory class ))))
  (⇔-converse (proof xs)))
  where
    class-proof = simple-class-existence-theorem {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys
    class = proj₁ class-proof
    proof = proj₂ class-proof

-- simple-exists-helper  {|x|-1 = |x|-1} {xᵒ = xᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys xs = {!!}
--   where
--     class-proof = simple-class-existence-theorem  {|x|-1 = suc |x|-1} {xᵒ = suc xᵒ} {xᵒ≤|x| = s≤s xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys
--     class = proj₁ class-proof
--     proof = proj₂ class-proof
--     rule = Dom-rule class

-- class-existence-theorem : {|x|-1 xᵒ |Y| Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ suc |x|-1} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} → (exp : NbgExpression (xᵒ) Yᵒ) → (Ys : Vec NbgClass |Y|) →
--   Σ[ X ∈ NbgClass ] (∀ (xs : Vec NbgSet (suc |x|-1)) → n-tuple xs !∈ X ⇔ (expression-set {suc |x|-1} {|Y|} {xᵒ} {Yᵒ} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp xs Ys))
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(suc (i₁ ⊔ i₂))} {Yᵒ = Yᵒ} (x' i₁ ∈' x' i₂) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(suc (i ⊔ i₁))} {Yᵒ = Yᵒ} (x' i =' x' i₁) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(xᵒ₁ ⊔ xᵒ₂)} {Yᵒ = .(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (_∧'_  {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) Ys = (class₁ ∩ class₂) , λ xs → ⇔-trans (∩-rule class₁ class₂ (n-tuple xs)) (⇔-×-dist (proof₁ xs) (proof₂ xs))
--   where
--     class-proof₁ = class-existence-theorem {xᵒ≤|x| = ≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ Ys
--     class₁ = proj₁ class-proof₁
--     proof₁ : (xs₁ : Vec NbgSet (suc |x|-1)) → n-tuple xs₁ !∈ class₁ ⇔ expression-set {xᵒ≤|x| = ≤-trans (m≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (m≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₁ xs₁ Ys
--     proof₁ = proj₂ class-proof₁
--     class-proof₂ = class-existence-theorem {xᵒ≤|x| = ≤-trans (n≤m⊔n xᵒ₁ xᵒ₂) xᵒ≤|x|} {Yᵒ≤|Y| = ≤-trans (n≤m⊔n Yᵒ₁ Yᵒ₂) Yᵒ≤|Y|} exp₂ Ys
--     class₂ = proj₁ class-proof₂
--     proof₂ = proj₂ class-proof₂
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(xᵒ₁ ⊔ xᵒ₂)} {Yᵒ = .(Yᵒ₁ ⊔ Yᵒ₂)} {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} (_∨'_  {xᵒ₁} {Yᵒ₁} {xᵒ₂} {Yᵒ₂} exp₁ exp₂) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(_ ⊔ _)} {Yᵒ = .(_ ⊔ _)} (exp ⇔' exp₁) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = .(_ ⊔ _)} {Yᵒ = .(_ ⊔ _)} (exp ⇒' exp₁) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = xᵒ} {Yᵒ = Yᵒ} (∃' .xᵒ exp) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = xᵒ} {Yᵒ = Yᵒ} (∀' .xᵒ exp) Ys = {!!}
-- class-existence-theorem {|x|-1 = |x|-1} {xᵒ = xᵒ} {Yᵒ = Yᵒ} (¬' exp) Ys = {!!}
-- -- class-existence-theorem {xᵒ-1} {Yᵒ} exp Ys = {!!}
-- 
-- expression-class : {|x|-1 xᵒ |Y| Yᵒ : ℕ} → {xᵒ≤|x| : xᵒ ≤ suc |x|-1} → {Yᵒ≤|Y| : Yᵒ ≤ |Y|} → (exp : NbgExpression (xᵒ) Yᵒ) → (Ys : Vec NbgClass |Y|) → NbgClass
-- expression-class {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys = proj₁ (class-existence-theorem {xᵒ≤|x| = xᵒ≤|x|} {Yᵒ≤|Y| = Yᵒ≤|Y|} exp Ys)

m≤n⇒n≡n-m+m : {m n : ℕ} → m ≤ n → n ≡ (n ∸ m) + m
m≤n⇒n≡n-m+m {0} {n} z≤n = sym (+-identityʳ n)
m≤n⇒n≡n-m+m {(suc m)} {(suc n)} (s≤s m≤n) rewrite +-suc (n ∸ m) m = cong suc (m≤n⇒n≡n-m+m m≤n)

-- id-func = expression-class {|x|-1 = 1} {xᵒ≤|x| = s≤s (s≤s z≤n)} {Yᵒ≤|Y| = z≤n} (( (x' 0)) =' (x' 1)) []


test : NbgExpression 4 0
test = ∃' 4 ( (x' 1) ∈' x' 4)

⊘≡∁V : ⊘-class ≡ ∁ V
⊘≡∁V = ∁-involutory ⊘-class

V-full : (x : NbgSet) → x !∈ V
V-full x = from (∁-rule V x) ∁V-empty
  where
    empty = λ A → ¬ x !∈ A
    ∁V-empty = transport {P = empty} ⊘≡∁V (⊘-class-empty x)

V^1+ : (n : ℕ) → NbgClass
V^1+ zero = V
V^1+ (suc n) = ×V (V^1+ n)

isSet⇔∈V : (x : NbgClass) → isSet x ⇔ x ∈ V
isSet⇔∈V x = record { to = λ isSetx → V-full (x , isSetx)
                     ; from = λ x∈V → V , x∈V
                     }
-- { (x₁, x₂) : x₂ = x₁ }
-- { (x₁, x₂) : ∀ x₃ (x₃ ∈ x₁ ⇔ x₃ ∈ x₂) }
-- { (x₁, x₂) : ∀ x₃ (x₃ ∈ x₁ ⇒ x₃ ∈ x₂ ∧ x₃ ∈ x₂ ⇒ x₃ ∈ x₁) }
-- { (x₁, x₂) : ∀ x₃ ((¬ x₃ ∈ x₁ ∨ x₃ ∈ x₂) ∧ (¬ x₃ ∈ x₂ ∨ x₃ ∈ x₁) }
-- { (x₁, x₂) : ∀ x₃ (¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) ∧ ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁) }
-- { (x₁, x₂) : ¬ ∃ x₃ ¬ (¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) ∧ ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁) }
-- ∁ ({ (x₁, x₂) : ∃ x₃ ¬ (¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) ∧ ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁) } ∩ V^1+ 1)
-- ∁ (Dom ({ (x₁, x₂, x₃) : ¬ (¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) ∧ ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁) }) ∩ V^1+ 1)
-- ∁ (Dom (∁ { (x₁, x₂, x₃) : ¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) ∧ ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁) } ∩ V^1+ 2)) ∩ V^1+ 1)
-- ∁ (Dom (∁ ({ (x₁, x₂, x₃) : ¬ (x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂) } ∩ { (x₁, x₂, x₃) : ¬ (x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁ }) ∩ V^1+ 2)) ∩ V^1+ 1)
-- ∁ (Dom (∁ (∁ { (x₁, x₂, x₃) : x₃ ∈ x₁ ∧ ¬ x₃ ∈ x₂ } ∩ V^1+ 2 ∩ ∁ { (x₁, x₂, x₃) : x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁ }) ∩ V^1+ 2)) ∩ V^1+ 1
-- ∁ (Dom (∁ (∁ ({ (x₁, x₂, x₃) : ¬ x₃ ∈ x₂ } ∩ { (x₁, x₂, x₃) : ¬ x₃ ∈ x₂ }) ∩ V^1+ 2 ∩ ∁ { (x₁, x₂, x₃) : x₃ ∈ x₂ ∨ ¬ x₃ ∈ x₁ }) ∩ V^1+ 2)) ∩ V^1+ 1

-- ⊆isSet→isSet : ∀ (a : NbgSet) → (B : NbgClass) → B ⊆ proj₁ a → isSet B
-- ⊆isSet→isSet a B B∈a = transport {P = isSet} {!!} {!isSet b!}
