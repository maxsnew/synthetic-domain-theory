{-# OPTIONS --safe --guardedness #-}
module SDT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ : Level

record Dominance {ℓ} : Type (ℓ-suc ℓ) where
  field
    isSemiDecidableProp : Type ℓ → Type ℓ
    isSemiDecidableProp→isProp : ∀ X → isSemiDecidableProp X → isProp X
    isPropisSemiDecidableProp : ∀ X → isProp (isSemiDecidableProp X)

  hSDProp : Type (ℓ-suc ℓ)
  hSDProp = TypeWithStr ℓ isSemiDecidableProp

  isSetSDProp : isSet hSDProp
  isSetSDProp = λ (X , a) (Y , b) →
    isPropRetract (cong fst)
                  (Σ≡Prop isPropisSemiDecidableProp)
                  (section-Σ≡Prop isPropisSemiDecidableProp)
                  (isOfHLevel≡ 1 (isSemiDecidableProp→isProp X a) (isSemiDecidableProp→isProp Y b))

  -- hSDPropExt : ∀ {A B} → isSemiDecidableProp A → isSemiDecidableProp B → (A → B) → (B → A) → A ≡ B
  -- hSDPropExt = {!!}

  field
    isSemiDecidable⊤ : isSemiDecidableProp Unit*
    isSemiDecidableΣ : ∀ {A B} → isSemiDecidableProp A → ((x : A) → isSemiDecidableProp (B x)) → isSemiDecidableProp (Σ A B)

-- Domains wrt the dominance must live in the next universe in a
-- predicative theory to accommoddate this notion of lifting.
-- related: https://arxiv.org/abs/2008.01422
module LiftMonad (ΣΣ : Dominance {ℓ}) where
  module ΣΣ = Dominance ΣΣ
  open ΣΣ
  L : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  L X = Σ[ ϕ ∈ hSDProp ] (⟨ ϕ ⟩ → X)

  when_,_ : ∀ {X} → (ϕ : hSDProp) → (⟨ ϕ ⟩ → X) → L X
  when ϕ , x~ = ϕ , x~

  supp : ∀ {X} → L X → hSDProp
  supp l = fst l

  elt : ∀ {X} → (l : L X) → ⟨ supp l ⟩ → X
  elt l p = snd l p

  isSetL : ∀ {A} → isSet A → isSet (L A)
  isSetL {A} a = isSetΣ ΣΣ.isSetSDProp (λ _ → isSet→ a)

  η : ∀ {X} → X → L X
  η x = when (Unit* , isSemiDecidable⊤) , λ tt → x

  ext : ∀ {X Y} → (X → L Y) → L X → L Y
  ext k l = when ((Σ ⟨ supp l ⟩ (λ p → ⟨ supp (k (elt l p)) ⟩)) , isSemiDecidableΣ (str (supp l)) λ p → str (supp (k (elt l p)))) ,
                 λ p → elt (k (elt l (fst p))) (snd p)

  map : ∀ {X Y} → (X → Y) → L X → L Y
  map f x~ = (supp x~) , (λ p → f (elt x~ p))

  data ω : Type (ℓ-suc ℓ) where
    think : L ω → ω

  foldω : ∀ {X} → (L X → X) → ω → X
  foldω f (think x) = f ((fst x) , (λ p → foldω f (snd x p)))

  ω-is-initial : ∀ {X} → isSet X → (f : L X → X) → ∃![ h ∈ (ω → X) ] (∀ (l : L ω) → h (think l) ≡ f (map h l))
  ω-is-initial {X} a f =
    uniqueExists (foldω f)
                 (λ l → refl)
                 (λ a' → isPropΠ λ x → a (a' (think x)) (f (map a' x)))
                 (λ h hyp i o → lem h hyp o i)
    where lem : (h : ω → X) → ((x : L ω) → h (think x) ≡ f (map h x)) → ∀ o → foldω f o ≡ h o
          lem h hyp (think x) =
            f (fst x , (λ p → foldω f (snd x p))) ≡⟨ (λ i → f ((fst x) , (λ p → lem h hyp (snd x p) i))) ⟩
            f (map h x) ≡⟨ sym (hyp x) ⟩
            h (think x) ∎

  -- final algebra
  record ω+ : Type (ℓ-suc ℓ) where
    coinductive
    field
      prj : L ω+

  -- TODO
  -- isSetω+ : isSet ω+
  -- isSetω+ x y = λ x₁ y₁ → {!!}

  open ω+
  unfoldω+ : ∀ {X} → (X → L X) → X → ω+
  unfoldω+ g x .prj = supp (g x) , λ p → unfoldω+ g (elt (g x) p)

  Ω : ω+
  Ω = unfoldω+ (λ x → (Unit* , isSemiDecidable⊤) , λ _ → tt*) (lift tt)

  -- TODO
  -- ω+-is-final : ∀ {X} → isSet X → (g : X → L X) → ∃![ h ∈ (X → ω+) ] (∀ x → ω+.prj (h x) ≡ map h (g x))
  -- ω+-is-final = {!!}

  ω→ω+ : ω → ω+
  ω→ω+ = unfoldω+ (foldω (map think))

  hasLimit : ∀ {X : Type (ℓ-suc ℓ)} → (ω → X) → Type (ℓ-suc ℓ)
  hasLimit {X} chainX = ∃![ limChain ∈ (ω+ → X) ] chainX ≡ (λ x → limChain (ω→ω+ x))

  limitPt : ∀ {X : Type (ℓ-suc ℓ)} → (ω+ → X) → X
  limitPt limChain = limChain Ω

  isPropHasLimit : ∀ {X} → (chain : ω → X) → isProp (hasLimit chain)
  isPropHasLimit chain = isProp∃!

  isComplete : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  isComplete X = ∀ (chain : ω → X) → hasLimit chain

  isPropIsComplete : ∀ {X} → isProp (isComplete X)
  isPropIsComplete = isPropΠ isPropHasLimit

  isWellComplete : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  isWellComplete X = isComplete (L X)

  

  isPredomain : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  isPredomain X = isSet X × isWellComplete X

  Predomain : Type (ℓ-suc (ℓ-suc ℓ))
  Predomain = TypeWithStr (ℓ-suc ℓ) isPredomain

  PREDOMAIN : Category _ _
  PREDOMAIN = FullSubcategory (SET (ℓ-suc ℓ)) λ x → isComplete ⟨ x ⟩

module SDT (ΣΣ : Dominance {ℓ})
           (⊥-isSemiDecidable : Dominance.isSemiDecidableProp ΣΣ ⊥*)
           (Σ-is-complete : LiftMonad.isComplete ΣΣ (Dominance.hSDProp ΣΣ))
           where
  -- Do we need another axiom?

  -- The last axiom in Fiore-Rosolini is that the lifting functor L
  -- has "rank", meaning it preserves κ-filtered colimits for some
  -- regular cardinal κ.

  -- but they say it is also sufficient that L preserve reflexive
  -- coequalizers which seems maybe possible to prove?

  module ΣΣ = Dominance ΣΣ
  open ΣΣ
  open LiftMonad ΣΣ

  -- | TODO:
  -- | 1. Prove Σ is *well*-complete, i.e., a predomain
  -- | 2. Show L is a monad on PREDOMAIN
  -- | 3. Prove Well-complete objects are complete
  -- | 4. Construct DOMAIN (w/ strict maps) as the EM category of L
  -- | 5. Construct a fixed point combinator for domains

  L-unit-R : ∀ {X} → (l : L X) → ext {X} η l ≡ l
  L-unit-R l = {!!}

  L-unit-L : ∀ {X Y} → (x : X) → (k : X → L Y) → ext k (η x) ≡ k x
  L-unit-L x k = {!!}

  L-assoc : ∀ {X Y Z} (l : L X) (k : X → L Y) (h : Y → L Z) → ext (λ x → ext h (k x)) l ≡ ext h (ext k l)
  L-assoc = {!!}

  L0≡1 : L ⊥* ≡ Unit*
  L0≡1 = ua (isoToEquiv (iso (λ x → lift tt) (λ x → (⊥* , ⊥-isSemiDecidable) , λ lifted → Cubical.Data.Empty.elim (lower lifted)) (λ b → refl) λ a → Σ≡Prop (λ x → isProp→ isProp⊥*) (Σ≡Prop isPropisSemiDecidableProp (ua (uninhabEquiv lower λ x → lower (snd a x))))))

  -- The information ordering
  _⊑_ : ∀ {X : Type (ℓ-suc ℓ)} → X → X → Type (ℓ-suc ℓ)
  _⊑_ {X} x y = (∀ (ϕ : X → hSDProp) → ⟨ ϕ x ⟩ → ⟨ ϕ y ⟩)

  isProp⊑ : ∀ {X} (x y : X) → isProp (x ⊑ y)
  isProp⊑ x y =  isPropΠ (λ ϕ → isProp→ (isSemiDecidableProp→isProp _ (str (ϕ y))))

  refl⊑ : ∀ {X} (x : X) → x ⊑ x
  refl⊑ x = λ ϕ x₁ → x₁

  trans⊑ : ∀ {X}{x₁ x₂ x₃ : X} → x₁ ⊑ x₂ → x₂ ⊑ x₃ → x₁ ⊑ x₃
  trans⊑ x12 x23 = λ ϕ p → x23 ϕ (x12 ϕ p)

  all-functions-are-monotone : ∀ {X Y} (f : X → Y) → ∀ {x}{x'} → x ⊑ x' → f x ⊑ f x'
  all-functions-are-monotone f {x}{x'} x⊑x' = λ ϕ p → x⊑x' (λ x₁ → ϕ (f x₁)) p

  _⊑→_ : ∀ {X Y : Type (ℓ-suc ℓ)} (f g : X → Y) → Type (ℓ-suc ℓ)
  _⊑→_ {X}{Y} f g = ∀ x → f x ⊑ g x

  record _◃_ (X Y : Predomain) : Type (ℓ-suc ℓ) where
    field
      embed  : ⟨ X ⟩ → ⟨ Y ⟩
      project : ⟨ Y ⟩ → ⟨ X ⟩
      retraction : ∀ x → project (embed x) ≡ x
      projection : ∀ y → y ⊑ embed (project y)
