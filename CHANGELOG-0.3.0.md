Version 0.3.0
===============

The library has been tested using Agda 2.8.0 and stdlib 2.3.0.

## Infrastructure changes

* Better caching, so that CI generally runs faster

## Changes affecting compatibility

### Removed modules

* `Categories.Adjoint.Equivalence.Properties`
main export `⊣equiv-preserves-diagram` is special case of `la-preserves-diagram`.

### Changes of fields

* `Categories.Diagram.Pullback`

  ```agda
  unique -> unique-diagram
  ```
* `Categories.Diagram.Pushout`
  Split `Pushout` into an `IsPushout` predicate and the data fields

### Changing definitions or names

* `Categories.Adjoint.Instance.Slice`
  Forgetful⊣Free -> TotalSpace⊣ConstantFamily

* `Categories.Category.Instance.Sets`
  ```agda
  _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ```
  to
  ```agda
  _≈_       = _≗_
  ```
  which makes `x` explicit.
	* `Categories.Functor.Slice`
	Forgetful -> TotalSpace
	Free -> ConstantFamily
	
## New modules

* `Categories.Adjoint.Instance.BaseChange`
* `Categories.Adjoint.Instance.Slice`
* `Categories.Bicategory.LocalCoequalizers`
* `Categories.Bicategory.Monad.Bimodule`
* `Categories.Bicategory.Monad.Bimodule.Homomorphism`
* `Categories.Category.Cocomplete.Properties.Construction`
* `Categories.Category.Construction.Bimodules`
* `Categories.Category.Construction.Bimodules.Properties`
* `Categories.Category.Construction.DaggerFunctors`
* `Categories.Category.Dagger.Construction.DaggerFunctors`
* `Categories.Category.Distributive.Properties`
* `Categories.Category.Instance.DagCats`
* `Categories.Category.Instance.Zero.Core`
* `Categories.Category.Instance.Zero.Properties`
* `Categories.Category.Lift.Properties`
* `Categories.Category.Monoidal.Construction.Kleisli`
* `Categories.Category.Monoidal.Construction.Kleisli.CounitalCopy`
* `Categories.Category.Monoidal.Construction.Kleisli.Symmetric`
* `Categories.Category.Monoidal.Construction.Reverse`
* `Categories.Category.Monoidal.CounitalCopy`
* `Categories.Category.Monoidal.CounitalCopy.Restriction`
* `Categories.Category.Monoidal.Symmetric.Properties`
* `Categories.Category.Restriction.Construction.Kleisli`
* `Categories.Category.Restriction.Properties.Poset`
* `Categories.Comonad.Distributive`
* `Categories.Comonad.Morphism`
* `Categories.Diagram.Coend.Colimit`
* `Categories.Diagram.Empty`
* `Categories.Diagram.End.Fubini`
* `Categories.Diagram.End.Instance.NaturalTransformations`
* `Categories.Diagram.End.Instances.NaturalTransformation`
* `Categories.Diagram.End.Limit`
* `Categories.Diagram.End.Parameterized`
* `Categories.Functor.Dagger`
* `Categories.Functor.Slice.BaseChange`
* `Categories.Monad.Commutative`
* `Categories.Monad.Commutative.Properties`
* `Categories.Monad.Distributive`
* `Categories.Monad.EquationalLifting`
* `Categories.Monad.Strong.Properties`
* `Categories.Object.Coproduct.Indexed`
* `Categories.Object.Coproduct.Indexed.Properties`
* `Categories.Object.Initial.Colimit`
* `Categories.Object.NaturalNumbers.Parametrized.Properties.F-Algebras`
* `Categories.Object.StrictInitial`

## Additions to existing modules

* `Categories.Adjoint.Properties`:
  ```agda
  la-preserves-diagram : (L⊣R : L ⊣ R) → Limit F → Limit (F ∘F L)
  ra-preserves-diagram : (L⊣R : L ⊣ R) → Colimit F → Colimit (F ∘F R)
  ```
* `Categories.Bicategory.Extras`
  ```agda
  identity₂² : id₂ ∘ᵥ id₂ ≈ id₂
  sym-assoc₂ : α ∘ᵥ β ∘ᵥ γ ≈ (α ∘ᵥ β) ∘ᵥ γ
  ∘ᵥ-distr-⊚ : (α ∘ᵥ γ) ⊚₁ (β ∘ᵥ δ) ≈ (α ⊚₁ β) ∘ᵥ (γ ⊚₁ δ)
  α⇐-⊚ : α⇐ ∘ᵥ (α ⊚₁ β ⊚₁ γ) ≈ ((α ⊚₁ β) ⊚₁ γ) ∘ᵥ α⇐
  α⇒-⊚ : α⇒ ∘ᵥ ((α ⊚₁ β) ⊚₁ γ) ≈ (α ⊚₁ β ⊚₁ γ) ∘ᵥ α⇒
  ◁-resp-≈ : α ≈ β → α ◁ f ≈ β ◁ f
  ▷-resp-≈ : α ≈ β → f ▷ α ≈ f ▷ β
  ▷-resp-sq : α ∘ᵥ β ≈ γ ∘ᵥ δ → f ▷ α ∘ᵥ f ▷ β ≈ f ▷ γ ∘ᵥ f ▷ δ
  ◁-resp-sq : α ∘ᵥ β ≈ γ ∘ᵥ δ → α ◁ f ∘ᵥ β ◁ f ≈ γ ◁ f ∘ᵥ δ ◁ f
  α⇒-▷-◁ : α⇒ ∘ᵥ ((f ▷ γ) ◁ g) ≈ (f ▷ (γ ◁ g)) ∘ᵥ α⇒
  pentagon-var : (i ▷ α⇒ ∘ᵥ α⇒) ∘ᵥ α⇒ ◁ f ≈ α⇒ ∘ᵥ α⇒
  pentagon-inv-var : α⇐ ◁ f ∘ᵥ α⇐ ∘ᵥ i ▷ α⇐ ≈ α⇐ ∘ᵥ α⇐
  pentagon-conjugate₁ : α⇐ ∘ᵥ i ▷ α⇒ ∘ᵥ α⇒ ≈ α⇒ ∘ᵥ α⇐ ◁ f
  pentagon-conjugate₂ : i ▷ α⇒ ∘ᵥ α⇒ ≈ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ f
  pentagon-conjugate₃ : α⇒ ◁ f ∘ᵥ α⇐ ≈ (α⇐ ∘ᵥ i ▷ α⇐) ∘ᵥ α⇒
  pentagon-conjugate₄ : α⇒ ∘ᵥ α⇐ ◁ f ≈ α⇐ ∘ᵥ i ▷ α⇒ ∘ᵥ α⇒
  pentagon-conjugate₅ : α⇐ ∘ᵥ i ▷ α⇒ ≈ α⇒ ∘ᵥ α⇐ ◁ f ∘ᵥ α⇐
  UnitorCoherence.unitorˡ-coherence-iso : unitorˡ ◁ᵢ g ≈ᵢ unitorˡ ∘ᵢ associator
  unitorˡ-coherence-inv : [ f ⊚₀ g ⇒ (id₁ ⊚₀ f) ⊚₀ g ]⟨ λ⇐ ◁ g ≈ λ⇐ ⇒⟨ id₁ ⊚₀ (f ⊚₀ g) ⟩ α⇐ ⟩
  unitorʳ-coherence-var₁ : [ (f ⊚₀ g) ⊚₀ id₁ ⇒ f ⊚₀ g ⊚₀ id₁ ]⟨ α⇒ ≈ ρ⇒ ⇒⟨ f ⊚₀ g ⟩ f ▷ ρ⇐ ⟩
  unitorʳ-coherence-var₂ : [ f ⊚₀ g ⇒ f ⊚₀ g ⊚₀ id₁ ]⟨ f ▷ ρ⇐ ≈ ρ⇐ ⇒⟨ (f ⊚₀ g) ⊚₀ id₁ ⟩ α⇒ ⟩
  unitorʳ-coherence-inv : [ f ⊚₀ g ⇒ (f ⊚₀ g) ⊚₀ id₁ ]⟨ f ▷ ρ⇐ ⇒⟨ f ⊚₀ g ⊚₀ id₁ ⟩ α⇐ ≈ ρ⇐ ⟩
  ```
* `Categories.Category.CartesianClosed.Properties`
  ```agda
  initial→product-initial : IsInitial ⊥ → IsInitial (⊥ × A)
  initial→strict-initial : IsInitial ⊥ → IsStrictInitial ⊥
  ```
* `Categories.Category.Cocartesian`
  ```agda
  ⊥+--id : NaturalIsomorphism (⊥ +-) idF
  -+⊥-id : NaturalIsomorphism (-+ ⊥) idF
  ```
* `Categories.Category.Construction.Functors`
  ```agda
  module ₀ (F : Bifunctor C₁ C₂ D)
  module uncurry
  ```
* `Categories.Category.Construction.Kleisli`
  ```agda
  module TripleNotation
    *∘F₁ : {f : Y ⇒ M.F.₀ Z} → f * ∘ M.F.₁ g ≈ (f ∘ g) *
    F₁∘* : {g : X ⇒ M.F.₀ Y} → M.F.₁ f ∘ g * ≈ (M.F.₁ f ∘ g) *
    *⇒F₁ : (η ∘ f) * ≈ M.F.₁ f
  ```
* `Categories.Category.Construction.TwistedArrow`
  ```agda
  Codomain : Functor TwistedArrow (𝒞.op ×ᶜ 𝒞)
  ```
* `Categories.Category.Distributive`
  ```agda
  distributeˡ⁻¹ : A × (B + C) ⇒ A × B + A × C
  distributeʳ⁻¹ : (B + C) × A ⇒ B × A + C × A
  ```
* `Categories.Category.Monoidal.Braided.Properties`
  ```agda
  assoc-reverse : [ X ⊗₀ (Y ⊗₀ Z) ⇒ (X ⊗₀ Y) ⊗₀ Z ]⟨ id ⊗₁ σ⇒ ⇒⟨ X ⊗₀ (Z ⊗₀ Y) ⟩ σ⇒ ⇒⟨ (Z ⊗₀ Y) ⊗₀ X ⟩ α⇒ ⇒⟨ Z ⊗₀ (Y ⊗₀ X) ⟩ id ⊗₁ σ⇐ ⇒⟨ Z ⊗₀ (X ⊗₀ Y) ⟩ σ⇐ ≈ α⇐ ⟩
  ```
* `Categories.Category.Monoidal.Properties`
  ```agda
  monoidal-Op : M.Monoidal C.op
  ```
* `Categories.Category.Monoidal.Reasoning`
  ```agda
  merge₁ʳ : f ⊗₁ h ∘ g ⊗₁ id ≈ (f ∘ g) ⊗₁ h
  merge₁ˡ : f ⊗₁ id ∘ g ⊗₁ h ≈ (f ∘ g) ⊗₁ h
  ```
* `Categories.Comonad`
  ```agda
  id : Comonad C
  ```
* `Categories.Diagram.Cocone.Properties`
  ```agda
  mapˡ : Functor (Cocones F) (Cocones (G ∘F F))
  mapʳ : Functor (Cocones F) (Cocones (F ∘F G))
  nat-map : Functor (Cocones G) (Cocones F)
  ```
* `Categories.Diagram.Coend.Properties`
  ```agda
  build-Coend : Coequalizer D s t → Coend P
  ```
* `Categories.Diagram.Coequalizer`
  ```agda
  up-to-iso-triangle : (coe₁ coe₂ : Coequalizer h i) → _≅_.from (up-to-iso coe₁ coe₂) ∘ Coequalizer.arr coe₁ ≈ Coequalizer.arr coe₂
  Coequalizers : Set (o ⊔ ℓ ⊔ e)
  Coequalizers = {A B : Obj} → (f g : A ⇒ B) → Coequalizer f g
  ```
* `Categories.Diagram.Coequalizer.Properties`
  ```agda
  splitCoequalizer⇒Coequalizer : (t : B ⇒ A) (s : C ⇒ B) (eq : e ∘ f ≈ e ∘ g) (tisSection : f ∘ t ≈ id) (sisSection : e ∘ s ≈ id) (sq : s ∘ e ≈ g ∘ t) → IsCoequalizer f g e
  splitCoequalizer⇒Coequalizer-sym : (t : B ⇒ A) (s : C ⇒ B) (eq : e ∘ f ≈ e ∘ g) (tisSection : g ∘ t ≈ id) (sisSection : e ∘ s ≈ id) (sq : s ∘ e ≈ f ∘ t) → IsCoequalizer f g e
  ⇒coequalize : (α : A₁ ⇒ A₂) (β : B₁ ⇒ B₂) (sq₁ : CommutativeSquare α f₁ f₂ β) (sq₂ : CommutativeSquare α g₁ g₂ β)(coeq₂ : Coequalizer f₂ g₂) → (arr coeq₂ ∘ β) ∘ f₁ ≈ (arr coeq₂ ∘ β) ∘ g₁
  ⇒MapBetweenCoeq : (α : A₁ ⇒ A₂) (β : B₁ ⇒ B₂) (sq₁ : CommutativeSquare α f₁ f₂ β) (sq₂ : CommutativeSquare α g₁ g₂ β)(coeq₁ : Coequalizer f₁ g₁) → (coeq₂ : Coequalizer f₂ g₂) → obj coeq₁ ⇒ obj coeq₂
  ⇒MapBetweenCoeqSq : (α : A₁ ⇒ A₂) (β : B₁ ⇒ B₂) (sq₁ : CommutativeSquare α f₁ f₂ β) (sq₂ : CommutativeSquare α g₁ g₂ β)(coeq₁ : Coequalizer f₁ g₁) → (coeq₂ : Coequalizer f₂ g₂) → CommutativeSquare β (arr coeq₁) (arr coeq₂) (⇒MapBetweenCoeq coeq₁ coeq₂)
  CoeqOfIsomorphicDiagram : (coeq : Coequalizer f g ) (a : A ≅ A') (b : B ≅ B') → Coequalizer (_≅_.from b ∘ f ∘ _≅_.to a) (_≅_.from b ∘ g ∘ _≅_.to a)
  module CoequalizerOfCoequalizer
  ```
* `Categories.Diagram.Colimit.Properties`
  ```agda
  build-colim : Coequalizer s t → Colimit F
  ```
* `Categories.Diagram.Cone.Properties`
  ```agda
  mapˡ : Functor (Cones F) (Cones (G ∘F F))
  mapʳ : Functor (Cones F) (Cones (F ∘F G))
  nat-map : Functor (Cones F) (Cones G)
  ```
* `Categories.Diagram.End.Properties`
  ```agda
  end-η : (F : Functor E (Functors (Product (Category.op C) C) D))
    {{ef : ∫ F}} {{eg : ∫ G}} → end ef ⇒ end eg
  end-unique : (ω₁ ω₂ : ∫ F) → ∫.E ω₁ ≅ ∫.E ω₂
  end-identity : (F : Bifunctor (Category.op C) C D) {{ef : ∫ F}} → end-η (idN {F = F}) ≈ id
  end-η-commute : {{ef : ∫ F}} {{eg : ∫ G}} (α : NaturalTransformation F G)
    (c : C.Obj) → ∫.dinatural.α eg c ∘ end-η α ≈ α .η (c , c) ∘ ∫.dinatural.α ef c
  end-η-resp-≈ : {{ef : ∫ F}} {{eg : ∫ G}} {α β : NaturalTransformation F G} → α ≃ⁿ β →
    end-η α ≈ end-η β
  end-resp-≅ : (F≃G : F ≃ⁱ G) {{ef : ∫ F}} {{eg : ∫ G}} → ∫.E ef ≅ ∫.E eg
  build-End : Equalizer D s t → ∫ P
```
* `Categories.Diagram.Limit.Properties`
  ```agda
  build-lim : {OP : IndexedProductOf (Functor.₀ F)}
    {MP : IndexedProductOf λ f → Functor.₀ F (Morphism.cod f)} →
    Equalizer MP.⟨ (λ f → F.₁ (Morphism.arr f) ∘ OP.π (Morphism.dom f)) ⟩
              MP.⟨ (λ f → OP.π (Morphism.cod f)) ⟩ →
    Lim.Limit F
  ```
* `Categories.Diagram.Pullback.Properties`
  ```agda
  module PullbackPartingLaw (ABDE : i ∘ f ≈ k ∘ h) (BCEF : j ∘ g ≈ l ∘ i) (pbᵣ : IsPullback g i j l)
  PullbackPartingLaw.leftPullback⇒bigPullback : IsPullback f h i k → IsPullback (g ∘ f) h j (l ∘ k)
  PullbackPartingLaw.bigPullback⇒leftPullback : IsPullback (g ∘ f) h j (l ∘ k) → IsPullback f h i k
```
* `Categories.Function.Instance.Twisted`
  ```agda
  Twistⁿⁱ : ∀ {F G : Functor (C.op ×ᶜ C) D } → (F ≃ G) → Twist F ≃ Twist G
  ```
* `Categories.Functor.Properties`
  ```agda
  PreservesCoequalizers : Functor C D → Set
  PreservesCoequalizers {coeq : Coequalizer C f g} → IsCoequalizer D (F₁ f) (F₁ g) (F₁ (arr coeq))
  ```
* `Categories.Monad.Strong`
  ```agda
  strength-natural-id : (f : X ⇒ Y) → t.η (Y , Z) ∘ (f ⊗₁ id) ≈ F₁ (f ⊗₁ id) ∘ t.η (X , Z)
  record RightStrength (V : Monoidal C) (M : Monad C)
  record RightStrongMonad (V : Monoidal C)
  ```
* `Categories.Morphism.Reasoning.Core`
  Introduction of new re-associators on compositions of 4 morphisms.
  Each successive association is given a Greek letter, from 'α' associated all
  the way to the left, to 'ε' associated all the way to the right. Then,
  'assoc²XY' is the proof that X is equal to Y. Explicitly:
   * 
  ```agda
  α = ((i ∘ h) ∘ g) ∘ f
  ```
  *
  ```agda
  β = (i ∘ (h ∘ g)) ∘ f
  ```
    * 
	```agda
	γ = (i ∘ h) ∘ (g ∘ f)
	```
  * 
  ```agda
  δ = i ∘ ((h ∘ g) ∘ f)
  ```
  * 
  ```agda
  ε = i ∘ (h ∘ (g ∘ f))
  ```
* `Categories.Object.Duality`
  ```agda
  IndexedCoproductOf⇒coIndexedProductOf : IndexedCoproductOf P → IndexedProductOf P
  ```
* `Categories.Object.Product.Indexed.Properties`
  ```agda
  lowerAllProductsOf : ∀ j → AllProductsOf (i ⊔ j) → AllProductsOf i
  ```
