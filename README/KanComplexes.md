# Kan Complexes

The classical definition of Kan Complex is a bit tricky in Agda, as
they explicitly don't specify a choice of filler for horns, merely their
existence. Instead, we have opted to implement *Algebraic Kan Complexes*,
which are Kan Complexes with a distinguished choice of filler. This does
mean that the Category of Kan Complexes needs morphisms to preserve these
distinguished fillers.

## Implementation Notes
* The inequality in the definition of Horn seems like it could become a bit awkward down the line?
  As equality of `Fin` is decidable, it isn't *too* bad, but does pose the potential to be annoying.
* The unfolded equality in ∂Δ[_] and Λ[_,_] does better than just lifting the equality from Δ, but it still falls on it's face from time to time

## References
* https://ncatlab.org/nlab/show/Kan+complex
* https://ncatlab.org/nlab/show/weak+Kan+complex
* https://ncatlab.org/nlab/show/algebraic+Kan+complex
