{-
NameGen is intended to be treated as a linear type, 
which to my knowledge doesn't exist in Elm. 
It is generally used to create fresh variable names that haven't been used yet
The names are string-versions of integers, 
since it's impossible to pick these names in the language,
and since it's easy to get the next unused name.
As of writing, this type is used heavily by both the (hindley-milner) Typecheck.elm file and
the Continuation-Passing-Style conversion file (CPS.elm)
-}
module emerson-lang.NameGen exposing (NameGen, init, withFresh, withTwoFresh)

{-
The name generator (linear) datatype
-}
type NameGen = NameGen Int -- the main datatype

-- spawn a fresh name generator such that the first produced name will be "0"
init : NameGen
init = NameGen -1 

{- 
Produce and use a new name from the name generator, structured so as to ensure linearity.
For multiple fresh variables at once, consider using withTwoFresh instead or as a combination
-}
withFresh : (NameGen -> String -> (NameGen, a)) -> NameGen -> (NameGen, a)
withFresh f nameGen = case nameGen of
    NameGen i ->
        let newvar = String.fromInt (i + 1) in
        let newNameGen = NameGen (i + 1) in
        f newNameGen newvar

{- 
Same as using a `withFresh` immediately nested inside another `withFresh`, but of course far less verbose. 
For more fresh variables you can still nest any combination of withFresh and withTwoFresh
-}
withTwoFresh : (NameGen -> String -> String -> (NameGen, a)) -> NameGen -> (NameGen, a)
withTwoFresh f nameGen = case nameGen of
    NameGen i ->
        let newvar1 = String.fromInt (i+1) in
        let newvar2 = String.fromInt (i+2) in
        let newNameGen = NameGen (i+2) in
        f newNameGen newvar1 newvar2