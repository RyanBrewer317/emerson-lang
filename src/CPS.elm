{-
Convert the type-annotated AST from Typecheck.elm to
a Continuation-Passing-Style AST, for easier conversion
to webassembly later on. 
Primary reference is the book "Compiling With Continuations" by Andrew Appel of Princeton
The main divergences from the book are my much more restricted use of CPS control-flow features, 
and how much information I've chosen to keep in the CPS AST from the source code.
Eventually I hope to do refinement-type-checking on the CPS AST, if I can get the mapping to the source code right
-}
module CPS exposing (toCPS, Value(..), CExpr(..), AccessPath(..))
import Typecheck
import Lang exposing (..)
import NameGen exposing (NameGen)
import Typecheck exposing (Type(..), Annot(..))
import Dict exposing (Dict)

{- atomic CPS values -}
type Value = Var String --Type
        --    | Label String
           | Bool Int
           | Int Int
           | Float Float
           | String String

-- typeOf : Value -> Type
-- typeOf val = case val of
--     Var _ t -> t
--     Bool _ -> TBool
--     Int _ -> TNum
--     Float _ -> TNum
--     String _ -> TString

{-used for pointer operations like offsets-}
type AccessPath = OFFp Int
                -- | SELp Int AccessPath

{-a continuation expression, in term of atomic CPS `Value`s. -}
type CExpr  = Tuple (List (Value, AccessPath)) String (Located CExpr)
            -- | Select Int Value String (Located CExpr)
            -- | Offset Int Value String (Located CExpr)
            | Call Value (List Value)
            | Funcs (List (String, List String, (Located CExpr))) (Located CExpr)
            -- | Switch Value (List Value)
            | PrimOp String (List Value) (List String) (List (Located CExpr))

type alias RenameTable = Dict String String

convertExpr : NameGen -> RenameTable -> Located Annot -> (NameGen -> RenameTable -> Value -> (NameGen, (RenameTable, Located CExpr))) -> (NameGen, (RenameTable, Located CExpr))
convertExpr gen renames loc cont = case loc.value of
    AnnotPrim {val{-, typ-}} ->
        case val of
            Ident n -> Dict.get n renames |> Maybe.map (\var->cont gen renames (Var var {-typ-})) |> Maybe.withDefault (NameGen.withFresh (\gen2 v->Var (v++n) {-typ-} |> cont gen2 (Dict.insert n (v++n) renames)) gen)
            NumberLit n -> Float n |> cont gen renames
            CharLit c -> Char.toCode c |> Int |> cont gen renames
            StringLit s -> String s |> cont gen renames
            _ -> Debug.todo "unknown annotprim"
    AnnotTuple {vals{-, typ-}} ->
        case vals of
            [] -> Int 0 |> cont gen renames
            _ -> gen |> 
                    NameGen.withFresh (\gen2 var->
                        convertTupleHelper gen2 renames vals (\vars gen3 renames2->
                            let (gen4, (renames3, c)) = Var var {-typ-} |> cont gen3 renames2 in 
                            (gen4, (renames3, Tuple (List.map (\v->(v, OFFp 0)) vars) var c |> locmap loc))
                        )
                    )
    AnnotPrefix {op, right{-, typ-}} -> 
        case op of
            "-" -> gen |> 
                    NameGen.withFresh (\gen2 var->
                        convertExpr gen2 renames right (\gen3 renames2 v->
                            let (gen4, (renames3, c)) = Var var {-TNum-} |> cont gen3 renames2 in 
                            (gen4, (renames3, PrimOp "~" [v] [var] [c] |> locmap loc))
                        )
                    )
            "!" -> gen |> 
                    NameGen.withTwoFresh (\gen2 var1 var2->
                        convertExpr gen2 renames right (\gen3 renames2 v->
                            let (gen4, (renames3, c)) = Var var2 {-TBool-} |> cont gen3 renames2 in 
                            (gen4, (renames3, Funcs [(var1, [var2], c)] (PrimOp op [v] [] [Call (Var var1 {-typ-}) [Bool 1] |> locmap loc, Call (Var var1 {-typ-}) [Bool 0] |> locmap loc] |> locmap loc) |> locmap loc))
                        )
                    )
            _ -> Debug.todo <| "unknown prefix " ++ op
    AnnotInfix {left, op, right{-, typ-}} -> 
        let oneResult = \_->gen |> 
                NameGen.withFresh (\gen2 var->
                    {-let outputType = (case typ of
                            TFunc _ t -> t
                            _ -> TBool) in-}
                    let (gen3, (renames2, c)) = Var var {-outputType-} |> cont gen2 renames in 
                    convertTupleHelper gen3 renames2 [left, right] (\a gen4 renames3->
                        (gen4, (renames3, PrimOp op a [var] [c] |> locmap loc))
                    )
                ) in
        let twoBranch = \_->gen |> 
                NameGen.withTwoFresh (\gen2 var1 var2->
                    let (gen3, (renames2, c)) = Var var2 {-TBool-} |> cont gen2 renames in 
                    convertTupleHelper gen3 renames2 [left, right] (\a gen4 renames3->
                        (gen4, (renames3, Funcs [(var1, [var2], c)] (PrimOp op a [] [Call (Var var1 {-typ-}) [Bool 1] |> locmap loc, Call (Var var1 {-typ-}) [Bool 0] |> locmap loc] |> locmap loc) |> locmap loc))
                    )
                ) in
        case op of
            "+" -> oneResult()
            "<" -> twoBranch()
            _ -> oneResult()
    AnnotFunc {args, block, typ} -> gen |> 
        NameGen.withTwoFresh (\gen2 var1 var2->
            let (inputType, outputType) = (case typ of
                    TFunc t u -> (t, u)
                    Forall _ (TFunc t u) -> (t, u)
                    _ -> Debug.todo <| "nonfunc func " ++ Debug.toString typ
                    ) in
            let (gen3, (renames2, renamedArgs)) = List.foldr (\(arg, _) (genx, (renamesx, soFar))->
                        String.uncons arg |> Maybe.map (\(char, _)->
                        if Char.isAlpha char then 
                            genx |> NameGen.withFresh (\genx2 v->(genx2, (Dict.insert arg (v++arg) renames, (v++arg)::soFar)))
                        else
                            (genx, (renamesx, arg::soFar)))
                        |> Maybe.withDefault (genx, (renamesx, arg::soFar))
                    ) (gen2, (Dict.empty, [])) args in
            let (gen4, (renames3, c)) = Var var2 {-(addArg inputType outputType (TFunc outputType outputType))-} |> cont gen3 renames in 
            let (gen5, (_, bod)) = convertExpr gen4 renames2 block (\gen6 renames5 z->(gen6, (renames5, Call (Var var1 {-(TFunc outputType outputType)-}) [z] |> locmap loc))) in
            (gen5, (renames3, Funcs [(var2, (renamedArgs++[var1]), bod)] c |> locmap loc))
        )
    AnnotCall {func, args, typ} -> gen |>
        NameGen.withTwoFresh (\gen2 var1 var2->
            case args.value of
                AnnotTuple {vals} -> 
                    convertTupleHelper gen2 renames vals (\vars gen3 renames2->
                        let (gen4, (renames3, c)) = Var var2 {-typ-} |> cont gen3 renames2 in
                        let (gen5, (renames5, foo)) = convertExpr gen4 renames3 func (\gen6 renames4 f-> (gen6, (renames4, Call f (vars++[Var var1 {-(TFunc typ typ)-}]) |> locmap loc))) in
                        (gen5, (renames5, Funcs [(var1, [var2], c)] foo |> locmap loc))
                    )
                _ -> 
                    convertTupleHelper gen2 renames [args] (\vars gen3 renames2->
                        let (gen4, (renames3, c)) = Var var2 {-typ-} |> cont gen3 renames2 in
                        let (gen5, (renames5, foo)) = convertExpr gen4 renames3 func (\gen6 renames4 f-> (gen6, (renames4, Call f (vars++[Var var1 {-(TFunc typ typ)-}]) |> locmap loc))) in
                        (gen5, (renames5, Funcs [(var1, [var2], c)] foo |> locmap loc))
                    )
        )
    AnnotLet {name, expr, val, typ} ->
        let varType = Typecheck.typeOf val.value in
        convertExpr gen renames (locmap loc <| AnnotCall {args=val, typ=typ, func=locmap loc <| AnnotFunc {args=[(name, varType)], block=expr, typ=TFunc varType typ}}) cont
    _ -> Debug.todo "unfinished case convertExpr"--cont gen (Var "this shouldn't happen..." TBool)

addArg inputType outputType argType = case inputType of
    TTuple [] -> TFunc argType outputType
    TTuple ts -> TFunc (TTuple (ts++[argType])) outputType
    _ -> TFunc (TTuple ([inputType, argType])) outputType

convertTupleHelper : NameGen -> RenameTable -> List (Located Annot) -> (List Value -> NameGen -> RenameTable -> (NameGen, (RenameTable, Located CExpr))) -> (NameGen, (RenameTable, Located CExpr))
convertTupleHelper gen renames vals cont =
    let g gen2 renames2 exprs vars = (case exprs of
            e::rest -> convertExpr gen2 renames2 e (\gen3 renames3 v->g gen3 renames3 rest (v::vars))
            [] -> cont (List.reverse vars) gen2 renames2) in
    g gen renames vals []

toCPS annotAST = convertExpr NameGen.init Dict.empty annotAST (\gen renames val->(gen, (renames, Call (Var "halt") [val] |> locmap annotAST)))