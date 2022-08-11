module Optimize exposing (..)
import Dict exposing (Dict)
import CPS exposing (..)
import emerson-lang.Lang exposing (Located, locmap)

type Fact = FuncFact {formal_args : (List String), body : Located CExpr, arity : Int, irreducible : Bool}
          | TupleFact (List (Value, AccessPath))
          | IntervalFact {min : Float, max : Float}
          | EmptyFact 

type alias Facts = Dict String {fact : Fact, used : Int, escaped : Int}

type FactError = NotAFact
               | NotInFacts String

factFromVal : Facts -> Value -> Result FactError (String, {fact : Fact, used : Int, escaped : Int})
factFromVal facts val = case val of
    Var n -> Dict.get n facts |> Maybe.map Ok |> Maybe.withDefault (Err <| NotInFacts n) |> Result.map(\fact->(n, fact))
    _ -> Err NotAFact

findFacts : Facts -> Located CExpr -> Facts
findFacts facts ast = 
        case ast.value of
            Tuple vals var cont -> 
                let newFacts = Dict.insert var {fact=TupleFact vals, used=0, escaped=0} facts in
                List.foldr (\(val, _) fs->
                    case factFromVal fs val of
                        Ok (n, fact)->Dict.insert n {fact|escaped=fact.escaped+1,used=fact.used+1} fs
                        Err NotAFact->fs
                        Err (NotInFacts n)->Dict.insert n {fact=EmptyFact, used=0, escaped=1} fs
                ) (findFacts newFacts cont) vals
            Call func args -> 
                let newFacts = (
                        List.foldr (\arg fs->
                            case factFromVal fs arg of
                                Ok (n, fact) -> Dict.insert n {fact|escaped=fact.escaped+1,used=fact.used+1} fs
                                Err NotAFact -> fs
                                Err (NotInFacts n) -> Dict.insert n {fact=EmptyFact, used=0, escaped=1} fs
                        ) facts args) in
                case factFromVal newFacts func of
                    Ok (n, fact)->
                        case fact.fact of
                            FuncFact f -> Dict.insert n {fact=FuncFact{f | arity=List.length args},used=fact.used+1,escaped=fact.escaped} newFacts
                            _ -> Dict.insert n {fact|used=fact.used+1} newFacts
                    Err NotAFact->newFacts
                    Err (NotInFacts n)->Dict.insert n {fact=EmptyFact, used=0, escaped=0} newFacts
            Funcs funcs dom ->
                let funcFacts = List.foldr (\(func, args, blockLoc) fs->
                            List.foldr (\arg fs2->
                                Dict.insert arg {fact=EmptyFact, used=0, escaped=0} fs2
                            ) fs (args) |>
                            (\facts2->findFacts facts2 blockLoc) |>
                            Dict.insert func {fact=FuncFact {formal_args=args, body=blockLoc, arity=0, irreducible=False}, used=0, escaped=0}
                        ) facts funcs in
                findFacts funcFacts dom
            PrimOp op args mbvar branches ->
                let do = \f-> case mbvar of
                            [var] ->
                                (case args of
                                    [arg1, arg2]->
                                        case arg1 of
                                            Var n ->
                                                Dict.get n facts |> Maybe.andThen (\fact->
                                                let newFacts = Dict.insert n {fact|used=fact.used+1} facts in
                                                case fact.fact of
                                                    IntervalFact interval ->
                                                        case arg2 of
                                                            Var m -> 
                                                                Dict.get m newFacts |> Maybe.map (\fact2->
                                                                let newFacts2 = Dict.insert m {fact2|used=fact2.used+1} newFacts in
                                                                case fact2.fact of
                                                                    IntervalFact interval2 ->
                                                                        Dict.insert var {fact=IntervalFact {min=f interval.min interval2.min, max=f interval.max interval.max}, used=0, escaped=0} newFacts2
                                                                    _-> Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts2)
                                                            Int m  -> Just <| Dict.insert var {fact=IntervalFact {min=f (toFloat m) interval.min, max=f (toFloat m) interval.max}, used=0, escaped=0} newFacts
                                                            Bool i -> Just <| Dict.insert var {fact=IntervalFact {min=f (toFloat i) interval.min, max=f (toFloat i) interval.max}, used=0, escaped=0} newFacts
                                                            Float m-> Just <| Dict.insert var {fact=IntervalFact {min=f m interval.min, max=f m interval.max}, used=0, escaped=0} newFacts
                                                            String _ -> Just <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts
                                                    _ -> Just <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                |> Maybe.withDefault (
                                                    let newFacts = Dict.insert n {fact=EmptyFact, used=0, escaped=0} facts in
                                                    case arg2 of
                                                        Var m -> 
                                                            Dict.get m newFacts |> Maybe.map (\fact2->
                                                            Dict.insert m {fact2|used=fact2.used+1} <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                            |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        _ -> Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                            Int n ->
                                                case arg2 of
                                                    Var m ->
                                                        Dict.get m facts |> Maybe.andThen (\fact->
                                                        let newFacts = Dict.insert m {fact|used=fact.used+1} facts in
                                                        case fact.fact of
                                                            IntervalFact interval ->
                                                                Just <| Dict.insert var {fact=IntervalFact {min=f (toFloat n) interval.min, max=f (toFloat n) interval.max}, used=0, escaped=0} newFacts
                                                            _ -> Just <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} facts)
                                                    _ -> Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts
                                            Bool i -> 
                                                case arg2 of
                                                    Var m -> 
                                                        Dict.get m facts |> Maybe.andThen (\fact->
                                                        let newFacts = Dict.insert m {fact|used=fact.used+1} facts in
                                                        case fact.fact of
                                                            IntervalFact interval ->
                                                                Just <| Dict.insert var {fact=IntervalFact {min=f (toFloat i) interval.min, max=f (toFloat i) interval.max}, used=0, escaped=0} newFacts
                                                            _ -> Just <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} facts)
                                                    _ -> Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts
                                            Float n ->
                                                case arg2 of
                                                    Var m ->
                                                        Dict.get m facts |> Maybe.andThen (\fact->
                                                        let newFacts = Dict.insert m {fact|used=fact.used+1} facts in
                                                        case fact.fact of
                                                            IntervalFact interval ->
                                                                Just <| Dict.insert var {fact=IntervalFact {min=f n interval.min, max=f n interval.max}, used=0, escaped=0} newFacts
                                                            _ ->Just <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} facts)
                                                    _-> Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts
                                            String _ -> 
                                                case arg2 of
                                                    Var m -> Dict.get m facts |> Maybe.map (\fact->
                                                        let newFacts = Dict.insert m {fact|used=fact.used+1} facts in
                                                        Dict.insert var {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} <| Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts)
                                                    _ -> Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts
                                    _ -> Debug.todo "dummy value")
                            _ -> Debug.todo "dummy value" in
                let opfacts = (case op of
                        "+" -> do(+)
                        "-" -> do(-)
                        "*" -> do(*)
                        "/" -> do(/)
                        "^" -> do(^)
                        "%" -> do(\f1 f2->let d = f1/f2 in let rem = d - toFloat (floor d) in rem*f2)
                        _ -> 
                            case mbvar of
                                [var] ->
                                    let newFacts = Dict.insert var {fact=EmptyFact, used=0, escaped=0} facts in
                                    case args of
                                        [arg1, arg2]->
                                            case arg1 of
                                                Var n->
                                                    let newFacts2 = Dict.get n newFacts |> Maybe.map(\fact->Dict.insert n {fact|used=fact.used+1} newFacts) |> Maybe.withDefault (Dict.insert n {fact=EmptyFact, used=0, escaped=0} newFacts) in
                                                    case arg2 of
                                                        Var m ->
                                                            Dict.get m newFacts2 |> Maybe.map (\fact->Dict.insert m {fact|used=fact.used+1} newFacts2) |> Maybe.withDefault (Dict.insert m {fact=EmptyFact, used=0, escaped=0} newFacts2)
                                                        _ -> newFacts2
                                                _ -> 
                                                    case arg2 of
                                                        Var n ->
                                                            Dict.get n newFacts |> Maybe.map (\fact->Dict.insert n {fact|used=fact.used+1} newFacts) |> Maybe.withDefault (Dict.insert n {fact=EmptyFact, used=0, escaped=0} newFacts)
                                                        _ -> newFacts
                                        _ -> newFacts
                                _ -> facts) in
                List.foldr (\branch facts2->Dict.union facts2 <| findFacts opfacts branch) (Dict.empty) branches

subValue : String -> Value -> Value -> Value
subValue var1 var2 val = case val of
    Var x -> if x == var1 then var2 else Var x
    _ -> val

sub : String -> Value -> Located CExpr -> Located CExpr
sub var1 var2 cexpr = case cexpr.value of
    Tuple vals var cont -> Tuple (List.foldr (\(val, path) vals2 -> (subValue var1 var2 val, path) :: vals2) [] vals |> List.reverse) var (sub var1 var2 cont) |> locmap cexpr
    Call foo args -> Call (subValue var1 var2 foo) (List.map (subValue var1 var2) args) |> locmap cexpr
    Funcs funcs dom -> Funcs (List.map (\(f, args, b)->(f, args, sub var1 var2 b)) funcs) (sub var1 var2 dom) |> locmap cexpr
    PrimOp op args mbvar branches -> PrimOp op (List.map (subValue var1 var2) args) mbvar (List.map (\loc->sub var1 var2 loc) branches) |> locmap cexpr

phase1 : Facts -> Located CExpr -> Located CExpr
phase1 facts stmt =  case stmt.value of
    Funcs funcs domain -> 
        let newFuncs = List.filter (\(f, _, _)->Dict.get f facts |> Maybe.map(\fact->fact.used > 1 || fact.escaped > 0) |> Maybe.withDefault True) funcs in
        if List.length newFuncs > 0 then
            Funcs (List.map (\(f, args, bod)->(f, args, phase1 facts bod)) newFuncs) (phase1 facts domain) |> locmap stmt
        else
            phase1 facts domain
    Call func args -> 
        case func of
            Var f -> 
                case Dict.get f facts of
                    Just fact->
                        case fact.fact of
                            FuncFact {body, formal_args}->
                                if fact.used == 1 && fact.escaped == 0 then 
                                    phase1 facts <|
                                        List.foldr (\(farg, arg) bod->
                                            sub farg arg bod
                                        ) body (List.map2 Tuple.pair formal_args args)
                                else 
                                    Call func args |> locmap stmt
                            EmptyFact ->Call func args |> locmap stmt
                            _ -> Debug.todo <| "nonfunc fact for " ++ f
                    _ -> Debug.todo <| "no fact for " ++ f
            _ -> {-if args == [] then Call (Var "halt") [func] |> locmap stmt else-} Debug.todo "nonvar getting called"
    PrimOp op args mbvar branches -> 
        case mbvar of
            [var] -> case branches of
                [cont] -> 
                    let res = \_->PrimOp op args mbvar [phase1 facts cont] |> locmap stmt in
                    case Dict.get var facts of
                        Just fact -> 
                            if fact.used == 0 then
                                case op of
                                    "+" -> res()
                                    "-" -> res()
                                    "/" -> 
                                        List.tail args |> Maybe.andThen (\tail->
                                        List.head tail |> Maybe.andThen (\denom->
                                        case denom of 
                                            Float f-> if f == 0 then Just (res()) else Just (phase1 facts cont)
                                            Int i -> if i == 0 then Just (res()) else Just (phase1 facts cont)
                                            _ -> Nothing))
                                        |> Maybe.withDefault (res())
                                    "*" -> res()
                                    "^" -> res()
                                    "%" -> res()
                                    _ -> phase1 facts cont
                            else
                                res()
                        _ -> Debug.todo <| "no fact for " ++ var
                _ -> Debug.todo "binds variable but has non-one branches"
            _ -> PrimOp op args mbvar (List.map (phase1 facts) branches) |> locmap stmt
    _ -> stmt