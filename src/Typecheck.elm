module emerson-lang.Typecheck exposing (..)
import emerson-lang.Lang exposing (..)
import Dict
import NameGen exposing (NameGen)

type Type = TBool
          | TNum
          | TChar
          | TString
          | TFunc Type Type
          | TTuple (List Type)
          | TVar String
          | Forall (List Type) Type
          | ADT String (List Type)

type Annot = AnnotPrim   {val : Expr, typ : Type}
           | AnnotFunc   {args : (List (String, Type)), block : Located Annot, typ : Type}
           | AnnotCall   {func : Located Annot, args : Located Annot, typ : Type}
           | AnnotIf     {cond : Located Annot, cons : Located Annot, alt : Located Annot, typ : Type}
           | AnnotTuple  {vals : (List (Located Annot)), typ : Type}
           | AnnotArray  {vals : (List (Located Annot)), typ : Type}
           | AnnotPrefix {op : String, right : Located Annot, typ : Type}
           | AnnotInfix  {left : Located Annot, op : String, right : Located Annot, typ : Type}
           | AnnotIndex  {coll : Located Annot, idx : Located Annot, typ : Type}
           | AnnotLet    {name : String, val : Located Annot, expr : Located Annot, typ : Type}

-- evalTypeLit : TypeLit -> Type
-- evalTypeLit t = case t of
--     TNumLit -> TNum
--     TBoolLit -> TBool
--     TFuncLit u v -> TFunc (evalTypeLit u) (evalTypeLit v)

type Constraint = Equation Type Type

type alias Scope = Dict.Dict String Type

typeToStringHelper : Type -> String
typeToStringHelper t = case t of
    TBool -> "Bool"
    TNum -> "Number"
    TChar -> "Char"
    TString -> "String"
    TFunc u v -> typeToStringHelper u ++ "->" ++ typeToStringHelper v
    TTuple ts -> "(" ++ String.join ", " (ts |> List.map typeToStringHelper) ++ ")"
    TVar n -> n
    ADT n ts -> n ++ "<" ++ String.join ", " (ts |> List.map typeToStringHelper) ++ ">"
    Forall vars u -> case vars of
        [] -> typeToStringHelper u
        _ -> 
            let (showVars, showType, _) = List.foldr (\tvar (showvars, typ, supply)->
                    case tvar of 
                        TVar _->case supply of
                            [] -> ("ba"::showvars, sub tvar (TVar "ba") typ, [])
                            x::xs -> (x :: showvars, sub tvar (TVar x) typ, xs)
                        _->("" :: showvars, typ, supply)) ([], u, String.toList "abcdefghijklmnopqrstuvwxyz" |> List.map String.fromChar) vars in
            typeToStringHelper showType

typeToString : Type -> String
typeToString t = case t of
    Forall _ _ -> typeToStringHelper t
    _ -> typeToStringHelper <| generalize (Dict.empty) t (Forall [] t)

locToPosString : Located a -> String
locToPosString loc = "("++(
    case loc.start of 
        (row, col)->String.fromInt row++", "++String.fromInt col
    )++")"
typeMismatch : Located a -> Type -> Type -> String
typeMismatch loc t u = "TypeError " ++ locToPosString loc ++ ": expected " ++ typeToString t ++ ", got " ++ typeToString u
nameErr : Located a -> String -> String
nameErr loc n = "NameError " ++ locToPosString loc ++ ": unknown identifier " ++ n

argsToType : List (String, Type) -> Type
argsToType args = case args of
    [(_, t)] -> t
    _ -> TTuple <| List.map Tuple.second args

typecheckExpr : Scope -> NameGen -> Located Expr -> Result String (NameGen, Located Annot, List (Located Constraint))
typecheckExpr scope gen loc = 
    case loc.value of
        Ident n -> case Dict.get n scope of
            Just t -> instantiate gen t |> (\(gen2, t2)->Ok (gen2, AnnotPrim {val=loc.value, typ=t2} |> locmap loc, []))
            Nothing -> Err <| nameErr loc n
        Function args body ->
            let (gen2, argTypes) = List.foldr (\ident (genx, argsSoFar) -> NameGen.withFresh(\genx2 v-> (genx2, ((ident, TVar v)::argsSoFar))) genx) (gen, []) args in 
            let newScope = Dict.union (Dict.fromList (argTypes)) scope in
            typecheckExpr newScope gen2 body
            |> Result.map (\(gen3, bodyAnnotLoc, bodyConstraints)->
                let argsType = argsToType argTypes in
                let bodyType = typeOf bodyAnnotLoc.value in
                let exprType = TFunc argsType bodyType in
                ( gen3
                , AnnotFunc {args=argTypes, block=bodyAnnotLoc, typ=exprType} |> locmap loc
                , bodyConstraints)
            )
        Call foo bar -> 
            typecheckExpr scope gen foo |> Result.andThen (\(gen2, fooAnnotLoc, fooConstraints)->
            typecheckExpr scope gen2 bar
            |> Result.map (\(gen3, barAnnotLoc, barConstraints)->
                NameGen.withFresh (\gen4 v-> 
                    let exprType = TVar v in
                    let fooType = typeOf fooAnnotLoc.value in
                    let barType = typeOf barAnnotLoc.value in
                    ( gen4
                    , (AnnotCall {func=fooAnnotLoc, args=barAnnotLoc, typ=exprType} |> locmap loc
                    , locmap loc (Equation fooType (TFunc barType exprType))::
                      fooConstraints++barConstraints
                    ))
                ) gen3
                |> (\(gen4, (annCall, consts))->(gen4, annCall, consts))
            ))
        BoolLit _ -> Ok (gen, AnnotPrim {val=loc.value, typ=TBool} |> locmap loc, [])
        NumberLit _ -> Ok (gen, AnnotPrim {val=loc.value, typ=TNum} |> locmap loc, [])
        If cond cons alt ->
            typecheckExpr scope gen cond |> Result.andThen (\(gen2, condAnnotLoc, condConstraints)->
            typecheckExpr scope gen2 cons |> Result.andThen (\(gen3, consAnnotLoc, consConstraints)->
            typecheckExpr scope gen3 alt  |> Result.map     (\(gen4, altAnnotLoc , altConstraints )->
            NameGen.withFresh(\gen5 v->
                let exprType = TVar v in
                let condType = typeOf condAnnotLoc.value in
                let consType = typeOf consAnnotLoc.value in
                let altType  = typeOf altAnnotLoc.value in
                ( gen5
                , ( AnnotIf {cond=condAnnotLoc, cons=consAnnotLoc, alt=altAnnotLoc, typ=exprType} |> locmap loc
                  , locmap cond (Equation condType TBool   ) ::
                    locmap cons (Equation consType exprType) ::
                    locmap alt  (Equation altType  exprType) ::
                    condConstraints++consConstraints++altConstraints
                ))
            ) gen4 
            |> (\(gen5, (annIf, ifConsts))->(gen5, annIf, ifConsts)))))
        CharLit _ -> Ok (gen, AnnotPrim {val=loc.value, typ=TChar} |> locmap loc, [])
        StringLit _ -> Ok (gen, AnnotPrim {val=loc.value, typ=TString} |> locmap loc, [])
        Infix left op right ->
            case Dict.get op scope of
                Nothing -> Err <| nameErr loc op
                Just t -> 
                    let (gen2, opType) = instantiate gen t in
                    typecheckExpr scope gen2 left  |> Result.andThen (\(gen3, leftAnnotLoc , leftConstraints )->
                    typecheckExpr scope gen3 right |> Result.map     (\(gen4, rightAnnotLoc, rightConstraints)->
                    NameGen.withFresh(\gen5 v->
                        let exprType = TVar v in
                        let rightType = typeOf rightAnnotLoc.value in
                        let leftType  = typeOf leftAnnotLoc.value in
                        ( gen5
                        , ( AnnotInfix {right=rightAnnotLoc, op=op, left=leftAnnotLoc, typ=exprType} |> locmap loc
                          , locmap loc (Equation opType (TFunc (TTuple [leftType, rightType]) exprType)) ::
                            leftConstraints++rightConstraints
                          )
                        )
                    ) gen4
                    |> (\(gen5, (annInfix, consts))->(gen5, annInfix, consts))))
        Prefix op right ->
            case Dict.get op scope of
                Nothing -> Err <| nameErr loc op
                Just typ ->
                    let t = (case op of
                            "-" -> Forall [TVar "a"] (TFunc TNum TNum)
                            _ -> typ) in
                    let (gen2, opType) = instantiate gen t in
                    typecheckExpr scope gen2 right |> Result.map (\(gen3, rightAnnotLoc, rightConstraints)->
                    NameGen.withFresh(\gen4 v->
                        let exprType = TVar v in
                        let rightType = typeOf rightAnnotLoc.value in
                        ( gen4
                        , ( AnnotPrefix {op=op, right=rightAnnotLoc, typ=exprType} |> locmap loc
                          , locmap loc (Equation opType (TFunc rightType exprType))::
                            rightConstraints
                          )
                        )
                    ) gen3
                    |> (\(gen4, (annPrefix, consts))->(gen4, annPrefix, consts)))
        ArrayLit exprs -> 
            NameGen.withFresh (\gen2 v->
                let res = List.foldr (\expr r -> 
                        r                             |> Result.andThen (\{genx, innerType, annotLocs, constraints}->
                        typecheckExpr scope genx expr |> Result.map     (\(genx2, annotLoc, typeConstraints)->
                        {genx=genx2, innerType=innerType, annotLocs=annotLoc::annotLocs, constraints=locmap expr (Equation innerType (typeOf annotLoc.value))::typeConstraints++constraints}))) (Ok {genx=gen2, innerType=TVar v, annotLocs=[], constraints=[]}) (List.reverse exprs)
                in
                (gen, res |> Result.map(\{genx, innerType, annotLocs, constraints}->
                let exprType = ADT "Array" [innerType] in
                ( genx
                , ( AnnotArray {vals=annotLocs, typ=exprType} |> locmap loc
                  , constraints
                  )
                )
                )
            )) gen 
            |> Tuple.second |> Result.map (\(gen2, (annArr, consts))->(gen2, annArr, consts))
        Index coll idx -> 
            typecheckExpr scope gen coll |> Result.andThen (\(gen2, collAnnotLoc, collConstraints)->
            typecheckExpr scope gen2 idx |> Result.map     (\(gen3, idxAnnotLoc , idxConstraints )->
            NameGen.withFresh(\gen4 v->
                let exprType = TVar v in
                let collType = typeOf collAnnotLoc.value in
                let idxType  = typeOf idxAnnotLoc.value in
                ( gen4
                , ( AnnotIndex {coll=collAnnotLoc, idx=idxAnnotLoc, typ=exprType} |> locmap loc
                  , locmap coll (Equation collType (ADT "Array" [exprType]))::
                    locmap idx  (Equation idxType  TNum)::
                    collConstraints++idxConstraints
                  )
                )
            ) gen3 
            |> (\(gen4, (annIndex, consts))->(gen4, annIndex, consts))))
        Tuple exprs ->
            List.foldr (\expr res->res|>Result.andThen(\(genx, annots, consts)->typecheckExpr scope genx expr|>Result.map(\(genx2,annot,exprConsts)->(genx2,annot::annots,exprConsts++consts)))) (Ok <| (gen, [], [])) exprs
            |> Result.map (\(gen2,annotLocs,consts)->(gen2,AnnotTuple {vals=annotLocs,typ=TTuple <| List.map (\annotLoc->typeOf annotLoc.value) annotLocs}|>locmap loc,consts))
        LetBlock line expr -> 
            case line.value of
                (n, e) -> 
                    letTypeOf scope gen e
                    |> Result.andThen (\(scope2, gen2, annotE)->
                        typecheckExpr (Dict.insert n (typeOf annotE.value) scope2) gen2 expr
                        |> Result.map (\(gen3, annotExpr, exprConsts)->
                            (gen3, AnnotLet {name=n, val=annotE, expr=annotExpr, typ=typeOf annotExpr.value} |> locmap loc, exprConsts)))
        -- _ -> Err ""

typeOf : Annot -> Type
typeOf a = case a of
    AnnotPrim   {typ} -> typ
    AnnotFunc   {typ} -> typ
    AnnotCall   {typ} -> typ
    AnnotIf     {typ} -> typ
    AnnotTuple  {typ} -> typ
    AnnotArray  {typ} -> typ
    AnnotPrefix {typ} -> typ
    AnnotInfix  {typ} -> typ
    AnnotIndex  {typ} -> typ
    AnnotLet    {typ} -> typ

updateType : (Type -> Type) -> Located Annot -> Located Annot
updateType f loc = case loc.value of
    AnnotPrim   ({typ} as a) -> {loc | value=AnnotPrim   {a | typ=f typ}}
    AnnotFunc   ({typ} as a) -> {loc | value=AnnotFunc   {a | typ=f typ}}
    AnnotCall   ({typ} as a) -> {loc | value=AnnotCall   {a | typ=f typ}}
    AnnotIf     ({typ} as a) -> {loc | value=AnnotIf     {a | typ=f typ}}
    AnnotTuple  ({typ} as a) -> {loc | value=AnnotTuple  {a | typ=f typ}}
    AnnotArray  ({typ} as a) -> {loc | value=AnnotArray  {a | typ=f typ}}
    AnnotPrefix ({typ} as a) -> {loc | value=AnnotPrefix {a | typ=f typ}}
    AnnotInfix  ({typ} as a) -> {loc | value=AnnotInfix  {a | typ=f typ}}
    AnnotIndex  ({typ} as a) -> {loc | value=AnnotIndex  {a | typ=f typ}}
    AnnotLet    ({typ} as a) -> {loc | value=AnnotLet    {a | typ=f typ}}

updateTypes : (Type -> Type) -> Located Annot -> Located Annot
updateTypes f loc = case loc.value of
    AnnotPrim   ({typ} as a)                    -> {loc | value=AnnotPrim   {a | typ=f typ}}
    AnnotFunc   ({block, typ} as a)             -> {loc | value=AnnotFunc   {a | block=updateTypes f block, typ=f typ}}
    AnnotCall   ({func, args, typ} as a)        -> {loc | value=AnnotCall   {a | func=updateTypes f func, args=updateTypes f args, typ=f typ}}
    AnnotIf     ({cond, cons, alt, typ} as a)   -> {loc | value=AnnotIf     {a | cond=updateTypes f cond, cons=updateTypes f cons, alt=updateTypes f alt, typ=f typ}}
    AnnotTuple  ({vals, typ} as a)              -> {loc | value=AnnotTuple  {a | vals=List.map (updateTypes f) vals, typ=f typ}}
    AnnotArray  ({vals, typ} as a)              -> {loc | value=AnnotArray  {a | vals=List.map (updateTypes f) vals, typ=f typ}}
    AnnotPrefix ({right, typ} as a)             -> {loc | value=AnnotPrefix {a | right=updateTypes f right, typ=f typ}}
    AnnotInfix  ({left, right, typ} as a)       -> {loc | value=AnnotInfix  {a | left=updateTypes f left, right=updateTypes f right, typ=f typ}}
    AnnotIndex  ({coll, idx, typ} as a)         -> {loc | value=AnnotIndex  {a | coll=updateTypes f coll, idx=updateTypes f idx, typ=f typ}}
    AnnotLet    ({expr, val, typ} as a)         -> {loc | value=AnnotLet    {a | expr=updateTypes f expr, val=updateTypes f val, typ=f typ}}

-- typeOf : Scope -> NameGen (Located Expr) -> Result String (NameGen Type)
-- typeOf scope genexpr = typecheckExpr scope genexpr |> Result.andThen (\(gent, constraints)->
--                     solve constraints [] [] |> Result.map (\substitutions->
--                     List.foldr (\(Subst t1 t2) genb->NameGen.fmap(sub (TVar t1) t2) genb) gent substitutions))

letTypeOf : Scope -> NameGen -> Located Expr -> Result String (Scope, NameGen, Located Annot)
letTypeOf scope gen expr = typecheckExpr scope gen expr |> Result.andThen (\(gen2, annotLoc, constraints)->preGeneralize scope constraints annotLoc|>Result.map(\(s, a)->(s, gen2, a)))

type Subst = Subst String Type

typeErr : Located a -> String -> Result String value
typeErr loc s = Err <| "TypeError " ++ locToPosString loc ++ ": " ++ s

solve : (List (Located Constraint)) -> (List Subst) -> (List (Located Constraint))-> Result String (List Subst)
solve constraints substitutions skipped = case constraints of
    loc::rest -> case loc.value of
        Equation t1 t2 ->
            let continue = \_->solve rest substitutions (loc::skipped) in
            let err = \_->typeErr loc <| typeToString t1 ++ " can't equal " ++ typeToString t2 in
            let removeAndContinue = \_->solve rest substitutions skipped in
            let handleVarIsolationAndContinue = \v->solve (substituteAll rest t2 t1) (Subst v t1::substitutions) (substituteAll skipped t2 t1) in
            if t1 == t2 then
                solve rest substitutions skipped
            else case t1 of
                TFunc a b ->
                    case t2 of
                        TFunc c d -> solve (locmap loc (Equation a c) :: locmap loc (Equation b d) :: rest) substitutions skipped
                        TVar x -> 
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                TTuple ts ->
                    case t2 of
                        TTuple ts2 -> 
                            if List.length ts /= List.length ts2 then
                                err()
                            else
                                solve ((List.map2 (\l r->locmap loc (Equation l r)) ts ts2)++rest) substitutions skipped
                        TVar x ->
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                ADT n ts ->
                    case t2 of
                        ADT n2 ts2 ->
                            if n /= n2 || List.length ts /= List.length ts2 then
                                err()
                            else
                                solve ((List.map2 (\l r ->locmap loc (Equation l r)) ts ts2)++rest) substitutions skipped
                        TVar x ->
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                TVar x -> 
                    if occurs t1 t2 then
                        continue()
                    else
                        solve (substituteAll rest t1 t2) (Subst x t2::substitutions) (substituteAll skipped t1 t2)
                TBool ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TBool -> removeAndContinue() -- theoretically impossible but this would be the right thing to do if it happened
                        _ -> err()
                TNum ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TNum -> removeAndContinue() -- theoretically impossible but this would be the right thing to do if it happened
                        _ -> err()
                TChar ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TChar -> removeAndContinue()
                        _ -> err()
                TString ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TString -> removeAndContinue()
                        _ -> err()
                Forall _ _ -> Err "something went wrong, Forall found after it should be instantiated"
                -- _ -> continue()
    [] -> if List.isEmpty skipped then Ok substitutions else solve skipped substitutions []

substituteAll : List (Located Constraint) -> Type -> Type -> List (Located Constraint)
substituteAll constraints var val = case constraints of
    [] -> []
    loc::rest -> case loc.value of
        Equation u v ->
            let u2 = sub var val u in
            let v2 = sub var val v in
            locmap loc (Equation u2 v2)::substituteAll rest var val

sub : Type -> Type -> Type -> Type
sub var val t = case t of
    TVar _ -> if t == var then val else t
    TBool -> t
    TNum -> t
    TChar -> t
    TString -> t
    TFunc a b -> TFunc (sub var val a) (sub var val b)
    TTuple ts -> TTuple (List.map (sub var val) ts)
    ADT n ts -> ADT n (List.map (sub var val) ts)
    Forall vars u -> Forall vars (sub var val u)

occurs : Type -> Type -> Bool
occurs var t = case t of
    TVar _ -> t == var
    TBool -> False
    TNum -> False
    TChar -> False
    TString -> False
    TFunc a b -> occurs var a && occurs var b
    TTuple ts -> List.any (occurs var) ts
    ADT _ ts -> List.any (occurs var) ts
    Forall vars u -> List.any (\v->v==var) vars || occurs var u

instantiate : NameGen  -> Type -> (NameGen, Type)
instantiate gen t = case t of
    TBool -> (gen, t)
    TNum -> (gen, t)
    TChar -> (gen, t)
    TString -> (gen, t)
    TFunc a b -> 
        let (gen2, a2) = instantiate gen a in 
        let (gen3, b2) = instantiate gen2 b in
            (gen3, (TFunc a2 b2))
    TTuple ts -> Tuple.mapSecond TTuple <| List.foldr (\typ (genx, types)-> instantiate genx typ |> Tuple.mapSecond (\newt->newt::types)) (gen, []) ts
    TVar _ -> (gen, t)
    ADT n ts -> Tuple.mapSecond (ADT n) <| List.foldr (\typ (genx, types)-> instantiate genx typ |> Tuple.mapSecond (\newt->newt::types)) (gen, []) ts
    Forall vars u -> List.foldr (\var (genx, typ)->NameGen.withFresh (\genx2 v->(genx2, sub var (TVar v) typ)) genx) (gen, u) vars

generalize : Scope -> Type -> Type -> Type
generalize scope t scheme =
    case scheme of
        Forall vars typ ->
            case t of
                TVar x -> 
                    if occursInScope scope x || List.member t vars then 
                        scheme 
                    else 
                        Forall (t::vars) typ
                TChar -> scheme
                TBool -> scheme
                TNum -> scheme
                TString -> scheme
                TFunc a b -> 
                    let (varsA, _) = Maybe.withDefault ([], a) <| schemeFrom <| generalize scope a scheme in 
                    let (varsB, _) = Maybe.withDefault ([], b) <| schemeFrom <| generalize scope b scheme in 
                    let set = List.foldr (\item l->if List.member item l then l else item :: l) [] (vars++varsA++varsB) in
                    Forall set typ
                TTuple ts -> List.foldr (\u schem-> generalize scope u schem) scheme ts
                ADT _ ts -> List.foldr (\u schem-> generalize scope u schem) scheme ts
                Forall _ _ -> t
        _ -> Forall [] t -- this shouldn't happen...

schemeFrom : Type -> Maybe (List Type, Type)
schemeFrom t = case t of
    Forall vars u -> Just (vars, u)
    _ -> Nothing

preGeneralize : Scope -> List (Located Constraint) -> Located Annot -> Result String (Scope, Located Annot)
preGeneralize scope constraints annotLoc = 
    solve constraints [] [] |> Result.map(\substitutions->
    let env = List.foldr (\(Subst x u) scop->Dict.map (\_ v->sub (TVar x) u v) scop) scope substitutions in
    let annot2 = List.foldr (\(Subst x u) annotx->updateTypes (\t->sub (TVar x) u t) annotx) annotLoc substitutions in 
    let scheme = updateType (\t->generalize scope t (Forall [] t)) annot2 in
    (env, scheme))

occursInScope : Scope -> String -> Bool
occursInScope scope var = Dict.toList scope |> List.any (\(_, t)->occurs (TVar var) t)

typecheckLines : Scope -> NameGen -> List (Located (String, Located Expr)) -> List (Located (String, Located Annot)) -> Result String (Scope, NameGen, List (Located (String, Located Annot)))
typecheckLines scope gen ast sofar = case ast of
    [] -> Ok (scope, gen, List.reverse sofar)
    stmt::rest -> 
        letTypeOf scope gen (Tuple.second stmt.value) |> Result.andThen (\(scope2, gen2, annotLoc)->
        typecheckLines (Dict.insert (Tuple.first stmt.value) (typeOf annotLoc.value) scope2) gen2 rest (locmap stmt (Tuple.first stmt.value, annotLoc) :: sofar))

typecheck : Scope -> NameGen -> Located Expr -> Result String (Scope, NameGen, Located Annot)
typecheck scope gen ast = letTypeOf scope gen ast