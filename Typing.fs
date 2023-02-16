(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

let mutable var_counter = 0

let reset_fresh_variable () =
    var_counter <- 0
    //TyVar var_counter

let get_fresh_variable () = 
    var_counter <- var_counter + 1
    TyVar var_counter

type subst = (tyvar * ty) list

// The function apply_substs receives as parameters (s: a list of (tyvar*ty)) and (t: a type ty).
// The function search recursively inside "s" the type to substitute.
let rec apply_subst (s : subst) (t : ty): ty =
    match t with
    | TyName _ -> t
    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)
    | TyVar tv ->
        try
            let _, t1 = List.find (fun (tv1, _) -> tv1 = tv) s in t1            // /Alfa->t) belongs to sub
        with _KeyNotFoundException -> t                                         //If alfa is not in s, we keep t
    | TyTuple ts -> TyTuple (List.map (apply_subst s) ts)

// It composes two subst. s1 and s2 into a single substituion.
let compose_subst (s1 : subst) (s2 : subst) : subst =
    let s1_applied = List.map (fun (y, x) -> (y, apply_subst s2 x)) s1
    let composed = List.append s1_applied s2
    List.distinctBy fst composed    //Remove of duplicates according to the type



// The function receives two parameter: a subst  and a scheme env.
// The function use the map function to apply the substitution subs to each scheme of the environment
// It updates the type t of scheme with the substitution subst, then it creates a new schem env with the new t computed before.
let apply_susbs_to_env (subst: subst) (env : scheme env) : scheme env =
    List. map (fun (name, Forall (tvs,t)) -> 
        let temp = apply_subst subst t
        (name, Forall (tvs, temp))
       ) env
    

// Get the set of free-type-variables in the type. The ftv of a type are all the type vars appearing on the type.
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty //No free var
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)   //Cerca le free var in t1, t2 e poi unisce i due risultati
    | TyVar tv -> Set.singleton tv //Ritorna solo tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts 
    // For a tyTuple, the method uses fold to compute the set of freevars for each t in the tuple.
    // It takes two param. in input: the accumulator and the current freevar of t
    // At the end it returns the sets of freevars computed at each iteration


let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs


// The method computes for each scheme contained in the environment its set of freevar.
// Therefore, it returns the set of freevar of each scheme of the environment.
let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env
    

// Instantiation converts a type scheme into a type by refreshing its polymorphic type variables.
// It is used to assign a fresh variable when a variable identifier is met in the VAR rule. 
let inst (Forall (tvs, t)) : ty =
    let free_vars = freevars_ty t                               // 1. Computation of set of freevars on the type of the scheme
    let vars_to_be_refresh = Set.intersect free_vars tvs        // 2. Intersection between the set of universally quantified type variable and free vars.
    let sub =                                                   // 3. This set of var is then transformed into a subst by mapping each vars into a a fresh variable
        vars_to_be_refresh                              
        |> Set.toList
        |> List.map (fun v -> (v, (get_fresh_variable())))
    apply_subst sub t                                           // 4. Then it applies the substitution on the type of the scheme


// Generalization promotes a type τ into a type scheme σ by quantifying type variables that represent
// polymorphic types through the forall universal quantifier (∀):
let generalization(env: scheme env) (t:ty) : scheme =
    let tvs = Set.difference(freevars_ty t) (freevars_scheme_env env)
    Forall(tvs,t) 
    
// The method unify takes two types t1 and t2 and produces the MGU, that is a subst which makes them equal
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1,t2) with
    | TyName s1, TyName s2 when s1 = s2 -> []   

    | TyVar tv,t                    //Substitution is symmetric, tv is the type var
    | t, TyVar tv -> [tv,t]

    | TyArrow(t1,t2), TyArrow(t3,t4) -> 
        let s = unify t1 t3
        in s @ (unify (apply_subst s t2) (apply_subst s t4)) //s is used to concatenate two lists
        // First it unifies the input of thet tpe arrows, then concatenates the substs computed before 
        // with the output and it unifies the resulting part

    // It iteratively unifies each pair of elements in the tuples and accumulate the resulting substitutions.
    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1,t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
    
    | _ -> type_error "cannot unify types %O and %O" t1 t2



// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("%", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (">", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("<=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (">=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("<>", TyArrow (TyInt, TyArrow (TyInt, TyBool)))

    ("and", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ("or", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
]

let gamma_scheme_env = 
    gamma0 
    |> List.map (fun (x, y) -> (x, Forall (Set.empty, y) ))


let check_type t:ty = 
    match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat


// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    // Var x: if x exists in the environment, it extracts its scheme.
    // Then it uses the method inst on the scheme to obtain the type t'
    // At the end it returns the type t' and the empty substitution
    | Var x -> 
        try
            let exists_type = fun(t,_) -> t = x
            match List.find exists_type env with //x belongs to environment
            | (_,sc) -> inst sc, [] // [] is the substitution,
        with
            | _ -> failwithf"Error on Var X" 

    
    // I have splitted the Lambda rule in two cases: 
    // The first is when the type of x is specified and the second not.

    // Case where x has no annotated type: we'll use a fresh variable as type of it
    | Lambda (x, None, e) ->
        let ty = get_fresh_variable()
        let te,se = typeinfer_expr ((x, Forall(Set.empty, ty)) :: env  ) e
        let t1 = apply_subst se ty
        TyArrow (t1, te), se
    
    | Lambda (x, Some ty, e) ->
        let te,se = typeinfer_expr ((x, Forall(Set.empty, ty)) :: env  ) e
        let t1 = apply_subst se ty
        TyArrow (t1, te), se



    // Application case with two parameters
    // 1. Type inference of first expression, obtain of t1,s1
    // 2. The substitution computed before is applied on the environment for the second rule
    // 3. Second rule: type inf. of t2,s2 by using the update environment and the second expression
    // 4. Obtaining of a new fresh variable for the third rule
    // 5. Unification of t1; t2->fresh_var
    // 6. Composition of substitution and then use of apply_substs to get the final type
    | App (e1, e2) ->
        let t1,s1 = typeinfer_expr env e1
        let env = apply_susbs_to_env s1 env
        let t2, s2 = typeinfer_expr env e2
        let fresh_var = get_fresh_variable ()

        let s3 = unify (apply_subst s2 t1) (TyArrow (t2, fresh_var))
        let s1_s2_s3 = compose_subst s1 (compose_subst s2 s3)
        apply_subst s1_s2_s3 fresh_var, s1_s2_s3



    // If-Then-Else case
    // 1. Inference of t1 and s1 and unification of t1 with TyBool
    // 2. Composition of substitution to infer t2 and s4
    // 3. E3o -> None | type error or TyUnit
    // 4. E3o -> Some 
    //    -> Apply subst to environment, composition of subst and 
    //    -> type inference on e3 to get t3, s6
    //    -> Unify to get t8, at the end return of t3 the final comp. of substs
    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s3 = compose_subst s1 (unify t1 TyBool)

        let env = apply_susbs_to_env s3 env

        let t2,s4 = typeinfer_expr env e2  
        let s5 = compose_subst s4 s3
       
        match e3o with
        | None -> 
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit, s5
                    
        | Some e3 ->
            let env = apply_susbs_to_env s5 env
            let t3, s6 = typeinfer_expr env e3
            let s7 = compose_subst s5 s6
            let s8 = unify (apply_subst s7 t2) (apply_subst s7 t3)
            t3, compose_subst s8 s7

    
    
    // Let rule: type inference of t1 and s1.
    // Application of the substitution s1 to t1.
    // Result type is then transformed into scheme by generalization method
    // Extension of the environment with the new scheme and var
    // Update of the environment by applying the substitution s1.
    // Inference of t2 and s2 and return of t2, compose susbst s2 s1.
    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let sch = generalization env (apply_subst s1 t1)
        let env2 = apply_susbs_to_env s1 ((x,sch)::env)
        let t2, s2 =typeinfer_expr env2 e2
        match tyo with
        | Some (t2_user) when t2_user <> t2 -> type_error "The expected type of this expression is %s but got instead %s"(pretty_ty t2_user) (pretty_ty t2)
        | _ -> t2, compose_subst s2 s1
    

    // Let-Rec rule.
    // First, the method gets a fresh variable to use for the first rule.
    // The environment is first extended adding the f received as parameter and
    // the scheme created using as type the new fresh var.
    // Second, it infers the expression e1 and get t1,s1.
    // If the optional type is not expressed
    // Computation of the type scheme o1 by applying the method generalization.
    // Update and extension of the environment to infer t2 and s2
    // Return of t2 and s2
    |LetRec (f ,tyo, e1, e2) ->
        let fresh_var = get_fresh_variable()
        let env = (f,Forall(Set.empty,fresh_var))::env
        let t1,s1  = typeinfer_expr env e1
        match tyo with
        | Some (tyo) when t1 <> tyo -> type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tyo) (pretty_ty t1)
        | _ -> 
            let sch = generalization env (apply_subst s1 t1)
            let current_env = apply_susbs_to_env s1 env
            let t2,s2 = typeinfer_expr ((f,sch)::current_env) e2
            t2,s2 


    // The method fold starts with an empty set
    // At each iteration, it requires Theta (i-1), and the current expression
    // It uses the method typeperf_expr to infer the type ti and the subst si.
    // The output has to be a t1*..*tn of types and the substs n.
    | Tuple es ->
        let final_ts, final_subst = List.fold (fun ((ts, s):ty list * subst) (e : expr) ->
                let current_env = apply_susbs_to_env s env 
                let ti, si = typeinfer_expr current_env e
                let ts = List.map (fun t -> apply_subst si t) ts
                let current_sub = compose_subst si s in ti::ts, current_sub) ([], []) es
        TyTuple(List.rev(final_ts)), final_subst


    // op indicates the operator to use with e1 and e2.
    // If op exists, the method calls the typeinfer_expr treating the expression as application 
    // In the class eval, there are the methods which express how to evaluate the expression expressed by op
    | BinOp (e1, op, e2) when 
        (List.exists (fun (x, _) -> op = x) gamma0) -> typeinfer_expr env (App ((App (Var op, e1)), e2))
      

// type checker //
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
