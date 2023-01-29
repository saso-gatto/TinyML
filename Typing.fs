﻿(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

let mutable var_counter = 0

type subst = (tyvar * ty) list

// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2
 
let refresh (t:tyvar): tyvar = t+1

let rec re (powerset : Set<tyvar>, t :ty) : ty =
    match t with
    | TyName _ -> t
    | TyVar tv -> 
        if not (Set.contains tv powerset) then 
            t 
        else 
            var_counter <- var_counter+1
            TyVar(var_counter)

    | TyArrow (t1, t2) -> TyArrow (re (powerset, t1), re (powerset, t2))
    | TyTuple ts -> TyTuple (List.map (fun x -> re (powerset, x)) ts)
    
let inst (Forall(tvs,t)): ty = re (tvs, t)

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1,t2) with
    | TyName s1, TyName s2 when s1 = s2 -> []

    | TyVar tv,t
    | t, TyVar tv -> [tv,t]

    | TyArrow(t1,t2), TyArrow(t3,t4) -> compose_subst (unify t1 t3) (unify t2 t4)

    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1,t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
    
    | _ -> type_error "cannot unify types %O and %O" t1 t2

// TODO implement this
let apply_subst (t : ty) (s : subst) : ty = t


let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env


// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
]


// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x -> TyInt, []
          (*let tmp = freevars_scheme_env env

          // inst è una funzione che riceve un set tyvar e ty
          let inst2 = inst(Forall(tmp,t))
          failwithf "Sono qui"
//        let tvs = freevars_ty *)

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst s2 s1
    | _ -> failwithf "not implemented"

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
