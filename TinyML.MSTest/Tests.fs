namespace TinyML.MSTest

open System
open Microsoft.VisualStudio.TestTools.UnitTesting
open System.IO
open FSharp.Common
open TinyML.Ast
open TinyML



module Evaluate =
    let mutable tenv = TinyML.Typing.gamma_scheme_env
    let mutable venv = []

    let parse_from_TextReader rd filename parser = 
        Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser TinyML.Lexer.tokenize TinyML.Parser.tokenTagToTokenId

    let parse_from_string line filename parser = 
        Parsing.parse_from_string SyntaxError line filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId


    let compute_prg_str prg = 
        let rd = new StringReader(prg)
        parse_from_TextReader rd "LINE" TinyML.Parser.program

    let get_type_expression line = 
        let x, (t, v) =
            match parse_from_string line "LINE" Parser.interactive with 
            | IExpr e ->
                "it", Main.interpret_expr tenv venv e

            | IBinding (_, x, _, _ as b) ->
                let t, v = Main.interpret_expr tenv venv (LetIn (b, Var x))
                let tmp = Forall(Set.empty, t)
                tenv <- (x, tmp) :: tenv
                venv <- (x, v) :: venv
                x, (t, v)
        t
    
    let reset_environment () =
        tenv <- Typing.gamma_scheme_env
        venv <- []
        Typing.reset_fresh_variable()


[<TestClass>]
type TestClass () =

    [<TestMethod>]
    member _.Test_fx_x_plus_1()=
        let t = Evaluate.get_type_expression("let f x = x + 1 ;;")
        let expected_type = TyArrow(TyInt, TyInt)
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Int_Tuple()=
        let t = Evaluate.get_type_expression("let x = (1,2);;");
        let expected_type = TyTuple[TyInt;TyInt]
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Int_String_Tuple()=
        let t = Evaluate.get_type_expression("let x = (1,\"Test TinyML\");;")
        let expected_type = TyTuple[TyInt;TyString]
        Assert.AreEqual(t,expected_type)


    [<TestMethod>]
    member _.Test_Int_String_Float_Bool()=
        let t = Evaluate.get_type_expression("let x = (1,\"Test TinyML\",5.0,true);;")
        let expected_type = TyTuple[TyInt;TyString;TyFloat;TyBool]
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Let_Int()=
        let t = Evaluate.get_type_expression("let x = 5;;")
        let expected_type = TyInt
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Let_String()=
        let t = Evaluate.get_type_expression("let x =\"Test_Let\";;")
        let expected_type = TyString
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Let_Float()=
        let t = Evaluate.get_type_expression("let x = 5.0;;")
        let expected_type = TyFloat
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_LetRec()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let rec f x = f x + 1;;")
        let expected_type = TyArrow(TyVar 6,TyInt)
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_TupleInt()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("fun x -> x + 1;;")
        let expected_type = TyArrow(TyInt,TyInt)
        Assert.AreEqual(t,expected_type)


    [<TestMethod>]
    member _.Test_High_Order_Function()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let f = fun x -> fun y -> if x>0 then y x else y (x+1);;")
        let y = TyArrow(TyArrow(TyInt,TyVar 9),TyVar 9)
        let expected_type = TyArrow(TyInt, y)
        Assert.AreEqual(t,expected_type)

    //By F#: val it: x: ('a -> int) -> y: 'a -> int
    [<TestMethod>]
    member _.Test_Double_Lambda_Function()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("fun x -> fun y -> x y + 1;;")
        let expected_type = TyArrow((TyArrow(TyVar 2, TyInt)),TyArrow(TyVar 2, TyInt))
        Assert.AreEqual(t,expected_type)

    //By If-Then-Else 
    [<TestMethod>]
    member _.Test_If_Then_Else()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let x = 5 in if x>0 then 0 else 1;;")
        let expected_type = TyInt
        Assert.AreEqual(t,expected_type)

    // let z x y = fun z -> x y;;
    // val z: x: ('a -> 'b) -> y: 'a -> z: 'c -> 'b
    // val z : ( '5 ->  '7) -> ( '5 -> ( '6 ->  '7)) = <|[];x;fun y -> fun z -> x y|>
    [<TestMethod>]
    member _.Test_Lambda_App()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let z x y = fun z -> x y;;")
        let type_x = TyArrow(TyVar 5, TyVar 7)
        let type_yz = TyArrow(TyVar 5, TyArrow(TyVar 6, TyVar 7))
        let expected_type = TyArrow(type_x,type_yz)
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Lambda_Shadowed()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let g = fun x -> ( x + 1, let x = \"ciao\" in x , fun x -> x ) in g 5;;")
        let expected_type = TyTuple[TyInt;TyString;TyArrow(TyVar 5, TyVar 5)]
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Fibonacci() = 
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let rec fib = fun x -> if x = 0 then 0 else if x = 1 then 1 else fib (-1 + x) + fib (-2 + x) in fib 10;;")
        Assert.AreEqual(t,TyInt)

    [<TestMethod>]
    member _.Test_Bin_Op_Greater_Than() = 
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("5>3;;")
        Assert.AreEqual(t,TyBool)

    [<TestMethod>]
    member _.Test_Bin_Op_Lower_Than() = 
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("10<15;;")
        Assert.AreEqual(t,TyBool)

    [<TestMethod>]
    member _.Test_Bin_Op_Equal() = 
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("5=5;;")
        Assert.AreEqual(t,TyBool)

    [<TestMethod>]
    member _.Test_Plus_Op_Int()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("5+5;;")
        Assert.AreEqual(t,TyInt)

    [<TestMethod>]
    member _.Test_IfThenElse2()=
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let x y = fun x -> if y-x>0 then y-x else y+x;;")
        let expected_type = TyArrow(TyInt,TyArrow(TyInt,TyInt))
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Recursive_polymorphic_multiple_times_on_let_bindings() =
        Evaluate.reset_environment()
        let t = Evaluate.get_type_expression("let z = 2 in 
                    let rec f x y = 
                        x (y+1)
                    in let g = f (fun x -> x) 5
                    in let w = f
                    in let z = f (fun (x: int) -> x/z)
                    in let s = f (fun x -> \"Test String\")
                    in let a = f
                    in (g, w, z, s, a);;")
        let expectedType = TyTuple [TyInt;TyArrow (TyArrow (TyInt, TyVar 20), TyArrow (TyInt, TyVar 20)); TyArrow (TyInt, TyInt); TyArrow (TyInt, TyString);TyArrow (TyArrow (TyInt, TyVar 21), TyArrow (TyInt, TyVar 21))]
        Assert.AreEqual(t,expectedType)

