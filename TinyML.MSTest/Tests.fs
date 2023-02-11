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

    let evaluate line = 
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
        x, t, pretty_value v
    
    let reset_environment () =
        tenv <- Typing.gamma_scheme_env
        venv <- []
        Typing.reset_fresh_variable()


[<TestClass>]
type TestClass () =

    [<TestMethod>]
    member _.Test_fx_x_plus_1()=
        let x,t,v = Evaluate.evaluate("let f x = x + 1 ;;")
        let expected_type = TyArrow(TyInt, TyInt)
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Int_Tuple()=
        let x,t,v = Evaluate.evaluate("let x = (1,2);;");
        let expected_type = TyTuple[TyInt;TyInt]
        Assert.AreEqual(t,expected_type)

    [<TestMethod>]
    member _.Test_Int_String_Tuple()=
        let x,t,v = Evaluate.evaluate("let x = (1,\"Test TinyML\");;")
        let expected_type = TyTuple[TyInt;TyString]
        Assert.AreEqual(t,expected_type)


    [<TestMethod>]
    member _.Test_Int_String_Float_Bool()=
        let x,t,v = Evaluate.evaluate("let x = (1,\"Test TinyML\",5.0,true);;")
        let expected_type = TyTuple[TyInt;TyString;TyFloat;TyBool]
        Assert.AreEqual(t,expected_type)