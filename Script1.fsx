type tyvar = int
// Ty corresponds to the greek letters tao of the notes.
type ty =
    | TyName of string      //Type constructors of types such as int, float, etch.
    | TyArrow of ty * ty
    | TyVar of tyvar
    | TyTuple of ty list

// pseudo data constructors for literal types
let TyFloat = TyName "float"
let TyInt = TyName "int"
let TyChar = TyName "char"
let TyString = TyName "string"
let TyBool = TyName "bool"
let TyUnit = TyName "unit"

type scheme = Forall of tyvar Set * ty

let test = Set.ofList ["mon"; "tues"; "wed"; "thurs"; "fri"]
let toList test = Set.fold (fun l se -> se::l) [] test
let elem = List.find(fun x -> "tues" = x )

let valuesList = [ ("a", 1); ("b", 2); ("c", 3) ]

let resultPick = List.pick (fun elem ->
                    match elem with
                    | (value, 2) -> Some value
                    | _ -> None) valuesList
printfn "%A" resultPick