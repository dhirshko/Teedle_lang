// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

// Based on Andrej Bauer's "How to implement dependent type theory I"
// Found at http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/

// Tiny abstract grammar for a tiny language
type variable =
| String of string
| Gensym of string * int
| Dummy

type expr =
| Var of variable
| Universe of int
| Pi of abstraction
| Lambda of abstraction
| App of expr * expr
| Noexpr // this might be a problem...
and abstraction = variable * expr * expr

// refresh x generates a fresh variable w/ preferred name x
let refresh = 
    let k = ref 0 in
        function
        | String x | Gensym (x, _) -> (incr k; Gensym (x, !k))
        | Dummy -> (incr k ; Gensym ("_", !k))

// helper for alists
let assoc k = List.tryFind (fst >> ((=) k))
// subst (x1,e1)...(xn,en) substitutes e for x
let rec subst s = 
    function
    | Var x -> let l = assoc x s in
                match l with 
                | None -> Var x
                | Some e -> Var (fst e)
    | Universe k -> Universe k
    | Pi a -> Pi (subst_abstraction s a)
    | Lambda a -> Lambda (subst_abstraction s a)
    | Noexpr -> failwith "not an expression"
    | App (e1, e2) -> App (subst s e1, subst s e2)

and subst_abstraction s (x, t, e) =
    let x' = refresh x in
        (x', subst s t, subst ((x, Var x') :: s) e)

// Type inference! 
type context = (variable * (expr * expr option)) list

// (dumb) helper since I used options instead of exceptions
let lookup f x ctx =
    let m_t = (assoc x ctx) in
        match m_t with
        | Some tup -> f tup
        | None -> failwith "lookup failed"

// lookup_ty x ctx returns type of x in context ctx
let lookup_ty x ctx = lookup fst x ctx
// lookup_value x ctx returns val of x in context ctx
let lookup_value x ctx = lookup snd x ctx        

// extend x t v ctx returns ctx with x of type t and value v
let extend x t v ctx = (x, (t, v)) :: ctx

let rec normalize ctx = function
    | Var x -> match lookup_value x (ctx : context) with
                | (_, None) -> Var x
                | (_, Some Noexpr) -> Var x // TODO: check this
                | (_, Some e) -> normalize ctx e     
    | App (e1, e2) ->
      let e2 = normalize ctx e2 in
        match normalize ctx e1 with
        | Lambda (x, _, e1') -> normalize ctx (subst [(x, e2)] e1')
        | e1 -> App (e1, e2)
    | Universe k -> Universe k
    | Pi a -> Pi (normalize_abstraction ctx a)
    | Lambda a -> Lambda (normalize_abstraction ctx a)
    | Noexpr -> Noexpr // TODO: check this

and normalize_abstraction ctx (x, t, e) =
    let t = normalize ctx t in
        (x, t, normalize (extend x t None ctx) e)

let equal ctx e1 e2 =
    let rec equal e1 e2 = 
        match e1, e2 with
        | Var x1, Var x2 -> x1 = x2
        | App (e11, e12), App (e21, e22) -> equal e11 e21 && equal e12 e22
        | Universe k1, Universe k2 -> k1 = k2
        | Pi a1, Pi a2 -> equal_abstraction a1 a2
        | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
        | _,_ -> false
    and equal_abstraction (x, t1, e1) (y, t2, e2) =
        equal t1 t2 && (equal e1 (subst [(y, Var x)] e2))
    in
        equal (normalize ctx e1) (normalize ctx e2)

// infer type of e in ctx
let rec infer_type (ctx : context) = function
    | Var x -> Var (lookup_ty x ctx) // TODO: check this is correct
    | Universe k -> Universe (k + 1)
    | Pi (x, t1, t2) -> 
      let k1 = infer_universe ctx t1 in
      let k2 = infer_universe (extend x t1 None ctx) t2 in
        Universe (max k1 k2)
    | Lambda (x, t, e) -> 
      let _ = infer_universe ctx t in
      let te = infer_type (extend x t None ctx) e in
        Pi (x, t, te)
    | App (e1, e2) ->
      let (x, s, t) = infer_pi ctx e1 in
      let te = infer_type ctx e2 in
        check_equal ctx s te ;
        subst [(x, e2)] t
    | Noexpr -> failwith "bad"

and infer_universe ctx t =
    let u = infer_type ctx t in
        match normalize ctx u with
            | Universe k -> k
            | _ -> failwith "type expected"

and infer_pi ctx e =
    let t = infer_type ctx e in
        match normalize ctx t with
            | Pi a -> a
            | _ -> failwith "function expected"

and check_equal (ctx : context) e1 e2 = 
    if not (equal ctx e1 e2)
    then failwith "expressions foo and bar not equal" //TODO: add printing of exprs



[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code





