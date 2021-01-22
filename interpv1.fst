module Interpv1

open FStar.Mul

type expr =
  | Const : int -> expr
  | Add   : expr -> expr -> expr
  | Sub   : expr -> expr -> expr
  | Mul   : expr -> expr -> expr

(*
  Concepts
  ========
  + Type defintiion
  + Constructors
*)

let rec interp e =
  match e with
  | Const i -> i
  | Add a b -> interp a + interp b
  | Sub a b -> interp a - interp b
  | Mul a b -> interp a * interp b

(*
  Concepts
  ========
  + Function definition, type inference
  + Pattern matching 
*)


(* (5 + 6) - 3 *)
let e = Sub (Add (Const 5) (Const 6)) (Const 3)
let _ = assert (interp e = 8)
