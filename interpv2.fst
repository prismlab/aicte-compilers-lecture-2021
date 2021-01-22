module Interpv2

open FStar.Mul

type expr =
  | Const : int -> expr
  | Add   : expr -> expr -> expr
  | Sub   : expr -> expr -> expr
  | Mul   : expr -> expr -> expr
  | Div_  : expr -> expr -> expr

val interp : expr -> int
let rec interp e =
  match e with
  | Const i -> i
  | Add a b -> interp a + interp b
  | Sub a b -> interp a - interp b
  | Mul a b -> interp a * interp b
  | Div_ a b -> interp a / interp b

(*
val interp2 : expr -> int
let rec interp2 e =
  match e with
  | Const i -> i
  | Add a b -> interp2 a + interp2 b
  | Sub a b -> interp2 a - interp2 b
  | Mul a b -> interp2 a * interp2 b
  | Div_ a b -> 
      let vb = interp2 b in
      if vb = 0 then 0
      else (* vb != 0 *) interp2 a / vb
*)
