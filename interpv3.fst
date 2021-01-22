module Interpv3

open FStar.Mul

type nat = i:int{i >= 0}
(*
  Concept
  =======
  + Refinement types
*)

type expr =
  | Const : nat -> expr
  | Add   : expr -> expr -> expr
  | Sub   : expr -> expr -> expr
  | Mul   : expr -> expr -> expr
  | Div_  : expr -> expr -> expr

val interp : expr -> nat
let rec interp e =
  match e with
  | Const i -> i
  | Add a b -> interp a + interp b
  | Sub a b -> interp a - interp b 
  | Mul a b -> interp a * interp b
  | Div_ a b -> 
      let vb = interp b in 
      if vb = 0 then 0
      else interp a / interp b

(*
val interp2 : expr -> nat
let rec interp2 e =
  match e with
  | Const i -> i
  | Add a b -> interp2 a + interp2 b
  | Sub a b -> 
      let va = interp2 a in
      let vb = interp2 b in
      if vb > va then 0
      else va - vb
  | Mul a b -> interp2 a * interp2 b
  | Div_ a b -> 
      let vb = interp2 b in
      if vb = 0 then 0
      else interp2 a / vb
*)
