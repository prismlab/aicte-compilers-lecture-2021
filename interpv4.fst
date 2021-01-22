module Interpv4

open FStar.Mul

type nat = i:int{i >= 0}

noeq type const : Type -> Type =
  | Nat : nat -> const nat
  | Bool : bool -> const bool
(*
  Concept
  =======
  + Type-level function
*)

noeq type expr : Type -> Type =
  | Add   : expr nat -> expr nat -> expr nat 
  | Sub   : expr nat -> expr nat -> expr nat
  | Mul   : expr nat -> expr nat -> expr nat
  | Div_  : expr nat -> expr nat -> expr nat
  | Eq    : expr nat -> expr nat -> expr bool
  | Ite   : #a:Type -> expr bool -> expr a -> expr a -> expr a
  | Const : #a:Type -> const a -> expr a
(*
  Concept
  =======
  + Polymorphic types
*)


val interp : expr 'a -> const 'a
let rec interp e =
  match e with
  | Const v -> v
  | Add a b ->
      let Nat v1 = interp a in
      let Nat v2 = interp b in
      Nat (v1 + v2)
  | Sub a b -> 
      let Nat v1 = interp a in
      let Nat v2 = interp b in
      if v2 > v1 then Nat 0
      else Nat (v1 - v2)
  | Mul a b -> 
      let Nat v1 = interp a in
      let Nat v2 = interp b in
      Nat (v1 * v2)
  | Div_ a b -> 
      let Nat v1 = interp a in
      let Nat v2 = interp b in
      if v2 = 0 then Nat 0
      else Nat (v1 / v2)
  | Eq a b -> 
      let Nat v1 = interp a in
      let Nat v2 = interp b in 
      Bool (v1 = v2)
  | Ite p t f ->
      let Bool b = interp p in
      if b then interp t else interp f


let e1 = Ite (Eq (Const (Nat 5)) (Const (Nat 6))) (Const (Nat 23)) (Const (Nat 24))

let e2 = Ite (Add (Const (Nat 5)) (Const (Nat 6))) (Const (Nat 23)) (Const (Nat 24))
