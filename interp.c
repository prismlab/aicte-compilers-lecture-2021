#include <stdio.h>
#include <stdlib.h>

typedef enum {
  Const, Add, Sub, Mul, Div, Eq, Ite
} expr_tag;

typedef struct expr {
  expr_tag tag;
  union {
    int int_value;
    struct expr** args;
  } info;
} expr;

int interp (expr* e) {
  int v1, v2, result;

  switch (e->tag) {
    case Const:
      result = e->info.int_value;
      break;
    case Add:
      v1 = interp (e->info.args[0]);
      v2 = interp (e->info.args[1]);
      result = v1 + v2;
      break;
    case Sub:
      v1 = interp (e->info.args[0]);
      v2 = interp (e->info.args[1]);
      result = v1 - v2;
      break;
    case Mul:
      v1 = interp (e->info.args[0]);
      v2 = interp (e->info.args[1]);
      result = v1 * v2;
      break;
    case Div:
      v1 = interp (e->info.args[0]);
      v2 = interp (e->info.args[1]);
      result = v1 / v2;
      break;
    case Eq:
      v1 = interp (e->info.args[0]);
      v2 = interp (e->info.args[1]);
      result = v1 == v2;
      break;
    case Ite:
      v1 = interp (e->info.args[0]);
      if (v1) {
        result = interp (e->info.args[1]);
      } else {
        result = interp (e->info.args[2]);
      }
      break;
  }
  return result;
}

expr* mk_const (int i)
{
  expr* e = (expr*)malloc(sizeof(expr));
  e->tag = Const;
  e->info.int_value = i;
  return e;
}

expr* mk_binop (expr_tag t, expr* e1, expr* e2)
{
  expr* e = (expr*)malloc(sizeof(expr));
  expr** args = (expr**)malloc(2 * sizeof(expr*));
  e->tag = t;
  e->info.args = args;
  args[0] = e1;
  args[1] = e2;
  return e;
}

expr* mk_add (expr* e1, expr* e2)
{
  return mk_binop(Add,e1,e2);
}

expr* mk_mul (expr* e1, expr* e2)
{
  return mk_binop(Mul,e1,e2);
}

expr* mk_div (expr* e1, expr* e2)
{
  return mk_binop(Div,e1,e2);
}

expr* mk_eq (expr* e1, expr* e2)
{
  return mk_binop(Eq,e1,e2);
}

expr* mk_ite (expr* e1, expr* e2, expr* e3)
{
  expr* e = (expr*)malloc(sizeof(expr));
  expr** args = (expr**)malloc(3 * sizeof(expr*));
  e->tag = Ite;
  e->info.args = args;
  args[0] = e1;
  args[1] = e2;
  args[2] = e3;
  return e;
}

int main () {
  expr* e = mk_ite (mk_eq(mk_add(mk_const(5),
                                 mk_const(6)),
                          mk_const(11)),
                    mk_div(mk_const(12),mk_const(6)),
                    mk_mul(mk_const(3),mk_const(4)));
  printf("%d\n", interp(e));
}
