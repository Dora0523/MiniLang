# MiniLang
Create a mini programming language using Ocaml
explored concepts such as free variables, substitution, evaluation, type checking, and type inference.

SOME EXAMPLES OF MINI LANG
#EX1.
(* (fun (x: int, y: int) => (x * x) + (y * y)). *)



    Fn ([("x", Int); ("y", Int)],

           Primop (Plus,
      
              [Primop (Times, [Var "x"; Var "x"]);
              
               Primop (Times, [Var "y"; Var "y"])]
               
              )
     
     )



#EX2.
(* let f = (fun (x: int, y: int) => (x * x) + (y * y)) in  f (3, 4). *)

      Let ("f", ex1, Apply (Var "f", [I 3; I 4]))


