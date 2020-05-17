(* TODO: Write a good set of tests for unused_vars. *)
let unused_vars_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (Let ("x", I 1, I 5), ["x"]);
  (Rec ("x", Int, Var "x"), []);
  (Rec ("x", Int, Fn ([("x", Int)],Var "x"))
  , ["x"]);
  (Fn ([("x", Int);("y", Int)],Var "x"), ["y"]);
  (Fn ([("x", Int)],Var "x"), []);
  (Apply ( Fn ([("x", Int);("y", Int)], Primop(Plus, [Var "x"; Var"y"]))
         , [I 1; I 3]), [])

]

(* TODO: Implement the missing cases of unused_vars. *)
let rec unused_vars =
  function
  | Var _ | I _ | B _ -> []
  | If (e, e1, e2) -> unused_vars e @ unused_vars e1 @ unused_vars e2
  | Primop (_, args) ->
      List.fold_left (fun acc exp -> acc @ unused_vars exp) [] args
  | Let (x, e1, e2) ->
      let unused = unused_vars e1 @ unused_vars e2 in
      if List.mem x (free_variables e2) then
        unused
      else
        x :: unused

  | Rec (x, _, e) -> 
      if List.mem x (free_variables e) then [] @ unused_vars e
      else [x] @ unused_vars e
  
  
  
  | Fn (xs, e) -> 
      (let (namelst,tplst) = List.split (xs) in
       unused_vars e @ delete (free_variables e) namelst 
      ) 

  | Apply (e, es) -> 
      (unused_vars e) @ List.fold_left (fun b a -> unused_vars a @ b) [] es
                  
      
      
      
(* TODO: Write a good set of tests for subst. *)
(* Note: we've added a type annotation here so that the compiler can help
   you write tests of the correct form. *)
let subst_tests : (((exp * name) * exp) * exp) list = [
  (* An example test case. If you have trouble writing test cases of the
     proper form, you can try copying this one and modifying it.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (((I 1, "x"), (* [1/x] *)
    (* let y = 2 in y + x *)
    Let ("y", I 2, Primop (Plus, [Var "y"; Var "x"]))),
   (* let y = 2 in y + 1 *)
   Let ("y", I 2, Primop (Plus, [Var "y"; I 1])));
  
  
  
  (********REC*)
  (((I 1, "x"), (* [1/x] *) 
    Rec ("x", Int, Var "x")),
   Rec ("x", Int, Var "x")); 
  
  (((I 1, "x"), (* [1/x] *) 
    Rec ("y", Int, Var "x")),
   Rec ("y", Int, I 1));
  
  (((Var "x", "y"), (* [x/y] *) 
    Rec ("x", Int, Primop (Plus, [Var "x"; Var "y"]))),
   Rec ("x'", Int, Primop (Plus, [Var "x'"; Var "x"])));
  
  (*********FN*)
  (((I 1, "x"), (* [1/x] *) 
    (Fn ([("x", Int)],Var "x"))),
   (Fn ([("x", Int)],Var "x")));
  
  
  (((I 1, "y"),  
    (Fn ([("x", Int)], Primop(Plus, [Var "x"; Var"y"])))),
   (Fn ([("x", Int)], Primop(Plus, [Var "x"; I 1]))));
  
  (((Var "x", "y"), (* [x/y] *) 
    (Fn ([("x", Int)], Primop(Plus, [Var "x"; Var"y"])))),
   (Fn ([("x'", Int)], Primop(Plus, [Var "x'"; Var"x"]))));
  
  (**********App*)
  (((I 1, "x"), (* [1/x] *) 
    Apply (Var"x", [Var"x";Var"y";Var"z"])),
   Apply (I 1, [I 1;Var"y";Var"z"])); 

  (((Var "x", "y"), 
    Apply (Var"x", [Var"x";Var"y";Var"z"])),
   Apply (Var "x", [Var "x" ;Var"x";Var"z"]))

]

(* TODO: Implement the missing cases of subst. *)
let rec subst ((e', x) as s) exp =
  match exp with
  | Var y ->
      if x = y then e'
      else Var y
  | I n -> I n
  | B b -> B b
  | Primop (po, args) -> Primop (po, List.map (subst s) args)
  | If (e, e1, e2) ->
      If (subst s e, subst s e1, subst s e2)
  | Let (y, e1, e2) ->
      let e1' = subst s e1 in
      if y = x then
        Let (y, e1', e2)
      else
        let (y, e2) =
          if List.mem y (free_variables e') then
            rename y e2
          else
            (y, e2)
        in
        Let (y, e1', subst s e2)

          
  | Rec (y, t, e) -> 
      if x = y then exp
      else
        let (y',exp') =
          if List.mem y (free_variables e')
          then rename y e
          else (y,e)
        in Rec (y',t, subst s exp') 
  

  | Fn (xs, e) -> 
      let namelst = (List.map (fun (n,_) -> n) xs) in
      
      if List.mem x namelst then exp 
        
      else 
        let filtername = List.filter (fun x -> (List.mem x (free_variables e'))) namelst  in 
        let (name',e') = rename_all filtername e in
        let l = List.combine filtername name' in
        let newl =
          
          let rec nlst xs l acc =
            match (xs,l) with
            |(lst,[]) -> (acc @ lst)
            |(((h,e)::tl),((x,x')::xs)) ->
                if h = x
                then nlst (tl) (xs) (acc@ [(x',e)])
                else
                  nlst (tl) (l) (acc@[(h,e)]) 
            |_ ->[]
          in nlst xs l []
        in Fn (newl, subst s e')
        
      
  
  | Apply (e, es) -> 
      Apply (subst s e, List.map (subst s) es) 

and rename x e =
  let x' = freshVar x in
  (x', subst (Var x', x) e)

and rename_all names exp =
  List.fold_right
    (fun name (names, exp) -> 
       let (name', exp') = rename name exp in
       (name' :: names, exp'))
    names
    ([], exp)
    
(* Applying a list of substitutions to an expression, leftmost first *)
let subst_list subs exp =
  List.fold_left (fun exp sub -> subst sub exp) exp subs


(* TODO: Write a good set of tests for eval. *)
let eval_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec and Apply!
  *)
  (Let ("x", I 1, Primop (Plus, [Var "x"; I 5])), I 6);
  (Rec ("x", Int, (Let ("x", I 1, Var"x"))), I 1); 
  
  (Apply (Fn ([("x",Int)], Primop (Plus, [Var "x"; I 1])), [I 1]), (I 2));
  
  (Apply (Fn ([("x",Int); ("y", Int)], Primop (Plus, [Var "x"; Var "y"])), [I 1; I 2]), (I 3));

  (Apply ((Fn ([], (I 1))),[]), (I 1)) ;  
    
  ((( Apply(
       Rec("r", 
           Arrow ([Int;Int],Int), 
           (Fn ([("x", Int);("y",Int)], 
                If ((Primop (LessThan, [Var"x"; I 5]),
                     (Apply(Var "r", [(Primop (Plus,[Var "x"; I 1]));Var "y"])),
                     (Var"y")))
               ))),
       [I 3; I 5]))), I 5)
]

(* TODO: Implement the missing cases of eval. *)
let rec eval exp =
  match exp with
  (* Values evaluate to themselves *)
  | I _ -> exp
  | B _ -> exp
  | Fn _ -> exp

  (* This evaluator is _not_ environment-based. Variables should never
     appear during evaluation since they should be substituted away when
     eliminating binding constructs, e.g. function applications and lets.
     Therefore, if we encounter a variable, we raise an error.
*)
  | Var x -> raise (Stuck (Free_variable x))

  (* Primitive operations: +, -, *, <, = *)
  | Primop (po, args) ->
      let args = List.map eval args in
      begin
        match eval_op po args with
        | None -> raise (Stuck Bad_primop_args)
        | Some v -> v
      end

  | If (e, e1, e2) ->
      begin
        match eval e with
        | B true -> eval e1
        | B false -> eval e2
        | _ -> raise (Stuck If_non_true_false)
      end

  | Let (x, e1, e2) ->
      let e1 = eval e1 in
      eval (subst (e1, x) e2)

  | Rec (f, _, e) -> 
      eval (subst (exp,f) e)

  | Apply (e, es) -> 
      match eval e with
      |Fn(xs,exp) ->
          if List.length es != List.length xs then raise (Stuck Arity_mismatch)
          else
            let lst = List.combine (List.map eval es) (List.map (fun (n,t) -> n) xs)
            in eval (subst_list lst exp)
              
      |_ -> raise (Stuck Apply_non_fn)
              

(* TODO: Write a good set of tests for infer. *)
let infer_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (([("x", Int)], Var "x"), Int);
  
  (([], (Fn([("x", Int);("y", Int)], Primop(Plus,[Var"x";Var"y"])))), Arrow ([Int;Int],Int));
  
  (([], (Fn([], I 3))), Arrow ([],Int));
  
  (([], (Fn([("x",Int)], Var"x"))), Arrow ([Int],Int));

  (([], Apply ((Fn([("x", Int)], Var"x")),[I 3])), Int);

  
  (([("x", Int)], (Apply ((Fn([("x", Int);("y", Int)], 
                              Primop(Plus,[Var"x";Var"y"]))),[Var"x";I 3]))), Int);
  
  (([], Apply ((Fn([], I 3)),[])), Int);
  
  (([], (Rec("r", 
             Arrow ([Int;Int],Int), 
             (Fn ([("x", Int);("y",Int)], 
                  If ((Primop (LessThan, [Var"x"; I 5]),
                       (Apply(Var "r", [(Primop (Plus,[Var "x"; I 1]));Var "y"])),
                       (Var"y")))
                 ))))), Arrow([Int;Int],Int))
  

]

(* TODO: Implement the missing cases of infer. *)
let rec infer ctx e =
  match e with
  | Var x ->
      begin
        try lookup x ctx
        with Not_found -> raise (TypeError (Free_variable x))
      end
  | I _ -> Int
  | B _ -> Bool

  | Primop (po, exps) ->
      let (domain, range) = primopType po in
      check ctx exps domain range

  | If (e, e1, e2) ->
      begin
        match infer ctx e with
        | Bool ->
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            if t1 = t2 then t1
            else type_mismatch t1 t2
        | t -> type_mismatch Bool t
      end

  | Let (x, e1, e2) ->
      let t1 = infer ctx e1 in
      infer (extend ctx (x, t1)) e2

  | Rec (f(*name*), t(*type*), e(*exp*)) -> 
      let et = infer (extend ctx (f,t)) e in
      if et<> t then raise (TypeError (type_mismatch t et));
      et

  | Fn (xs, e) -> 
      let (nl,tl) = List.split xs in 
      let t = infer (extend_list (ctx) (xs)) e
      in Arrow (tl,t)
  
  | Apply (e, es) -> 
      begin match infer ctx e with
        |Arrow (tv,exp) -> 
            let l1 = tv in
            let l2 = (List.map (fun x -> infer ctx x) es)
            in
            let rec f l1 l2 =
              match l1,l2 with
              |([],[]) -> exp
              |(t1::ts1),(t2::ts2) -> 
                  if t1 <> t2 then raise (TypeError (type_mismatch t1 t2)) 
                  else f ts1 ts2
              |_ -> raise(TypeError (Arity_mismatch)) 
            in f l1 l2 
        |t -> raise (TypeError( Apply_non_arrow (t)))
      end
  

and check ctx exps tps result =
  match exps, tps with
  | [], [] -> result
  | e :: es, t :: ts ->
      let t' = infer ctx e in
      if t = t' then check ctx es ts result
      else type_mismatch t t'
  | _ -> raise (TypeError Arity_mismatch)
