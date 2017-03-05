signature SEMANT =
sig
  type ir_code
  val transprog : Absyn.exp -> {exp: ir_code, ty: Types.ty}
end

structure Semant : SEMANT = 
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  val error = ErrorMsg.error
  type ir_code = unit (* not used for the time being *)

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* ...... *)

  fun checkInt ({exp, ty}, pos) = case ty of T.INT => ()
                                     | T.STRING => (error pos "integer required, string found"; ())
                                     | T.NIL => (error pos "integer required, nil found"; ())
                                     | T.UNIT => (error pos "integer required, unit found"; ())
                                     | _ => (error pos "integer required, unknown type found"; ())
  
  fun checkMatchingTypes (ty1, ty2, pos) =
    case (ty1, ty2) of (T.INT, T.INT) => ()
       | (T.STRING, T.STRING) => ()
       | (_, _) => ((error pos "TODO nonmatching types"); ())

  fun checkEqualityTypes ({exp=exp1, ty=ty1}, {exp=exp2, ty=ty2}, pos) =
    case (ty1, ty2) of (T.INT, T.INT) => ()
       | (_, _) => ((error pos "TODO eq and neq only cover ints"); ())

  fun getValue (lst : (S.symbol * T.ty) list, key : S.symbol, pos) =
    case lst of [] => (error pos "record type not found"; T.UNIT)
       | (k, v)::rest => if (key = k) then v else getValue(rest, key, pos)

 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) = 
    (* TODO: figure out uniq stuff (ref unit) *)
  let val typ = S.look (tenv, id (* ARRAY TYPE: type a = array of int *))
  in
    case typ of SOME ty => (T.ARRAY(ty, ref ()), pos)
       | NONE => (error pos "missing type"; (T.ARRAY(T.UNIT, ref ()), pos))
  end
    | transty (tenv, A.NameTy(id, pos)) = (* NAME TYPE: type a = int *)
  let val typ = S.look (tenv, id)
  in
    (T.NAME(id, ref typ), pos)
  end
    | transty (tenv, A.RecordTy fields) = (* RECORD TYPE: type a = {key : int, value : int}*)
    case fields of [] =>
      (T.RECORD([], ref ()), 0)
       | {name, typ, pos}::rest =>
      (T.RECORD(map(
        fn {name, typ, pos} => 
          let val ty = S.look (tenv, typ)
          in
            case ty of NONE => (error pos "unknown type"; (name, T.UNIT))
               | SOME ty => (name, ty)
          end
        ) fields, ref ()), pos)




 (**************************************************************************
  *                   TRANSLATING EXPRESSIONS                              *
  *                                                                        *
  *  transexp : (E.env * E.tenv) -> (A.exp -> {exp : ir_code, ty : T.ty})  *
  **************************************************************************)
  fun transexp (env, tenv) expr =
    let fun g (A.OpExp {left,oper=A.NeqOp,right,pos}) = 
                   (checkEqualityTypes (g left, g right, pos); {exp=(), ty=T.INT})

          | g (A.OpExp {left,oper=A.EqOp,right,pos}) =
                   (checkEqualityTypes (g left, g right, pos); {exp=(), ty=T.INT})

          | g (A.OpExp {left,oper,right,pos}) =
 		   (checkInt (g left, pos);
		    checkInt (g right, pos);
 		    {exp=(), ty=T.INT})

          | g (A.RecordExp {typ,fields,pos}) =
                   (* ... *) {exp=(), ty=T.RECORD ((* ? *) [], ref ())}
          | g (A.StringExp (s, pos)) =
                   (* ... *) {exp=(), ty=T.STRING}
          | g (A.NilExp) =
                   (* ... *) {exp=(), ty=T.NIL}
          | g (A.IntExp i) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.AppExp {func, args, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.SeqExp seqs) =
                   (* Expression sequence *)
            (case seqs of [] => {exp=(), ty=T.UNIT}
               | [(ex, pos)] => (transexp (env, tenv) ex)
               | (ex, pos)::rest => (g (A.SeqExp rest)))
          | g (A.AssignExp {var, exp, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.IfExp {test, then', else' : A.exp option, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.WhileExp {test, body, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.ForExp {var, lo, hi, body, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.BreakExp pos) =
                   (* TODO implement this *) {exp=(), ty=T.INT}
          | g (A.LetExp {decs, body, pos}) =
                   (* let exp *)
                     transexp(transdecs(env, tenv, decs)) body
          | g (A.ArrayExp {typ, size, init, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g _ (* other cases *) = 
                             ((error 0 "unknown expression type"); {exp=(), ty=T.INT})

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (* SIMPLE VAR: a *)
          let val ty = S.look(tenv, id) in
            case ty of NONE => (error pos "unknown type"; {exp=(), ty=T.UNIT})
               | SOME ty => {exp=(), ty=ty}
          end
	  | h (A.FieldVar (v,id,pos)) = (* FIELD VAR: a.key *)
      let val {exp, ty} = h(v) in
        case ty of T.RECORD(fields, uniq) => 
          let val field_ty = getValue(fields, id, pos)
          in
            {exp=(), ty=field_ty}
          end
           | _ => (error pos "not a record"; {exp=(), ty=T.UNIT})
      end

	  | h (A.SubscriptVar (v,exp,pos)) = (* ARRAY SUBSCRIPT VAR: a[23] *)
      let val {exp, ty} = h(v) in
        case ty of T.ARRAY(typ, uniq) => {exp=(), ty=typ}
           | _ => (error pos "not an array"; {exp=(), ty=T.UNIT})
      end

     in g expr
    end

 (**************************************************************************
  *                   TRANSLATING DECLARATIONS                             *
  *                                                                        *
  *  transdec : (E.env * E.tenv * A.dec) -> (E.env * E.tenv)               *
  **************************************************************************)
  and transdec (env, tenv, A.VarDec {var={name, escape}, typ, init, pos}) = 
      (* VARIABLE DECLARATION, TODO: Make sure expression of type NIL is record *)
      let val {exp, ty} = (transexp(env, tenv) init)
      in
        (* first check if constraint *)
        case typ of SOME(symbol, pos) => let val ty2 = S.look (tenv, symbol)
            in
              case ty2 of NONE => ()
                 | SOME ty2 => checkMatchingTypes(ty, ty2, pos)
            end
           | NONE => ();
        (S.enter(env, name, E.VARentry{access=(), ty=ty}), tenv)
      end
    | transdec (env, tenv, A.FunctionDec(declist)) = 
      (* TODO: FUNCTION DECLARATION *) (env, tenv)
    | transdec (env, tenv, A.TypeDec(declist)) = 
      (* TYPE DECLARATION *) 
      case declist of [] => (env, tenv)
         | [{name, ty, pos}] =>
             let val (ty, pos) = transty(tenv, ty)
             in 
               (env, S.enter(tenv, name, ty))
             end
         | {name, ty, pos}::rest => 
             let val (ty, pos) = transty(tenv, ty)
             in 
               transdec(env, S.enter(tenv, name, ty), A.TypeDec(rest))
             end

  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
  

