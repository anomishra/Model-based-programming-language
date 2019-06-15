(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

exception runtime_error;
fun error msg = ( print msg; raise runtime_error );

fun getType(types, loc) = types;
fun getLoc( types, loc ) = loc;

fun value_to_bool(Boolean v) = v
  | value_to_bool(Integer v) = raise Fail("Not a Boolean");
  
fun value_to_int(Integer v) = v
  | value_to_int(Boolean v) = raise Fail("Not an Integer");

fun power (m, n) = if n <= 0 then 1
				   else m * power(m, n-1);

(*accessStore: location * model -> value*)
fun accessStore(loc1, (env,l,store)) =
	let
          val msg = "Error: accessEnv not found.";
          fun aux [] = error msg
            | aux ((loc,value)::store) = 
                     if loc1 = loc then (value)
                     else aux store;
       in
          aux store
       end;
(*accessEnv: identifier  * model -> type * location*)		
fun accessEnv( id1, (env,l,store) ) = 
       let
          val msg = "Error: accessEnv " ^ id1 ^ " not found.";
          fun aux [] = error msg
            | aux ((id,t,loc)::env) = 
                     if id1 = id then (t,loc)
                     else aux env;
       in
          aux env
       end;

		
(*updateEnv: identifier * type * model -> model*)
fun updateEnv(id, types, (env,l, store)) = ((id, types, l)::env,l+1, store);

(*updateStore: location * value * model -> model*)
fun updateStore(loc, value1, (env,l,store)) =
	let
		fun aux(~1, _, []) = []
			|aux(point, newV, []) = (point, newV)::[]
			|aux (point, newV, x::xs) =
				if #1x = point then (point,newV)::aux(~1, newV, xs)
				else x::aux(point, newV, xs);
	in 
		(env, l, aux(loc, value1, store))
	end;


(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)












