(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun M( itree(inode("prog",_),
			[
				stmtList1              
			]
		),
	m0
	) = M(stmtList1, m0)

  | M( itree(inode("stmt_list",_),
			[
				stmt1,
				stmtList1
			]
		),
	m0
	) = M( stmtList1, M(stmt1, m0) )
	
  | M( itree(inode("stmt_list",_),
			[
				epsilon1
			]
		),
	m0
	) = M(epsilon1, m0)
	
  | M( itree(inode("epsilon",_),[itree(inode("",_), [] )]),m0) = m0
	
  | M( itree(inode("stmt",_),
			[
				itree(inode("skip",_),
					[
						epsilon1
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
	) = M(epsilon1, m0)
	
  | M(itree(inode("stmt", _),
			[
				itree(inode("assign",_),
					[
						id1,
						itree(inode("=",_), [] ),
						expr1
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
	) =
		let
			val (dv1, m1)  = E'(expr1, m0)
			val m2 = updateStore(getLoc(accessEnv(getLeaf(id1), m1)), dv1, m1)
		in
			m2
		end
			
  | M(itree(inode("assign",_),
			[
				id1,
				itree(inode("=",_), [] ),
				expr1
			]
		),
	m0
	) =
		let
			val (dv1, m1)  = E'(expr1, m0)
			val m2 = updateStore(getLoc(accessEnv(getLeaf(id1), m1)), dv1, m1)
		in
			m2
		end
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("decl", _),
					[
						itree(inode("type", _),
							[
								itree(inode("bool",_), [] )
							]),
						itree(inode("assign",_),
							[
								id1,
								itree(inode("=",_), [] ),
								expr1
							])
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
		)=
		let
			val (dv1, m1)  = E'(expr1, m0)
			val m2 = updateEnv(getLeaf(id1), BOOL, m1)
			val m3 = updateStore(getLoc(accessEnv(getLeaf(id1), m2)), dv1, m2)
		in
			m3
		end
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("decl", _),
					[
						itree(inode("type", _),
							[
								itree(inode("int",_), [] )
							]),
						itree(inode("assign",_),
							[
								id1,
								itree(inode("=",_), [] ),
								expr1
							])
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
		)=
		let
			val (dv1, m1)  = E'(expr1, m0)
			val m2 = updateEnv(getLeaf(id1), INT, m1)
			val m3 = updateStore(getLoc(accessEnv(getLeaf(id1), m2)), dv1, m2)
		in
			m3
		end	
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("decl", _),
					[
						itree(inode("type", _),
							[
								itree(inode("int",_), [] )
							]),
						id1
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
	) = updateEnv(getLeaf(id1), INT, m0)
	
  | M(itree(inode("stmt", _),
			[
				itree(inode("decl", _),
					[
						itree(inode("type", _),
							[
								itree(inode("bool",_), [] )
							]),
						id1
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
	) = updateEnv(getLeaf(id1), BOOL, m0)
	
  | M(itree(inode("stmt", _),
			[
				itree(inode("block", _),
					[
						itree(inode("{",_), [] ),
						stmt_list1,
						itree(inode("}",_), [] )
					]
				)
			]
		),
	(env0,l0, s0)
	) =
		let
			val (env1,l1, s1) = M(stmt_list1, (env0,l0, s0))
			val m2 = (env0,l0, s1)
		in
			m2
		end
		
  | M(itree(inode("block", _),
			[
				itree(inode("{",_), [] ),
				stmt_list1,
				itree(inode("}",_), [] )
			]
		),
	(env0,l0, s0)
	) =
		let
			val (env1,l1, s1) = M(stmt_list1, (env0,l0, s0))
			val m2 = (env0,l0, s1)
		in
			m2
		end
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("cond", _),
					[
						itree(inode("if",_), [] ), 
						itree(inode("(",_), [] ),
						expr1, 
						itree(inode(")",_), [] ),
						block1
					]
				)
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(expr1, m0)
		in
			if (value_to_bool(dv1)) then
				let
					val m2 = M(block1, m1)
				in
					m2
				end
			else
				m1    
			end
	
  | M(itree(inode("stmt", _),
			[
				itree(inode("cond", _),
					[
						itree(inode("if",_), [] ), 
						itree(inode("(",_), [] ),
						expr1, 
						itree(inode(")",_), [] ),
						block1,
						itree(inode("else",_), [] ),
						block2
					]
				)
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(expr1, m0)
		in
			if (value_to_bool(dv1)) then
				let
					val m2 = M(block1, m1)
				in
					m2
				end
			else
				let
					val m3 = M(block2, m1)
				in
					m3
				end
		end
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("iterator" ,_),
					[
						itree(inode("for",_), [] ),
						itree(inode("(",_), [] ),
						assign1,
						itree(inode(";",_), [] ),
						expr1,
						itree(inode(";",_), [] ),
						inc1,
						itree(inode(")",_), [] ),
						block1
					]
				)
			]
		),
	m0
	)=
		let
			val m1 = M(assign1, m0)
			val m2 = N(expr1, inc1, block1, m1)
		in
			m2
		end
		
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("iterator" ,_),
					[
						itree(inode("while",_), [] ),
						itree(inode("(",_), [] ),
						expr1,
						itree(inode(")",_), [] ),
						block1
					]
				)
			]
		),
	m0
	)=
		N'(expr1, block1, m0)
		
  | M(itree(inode("stmt", _),
			[
				itree(inode("print_stmt",_),
					[
						itree(inode("print",_), [] ),
						itree(inode("(",_), [] ), 
						expr1,
						itree(inode(")",_), [] )
					]
				),
                                itree(inode(";",_), [] )
			]
		),
	m0
	)=
		let
			val (dv1, m1) = E'(expr1, m0)
			val dv2 = case dv1 of Boolean dv1 => Bool.toString(dv1)
								| Integer dv1 => Int.toString(dv1)
		in
			print(dv2^"\n");
			m1
		end
		
  | M(itree(inode("stmt", _),
			[
				inc1,
                                itree(inode(";",_), [] )
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(inc1, m0)
		in
			m1
		end

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  | M _ = raise Fail("error in Semantics.M - this should never occur")
  
and N(expr1, inc1, block1, m0) =
    let
		val (v1, m1) = E'(expr1, m0)
    in
        if ( value_to_bool(v1) ) then
			let
				val m2 = M(block1, m1)
				val (v2, m3) = E'(inc1, m2)
				val m4 = N(expr1, inc1, block1, m3)
			in    
				m4
			end
        else
			m1
    end
	
and N'(expr1, block1, m0 ) = 
	let
		val (v1,m1) = E'( expr1, m0 )
	in
		if ( value_to_bool(v1) ) then 
			let
				 val m2 = M( block1, m1 )
				 val m3 = N'( expr1, block1, m2 )
			in
			   m3
			end 
		else m1
	end
	
and E'( itree(inode("exprBase", _),
				[
					itree(inode("exprBool", _),
						[
							boolean1
						]
					)
				]
            ),
    m0
    ) = (Boolean(valOf(Bool.fromString (getLeaf(boolean1)))) , m0)

  | E'( itree(inode("exprBase", _),
				[
					itree(inode("exprInt", _),
						[
							integer1
						]
					)
				]
            ),
    m0
    ) = (Integer(valOf(Int.fromString (getLeaf(integer1)))) , m0)
	
  | E'( itree(inode("exprBase", _),
				[
					itree(inode("exprId", _),
						[
							id1
						]
					)
				]
            ),
    m0
    ) = (accessStore(getLoc(accessEnv(getLeaf(id1), m0)), m0), m0)

  | E'( itree(inode("expr", _),
			[
				exprOr1
			]
		),
	m0
	) = E'(exprOr1, m0)

  | E'(itree(inode("exprOr", _),
			[
				exprOr1,
				itree(inode("OR",_), [] ),
				exprAnd1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprOr1, m0)
			val (dv2, m2) = E'(exprAnd1, m1)
		in
			(Boolean(value_to_bool(dv1) orelse value_to_bool(dv2)), m2)
		end
	
  | E'(itree(inode("exprOr", _),
			[
				exprAnd1
			]
		),
	m0
	) = E'(exprAnd1, m0)
	
  | E'(itree(inode("exprAnd", _),
			[
				exprAnd1,
				itree(inode("AND",_), [] ),
				exprEql1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprAnd1, m0)
			val (dv2, m2) = E'(exprEql1, m1)
		in
			(Boolean(value_to_bool(dv1) andalso value_to_bool(dv2)), m2)
		end
	
  | E'(itree(inode("exprAnd", _),
			[
				exprEql1
			]
		),
	m0
	) = E'(exprEql1, m0)
	
  | E'(itree(inode("exprEql", _),
			[
				exprEql1,
				itree(inode("!=",_), [] ),
				exprComp1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprEql1, m0)
			val (dv2, m2) = E'(exprComp1, m1)
		in
			case dv1 of Boolean dv1 => (Boolean(dv1 <> value_to_bool(dv2)), m2)
					  | Integer dv1 => (Boolean(dv1 <> value_to_int(dv2)), m2)
		end

  | E'(itree(inode("exprEql", _),
			[
				exprEql1,
				itree(inode("==",_), [] ),
				exprComp1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprEql1, m0)
			val (dv2, m2) = E'(exprComp1, m1)
		in
			case dv1 of Boolean dv1 => (Boolean(dv1 = value_to_bool(dv2)), m2)
					  | Integer dv1 => (Boolean(dv1 = value_to_int(dv2)), m2)
		end
		
  | E'(itree(inode("exprEql", _),
				[
					exprComp1
				]
			),
		m0
		) = E'(exprComp1, m0)
		
  | E'(itree(inode("exprComp", _),
			[
				exprComp1,
				itree(inode(">",_), [] ),
				exprAdd1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprComp1, m0)
			val (dv2, m2) = E'(exprAdd1, m1)
		in
			(Boolean(value_to_int(dv1) > value_to_int(dv2)), m2)
		end

  | E'(itree(inode("exprComp", _),
			[
				exprComp1,
				itree(inode("<",_), [] ),
				exprAdd1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprComp1, m0)
			val (dv2, m2) = E'(exprAdd1, m1)
		in
			(Boolean(value_to_int(dv1) < value_to_int(dv2)), m2)
		end
		
  | E'(itree(inode("exprComp", _),
				[
					exprAdd1
				]
			),
		m0
		) = E'(exprAdd1, m0)
		
  | E'(itree(inode("exprAdd", _),
			[
				exprAdd1,
				itree(inode("+",_), [] ),
				exprMult1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprAdd1, m0)
			val (dv2, m2) = E'(exprMult1, m1)
		in
			(Integer(value_to_int(dv1) + value_to_int(dv2)), m2)
		end
  | E'(itree(inode("exprAdd", _),
			[
				exprAdd1,
				itree(inode("-",_), [] ),
				exprMult1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprAdd1, m0)
			val (dv2, m2) = E'(exprMult1, m1)
		in
			(Integer(value_to_int(dv1) - value_to_int(dv2)), m2)
		end

  | E'(itree(inode("exprAdd", _),
				[
					exprMult1
				]
			),
		m0
		) = E'(exprMult1, m0)
		
  | E'(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("*",_), [] ),
				exprNeg1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprMult1, m0)
			val (dv2, m2) = E'(exprNeg1, m1)
		in
			(Integer(value_to_int(dv1) * value_to_int(dv2)), m2)
		end
		
  | E'(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("/",_), [] ),
				exprNeg1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprMult1, m0)
			val (dv2, m2) = E'(exprNeg1, m1)
		in
			(Integer(value_to_int(dv1) div value_to_int(dv2)), m2)
		end
		
  | E'(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("%",_), [] ),
				exprNeg1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprMult1, m0)
			val (dv2, m2) = E'(exprNeg1, m1)
		in
			(Integer(value_to_int(dv1) mod value_to_int(dv2)), m2)
		end
		
  | E'(itree(inode("exprMult", _),
				[
					exprNeg1
				]
			),
		m0
		) = E'(exprNeg1, m0)

  | E'(itree(inode("exprNeg", _),
			[
				itree(inode("-",_), [] ),
				exprPwr1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprPwr1, m0)
		in
			(Integer(~(value_to_int(dv1))), m1)
		end		
		
  | E'(itree(inode("exprNeg", _),
				[
					exprPwr1
				]
			),
		m0
		) = E'(exprPwr1, m0)

  | E'(itree(inode("exprPwr", _),
			[
				exprBase1,
				itree(inode("^",_), [] ),
				exprPwr1
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(exprBase1, m0)
			val (dv2, m2) = E'(exprPwr1, m1)
		in
			(Integer(power(value_to_int(dv1), value_to_int(dv2))), m2)
		end
		
  | E'(itree(inode("exprPwr", _),
				[
					exprBase1
				]
			),
		m0
		) = E'(exprBase1, m0)
		
  | E'(itree(inode("exprBase", _),
				[
					itree(inode("(",_), [] ),
					expr1,
					itree(inode(")",_), [] )
				]
			),
		m0
		) = E'(expr1, m0)
		
  | E'(itree(inode("exprBase", _),
			[
				itree(inode("abs",_), [] ),
				itree(inode("(",_), [] ),
				expr1,
				itree(inode(")",_), [] )
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(expr1, m0)
		in
			(Integer(Int.abs(value_to_int(dv1))), m1)
		end	

  | E'(itree(inode("exprBase", _),
			[
				itree(inode("NOT",_), [] ),
				itree(inode("(",_), [] ),
				expr1,
				itree(inode(")",_), [] )
			]
		),
	m0
	) =
		let
			val (dv1, m1) = E'(expr1, m0)
		in
			(Boolean(not(value_to_bool(dv1))), m1)
		end

  | E'(itree(inode("exprBase", _),
				[
					inc1
				]
			),
		m0
		) = E'(inc1, m0)
		
  | E'(itree(inode("inc", _),
				[
					itree(inode("++",_), [] ), 
					id1
				]
			), 
		m0) =
		let
			val dv1 = accessStore(getLoc(accessEnv(getLeaf(id1), m0)), m0)
			val dv2 = Integer(value_to_int(dv1) + 1)
			val m1 = updateStore(getLoc(accessEnv(getLeaf(id1), m0)), dv2, m0)
		in
			(dv2, m1)
		end

  | E'(itree(inode("inc", _),
				[
					itree(inode("--",_), [] ), 
					id1
				]
			), 
		m0) =
		let
			val dv1 = accessStore(getLoc(accessEnv(getLeaf(id1), m0)), m0)
			val dv2 = Integer(value_to_int(dv1) - 1)
			val m1 = updateStore(getLoc(accessEnv(getLeaf(id1), m0)), dv2, m0)
		in
			(dv2, m1)
		end
		
  | E'(itree(inode("inc", _),
				[
					id1,
					itree(inode("++",_), [] )
				]
			), 
		m0) =
		let
			val dv1 = accessStore(getLoc(accessEnv(getLeaf(id1), m0)), m0)
			val dv2 = Integer(value_to_int(dv1) + 1)
			val m1 = updateStore(getLoc(accessEnv(getLeaf(id1), m0)), dv2, m0)
		in
			(dv1, m1)
		end
		
  | E'(itree(inode("inc", _),
				[
					id1,
					itree(inode("--",_), [] )
				]
			), 
		m0) =
		let
			val dv1 = accessStore(getLoc(accessEnv(getLeaf(id1), m0)), m0)
			val dv2 = Integer(value_to_int(dv1) - 1)
			val m1 = updateStore(getLoc(accessEnv(getLeaf(id1), m0)), dv2, m0)
		in
			(dv1, m1)
		end
		
  | E'(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E' root = " ^ x_root ^ "\n\n")
  
  | E' _ = raise Fail("error in Semantics.E' - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








