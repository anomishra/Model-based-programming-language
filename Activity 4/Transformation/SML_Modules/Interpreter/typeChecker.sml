(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)


fun typeCheck( itree(inode("prog",_),
			[
				stmtList1              
			]
		),
	m0
	) = typeCheck(stmtList1, m0)

  | typeCheck( itree(inode("stmt_list",_),
			[
				stmt1,
				stmt_list1
			]
		),
	m0
	) = 
		let
			val m1 = typeCheck(stmt1, m0)
			val m2 = typeCheck(stmt_list1, m1)
		in
			m2
		end

	
  | typeCheck( itree(inode("stmt_list",_),
			[
				epsilon1
			]
		),
	m0
	) = typeCheck(epsilon1, m0)
	
  | typeCheck( itree(inode("epsilon",_),[itree(inode("",_), [] )]),m0) = m0
	
  | typeCheck( itree(inode("stmt",_),
			[
				itree(inode("skip",_),
					[
						epsilon1
					]),
				itree(inode(";",_), [] )
			]
		),
	m0
	) = typeCheck(epsilon1, m0)
	
  | typeCheck(itree(inode("stmt", _),
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
			val t1 = typeOf(expr1, m0)
			val t2 = getType(accessEnv(getLeaf(id1), m0))
		in
			if t1 = t2 then m0 else raise Fail("Type check fail: id  = expr")
		end
			
  | typeCheck(itree(inode("assign",_),
			[
				id1,
				itree(inode("=",_), [] ),
				expr1
			]
		),
	m0
	) =
		let
			val t1 = typeOf(expr1, m0)
			val t2 = getType(accessEnv(getLeaf(id1), m0))
		in
			if t1 = t2 then m0 else raise Fail("Type check fail: id  = expr")
		end
		
  | typeCheck(itree(inode("stmt", _),
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
			val m1 = updateEnv(getLeaf(id1), BOOL, m0)
			val t1 = typeOf(expr1, m0)
			val t2 = getType(accessEnv(getLeaf(id1), m1))
		in
			if t1 = t2 then m1 else raise Fail("Type check fail: bool id  = expr")
		end

		
  | typeCheck(itree(inode("stmt", _),
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
			val m1 = updateEnv(getLeaf(id1), INT, m0)
			val t1 = typeOf(expr1, m0)
			val t2 = getType(accessEnv(getLeaf(id1), m1))
		in
			if t1 = t2 then m1 else raise Fail("Type check fail: int id  = expr")
		end
		
  | typeCheck(itree(inode("stmt", _),
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
	
  | typeCheck(itree(inode("stmt", _),
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
	
  | typeCheck(itree(inode("stmt", _),
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
			val (env1,l1, s1) = typeCheck(stmt_list1, (env0,l0, s0))
			val m2 = (env0,l0, s1)
		in
			m2
		end
		
  | typeCheck(itree(inode("block", _),
			[
				itree(inode("{",_), [] ),
				stmt_list1,
				itree(inode("}",_), [] )
			]
		),
	(env0,l0, s0)
	) = 
		let
			val (env1,l1, s1) = typeCheck(stmt_list1, (env0,l0, s0))
			val m2 = (env0,l0, s1)
		in
			m2
		end
		
  | typeCheck(itree(inode("stmt", _),
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
			val t1  = typeOf(expr1, m0)
			val m1 = typeCheck(block1, m0)
		in
			if t1 = BOOL then m0 else raise Fail("Type check fail: if(expr) block")
		end
	
  | typeCheck(itree(inode("stmt", _),
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
			val t1  = typeOf(expr1, m0)
			val m1 = typeCheck(block1, m0)
			val m2 = typeCheck(block2, m0)
		in
			if t1 = BOOL then m0 else raise Fail("Type check fail: if(expr) block else block")
		end
		
  | typeCheck(itree(inode("stmt", _),
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
			val t1 = typeOf(expr1, m0)
			val m1 = typeOf(inc1, m0)
			val m2 = typeCheck(block1, m0)
			val m3 = typeCheck(assign1, m0)
		in
			if t1 = BOOL then m0 else raise Fail("Type check fail: for(assign; expr; inc) block")
		end
		
  | typeCheck(itree(inode("stmt", _),
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
		let
			val t1  = typeOf(expr1, m0)
			val m1 = typeCheck(block1, m0)
		in
			if t1 = BOOL then m0 else raise Fail("Type check fail: while(expr) block")
		end
		
  | typeCheck(itree(inode("stmt", _),
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
			val t1 = typeOf(expr1, m0)
		in
			if t1 = ERROR then raise Fail("Type check fail: print(expr)") else m0
		end
		
  | typeCheck(itree(inode("stmt", _),
			[
				inc1,
                                itree(inode(";",_), [] )
			]
		),
	m0
	) =
		let 
			val t1 = typeOf(inc1, m0)
		in
			if t1 = INT then m0 else raise Fail("Type check fail: inc")
		end
                
  | typeCheck( itree(inode(x_root,_), children),_) = 
            raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
        
        
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")
  
and typeOf(itree(inode("exprBase", _),[itree(inode("exprId", _),[id1])]),m0) = getType(accessEnv(getLeaf(id1), m0))
  | typeOf(itree(inode("exprBase", _),[itree(inode("exprBool", _),[boolean1])]),m0) =BOOL
  | typeOf(itree(inode("exprBase", _),[itree(inode("exprInt", _),[integer1])]),m0) = INT

  | typeOf(itree(inode("exprBase", _),
				[
					itree(inode("(",_), [] ),
					expr1,
					itree(inode(")",_), [] )
				]
			),
		m0
		) =  typeOf(expr1 ,m0)

  | typeOf(itree(inode("exprBase", _),[inc1]),m0) = typeOf(inc1 ,m0)
  | typeOf(itree(inode("inc", _),[itree(inode("++",_), [] ), id1]), m0) =
		let
			val t1 = getType(accessEnv(getLeaf(id1), m0))    
		in
			if t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("inc", _),[id1,itree(inode("++",_), [] )]), m0) =
		let
			val t1 = getType(accessEnv(getLeaf(id1), m0))    
		in
			if t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("inc", _),[id1,itree(inode("--",_), [] )]), m0) =
		let
			val t1 = getType(accessEnv(getLeaf(id1), m0))    
		in
			if t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("inc", _),[itree(inode("--",_), [] ), id1]), m0) =
		let
			val t1 = getType(accessEnv(getLeaf(id1), m0))    
		in
			if t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("exprBase", _),
			[
				itree(inode("abs",_), [] ),
				itree(inode("(",_), [] ),
				expr1,
				itree(inode(")",_), [] )
			]), m0) =
		let
			val t1 = typeOf(expr1, m0)
		in
			if t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("exprBase", _),
			[
				itree(inode("NOT",_), [] ),
				itree(inode("(",_), [] ),
				expr1,
				itree(inode(")",_), [] )
			]),	m0) =
		let
			val t1 = typeOf(expr1, m0)
		in
			if t1 = BOOL then BOOL
			else ERROR
		end
	
  | typeOf(itree(inode("exprPwr", _),
			[
				exprBase1,
				itree(inode("^",_), [] ),
				exprPwr1
			]),	m0) =
		let
			val t1 = typeOf(exprBase1, m0)
			val t2 = typeOf(exprPwr1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end
	
  | typeOf(itree(inode("exprNeg", _),[itree(inode("-",_), [] ),exprPwr1]),m0) =
		let
			val t1 = typeOf(exprPwr1, m0)
		in
			if t1 = INT then INT
			else ERROR
		end
	
  | typeOf(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("%",_), [] ),
				exprNeg1
			]), m0) =
		let
			val t1 = typeOf(exprMult1, m0)
			val t2 = typeOf(exprNeg1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end
		
  | typeOf(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("/",_), [] ),
				exprNeg1
			]), m0) =
		let
			val t1 = typeOf(exprMult1, m0)
			val t2 = typeOf(exprNeg1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end
	
  | typeOf(itree(inode("exprMult", _),
			[
				exprMult1,
				itree(inode("*",_), [] ),
				exprNeg1
			]), m0) =
		let
			val t1 = typeOf(exprMult1, m0)
			val t2 = typeOf(exprNeg1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end

  | typeOf(itree(inode("exprAdd", _),
			[
				exprAdd1,
				itree(inode("-",_), [] ),
				exprMult1
			]),	m0) =
		let
			val t1 = typeOf(exprAdd1, m0)
			val t2 = typeOf(exprMult1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end
	
  | typeOf(itree(inode("exprAdd", _),
			[
				exprAdd1,
				itree(inode("+",_), [] ),
				exprMult1
			]),	m0) =
		let
			val t1 = typeOf(exprAdd1, m0)
			val t2 = typeOf(exprMult1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
			else ERROR
		end
  | typeOf(itree(inode("exprOr", _),
			[
				exprOr1,
				itree(inode("OR",_), [] ),
				exprAnd1
			]),	m0) =
		let
			val t1 = typeOf(exprOr1, m0)
			val t2 = typeOf(exprAnd1, m0)
		in
			if t1 = t2 andalso t1 = BOOL then BOOL
			else ERROR
		end

  | typeOf(itree(inode("exprAnd", _),
			[
				exprAnd1,
				itree(inode("AND",_), [] ),
				exprEql1
			]),	m0) =
		let
			val t1 = typeOf(exprAnd1, m0)
			val t2 = typeOf(exprEql1, m0)
		in
			if t1 = t2 andalso t1 = BOOL then BOOL
			else ERROR
		end
	
  | typeOf(itree(inode("exprEql", _),
			[
				exprEql1,
				itree(inode("==",_), [] ),
				exprComp1
			]),	m0) =
		let
			val t1 = typeOf(exprEql1, m0)
			val t2 = typeOf(exprComp1, m0)
		in
			if t1 = t2 andalso t1 <> ERROR then BOOL
			else ERROR
		end

  | typeOf(itree(inode("exprEql", _),
			[
				exprEql1,
				itree(inode("!=",_), [] ),
				exprComp1
			]),	m0) =
		let
			val t1 = typeOf(exprEql1, m0)
			val t2 = typeOf(exprComp1, m0)
		in
			if t1 = t2 andalso t1 <> ERROR then BOOL
			else ERROR
		end

  | typeOf(itree(inode("exprComp", _),
			[
				exprComp1,
				itree(inode("<",_), [] ),
				exprAdd1
			]),	m0) =
		let
			val t1 = typeOf(exprComp1, m0)
			val t2 = typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
			else ERROR
		end

  | typeOf(itree(inode("exprComp", _),
			[
				exprComp1,
				itree(inode(">",_), [] ),
				exprAdd1
			]),	m0) =
		let
			val t1 = typeOf(exprComp1, m0)
			val t2 = typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
			else ERROR
		end

  | typeOf(itree(inode("expr", _),[exprOr1]),m0) = typeOf(exprOr1 ,m0)
  | typeOf(itree(inode("exprOr", _),[exprAnd1]),m0) = typeOf(exprAnd1 ,m0)
  | typeOf(itree(inode("exprAnd", _),[exprEql1]),m0) = typeOf(exprEql1, m0)
  | typeOf(itree(inode("exprEql", _),[exprComp1]),m0) = typeOf(exprComp1, m0)
  | typeOf(itree(inode("exprComp", _),[exprAdd1]),m0) = typeOf(exprAdd1, m0)
  | typeOf(itree(inode("exprAdd", _),[exprMult1]),m0) = typeOf(exprMult1, m0)
  | typeOf(itree(inode("exprMult", _),[exprNeg1]),m0) = typeOf(exprNeg1, m0)
  | typeOf(itree(inode("exprPwr", _),[exprBase1]),m0) = typeOf(exprBase1, m0)
  | typeOf(itree(inode("exprNeg", _),[exprPwr1]),m0) = typeOf(exprPwr1, m0)
  | typeOf(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








