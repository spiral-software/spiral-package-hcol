
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

update_type := function(vars, newType)
  vars.t := newType;
end;


Unique := (lst) -> 
       FoldL(lst, (b, a)->Concat( b, When(not a in b, [a], [])), []);

SubstList:= function(expr, list_match, list_replace)
   local new_expr, index;
   new_expr := expr;
   for index in [1..Length(list_match)] do
     new_expr := SubstBottomUp(new_expr, @(2).cond(dc->dc=list_match[index]), x->list_replace[index]);
   od;
   return new_expr;
end;



Class(RulesStateHCOL, RuleSet, rec(inType := "SigmaSPL", outType := "SigmaSPL"));
RewriteRules(RulesStateHCOL, rec(
   Constant_PointWise := ARule(OLCompose, [@(1, PointWise, e->Length(Collect(e.op.expr, e.op.vars[1]))=0), @(2)], e->[@(1).val])
));


Class(RulesTerminateReductionHCOL, RuleSet, rec(inType := "SigmaSPL", outType := "SigmaSPL"));
RewriteRules(RulesTerminateReductionHCOL, rec(
     Reduction_GathH := ARule(OLCompose, [@(1, Reduction), @(2, GathH)], 
       e->[ let(o:= @(1).val, i:= Ind(o.N), 
        ISumReduction(i, o.N, o.op, o.idval, o.isSaturated, eT(@(2).val.N, add(i*@(2).val.stride, @(2).val.base)))) ]),

    Reduction_terminate := Rule(@(1, Reduction), e->let(o:= @(1).val, i := Ind(o.N), 
        ISumReduction(i, o.N, o.op, o.idval, o.isSaturated, eT(o.N, i)))),  

	Scat1Union_Gath1 := ARule(OLCompose, [@(1, ScatHUnion, e1->e1.n=1), @(2, GathH, e2->e2.n=1)], 
		e->[ let(
		Print("Scat1Union_Gath1: ", @(1).val.N, " ", @(1).val.base, " ", @(2).val.N, " ", @(2).val.base,"\n"),
		OLCompose(
		  eUnion(@(1).val.N, @(1).val.base),
	      eT(@(2).val.N, @(2).val.base)
		)
	)]),
		
    ScatHUnion_GathH := ARule(OLCompose, [@(1, ScatHUnion), @(2, GathH)], 
        e->[let( i:= Ind(@(1).val.n),	
	  ISumUnion(i, @(1).val.n,
	    OLCompose(
	      eUnion(@(1).val.n, @(1).val.base+@(1).val.stride*i),
	      eT(@(2).val.n, @(2).val.base+@(2).val.stride*i)
	    )
	  )
	)]),

    GathH0_terminate := Rule(@(1, GathH, e->e.n=0), e->eT(0, -1)),
    GathH1_terminate := Rule(@(1, GathH, e->e.n=1), e->eT(@(1).val.N, @(1).val.base)),
    GathHN_terminate := Rule(@(1, GathH, e->e.n>1), 
        e-> let(i := Ind(@(1).val.n), 
	    	  ISumUnion(i, @(1).val.n, 
		    OLCompose(
			eUnion(@(1).val.n, i), 
			eT(@(1).val.N, @(1).val.base+@(1).val.stride*i))))),  

    ScatHUnion0_terminate := Rule(@(1, ScatHUnion, e->e.n=0), e->eUnion(0,-1)),   #eUnion(@(1).val.N, @(1).val.base)),
    ScatHUnion1_terminate := Rule(@(1, ScatHUnion, e->e.n<=1), e->eUnion(@(1).val.N, @(1).val.base)),
    ScatHUnionN_terminate := Rule(@(1, ScatHUnion, e->e.n>1), 
        e-> let(i := Ind(@(1).val.n), 
	       ISumUnion(i, @(1).val.n, 
 	         OLCompose(
			eUnion(@(1).val.N, @(1).val.base+@(1).val.stride*i), 
			eT(@(1).val.n, i)
	         )
               ))
    ) ));


Class(RulesSumsHCOLv2a, RuleSet, rec(inType := "SigmaSPL", outType := "SigmaSPL"));
RewriteRules(RulesSumsHCOLv2a, rec(
    OLCompose_Assoc := ARule(OLCompose, [ @(1,OLCompose) ],  e -> @(1).val.children() ),
    OLCompose_PointWise_PointWise := ARule(OLCompose, [ @(1, PointWise), @(2, PointWise) ],
        e -> [ PointWise(@(1).val.N, Lambda(@(2).val.op.vars, SubstVars(Copy(@(1).val.op.expr),
         rec((@(1).val.op.vars[2].id) := @(2).val.op.vars[2], (@(1).val.op.vars[1].id) := @(2).val.op.expr)))) ]),
    GathH_GathH := ARule(OLCompose, [@(1, GathH), @(2, GathH)],
        e -> [GathH(@(2).val.N, @(1).val.n, @(1).val.base+@(2).val.base, @(1).val.stride*@(2).val.stride)]),
    Reduction_ScatHUnion := ARule(OLCompose, [ @(1, Reduction), @(2, ScatHUnion, e->e.n=1) ], e->[]),
    PointWise_BinOp := ARule(OLCompose, [@(1, PointWise, e->e.N=1), @(2, BinOp, e->e.N=1)],
        e -> [BinOp(1,Lambda(@(2).val.op.vars, @(1).val.op.at(@(2).val.op.expr, V(0))))]),    
    PointWise_ISumUnion :=  ARule(OLCompose, [ @(1, PointWise), @(2, ISumUnion) ],
        e -> [ CopyFields(@(2).val, rec(
            _children :=  List(@(2).val._children, c -> OLCompose(@(1).val, c)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    PointWise_ScatHUnion := ARule(OLCompose, [@(1,PointWise), @(2, ScatHUnion)],
        e -> let(i := Ind(@(2).val.dims()[2]), [@(2).val, PointWise(@(2).val.dims()[2], 
            Lambda([@(1).val.op.vars[1], i], SubstVars(@(1).val.op.expr, rec((@(1).val.op.vars[2].id) := i*@(2).val.stride+@(2).val.base))))])),
    ISumXXX_YYY := ARule(OLCompose, [ @(1, [ISumUnion, ISumReduction]), @(2, [GathH, PointWise, Induction, eT]) ],
        e -> [ CopyFields(@(1).val, rec(
            _children :=  List(@(1).val._children, c -> OLCompose(c, @(2).val)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    SUMUnion_GathH := ARule(OLCompose, [@(1, SUMUnion), @(2, GathH)], 
       e ->[SUMUnion(List(@(1).val._children, c->OLCompose(c, @(2).val)))] ),
    ScatHUnion_SUMUnion := ARule(OLCompose, [ @(1, ScatHUnion), @(2, SUMUnion) ],    
        e -> [SUMUnion(List(@(2).val._children, c->OLCompose(@(1).val,c)))] ),
    ScatHUnion_ISumUnion := ARule(OLCompose, [@(1, ScatHUnion), @(2, ISumUnion)], 
        e -> [ISumUnion(@(2).val.var, @(2).val.domain, OLCompose(@(1).val, @(2).val._children[1]))]),
    ScatHUnion_ScatHUnion := ARule(OLCompose, [@(1, ScatHUnion), @(2, ScatHUnion)], 
        e -> [ScatHUnion(@1.val.N, @(2).val.n, @(1).val.base+@(2).val.base, @(2).val.stride)] ),
    SUMUnion_Assoc := ARule(SUMUnion, [@(1, SUMUnion) ], e->@(1).val.children())
));

Class(RulesSumsHCOLv2b, RuleSet, rec(inType := "SigmaSPL", outType := "SigmaSPL"));
RewriteRules(RulesSumsHCOLv2b, rec(
    OLCompose_Assoc := ARule(OLCompose, [ @(1,OLCompose) ],  e -> @(1).val.children() ),
    OLCompose_PointWise_PointWise := ARule(OLCompose, [ @(1, PointWise), @(2, PointWise) ],
        e -> [ PointWise(@(1).val.N, Lambda(@(2).val.op.vars, SubstVars(Copy(@(1).val.op.expr),
         rec((@(1).val.op.vars[2].id) := @(2).val.op.vars[2], (@(1).val.op.vars[1].id) := @(2).val.op.expr)))) ]),
    GathH_GathH := ARule(OLCompose, [@(1, GathH), @(2, GathH)],
        e -> [GathH(@(2).val.N, @(1).val.n, @(1).val.base+@(2).val.base, @(1).val.stride*@(2).val.stride)]),
    ISumReduction_PointWise := ARule(OLCompose, [ @(1, ISumReduction), @(2, PointWise) ],
        e -> [ ISumReduction(@(1).val.var, @(1).val.domain, @(1).val.op, @(1).val.idval, @(1).val.isSaturated,
                OLCompose(@(1).val._children[1], @(2).val))]),

    eT_Pointwise := ARule(OLCompose, [@(1, eT, e->IsVar(e.base)), @(2, PointWise)],      
         e -> let(i := Ind(1),
	     [PointWise(1, Lambda(
                SubstVars(Copy(@(2).val.op.vars), rec((@(2).val.op.vars[2].id):=i)),
                SubstVars(Copy(@(2).val.op.expr), rec((@(2).val.op.vars[2].id):=@(1).val.base)))), @(1).val])),
    ISumXXX_YYY := ARule(OLCompose, [ @(1, [ISumUnion, ISumReduction]), @(2, [GathH, PointWise, Induction, eT]) ],
        e -> [ CopyFields(@(1).val, rec(
            _children :=  List(@(1).val._children, c -> OLCompose(c, @(2).val)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    eT_ISumUnion := ARule(OLCompose, [ @(1, eT), @(2, ISumUnion, e->ObjId(e._children[1]._children[1])=eUnion)],
        e -> [ Drop(SubstVars(Copy(@(2).val._children[1]._children), rec((@(2).val.var.id) := (@(1).val.base)) ), 1)]),
    eT_Induction := ARule(OLCompose, [@(1, eT), @(2, Induction)],
        e -> [Inductor(@(2).val.N, @(1).val.base, @(2).val.op, @(2).val.initval)]),
  PointWise_ISumUnion :=  ARule(OLCompose, [ @(1, PointWise), @(2, ISumUnion) ],
        e -> [ CopyFields(@(2).val, rec(
            _children :=  List(@(2).val._children, c -> OLCompose(@(1).val, c)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),

   PointWise := ARule(OLCompose, [@(1, PointWise, e->Length(Collect(e.op.expr, e.op.vars[1]))=0), ...],
       e -> [@(1).val])
));





Class(RulesSumsHCOL, RuleSet, rec(inType := "SigmaSPL", outType := "SigmaSPL"));
RewriteRules(RulesSumsHCOL, rec(
    OLCompose_Assoc := ARule(OLCompose, [ @(1,OLCompose) ],  e -> @(1).val.children() ),
    OLCompose_PointWise_PointWise := ARule(OLCompose, [ @(1, PointWise), @(2, PointWise) ], 
        e -> [ PointWise(@(1).val.N, Lambda(@(2).val.op.vars, SubstVars(Copy(@(1).val.op.expr), 
         rec((@(1).val.op.vars[2].id) := @(2).val.op.vars[2], (@(1).val.op.vars[1].id) := @(2).val.op.expr)))) ]),
    PointWise_ISumUnion :=  ARule(OLCompose, [ @(1, PointWise), @(2, ISumUnion) ],
        e -> [ CopyFields(@(2).val, rec(
            _children :=  List(@(2).val._children, c -> OLCompose(@(1).val, c)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    PointWise_ScatHUnion := ARule(OLCompose, [@(1,PointWise), @(2, ScatHUnion)],
        e -> let(i := Ind(@(2).val.dims()[2]), [@(2).val, PointWise(@(2).val.dims()[2], 
            Lambda([@(1).val.op.vars[1], i], SubstVars(@(1).val.op.expr, rec((@(1).val.op.vars[2].id) := i*@(2).val.stride+@(2).val.base))))])),
    Reduction_ISumReduction :=  ARule(OLCompose, [ @(1, Reduction), @(2, ISumUnion) ],
        e -> [ ISumReduction(@(2).val.var, @(2).val.domain, @(1).val.op, @(1).val.idval, @(1).val.isSaturated,
               OLCompose(@(1).val, @(2).val._children[1]))]),
    Reduction_ScatHUnion := ARule(OLCompose, [ @(1, Reduction), @(2, ScatHUnion, e->e.n=1) ], e->[]),
    ISumReduction_PointWise := ARule(OLCompose, [ @(1, ISumReduction), @(2, PointWise) ],
        e -> [ ISumReduction(@(1).val.var, @(1).val.domain, @(1).val.op, @(1).val.idval, @(1).val.isSaturated,
                OLCompose(@(1).val._children[1], @(2).val))]),
    eT_Pointwise := ARule(OLCompose, [@(1, eT, e->IsVar(e.base)), @(2, PointWise)], 
        e -> let(i := Ind(1), 
            [PointWise(1, Lambda(
                SubstVars(Copy(@(2).val.op.vars), rec((@(2).val.op.vars[2].id):=i)),
                SubstVars(Copy(@(2).val.op.expr), rec((@(2).val.op.vars[2].id):=@(1).val.base)))), @(1).val])),
    ISumXXX_YYY := ARule(OLCompose, [ @(1, [ISumUnion, ISumReduction]), @(2, [GathH, PointWise, Induction, eT]) ],
        e -> [ CopyFields(@(1).val, rec(
            _children :=  List(@(1).val._children, c -> OLCompose(c, @(2).val)),
            dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    GathH_GathH := ARule(OLCompose, [@(1, GathH), @(2, GathH)],
        e -> [GathH(@(2).val.N, @(1).val.n, @(1).val.base+@(2).val.base, @(1).val.stride*@(2).val.stride)]),
    PointWise_BinOp := ARule(OLCompose, [@(1, PointWise, e->e.N=1), @(2, BinOp, e->e.N=1)],
        e -> [BinOp(1,Lambda(@(2).val.op.vars, @(1).val.op.at(@(2).val.op.expr, V(0))))]),
    eT_Induction := ARule(OLCompose, [@(1, eT), @(2, Induction)],
        e -> [Inductor(@(2).val.N, @(1).val.base, @(2).val.op, @(2).val.initval)]),
    ScatHUnion_ScatHUnion := ARule(OLCompose, [@(1, ScatHUnion), @(2, ScatHUnion)], 
        e -> [ScatHUnion(@1.val.N, @(2).val.n, @(1).val.base+@(2).val.base, @(2).val.stride)] )
));

Class(ToVectors, HierarchicalVisitor, rec(
    __call__ := meth(arg)
    local res;
        res := ApplyFunc(arg[1].visit, arg{[2..Length(arg)]});
       return res;
    end,
    PointWise := (self, o, opts) >> let(
      new_i := Ind(4), new_var := var.fresh_t("r", TReal), times := (o.N - Mod(o.N, 4))/4,
      DirectSum(
        List([0..times-1], i->PointWise(4, Lambda([new_var, new_i], new_var*i)) ),
	PointWise(Mod(o.N, 4), o.op)
      ) 
    )
));

max_value := var("max_val", TReal);
max_err := var("max_err", TReal);
Class(RulesErrorHCOL, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesErrorHCOL, rec(
  assign_const := Rule([@(1, assign), @(2, var), @(3, Value, v->v<>0)], 
					e->assign(@(2).val, @(3).val+@(3).val*max_err) ),
  assign_nth := Rule([@(1, assign), @(2, var), @(3, nth)], 
					e->assign(@(2).val, max_value+max_value*max_err) )
));


Class(RulesCodeHCOL, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesCodeHCOL, rec(
#only assignments to state but state is not used

	simplify_state := Rule(@@(1, decl, (e, cx)->(
	  let(
	  Length(Collect(e.cmd, decl))=0 and 
	  IsBound(cx.opts.state) and	  
	  Length(Collect(e.cmd, @(1,nth).cond(j->IsVar(j.loc) and j.loc.id=cx.opts.state.id))) > 0 and 
	  Length(Collect(e.cmd, @(1,nth).cond(j->IsVar(j.loc) and j.loc.id=cx.opts.state.id)))=Length(Collect(e.cmd, @(1, assign).cond(i->ObjId(i.loc)=nth and i.loc.loc.id = cx.opts.state.id))) ))),
	  (e, cx)-> let(Print("Remove State:\n", @@(1).val, "\n"), SubstTopDown(@@(1).val, [@(2, assign), @(3, nth).cond(i->i.loc.id=cx.opts.state.id), @(4)], j->skip()))),	

    chain_chain := Rule(@(1, chain, e->ObjId(e.cmds[1])=chain),   
        e -> let(chain(Concat(@(1).val.cmds[1].cmds, Drop(@(1).val.cmds, 1))))),

	#replaces TArray of length one with a scalar variable
    scalarize1 := Rule(@(1, decl, e->Length(Filtered(e.vars, i->ObjId(i.t)=TArray and i.t.size=1))>=1),
        e->let(							
			oldvar := Filtered(e.vars, i->ObjId(i.t)=TArray and i.t.size=1)[1], 
			Print("Scalarizing ", oldvar, "\n"),
		
			tmp := Collect(@(1).val, [@(5, assign), @(6).cond(ee->IsNth(ee) and ee.loc.id=oldvar.id), @(7)]),
			newType := UnifyTypes(List(tmp, i->i.exp.t)),
			newvar := var.fresh_t("s", newType),
			Print("Scalarizing ", oldvar, " with ", newvar, " of type: ", newType, "\n"),
			
		
            decl(
                SubstVars(@(1).val.vars, rec((oldvar.id):=newvar)),
                SubstTopDown(@(1).val.cmd, [@(2, nth), @(3).cond(e->IsVar(e) and e.id=oldvar.id), @(4).cond(e->IsValue(e) and e.v = 0)],
                    i->newvar)  
            ))),

	#replace each fixed index array reference (i.e. nth(X, i), where i is a constant value) with a variable
	#This can only be done if there are no array references to X that is variable (this is to prevent potential aliasing)
    scalarize_const := Rule(@(1, decl, e->Length(Filtered(Filtered(e.vars, j->IsArray(j.t)), k->ForAll(Collect(e.cmd, [@(2, nth), @(3, var, u->u.id=k.id), @(4)]), j->IsValue(j.idx))))>=1),
        e->let(
			oldvar := Filtered(Filtered(e.vars, j->IsArray(j.t)),   #find all array variables
	           k->ForAll(Collect(e.cmd, [@(2, nth), @(3, var, u->u.id=k.id), @(4)]), j->IsValue(j.idx)))[1],   #make sure only const index
			 			
            newvars := List([1..oldvar.t.size], j->var.fresh_t("q", oldvar.t.t)), 
            cmmd := @(1).val.cmd,
            lst := List([0..Length(newvars)-1], i->[i, newvars[i+1]]),
            f := (c,l)->SubstTopDown(c, [@(2, nth), @(3).cond(k->IsVar(k) and k.id=oldvar.id), @(4).cond(j->IsValue(j) and j.v = l[1])], i->l[2]),
            Print("Scalarize_const: ",oldvar,":: ", newvars, "\n"),
            decl(Concat(Filtered(@(1).val.vars, j->j.id <> oldvar.id), newvars), FoldL(lst, f, cmmd))
        )),
		
    chain_xyz_chain := ARule(chain, [@(1), @(2, chain)], 
        e->[chain(Concat([@(1).val], @(2).val.cmds))]),
    chain_chain_xyz := ARule(chain, [@(1, chain), @(2)], 
        e->[chain(Concat(@(1).val.cmds), [@(2).val])]),

    chain_creturn := ARule(chain, [@(1, creturn), @(2)], 
        e->[chain(Concat([@(2).val], [@(1).val]))] ),

    loop_pull_cond_1 := Rule([@(1, loop), @(2), @(3), [@(4, chain),  [@(5, assign), @(6,var), 
            [@(7,cond), @(8,eq, e->e.args[1]=@(2).val and e.args[2].v=0), @(9), @(10)]],...]],
        e->let(
	   chain(assign(@(6).val, @(9).val), loop(@(1).val.var, @(1).val.range, chain([assign(@(6).val, @(10).val)]::Drop(@(4).val.cmds,1)))))),

	   copyprop_var_val := Rule(@(1, decl, e->let(
		   #only propagate values if the variable is SSA and only if it is within a basic block
		   cnds := Collect(e.cmd, [assign, @(2, var, ee->ee in e.vars), @(3, Value)]),
		   actual_cnds := Filtered(cnds, i->Length(Collect(e.cmd, [assign, @(8, var, ee->ee.id = i.loc.id), @(9)]))=1),
		   #Print("CopyProp: ", cnds, "\n\n", e.cmd, "\n\n", actual_cnds, "\n"),
		   Length(actual_cnds) >= 1 and Length(Collect(e.cmd, [assign, @(4, var, ee->ee.id = actual_cnds[1].loc.id), @(5)]))=1)),
		e->let(			
			all_assigned_value := Collect(@(1).val.cmd, [assign, @(6, var, ee->ee in e.vars), @(7, Value)]),
			assigned_var_value := Filtered(all_assigned_value, i->Length(Collect(@(1).val.cmd, [assign, @(8, var, ee->ee.id = i.loc.id), @(9)]))=1)[1],
		   #Print("CopyProp_value: ", assigned_var_value, "\n"),
			decl(Filtered(@(1).val.vars, j->j.id<>assigned_var_value.loc.id), 
				 SubstVars(@(1).val.cmd, rec((assigned_var_value.loc.id) := assigned_var_value.exp)))
		)
       ),

	   copyprop_var_var := Rule(@(1, decl, e->let(
		   #only propagate var if the assigned variable is SSA
           cnds := Collect(e.cmd, [assign, @(2, var, ee->ee in e.vars), @(3, var, e->e.id<>@(2).val.id)]),
           Length(cnds)>=1 and cnds[1].loc in e.vars and Length(Collect(e.cmd, [assign, @(4, var, ee->ee.id=cnds[1].loc.id), @(5)]))=1)), 
        e->let(				
			   acnds := Collect(@(1).val.cmd, [assign, @(7, var, ee->ee in e.vars), @(8, var, e->e.id<>@(7).val.id)]), 
			   atests := Collect(e.cmd, [assign, @(9, var, ee->ee.id=acnds[1].loc.id), @(5)]),
			   a := atests[1],
			   decl(Filtered(@(1).val.vars, j->j <>a.loc), SubstVars(@(1).val.cmd, rec((a.loc.id) := a.exp))))),

    drop_selfassign_var := ARule(chain, [@(1, assign, e->IsVar(e.loc) and IsVar(e.exp) and e.exp=e.loc), @(2)], 
        e->let(
		[@(2).val])), 
	
    drop_selfassign2 := ARule(chain, [@(1, assign, e->e.exp=e.loc), @(2)], 
        e->[@(2).val]), 

	
	#this drops unused variables i.e. variables that are declared but not used.
    drop_unused_var := Rule(@(1, decl, e-> let(v := Collect(e.cmd, var), Filtered(e.vars, k->not k in v))<> []),
        e->let(v := Collect(@(1).val.cmd, var), 
            decl(Filtered(@(1).val.vars, k->k in v), @(1).val.cmd))),

	drop_unused_assign := Rule(@(1, decl, e->
			Filtered(List(e.vars, v->Collect(e.cmd, v)), l->Length(l)=1)<>[]) , 
	e->let(
      unused := Filtered(List(e.vars, v->Collect(e.cmd, v)), l->Length(l)=1)[1],
	  empty_list := List([1..Length(unused)], i->skip()),
	  target_list := Filtered(Collect(@(1).val.cmd, assign), a->a.loc in unused),
	  Print("Unused assignements:\n", target_list, "\n\n"),	  
	  decl(Filtered(@(1).val.vars, k->not k in unused), SubstList(@(1).val.cmd, target_list, empty_list))
	)),			
			
    loop_decl := Rule(@(1, loop, e->ObjId(e.cmd)=decl and Length(Collect(e.cmd, decl))=1 and Length(Collect(e.cmd, chain))<=1), 
        e -> decl(@(1).val.cmd.vars, loop(@(1).val.var, @(1).val.range, @(1).val.cmd.cmd))),

    chain_xyz_decl := ARule(chain, [@(1), @(2, decl)], 
        e->[decl(@(2).val.vars, chain(@(1).val, @(2).val.cmd))]),

    chain_decl := Rule(@(1, chain, e->ObjId(e.cmds[1])=decl), 
        e -> decl(@(1).val.cmds[1].vars, chain(Concat([@(1).val.cmds[1].cmd], Drop(@(1).val.cmds, 1))))),
    decl_decl := Rule(@(1, decl, e->ObjId(e.cmd)=decl), 
        e -> decl(Set(Concat(@(1).val.vars, @(1).val.cmd.vars)), @(1).val.cmd.cmd)),
));


Class(RulesHCOLnoAbsMax, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesHCOLnoAbsMax, rec(
    abs_cond := Rule([@(1, assign), @(2), @(3, abs)], 
        e->let(s := var.fresh_t("w", @(3).val.t), decl(s, chain(assign(s, @(3).val.args[1]), assign(@(1).val.loc, cond(geq(s, V(0)), s, neg(s))))))),
    max_cond := Rule(@(1, max), 
        e->cond(geq(@(1).val.args[1], @(1).val.args[2]), @(1).val.args[1], @(1).val.args[2])),
));

Class(RulesUnrollHCOL, RuleSet, RulesStrengthReduce, RulesCodeHCOL, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesUnrollHCOL, rec(
    unroll_wo_decl := Rule(@@(1, [loopn, loop], 
       (e, cx) -> Length(Collect(e.cmd, loop))=0 and
                  Length(Collect(e.cmd, decl))=0 and
	          e.var.range <= When(IsBound(cx.opts) and IsBound(cx.opts.globalUnrolling),
		       	                                           cx.opts.globalUnrolling,
                                              5)),
       (e,cx)->let(i := @@(1).val.var, 
	               rng := @@(1).val.range, 
		       vvars := Filtered(Collect(@@(1).val.cmd, var), j->j.t in [TReal, TDouble]),

           chain(	      
	      List(rng, j->let( 
		    ssvars := FoldL([[i, V(j)]], (b, a)->CopyFields(rec((a[1].id):= a[2]), b), rec()),
		    new_cmd := SubstVars(Copy(@@(1).val.cmd), ssvars),
 		    new_cmd )) 
    ))) ,			       
    unroll_w_decl := Rule(@@(1, [loop, loopn], 
           (e,cx)->Length(Collect(e.cmd, loop))=0 and 
				   Length(Collect(e.cmd, decl))=1 and
	           e.var.range <= When(IsBound(cx.opts) and IsBound(cx.opts.globalUnrolling),
           	                                          cx.opts.globalUnrolling,
                                              5)),
           (e,cx)->let(i := @@(1).val.var, 
	               rng := @@(1).val.range, 
		       vvars := Filtered(Collect(@@(1).val.cmd, var), j->j.t in [TReal, TDouble]),
		       
		       localvar := Collect(@@(1).val.cmd, decl)[1].vars,  

           chain(	      
	      List(rng, j->let( 

	      		        nvars :=FoldL(localvar, (b,a)->Concat([[a, var.fresh_t("u", a.t)]], b), [[i, V(j)]] ),
	      		        ssvars := FoldL(nvars, (b, a)->CopyFields(rec((a[1].id):= a[2]) , b), rec()),
						svars := FoldL(nvars, (b, a)->Concat( When(IsVar(a[2]) or a[2] in b, [a[2]], []), b), []),

				new_cmd := SubstVars(Copy(@@(1).val.cmd.cmd), ssvars),

				decl(svars, new_cmd) )

                                #decl(svars, new_cmd ) )
             ))
	  )
   )	
));

RewriteRules(RulesStrengthReduce, rec(
	addsub00 := Rule([@(1, addsub_2x64f), @(2).cond(e->Cond(IsValue(e), isValueZero(e), e=0)), _0], 
		e->@(2).val)
));

Class(RulesUnifyType, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesUnifyType, rec(
    unify_value := Rule(@(1,assign, e-> IsValue(e.exp) and IsVar(e.loc) and e.loc.t <> e.exp.t),
                        e->let(
                            newtype := UnifyTypes([@(1).val.exp.t, e.loc.t]),
                            Print("Unifying Type from a value to ", newtype,"\n"),
                            #if the newtype is the same as the loc, then need to cast the value
                            #else error, upcast the type of the variable since we are losing info.
                            Cond(newtype=e.loc.t, 
                            assign(@(1).val.loc, tcast(newtype, @(1).val.exp)),
                            let(
                            update_type(@(1).val.loc, newtype),
                            assign(@(1).val.loc, @(1).val.exp)
                            ))
                        )),
	unify_vartype := Rule(@(1,assign,e->IsVar(e.loc) and not IsValue(e.exp) and e.loc.t <> e.exp.computeType()),
	   e->let(
		  oldtype := @(1).val.exp.t,
		  newtype := @(1).val.exp.computeType(),
		  Print("Unifying Type from ", oldtype, " to ", newtype,"\n"),
		  update_type(@(1).val.loc, newtype),
		  assign(@(1).val.loc, @(1).val.exp)
	   )),
));
RulesTypeHCOL := CopyFields(MergedRuleSet(RulesUnifyType), 
    rec(inType:="iCode", outType := "iCode"));



RulesOrigCodeUnrollHCOL := CopyFields(MergedRuleSet(RulesUnrollHCOL, RulesStrengthReduce, RulesCodeHCOL, RulesHCOLnoAbsMax), 
    rec(inType:="iCode", outType := "iCode"));


RulesCodeUnrollHCOL := CopyFields(MergedRuleSet( RulesUnrollHCOL, RulesStrengthReduce,  RulesCodeHCOL, RulesHCOLnoAbsMax), 
    rec(inType:="iCode", outType := "iCode"));


RulesCodeNoUnrollHCOL := CopyFields(MergedRuleSet(RulesStrengthReduce, RulesCodeHCOL, RulesHCOLnoAbsMax), 
    rec(inType:="iCode", outType := "iCode"));

#changes behaviour so that Spiral outputs abs(a) and max(a,b) C-code instead of "(a >= b) ? a : b"
RulesCodeUnrollHCOLuseAbsMaxSR := CopyFields(MergedRuleSet(RulesUnrollHCOL, RulesStrengthReduce, RulesCodeHCOL), 
    rec(inType:="iCode", outType := "iCode"));

